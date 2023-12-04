from ryu.base import app_manager
from ryu.controller import mac_to_port
from ryu.controller import ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER, DEAD_DISPATCHER, HANDSHAKE_DISPATCHER
from ryu.controller.handler import set_ev_cls
from ryu.ofproto import ofproto_v1_3 as ofproto
from ryu.ofproto import ofproto_v1_3_parser as of_parser 
from ryu.lib.mac import haddr_to_bin
from ryu.lib.packet import packet
from ryu.lib.packet import arp
from ryu.lib.packet import ethernet
from ryu.lib.packet import ipv4
from ryu.lib.packet import ipv6

from ryu.lib.packet import tcp
from ryu.lib.packet import udp

from ryu.lib.packet import ether_types
from ryu.lib import dpid, mac, ip
from ryu.topology.api import get_switch, get_link
from ryu.app.wsgi import ControllerBase
from ryu.topology import event

from ryu.lib import dpid as dpid_lib
from collections import defaultdict
from operator import itemgetter, attrgetter, mul


from ryu.lib import hub
from ryu import utils

import os
import random
import time
import logging

from ryu.ofproto import ofproto_parser  

from dataclasses import dataclass
import random


TOS_MASK = 0xff00
PORT_NO_MASK = 0x00ff

# Don vi chung la kbps
REFERENCE_BW = int(100000000/1000) # 100 Mbps => kbps
NSEC         = 1000000000

TEST_METER1 = int(REFERENCE_BW*0.1)
TEST_METER2 = int(REFERENCE_BW*0.2)
TEST_METER3 = int(REFERENCE_BW*0.3)
TEST_BE = int(REFERENCE_BW*0.4)

VERBOSE = 0
DEBUGING = 0
BE_METER_ID = 1000

# Mark port has QoS meter
NONE_QOS = 0 
HAVE_QOS = 1

NUM_RANDOM = 0.95

@dataclass
class PortAttr:
    name: str
    have_qos: bool = NONE_QOS 
    available_bw: int = REFERENCE_BW
    physical_bw: int = REFERENCE_BW

@dataclass
class MeterAttr:
    meter_id: int = 0
    in_port: int = 0
    out_port: int = 0
    guaranteed_bw: int =0
    cr_bw_max: int =0
    cr_bw_need: int =0
    last_byte_in: int =0
    last_byte_drop: int =0
    last_sec: int =0
    last_nsec: int =0


test_meter = [MeterAttr(BE_METER_ID,1,2,TEST_BE,TEST_BE),
              MeterAttr(1,1,2,TEST_METER1,TEST_METER1),
              MeterAttr(2,1,2,TEST_METER2,TEST_METER2),
              MeterAttr(3,1,2,TEST_METER3,TEST_METER3)]
class ProjectController(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto.OFP_VERSION]


    def __init__(self, *args, **kwargs):
        super(ProjectController, self).__init__(*args, **kwargs)

        self.switches = [] #[switch_id]
        self.datapath_list = {} #{switch_id:datapath}
        self.sw_port = defaultdict(dict) # {switch_id:{port_no:PortAttr()}}
        

        self.qos_flows_cookie = defaultdict(int) # {switch_id:cookie}
        self.meter_bands = defaultdict(list) #{switch_id:[MeterAttr(),..]}
        self.request_table = defaultdict(list) #{meter_id:[path,bw]}

        
        if DEBUGING == 1:
            self.logger.setLevel(logging.DEBUG)
        else:
            self.logger.setLevel(logging.INFO)
            
        
        # monitor
        self.sleep = 1
        # self.datapaths = {}
        self.monitor_thread = hub.spawn(self._monitor)

    def remove_table_flows(self, datapath, table_id, match, instructions):
        """Create OFP flow mod message to remove flows from table."""
        ofproto = datapath.ofproto
        flow_mod = datapath.ofproto_parser.OFPFlowMod(datapath, 0, 0, table_id,
                                                      ofproto.OFPFC_DELETE, 0, 0,
                                                      1,
                                                      ofproto.OFPCML_NO_BUFFER,
                                                      ofproto.OFPP_ANY,
                                                      ofproto.OFPG_ANY, 0,
                                                      match, instructions)
        return flow_mod
      
    def delete_all_flow(self, datapath, table_id):   
        """Removing all flow entries."""
        parser = datapath.ofproto_parser
        ofproto = datapath.ofproto
        empty_match = parser.OFPMatch()
        instructions = []
        
        # Del/Mod flow table, group table
        flow_mod = self.remove_table_flows(datapath, table_id,
                                        empty_match, instructions)
        print("deleting all flow entries in table ", table_id)   
        datapath.send_msg(flow_mod)

    def get_meters(self, sw_id, port_no):
        ret = []
        bw = 0
        meters = self.meter_bands[sw_id]
        for meter in meters:
            if meter.in_port == port_no or meter.out_port == port_no:
                ret.append(meter)
                bw = bw + meter.cr_bw_need
        return bw,ret
    

    def have_qos_overload_meter(self, port_meters):  
        qos_overload = []
        qos_no_overload = []
        normalize = 0
        qos_excess_bw = 0
        for meter in port_meters:
            if meter.meter_id < BE_METER_ID:
                if meter.cr_bw_need > meter.cr_bw_max:
                    qos_overload.append(meter)
                    normalize += meter.guaranteed_bw
                else:
                    qos_no_overload.append(meter)
                    qos_excess_bw += (meter.cr_bw_max - meter.cr_bw_need)
        return qos_overload, normalize, qos_excess_bw, qos_no_overload
    
    def be_meter_excess_bw(self, port_meters):
        be_meter = None
        excess_bw = 0
        for meter in port_meters:
            if meter.meter_id == BE_METER_ID:
                be_meter = meter
                if meter.cr_bw_need < meter.cr_bw_max:
                    excess_bw = NUM_RANDOM*(meter.cr_bw_max - meter.cr_bw_need)
                    break

        return be_meter, excess_bw

    def remain_be_bw(self, be_meter, port_meters):
        for meter in port_meters:
            if meter != be_meter:
                borrowed_bw = meter.cr_bw_max - meter.guaranteed_bw
                if meter.cr_bw_need <= meter.guaranteed_bw and borrowed_bw >= 0:
                    be_meter.cr_bw_max += borrowed_bw
                    meter.cr_bw_max -= borrowed_bw

    def reset_meter(self, meter, reset_max_limit=False):
        meter.cr_bw_need = 0
        meter.last_byte_in = 0
        meter.last_byte_drop = 0
        meter.last_sec  = 0
        meter.last_nsec  = 0
        
        meter.cr_bw_max = meter.guaranteed_bw if reset_max_limit else meter.cr_bw_max

    def min_bw_algorithm(self):
        for sw_id in self.datapath_list.keys():
            # meters = self.meter_bands[sw_id]
            for port_no in self.sw_port[sw_id].keys():
                port_bw_usaged, port_meters = self.get_meters(sw_id,port_no)
                self.logger.info('port_bw_usaged %s',port_bw_usaged)
                # self.logger.info('port_meters %s', port_meters)
                # Bang thong su dung tren port sap vuot qua nguong vat ly 
                if port_bw_usaged > 0.95 * self.sw_port[sw_id][port_no].physical_bw:
                    for meter in port_meters:    
                        self.logger.info("jump into 1")
                        self.reset_meter(meter,True)
                        self.configure_meter_band(switch=self.datapath_list[sw_id],rate=int(meter.cr_bw_max),
                                                  meter_id=meter.meter_id, command=ofproto.OFPMC_MODIFY)
                else:
                    be_meter, be_excess_bw  = self.be_meter_excess_bw(port_meters)
                    # Nhung luong QoS khong dung het bw phai tra lai cho BE phan da muon
                    self.remain_be_bw(be_meter, port_meters)
                    qos_overload,sum_normalize_qos, qos_excess_bw, qos_no_overload = self.have_qos_overload_meter(port_meters)

                    if be_excess_bw > 0:
                        if qos_overload:
                            # lay bang thong cua BE meter chia cho overloaded QOS meters
                            be_meter.cr_bw_max -= be_excess_bw
                            self.logger.info("jump into 2")
                            self.configure_meter_band(switch=self.datapath_list[sw_id],rate=int(be_meter.cr_bw_max),
                                                    meter_id=be_meter.meter_id, command=ofproto.OFPMC_MODIFY)
                            self.reset_meter(be_meter,False)

                            for meter in qos_overload:
                                meter.cr_bw_max += be_excess_bw*(meter.guaranteed_bw)/sum_normalize_qos
                                self.logger.info("jump into 3")
                                self.configure_meter_band(switch=self.datapath_list[sw_id],rate=int(meter.cr_bw_max),
                                                        meter_id=meter.meter_id, command=ofproto.OFPMC_MODIFY)
                                
                                self.reset_meter(meter,False)
                    else:
                        if not qos_overload:
                            # chia phan bang thong du thua cho BE meter
                            be_meter.cr_bw_max += NUM_RANDOM*qos_excess_bw
                            self.logger.info("jump into 4")
                            self.configure_meter_band(switch=self.datapath_list[sw_id],rate=int(be_meter.cr_bw_max),
                                                    meter_id=be_meter.meter_id, command=ofproto.OFPMC_MODIFY)
                            self.reset_meter(be_meter,False)

    def have_overload_meter_2(self, port_meters):  
        ret = []
        normalize = 0
        qos_excess_bw = 0
        be_meter = None
        for meter in port_meters:
            if meter.meter_id == BE_METER_ID:
                be_meter = meter
            else:
                if meter.cr_bw_need > meter.guaranteed_bw:
                    ret.append(meter)
                    normalize += meter.guaranteed_bw
                else:
                    qos_excess_bw += (meter.guaranteed_bw - meter.cr_bw_need)
        return ret, normalize, qos_excess_bw, be_meter
    
    # def min_bw_algorithm_2(self):
    #     for sw_id in self.datapath_list.keys():
    #         # meters = self.meter_bands[sw_id]
    #         for port_no in self.sw_port[sw_id].keys():
    #             port_bw_usaged, port_meters = self.get_meters(sw_id,port_no)
    #             self.logger.info('port_bw_usaged %s',port_bw_usaged)
    #             # self.logger.info('port_meters %s', port_meters)
    #             meters_overload,sum_normalize_qos, qos_excess_bw, be_meter = self.have_overload_meter(port_meters)

    #             # Neu khong co hoac tat ca meter deu can bang thong thi reset ve trang thai ban dau
    #             if not meters_overload or meters_overload == port_meters:
    #                 for meter in port_meters:
    #                     self.configure_meter_band(switch=self.datapath_list[sw_id],rate=int(meter.guaranteed_bw),
    #                                             meter_id=meter.meter_id, command=ofproto.OFPMC_MODIFY)
    #                     self.reset_meter(meter,True)
    #             else:
    #                 for meter in meters_overload:
    #                     need_borrow = meter.cr_bw_need - meter.guaranteed_bw
    #                     can_borrow_from_be = be_meter.guaranteed_bw*(meter.guaranteed_bw/sum_normalize_qos)
    #                     # QoS meter can them bang thong
    #                     if meter.meter_id != BE_METER_ID:
    #                         # Muon bang thong cua BE truoc
    #                         if need_borrow < can_borrow_from_be:
    #                             be_meter = 
    #                             self.configure_meter_band(switch=self.datapath_list[sw_id],rate=int(be_meter.guaranteed_bw),
    #                                                     meter_id=meter.meter_id, command=ofproto.OFPMC_MODIFY)
    #                             self.reset_meter(meter,True)
                
    #             if be_excess_bw:
    #                 if qos_overload:
    #                     # lay bang thong cua BE meter chia cho overloaded QOS meters
    #                     be_meter.cr_bw_max -= be_excess_bw
    #                     self.logger.info("jump into 2")
    #                     self.configure_meter_band(switch=self.datapath_list[sw_id],rate=int(be_meter.cr_bw_max),
    #                                             meter_id=be_meter.meter_id, command=ofproto.OFPMC_MODIFY)
    #                     self.reset_meter(be_meter,False)

    #                     for meter in qos_overload:
    #                         meter.cr_bw_max += be_excess_bw*(meter.cr_bw_max)/sum_normalize_qos
    #                         self.logger.info("jump into 3")
    #                         self.configure_meter_band(switch=self.datapath_list[sw_id],rate=int(meter.cr_bw_max),
    #                                                 meter_id=meter.meter_id, command=ofproto.OFPMC_MODIFY)
                            
    #                         self.reset_meter(meter,False)
    #             else:
    #                 if not qos_overload:
    #                     # chia phan bang thong du thua cho BE meter
    #                     be_meter.cr_bw_max += NUM_RANDOM*qos_excess_bw
    #                     self.logger.info("jump into 4")
    #                     self.configure_meter_band(switch=self.datapath_list[sw_id],rate=int(be_meter.cr_bw_max),
    #                                             meter_id=be_meter.meter_id, command=ofproto.OFPMC_MODIFY)
    #                     self.reset_meter(be_meter,False)


    def _request_meter_stats(self, datapath, meter_id=ofproto.OFPM_ALL):
        self.logger.debug('send meter stats request: %016x', datapath.id)
        parser = datapath.ofproto_parser

        #Send MeterStatsRequest
        req = parser.OFPMeterStatsRequest(datapath, 0, meter_id=meter_id)
        datapath.send_msg(req)

    def configure_meter_band(self, switch ,rate, burst=0.1, meter_id=BE_METER_ID, command=ofproto.OFPMC_ADD):
        burst_Size = int(rate * burst) # Default burst size = 10% of rate limit
        dropband = of_parser.OFPMeterBandDrop(rate=rate, burst_size=burst_Size) # Only use drop band
        request = of_parser.OFPMeterMod(datapath=switch, 
                                   command=command, 
                                   flags=ofproto.OFPMF_KBPS, 
                                   meter_id=meter_id, 
                                   bands=[dropband])
        switch.send_msg(request)

    def _monitor(self):
                    
        while True:
            self.min_bw_algorithm()

            for switch_id in self.datapath_list.keys():
                dp = self.datapath_list[switch_id]
                # Monitor QoS flow
                # for cookie in self.qos_flows_cookie[switch_id]:
                #     self._request_flow_stats(dp, cookie=cookie)
                # Monitor meter in switches
                if self.meter_bands[switch_id]:
                    self._request_meter_stats(dp)

            hub.sleep(self.sleep)

    @set_ev_cls(ofp_event.EventOFPErrorMsg,
    [HANDSHAKE_DISPATCHER, CONFIG_DISPATCHER, MAIN_DISPATCHER])
    def error_msg_handler(self, ev):
        msg = ev.msg
        ofp = msg.datapath.ofproto
        self.logger.debug(
            "EventOFPErrorMsg received.\n"
            "version=%s, msg_type=%s, msg_len=%s, xid=%s\n"
            " `-- msg_type: %s\n"
            "OFPErrorMsg(type=%s, code=%s, data=b'%s')\n"
            " |-- type: %s\n"
            " |-- code: %s\n"
            " |-- dpid: %s\n"
            ,
            
            hex(msg.version), hex(msg.msg_type), hex(msg.msg_len),
            hex(msg.xid), ofp.ofp_msg_type_to_str(msg.msg_type),
            hex(msg.type), hex(msg.code), utils.binary_str(msg.data),
            ofp.ofp_error_type_to_str(msg.type),
            ofp.ofp_error_code_to_str(msg.type, msg.code),
            msg.datapath.id)
        if msg.type == ofp.OFPET_HELLO_FAILED:
            self.logger.debug(
                " `-- data: %s", msg.data.decode('ascii'))
        elif len(msg.data) >= ofp.OFP_HEADER_SIZE:
            (version, msg_type, msg_len, xid) = ofproto_parser.header(msg.data)
            self.logger.debug(
                " `-- data: version=%s, msg_type=%s, msg_len=%s, xid=%s\n"
                "     `-- msg_type: %s",
                hex(version), hex(msg_type), hex(msg_len), hex(xid),
                ofp.ofp_msg_type_to_str(msg_type))
        else:
            self.logger.warning(
                "The data field sent from the switch is too short: "
                "len(msg.data) < OFP_HEADER_SIZE\n"
                "The OpenFlow Spec says that the data field should contain "
                "at least 64 bytes of the failed request.\n"
                "Please check the settings or implementation of your switch.")
            
    # @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    # def _switch_features_handler(self, ev):
    #     print("switch_features_handler is called")
    #     datapath = ev.msg.datapath
    #     ofproto = datapath.ofproto
    #     parser = datapath.ofproto_parser
    #     match = parser.OFPMatch()
    #     actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,
    #                                       ofproto.OFPCML_NO_BUFFER)]
    #     self.delete_all_flow(datapath,0)
    #     self.delete_all_flow(datapath,1)

    #     self.add_flow(datapath, 0, match, actions)

    # Parsing switch's information
    @set_ev_cls(event.EventSwitchEnter)
    def switch_enter_handler(self, ev):
        switch = ev.switch.dp
        ports = ev.switch.ports
        
        # self.logger.info("ALL_SW: %s",ev.switch)
        
        if VERBOSE == 1:
            print("Switch In: ",switch.id)

        if switch.id not in self.switches:
            self.switches.append(switch.id)
            self.datapath_list[switch.id] = switch
            self.meter_bands[switch.id] = test_meter

            # Add a default Best-effort meter-band in every new switch.
            # self.configure_meter_band(switch ,REFERENCE_BW)
            self.configure_meter_band(switch ,TEST_BE)

            for port in ports:
                port_name = port.name.decode('utf-8')
                # By default, a port has bandwidth = REFERENCE_BW
                #  and doesn't have meter-band limit
                self.sw_port[switch.id][port.port_no] = PortAttr(port_name, NONE_QOS, REFERENCE_BW, REFERENCE_BW)
        
    @set_ev_cls(event.EventSwitchLeave, MAIN_DISPATCHER)
    def switch_leave_handler(self, ev):
        switch = ev.switch.dp.id
        if switch in self.switches:
            self.switches.remove(switch)
            del self.datapath_list[switch]
            del self.adjacency[switch]
            try:
                del self.sw_port[switch]
                del self.meter_bands[switch]
                # del self.flows_cookie[switch]
            except:
                pass

    @set_ev_cls(event.EventLinkAdd, MAIN_DISPATCHER)
    def link_add_handler(self, ev):
        s1 = ev.link.src
        s2 = ev.link.dst
        
        self.adjacency[s1.dpid][s2.dpid] = s1.port_no
        self.adjacency[s2.dpid][s1.dpid] = s2.port_no

    @set_ev_cls(ofp_event.EventOFPMeterStatsReply, MAIN_DISPATCHER)
    def meter_stats_reply_handler(self, ev):
        msg = ev.msg
        dp = msg.datapath
        meters = self.meter_bands[dp.id]
        
        log = []
        for stat in msg.body:
            log.append('meter_id=0x%08x flow_count=%d byte_in_count=%d '
                        'duration_nsec=%d band_stats=%s' %
                        (stat.meter_id, stat.flow_count,
                        stat.byte_in_count, stat.duration_nsec,
                        stat.band_stats))
            for meter in meters:
                if meter.meter_id == stat.meter_id:
                    drop_band = stat.band_stats[0]
                    arrival_sec = float((stat.duration_sec - meter.last_sec) + (stat.duration_nsec - meter.last_nsec)/NSEC)
                    #arival_byte = (stat.byte_in_count - meter.last_byte_in) - (drop_band.byte_band_count - meter.last_byte_drop)
                    arival_byte = stat.byte_in_count - meter.last_byte_in
                    meter.cr_bw_need = int(arival_byte / arrival_sec)
                    meter.cr_bw_need = int((8*meter.cr_bw_need)/1000)
                    meter.last_byte_in = stat.byte_in_count
                    meter.last_byte_drop = drop_band.byte_band_count
                    meter.last_sec = stat.duration_sec
                    meter.last_nsec = stat.duration_nsec
                    self.logger.debug('Meter.last_byte_in: %s\n', meter.last_byte_in)
                    break
                    
        self.logger.debug('MeterStats: %s', log)               
        
    
    # Active only when LLDP packet received
    @set_ev_cls(event.EventLinkDelete, MAIN_DISPATCHER)
    def link_delete_handler(self, ev):
        s1 = ev.link.src
        s2 = ev.link.dst
        # Exception handling if switch already deleted
        try:
            del self.adjacency[s1.dpid][s2.dpid]
            del self.adjacency[s2.dpid][s1.dpid]
        except KeyError:
            pass


                                
                            



                    
                    

