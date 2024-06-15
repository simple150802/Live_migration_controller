from ryu.base import app_manager
from ryu.controller import mac_to_port
from ryu.controller import ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER, DEAD_DISPATCHER, HANDSHAKE_DISPATCHER
from ryu.controller.handler import set_ev_cls
from ryu.ofproto import ofproto_v1_3 
from ryu.ofproto import ofproto_v1_3_parser as ofp_parser 

from ryu.ofproto import ofproto_parser  
from ryu.lib.mac import haddr_to_bin
from ryu.lib.packet import packet
from ryu.lib.packet import arp
from ryu.lib.packet import ethernet
from ryu.lib.packet import ipv4, icmp
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
from libovsdb import libovsdb
import os
import random
import time
import logging

import json
from ryu.lib.ovs import bridge
from ryu.ofproto import nx_match
from dataclasses import dataclass
# Best-effort meter id
BE_METER_ID = 1000
VERBOSE = 0
DEFAULT_BW = 0
NONE_QOS = 0
DEBUGING = 0
SHOW_PATH = 0
IDLE_TIMEOUT = 150
MAX_PATHS = 100
QUEUE_TYPE = 'linux-hfsc'
ovsdb_server = 'tcp:127.0.0.1:6640'
# Cookie mask
COOKIE_MASK = 1 >> 8
@dataclass
class PortAttr:
    name: str
    have_qos: bool = NONE_QOS 
    available_bw: int = DEFAULT_BW

class Ryu_con(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]

    def __init__(self, *args, **kwargs):
        super(Ryu_con, self).__init__(*args, **kwargs)
        # initialize mac address table.
        self.mac_to_port = {}
        self.LEARNING = 1
        self.FLAG = 0
        self.request_id = 1
        self.new_request = False
        
        self.topology_api_app = self
        self.datapath_list = {} #{switch_id:datapath}
        self.arp_table = {} #{'ip' : host}
        self.switches = [] #[switch_id]
        self.hosts = {} #{'host': (dpid, port)}
        self.multipath_group_ids = {}
        self.all_group_id = {}
        self.group_id_count =0
        self.group_ids = []
        self.adjacency = defaultdict(dict) #{dpid: {dpid lân cận: "port sw lân cận cắm với sw chính"}}
        self.bandwidths = defaultdict(lambda: defaultdict(lambda: DEFAULT_BW))
        self.sw_port = defaultdict(dict) #{switch_id:{port_no:PortAttr(name,have_qos,available_bw)}}
        self.count = 0
        self.path_install_cnt = 0
        
        self.max_bw = {}
        self.curr_max_bw = {}
        self.sw_reserve_bw = defaultdict(dict) #store remain banwidth
        self.port_reserve_bw = defaultdict(dict)
        
        self.vx_src_dst = {}
        #self.queue_config: {1: {0: '1000000', 1: '500000'}} nghĩa là cổng 1 có hai hàng đợi với băng thông tương ứng.
        self.queue_config = {}
        self.min_queue_config = {}
        
        self.request_table = {}
        self.host_request = {}
        self.request = {"max-rate":None,"min-rate":None}
        self.vni = None
        self.paths = []
        self.vni_map_src = {}
        self.vni_map_hv = {}
        self.change = False

        self.qos_flows_cookie = defaultdict(int) # {switch_id:cookie}
        self.meter_bands = defaultdict(defaultdict(int)) #{switch_id:{meter_id:(max_rate,in_port,out_port)}}
        
        self.init_bw_max = defaultdict(defaultdict(int)) #{switch_id:{meter_id:init_bw_max}
        self.cr_bw_max = defaultdict(defaultdict(int)) #{switch_id:{meter_id:cr_bw_max}}
        self.cr_bw_usage = defaultdict(defaultdict(int)) #{switch_id:{meter_id:cur_bw_usage}}

        
        if DEBUGING == 1:
            self.logger.setLevel(logging.DEBUG)
        else:
            self.logger.setLevel(logging.INFO)
            
        
        # monitor
        self.sleep = 1
        # self.datapaths = {}
        self.monitor_thread = hub.spawn(self._monitor)
        self.tx_pkt_cur = {}    # currently monitoring TX packets
        self.tx_byte_cur = {}   # currently monitoring TX bytes
        self.tx_pkt_int = {}    # TX packets in the last monitoring interval
        self.tx_byte_int = {}    # TX bytes in the last monitoring interval
        
        
        self.rx_pkt_cur = {}    # currently monitoring TX packets
        self.rx_byte_cur = {}   # currently monitoring TX bytes
        self.rx_pkt_int = {}    # TX packets in the last monitoring interval
        self.rx_byte_int = {}    # TX bytes in the last monitoring interval

    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER) #Waiting to receive SwitchFeatures message cho biết rằng phương thức này sẽ được gọi khi switch gửi thông điệp Features Reply sau khi kết nối.
    def switch_features_handler(self, ev):
        print("switch_features_handler is called")
        datapath = ev.msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser #chứa các lớp và phương thức để tạo các thông điệp OpenFlow.
        # install the table-miss flow entry.
        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,
                                          ofproto.OFPCML_NO_BUFFER)]
        self.delete_all_flow(datapath,0)
        self.delete_all_flow(datapath,1)
        self.add_flow(datapath, 0, match, actions)
    
    # def add_flow(self, datapath, priority, match, actions):
    #     ofproto = datapath.ofproto
    #     parser = datapath.ofproto_parser

    #     # construct flow_mod message and send it.
    #     inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,
    #                                          actions)]
    #     mod = parser.OFPFlowMod(datapath=datapath, priority=priority,
    #                             match=match, instructions=inst)
    #     datapath.send_msg(mod)
    def add_flow(self, datapath, priority, match, actions, idle_timeout=0, buffer_id=None,insts=None,table_id=0):
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,
                                             actions)]
        if insts:
            inst.append(insts)
        if buffer_id:
            mod = parser.OFPFlowMod(datapath=datapath, buffer_id=buffer_id,idle_timeout=idle_timeout,
                                    priority=priority, match=match,
                                    instructions=inst,table_id=table_id)

        else:
            mod = parser.OFPFlowMod(datapath=datapath,idle_timeout=idle_timeout, priority=priority,
                                    match=match, instructions=inst,table_id=table_id)
        datapath.send_msg(mod)

    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        msg = ev.msg
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        # get the received port number from packet_in message.
        in_port = msg.match['in_port']

        # get Datapath ID to identify OpenFlow switches.
        dpid = datapath.id
        self.mac_to_port.setdefault(dpid, {})

        # analyse the received packets using the packet library.
        pkt = packet.Packet(data=msg.data)
        self.logger.info("packet-in %s" % (pkt,))
        pkt_ethernet = pkt.get_protocol(ethernet.ethernet)

        if not pkt_ethernet:
            return
        arp_pkt = pkt.get_protocol(arp.arp)
        dst = pkt_ethernet.dst
        src = pkt_ethernet.src

        if src not in self.hosts:
            self.hosts[src]= (dpid, in_port)
            if VERBOSE == 1:
                print("---------------------------")
                print("\n List Host in Network: ", self.hosts)
                print("\n-------------------------")

        #IPv4 packet
        pkt_ipv4 = pkt.get_protocol(ipv4.ipv4)
        tos = 0 # default TOS bits
        src_port = 0
        dst_port = 0
        ip_proto = -1
        pkt_icmp = pkt.get_protocol(icmp.icmp)

        # avoid broadcast from LLDP
        if pkt_ethernet.ethertype == 35020:
            return
            
        # Drop the IPV6 Packets.
        if pkt.get_protocol(ipv6.ipv6):  
            match = parser.OFPMatch(eth_type=pkt_ethernet.ethertype)
            actions = []
            self.add_flow(datapath, 1, match, actions)
            return None

        #self.logger.info("packet in %s %s %s %s", dpid, src, dst, in_port)
        if arp_pkt:
            self.LEARNING == 1
            if VERBOSE == 1:
                print("datapath id: "+str(dpid))
                print("port: "+str(in_port))
                print(("pkt_eth.dst: " + str(pkt_ethernet.dst)))
                print(("pkt_eth.src: " + str(pkt_ethernet.src)))
                print(("pkt_arp: " + str(arp_pkt)))
                print(("pkt_arp:src_ip: " + str(arp_pkt.src_ip)))
                print(("pkt_arp:dst_ip: " + str(arp_pkt.dst_ip)))
                print(("pkt_arp:src_mac: " + str(arp_pkt.src_mac)))
                print(("pkt_arp:dst_mac: " + str(arp_pkt.dst_mac)))
            src_ip = arp_pkt.src_ip
            dst_ip = arp_pkt.dst_ip
            if arp_pkt.opcode == arp.ARP_REPLY:
                self.arp_table[src_ip] = src #ARP table IP-MAC
                h1 = self.hosts[src]
                h2 = self.hosts[dst]
            #Install path: dpid src, src in_port, dpid dst, dpid in_port, src_ip, dst_ip
            if VERBOSE == 1:
                print("Installing: Src:{}, Src in_port{}. Dst:{}, Dst in_port:{}, Src_ip:{}, Dst_ip:{}".format(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip,dst_port))
                out_port = self.install_paths_arp(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip,ip_proto,dst_port,src_ip, dst_ip, vni)
                self.install_paths_arp(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip,ip_proto,dst_port,src_ip, dst_ip, vni) # reverse
            elif arp_pkt.opcode == arp.ARP_REQUEST:
                if dst_ip in self.arp_table:
                    print("dst_ip found in arptable")
                    self.arp_table[src_ip] = src
                    dst_mac = self.arp_table[dst_ip]
                    h1 = self.hosts[src]
                    h2 = self.hosts[dst_mac]
                    out_port = self.install_paths_arp(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip,ip_proto,dst_port,src_ip, dst_ip, vni)
                    self.install_paths_arp(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip,ip_proto,dst_port,src_ip, dst_ip, vni) # reverse
        if isinstance(pkt_ipv4, ipv4.ipv4) :
            ip_proto = pkt_ipv4.proto
            src_ip = pkt_ipv4.src
            dst_ip = pkt_ipv4.dst
            if ip_proto == 6:
                tcp_pkt = pkt.get_protocol(tcp.tcp)
                dst_port = tcp_pkt.dst_port
                src_port = tcp_pkt.src_port
            if ip_proto == 17:
                udp_pkt = pkt.get_protocol(udp.udp)
                dst_port = udp_pkt.dst_port
                src_port = udp_pkt.src_port
                if pkt_ipv4.tos:
                    tos =  pkt_ipv4.tos
                
                self.arp_table[src_ip] = src
                if dst_ip in self.arp_table:
                    dst_mac = self.arp_table[dst_ip]
                    h1 = self.hosts[src]
                    h2 = self.hosts[dst_mac]
                    
    

                    #Install path: dpid src, src in_port, dpid dst, dpid in_port, src_ip, dst_ip, tos
                    out_port = self.install_paths(src=h1[0], first_port=h1[1], dst=h2[0], 
                                                  last_port=h2[1], ip_src=src_ip, ip_dst=dst_ip,
                                                  ip_proto=ip_proto,tos=tos)
                    self.install_paths(src=h2[0], first_port=h2[1], dst=h1[0], 
                                       last_port=h1[1], ip_src=dst_ip, ip_dst=src_ip,
                                       ip_proto=ip_proto, tos=tos) # reverse
         
        
        actions = [parser.OFPActionOutput(out_port)]


        data = None
        if msg.buffer_id == ofproto.OFP_NO_BUFFER:
            data = msg.data


        out = parser.OFPPacketOut(
            datapath=datapath, buffer_id=msg.buffer_id, in_port=in_port,
            actions=actions, data=data)
        datapath.send_msg(out)
        self.LEARNING = 0
        # learn a mac address to avoid FLOOD next time.
        self.mac_to_port[dpid][src] = in_port
        # if the destination mac address is already learned,
        # decide which port to output the packet, otherwise FLOOD.
        if dst in self.mac_to_port[dpid]:
            out_port = self.mac_to_port[dpid][dst]
        else:
            out_port = ofproto.OFPP_FLOOD

        # construct action list.
        actions = [parser.OFPActionOutput(out_port)]

        # install a flow to avoid packet_in next time.
        if out_port != ofproto.OFPP_FLOOD:
            match = parser.OFPMatch(in_port=in_port, eth_dst=dst)
            self.add_flow(datapath, 1, match, actions)

        # construct packet_out message and send it.
        out = parser.OFPPacketOut(datapath=datapath,
                                  buffer_id=ofproto.OFP_NO_BUFFER,
                                  in_port=in_port, actions=actions,
                                  data=msg.data)
        datapath.send_msg(out)
     # Parsing switch's information
    @set_ev_cls(event.EventSwitchEnter)
    def switch_enter_handler(self,ev):
        switch = ev.switch.dp
        ofp_parser = switch.ofproto_parser
        ports = ev.switch.ports
  
        if VERBOSE == 1:
            print("Switch In: ",switch.id)

        if switch.id not in self.switches:
            self.switches.append(switch.id)
            self.datapath_list[switch.id] = switch

            # Add a default Best-effort meter-band in every new switch.
            self.configure_meter_band(switch ,DEFAULT_BW)

            # Request port/link descriptions, useful for obtaining bandwidth
            req = ofp_parser.OFPPortDescStatsRequest(switch)
            switch.send_msg(req)

            for port in ports:
                port_name = port.name.decode('utf-8')
                # By default, a port has bandwidth = REFERENCE_BW
                #  and doesn't have meter-band limit
                self.sw_port[switch.id][port.port_no] = PortAttr(port_name, NONE_QOS, DEFAULT_BW)
            
    @set_ev_cls(event.EventSwitchLeave, MAIN_DISPATCHER)
    def switch_leave_handler(self, ev):
        switch = ev.switch.dp.id
        if switch in self.switches:
           # self.logger.info("not tracki")
            self.switches.remove(switch)
            del self.datapath_list[switch]
            del self.adjacency[switch]
            try:
                del self.sw_port[switch]
                del self.meter_bands[switch]  
            except:
                pass

    #Handler link event
    @set_ev_cls(event.EventLinkAdd, MAIN_DISPATCHER)
    def link_add_handler(self,ev):
        s1 = ev.link.src
        s2 = ev.link.dst
        self.adjacency[s1.dpid][s2.dpid] = s1.port_no
        self.adjacency[s2.dpid][s1.dpid] = s2.port_no
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

    #Handle real time link bandwidth and real-time stat
    def _monitor(self):
        while True:
            for switch_id in self.datapath_list.keys():
                dp = self.datapath_list[switch_id]
                # Monitor QoS flow
                for cookie in self.qos_flows_cookie[switch_id]:
                    self._request_flow_stats(dp, cookie=cookie)
                # Monitor meter in switches
                if self.meter_bands[switch_id]:
                    self._request_meter_stats(dp)
            hub.sleep(self.sleep)
    
    def _request_port_stats(self, datapath, port = None):
        self.logger.debug('send stats request: %016x', datapath.id)
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        req = parser.OFPFlowStatsRequest(datapath)
        datapath.send_msg(req)

        req = parser.OFPPortStatsRequest(datapath, 0, ofproto.OFPP_ANY)
        datapath.send_msg(req)

    def _request_meter_stats(self, datapath, meter_id=ofproto_v1_3.OFPM_ALL):
        self.logger.debug('send meter stats request: %016x', datapath.id)
        parser = datapath.ofproto_parser

        #Send MeterStatsRequest
        req = parser.OFPMeterStatsRequest(datapath, 0, meter_id=meter_id)
        datapath.send_msg(req)
     
    def _request_flow_stats(self, datapath, cookie=0, in_port=None):
        self.logger.debug('send flow stats request: %016x', datapath.id)
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        match = None
        if in_port:
            match = parser.OFPMatch(in_port=in_port)
        #If match is none, use cookie to query flow stats
        req = parser.OFPFlowStatsRequest(datapath, 0, 0,
                                        ofproto.OFPP_ANY, ofproto.OFPG_ANY,
                                        cookie=cookie, cookie_mask=cookie& COOKIE_MASK, match=match)
        datapath.send_msg(req)
    
    @set_ev_cls(ofp_event.EventOFPFlowStatsReply, MAIN_DISPATCHER)
    def _flow_stats_reply_handler(self, ev):
        body = ev.msg.body

        self.logger.info('datapath         '
                         'in-port  eth-dst           '
                         'out-port packets  bytes')
        self.logger.info('---------------- '
                         '-------- ----------------- '
                         '-------- -------- --------')
        for stat in sorted([flow for flow in body if flow.priority == 1],
                           key=lambda flow: (flow.match['in_port'],
                                             flow.match['eth_dst'])):
            self.logger.info('%016x %8x %17s %8x %8d %8d',
                             ev.msg.datapath.id,
                             stat.match['in_port'], stat.match['eth_dst'],
                             stat.instructions[0].actions[0].port,
                             stat.packet_count, stat.byte_count)

    @set_ev_cls(ofp_event.EventOFPPortStatsReply, MAIN_DISPATCHER)
    def _port_stats_reply_handler(self, ev):
        body = ev.msg.body

        self.logger.info('datapath         port     '
                         'rx-pkts  rx-bytes rx-error '
                         'tx-pkts  tx-bytes tx-error')
        self.logger.info('---------------- -------- '
                         '-------- -------- -------- '
                         '-------- -------- --------')
        for stat in sorted(body, key=attrgetter('port_no')):
            self.logger.info('%016x %8x %8d %8d %8d %8d %8d %8d',
                             ev.msg.datapath.id, stat.port_no,
                             stat.rx_packets, stat.rx_bytes, stat.rx_errors,
                             stat.tx_packets, stat.tx_bytes, stat.tx_errors)
    
    #Handle delete flows and flow tables
    def delete_all_flow(self, datapath, table_id):
        """Removing all flow entries."""
        parser = datapath.ofproto_parser
        ofproto = datapath.ofproto
        empty_match = parser.OFPMatch()
        instructions = []
        flow_mod = self.remove_table_flows(datapath, table_id,
                                        empty_match, instructions)
        print ("deleting all flow entries in table ", table_id)
        datapath.send_msg(flow_mod)
    

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
    
    #Handle group mod: each sw have some group id to foward packet to desired port
    def send_group_mod(self, datapath):
        ofp = datapath.ofproto
        ofp_parser = datapath.ofproto_parser  
        if not self.all_group_id or not self.all_group_id.setdefault(datapath.id,{}):
            return
        else:
            for group_id in self.all_group_id[datapath.id].keys():
                #buckets
                buckets = []
                for port in self.all_group_id[datapath.id][group_id].keys():
                    bucket_weight = self.all_group_id[datapath.id][group_id][port] 
                    bucket_action = [ofp_parser.OFPActionOutput(port)]
                    buckets.append(
                                    ofp_parser.OFPBucket(
                                        weight=bucket_weight,
                                        watch_port=port,
                                        watch_group=ofp.OFPG_ANY,
                                        actions=bucket_action
                                    )
                                )
                   
                    self.logger.info("dataid:%d gid:%d port:%d bucketw:%d buckets %s" 
                                        %(datapath.id,group_id,port,bucket_weight,buckets))
        
                req = ofp_parser.OFPGroupMod(datapath, ofp.OFPGC_MODIFY, ofp.OFPGT_SELECT, group_id)  
                datapath.send_msg(req)
        
    def delete_group_mod(self, datapath):

        ofp = datapath.ofproto
        ofp_parser = datapath.ofproto_parser
        if not self.all_group_id or not self.all_group_id.setdefault(datapath.id,{}):
            return
        else:
            for group_id in self.all_group_id[datapath.id].keys():
                #buckets
                req = ofp_parser.OFPGroupMod(datapath, ofp.OFPGC_DELETE, 0, group_id)  
                datapath.send_msg(req)
            del self.all_group_id[datapath.id]
    
    #Handle infomation about each host
    def get_host_from_dpid(self,dpid):
        return [k for k, v in self.hosts.items() if v[0] == dpid] 
    def get_ip_from_host(self,host):
        return [k for k, v in self.arp_table.items() if v == host] 
    def get_ip_from_dpid(self,dpid):
        hosts = self.get_host_from_dpid(dpid)
        ip = []
        for host in hosts: 
            a = [{k:v} for k, v in self.arp_table.items() if v == host]
            # 1 host has only 1 IP
            ip.append(a[0])
        return ip     
    
    #Calculate remain bw of host
    def banwidth_calculation_host(self,dpid):
        hosts = self.get_host_from_dpid(dpid)
        for host in hosts:
            h_temp = self.hosts[host] 
            h_temp_name = self.sw_port[dpid][h_temp[1]] #Assign port of switch
            total_bw_now = (self.tx_byte_int[dpid][h_temp[1]] + self.rx_byte_int[dpid][h_temp[1]])*8
            self.port_reserve_bw[dpid][h_temp_name] = DEFAULT_BW - total_bw_now 
    
    def banwidth_calculation(self,dpid):
        for dst in self.switches:
            try:
                e1 = self.adjacency[dpid][dst] #port connect bw 2 sw 
                e2 = self.adjacency[dst][dpid]
            except: 
                continue #if cant see any link, move to next sw
            try:
                total_bw_now = (self.tx_byte_int[dpid][e1] + self.tx_byte_int[dst][e2])*8
                reserve = DEFAULT_BW - total_bw_now
                self.sw_reserve_bw[dpid][dst] = reserve
                self.sw_reserve_bw[dst][dpid] = reserve
                
                e1_name = self.sw_port[dpid][e1]
                e2_name = self.sw_port[dst][e2]
                
                
                self.port_reserve_bw[dpid][e1_name] = reserve
                self.port_reserve_bw[dst][e2_name] = reserve
                
                self.banwidth_calculation_host(dpid)
                
                if VERBOSE == 1 and dpid == 1:
                    self.logger.info("BW1: %s \nBw2: %s" %(self.tx_byte_int[dpid][e1],self.tx_byte_int[dst][e2]))
            except:
                continue
    
    #Modify Qos path for different traffic (ARP, ICMP, TCP,...)
    #Hàm này tạo và cài đặt các flow entry với các hành động tương ứng như output và set queue vào bảng điều khiển OpenFlow trên một switch.
    def mod_qos_paths(self,node,vni,src_ip,dst_ip,out_port,queue_id):
        datapath = self.datapath_list[node]
        ofp = datapath.ofproto
        ofp_parser = datapath.ofproto_parser
        actions = [ofp_parser.OFPActionOutput(out_port)]
        #actions là một danh sách các hành động bao gồm gửi gói tin qua cổng out_port voi cac queue id khac nhau
        actions_queue = [ofp_parser.OFPActionSetQueue(queue_id)]
        actions_queue.append(ofp_parser.OFPActionOutput(out_port))
        
        
        match_arp = ofp_parser.OFPMatch(
                        eth_type=0x0806, 
                        arp_spa=src_ip, 
                        arp_tpa=dst_ip
                    )
        
        match_icmp = ofp_parser.OFPMatch(
                        eth_type=0x0800,
                        ip_proto=1,
                         
                        ipv4_src=src_ip, 
                        ipv4_dst=dst_ip,
                    )

        match_tcp = ofp_parser.OFPMatch(
                        eth_type=0x0800, 
                        ip_proto=6,
                        ipv4_src=src_ip, 
                        ipv4_dst=dst_ip
                    )
    
        match_vni = ofp_parser.OFPMatch(
                        eth_type=0x0800, 
                        ip_proto=17,
                        ipv4_src=src_ip, 
                        ipv4_dst=dst_ip,
                        udp_dst=6081,
                        # tunnel_id = int(vni)
                    )
        self.add_flow(datapath, 12, match_vni, actions_queue,IDLE_TIMEOUT)
                                 
        self.add_flow(datapath, 3, match_icmp, actions,IDLE_TIMEOUT)
                 
        self.add_flow(datapath, 10, match_tcp, actions,IDLE_TIMEOUT)
                         
        self.add_flow(datapath, 1, match_arp , actions,IDLE_TIMEOUT)
    
    #Handle Path between hosts using BFS
    def get_paths(self, src, dst):
        '''
        Get all paths from src to dst using DFS algorithm    
        '''
        if SHOW_PATH == 1:
            print("################################################")
        if src == dst:
            # host target is on the same switch
            return [[src]]    
        paths = []
        stack = [(src, [src])]
        
        if VERBOSE == 1:
            print("--stack",stack)
            print("---adjacency",self.adjacency)
            
        while stack:
            # stack pop the last item => LIFO
            (node, path) = stack.pop()
            
            if VERBOSE == 1:
                print((node, path))
                # set is sorted
                print("---adjacency[",node,']:',self.adjacency[node].keys())
                
            for next in set(self.adjacency[node].keys()) - set(path):
                if next is dst:
                    paths.append(path + [next])
                    
                    if VERBOSE == 1:
                        print("-paths",paths)
                else:
                    stack.append((next, path + [next]))
                    
                    if VERBOSE == 1:
                        print("--stack",stack)
        if SHOW_PATH == 1:
            print("################################################")
            print("Available paths from ", src, " to ", dst, " : ", paths)
        
        return paths
    
    #Handle cost of link 
    def get_link_cost(self, s1, s2):

        '''
        Get the link cost between two switches 
        '''
        e1 = self.adjacency[s1][s2]
        e2 = self.adjacency[s2][s1]
        #Check if sw s1 exist in dict tx_byte_int. If not, initiaze s1 with empty dict
        if not self.tx_byte_int.setdefault(s1,{}) or not self.tx_byte_int.setdefault(s2,{}):
            return 0
        if not self.rx_byte_int.setdefault(s1,{}) or not self.rx_byte_int.setdefault(s2,{}):
            return 0
    
        ew = (self.tx_byte_int[s1][e1]+self.tx_byte_int[s2][e2])*8
        #return cost between two sw  
        return ew
    
    #get link bw of host depend on bit through port of sw connect to host
    def get_host_link_cost(self, port, dpid):
        '''
        Get the link cost between switch and host
        '''   
        if not self.tx_byte_int.setdefault(dpid,{}):
            ew = 0
        
        if not self.rx_byte_int.setdefault(dpid,{}):
            ew = 0
            
        else:
            # VM send 1 traffic to switch port but many traffic from other VMs 
            # come from 1 switch port
            ew = (self.tx_byte_int[dpid][port]+self.rx_byte_int[dpid][port])*8
        return ew

    def get_path_cost(self, path,first_port,last_port):
        '''
        Get the path cost
        '''
        cost = 0
        for i in range(len(path) - 1):
            cost += self.get_link_cost(path[i], path[i+1])
        cost += self.get_host_link_cost(first_port, path[0])
        cost += self.get_host_link_cost(last_port, path[-1])
        return cost
    
    #Get bw between host and switch
    def get_host_link_bw_available(self, port, dpid):
        '''
        Get the bw availbe between host and switch
        '''
        self.min_queue_config.setdefault(dpid,{})
        self.min_queue_config[dpid].setdefault(port,0)
        # VM send 1 traffic to switch port but many traffic from other VMs 
        # come from 1 switch port 
        ew = DEFAULT_BW-self.min_queue_config[dpid][port]
        return ew
    #Get link bw between sw and host
    def get_link_bw_available(self, s1, s2):
        '''
        Get the bw availalbe between  switch and host
        '''
        e1 = self.adjacency[s1][s2]
        e2 = self.adjacency[s2][s1]
        
        self.min_queue_config.setdefault(s2,{})
        self.min_queue_config.setdefault(s2,{})
            # bl = min(self.tx_byte_int[s1][e1], self.tx_byte_int[s2][e2])
        self.min_queue_config[s1].setdefault(e1,0)
        self.min_queue_config[s2].setdefault(e2,0)
        # ew = self.min_queue_config[s1][e1]+self.min_queue_config[s2][e2]
        ew = DEFAULT_BW-self.min_queue_config[s1][e1]
        
        return ew
    # trả về một danh sách các chi phí có sẵn (bandwidth available) cho mỗi liên kết trong đường đi.
    def get_path_cost_qos(self, path,first_port,last_port):
        '''
        Get the path cost
        '''
        cost = []
        cost.append(self.get_host_link_bw_available(first_port, path[0]))
        for i in range(len(path) - 1):
            cost.append(self.get_link_bw_available(path[i], path[i+1]))
            
        cost.append(self.get_host_link_bw_available(last_port, path[-1]))
                    
        return cost
    
    #Sorted path based on weight 
    def sorted_path(self,paths,pw):
        # sorted paths based on pw
        zip_list = zip(pw,paths)
        sorted_zip_list = sorted(zip_list)
        sorted_list = [e for _, e in sorted_zip_list]
    #Return list of order path based on weight from min to max
        return sorted_list  
    
    def get_optimal_paths(self, src, dst,first_port,last_port):
        '''
        Get the n-most optimal paths according to MAX_PATHS
        '''
        paths = self.get_paths(src, dst)
        paths_count = len(paths) if len(
            paths) < MAX_PATHS else MAX_PATHS
        pw = []
        for path in paths:
            pw.append(self.get_path_cost(path,first_port,last_port))
        return self.sorted_path(paths,pw)[0:(paths_count)],sorted(pw[0:(paths_count)])
    
    #Get optimal path that have QoS
    def get_optimal_paths_qos(self, src, dst,first_port,last_port):
        '''
        Get the n-most optimal paths according to MAX_PATHS
        '''
        paths = self.get_paths(src, dst)
        paths_count = len(paths) if len(
            paths) < MAX_PATHS else MAX_PATHS
        pw = []
        for path in paths:
            pw.append(self.get_path_cost_qos(path,first_port,last_port))
        return self.sorted_path(paths,pw)[0:(paths_count)],sorted(pw[0:(paths_count)])
    
    #Add port_in, port_out of all sw in a path
    def add_ports_to_paths(self, paths, first_port, last_port):
        '''
        Add the ports that connects the switches for all paths
        '''
        paths_p = []
        for path in paths:
            p = {}
            in_port = first_port
            for s1, s2 in zip(path[:-1], path[1:]):
                out_port = self.adjacency[s1][s2]
                p[s1] = (in_port, out_port)
                in_port = self.adjacency[s2][s1]
            p[path[-1]] = (in_port, last_port)
            paths_p.append(p)
        return paths_p
    
    #Install path between src sw and dst sw: add port to path, install flow entries to all switches 
    def install_paths(self, src, first_port, dst, last_port, ip_src, ip_dst,ip_proto,tos):
        self.LEARNING = 1
        # computation_start = time.time()
        paths,pw = self.get_optimal_paths(src, dst, first_port, last_port)
        # paths = paths[0]
        # pw is total cost of a path (path weight), get the first path have smallest weight
        pw = pw[0]
        paths_with_ports = self.add_ports_to_paths(paths, first_port, last_port)
        #trả về các đường dẫn và trọng số như sau: paths = [[1, 2, 3, 4]] pw = [10]
        paths_with_ports = paths_with_ports[0]
        
        switches_in_paths = set().union(*paths)
        # print(switches_in_paths)
        if VERBOSE == 1:
            print(paths_with_ports)
            print(pw)
            print("#adjacency",self.adjacency)

        for node in paths[0]:
            dp = self.datapath_list[node]
            ofp_parser = dp.ofproto_parser
            # pw is total cost of a path (path weight)
            # ports contain inport:(outport,pw)
            ports = defaultdict(list)
            actions = []
      
            if node in paths_with_ports:
                in_port = paths_with_ports[node][0]
                out_port = paths_with_ports[node][1]
                if (out_port, pw) not in ports[in_port]:
                    ports[in_port].append((out_port, pw))
        
            if VERBOSE == 1:
                print("-------------------------------")
                print("\tnode {}: ports{}".format(node,ports) ) 

            for in_port in ports:
                out_ports = ports[in_port]
                actions = [ofp_parser.OFPActionOutput(out_ports[0][0])]
                meter_id = tos if tos else BE_METER_ID
                instr = [ofp_parser.OFPInstructionMeter(meter_id)]
                if ip_proto == 1:
                # Ipv4
                    match_icmp = ofp_parser.OFPMatch(
                        eth_type=0x0800,
                        ip_proto=1,
                        ipv4_src=ip_src, 
                        ipv4_dst=ip_dst,
                    )
                    self.add_flow(dp, 3, match_icmp, actions,IDLE_TIMEOUT)        

                    # ARP

                    
                if ip_proto == 6: # TCP
                    match_tcp = ofp_parser.OFPMatch(
                        eth_type=0x0800,
                        ip_proto=6,
                        ipv4_src=ip_src, 
                        ipv4_dst=ip_dst,
                    )
                    self.add_flow(dp, 10, match_tcp, actions,IDLE_TIMEOUT)

    
                elif ip_proto == 17: # UDP

                    ip_ecn = tos >> 6
                    ip_dscp = tos << 2
                    match_udp= ofp_parser.OFPMatch(
                        eth_type_nxm=0x0800, 
                        ip_proto_nxm=17,
                        ipv4_src=ip_src, 
                        ipv4_dst=ip_dst,
                        ip_ecn=ip_ecn,
                        ip_dscp=ip_dscp
                    )
                    self.add_flow(dp, 12, match_udp, actions,IDLE_TIMEOUT,insts=instr)

        # print("Path installation finished in ", time.time() - computation_start )
        # print(paths_with_ports[0][src][1])
        return paths_with_ports[src][1]
    #Install pathfor arp packet
    def install_paths_arp(self, src, first_port, dst, last_port, ip_src, ip_dst):

        self.LEARNING = 1
        computation_start = time.time()
        paths,pw = self.get_optimal_paths(src, dst,first_port,last_port)
        pw = pw[0]

        paths_with_ports = self.add_ports_to_paths(paths, first_port, last_port)
        paths_with_ports = paths_with_ports[0]
        
        
        switches_in_paths = set().union(*paths)
        # print(switches_in_paths)
        if VERBOSE == 1:
            print(paths_with_ports)
            # print(pw)
            print("#adjacency",self.adjacency)

        for node in paths[0]:

            dp = self.datapath_list[node]
            ofp = dp.ofproto
            ofp_parser = dp.ofproto_parser


            # pw is total cost of a path (path weight)
            # ports contain inport:(outport,pw)
            ports = defaultdict(list)
            actions = []
        
            if node in paths_with_ports:
                in_port = paths_with_ports[node][0]
                out_port = paths_with_ports[node][1]
                if (out_port, pw) not in ports[in_port]:
                    ports[in_port].append((out_port, pw))
        
            if VERBOSE == 1:
                print("-------------------------------")
                print("\tnode {}: ports{}".format(node,ports) ) 

            for in_port in ports:
                # ARP
                match_arp = ofp_parser.OFPMatch(
                    eth_type=0x0806, 
                    arp_spa=ip_src, 
                    arp_tpa=ip_dst
                )
            
                out_ports = ports[in_port]
                actions = [ofp_parser.OFPActionOutput(out_ports[0][0])]
                self.add_flow(dp, 1, match_arp, actions,IDLE_TIMEOUT)
        # print("Path installation finished in ", time.time() - computation_start )
        # print(paths_with_ports[0][src][1])
        return paths_with_ports[src][1]
    #Install path for two types packet
    def install_replace_paths(self, src, first_port, dst, last_port, ip_src, ip_dst,p,cost):
        if SHOW_PATH == 1:
            self.path_install_cnt +=1
            self.logger.info("installing path cnt: %d" % (self.path_install_cnt))
        self.LEARNING = 1
        computation_start = time.time()
        # paths,pw = self.get_optimal_paths(src, dst)
        paths = p
        pw = cost
        pw = pw[0]         
        
        paths_with_ports = self.add_ports_to_paths(paths, first_port, last_port)
        paths_with_ports = paths_with_ports[0]
        switches_in_paths = set().union(*paths)
        # print(switches_in_paths)
        if VERBOSE == 1:
            print(paths_with_ports)
            # print(pw)
            print("#adjacency",self.adjacency)

        for node in switches_in_paths:
            dp = self.datapath_list[node]
            ofp = dp.ofproto
            ofp_parser = dp.ofproto_parser

            # pw is total cost of a path (path weight)
            # ports contain inport:(outport,pw)
            ports = defaultdict(list)
            actions = []

            if node in paths_with_ports:
                in_port = paths_with_ports[node][0]
                out_port = paths_with_ports[node][1]
                if (out_port, pw) not in ports[in_port]:
                    ports[in_port].append((out_port, pw))
 
            if VERBOSE == 1:
                print("-------------------------------")

            for in_port in ports:
                out_ports = ports[in_port]
            
                # print("_MODOUTPORT",ports)
                
                match_ip = ofp_parser.OFPMatch(
                    eth_type=0x0800, 
                    ipv4_src=ip_src, 
                    ipv4_dst=ip_dst
                )
            
                # ARP
                match_arp = ofp_parser.OFPMatch(
                    eth_type=0x0806, 
                    arp_spa=ip_src, 
                    arp_tpa=ip_dst
                )
                                
                actions = [ofp_parser.OFPActionOutput(out_ports[0][0])]

                self.add_flow(dp, 32768, match_ip, actions)
                self.add_flow(dp, 1, match_arp, actions)
        return 
    
    #modify the meter.
    def configure_meter_band(self, switch ,rate, burst=0.1, meter_id=BE_METER_ID, command=ofproto_v1_3.OFPMC_ADD):
        bands = []
        burst_Size = rate * burst # Default burst size = 10% of rate limit
        dropband = ofp_parser.OFPMeterBandDrop(rate=rate, burst_size=burst_Size) # Only use drop band
        bands.append(dropband)
        request = ofp_parser.OFPMeterMod(datapath=switch, 
                                   command=command, 
                                   flags=ofproto_v1_3.OFPMF_KBPS, 
                                   meter_id=meter_id, 
                                   bands=bands)
        switch.send_msg(request)
    
    #Configure QOS for a port in a OVS 
    def configure_qos(self,port):
        ovs_bridge = bridge.OVSBridge(self.CONF, dpid, ovsdb_server)
        try:
            if self.queue_config[port]:
                ovs_bridge.set_qos(port, type=QUEUE_TYPE,
                                        max_rate=str(DEFAULT_BW),
                                        queues=self.queue_config[port])
            else:
                ovs_bridge.set_qos(port, type=QUEUE_TYPE,
                                        max_rate=str(DEFAULT_BW))
        except Exception as msg:
            raise ValueError(msg)

    #Process demand about bandwwidth and install config for QoS in port
    def accept_demand(self,request,path,dst_port,vni,src_ip,dst_ip):
        for i in range(len(path)-1):
            s1 = path[i]
            s2 = path[i+1]
            #port from s1 to s2
            e1 = self.adjacency[s1][s2]
            # Khởi tạo cấu hình hàng đợi cho e1 nếu chưa có.
            self.queue_config.setdefault(e1,[])
            #Port nane of e1
            e1_name = self.sw_port[s1][e1]
            #Add rq to e1 queue
            self.queue_config[e1_name].append(request)
            
            # Install qos and queue in ovsdb of ovs
            self.configure_qos(e1_name)
            queue_id = len(self.queue_config[e1_name])-1
            self.request_table[self.request_id]['queue_bind'][e1_name] = queue_id
            self.host_request[src_ip,dst_ip]['queue_bind'][e1_name] = queue_id
            
            # Install flow qos in ovs
            self.mod_qos_paths(s1,vni,src_ip,dst_ip,e1,queue_id)
            
            # Install in OVNDB
            # self.install_ovn(self,queue_id,request)
        #Process des port    
        dst_p_name = self.sw_port[path[-1]][dst_port]
        self.queue_config.setdefault(dst_port,[])
        self.queue_config[dst_p_name].append(request)
        
        queue_id = len(self.queue_config[dst_p_name])-1
        self.configure_qos(dst_p_name)
        self.mod_qos_paths(path[-1],vni,src_ip,dst_ip,dst_port,queue_id)
        self.request_table[self.request_id]['queue_bind'][dst_p_name] = queue_id
        self.host_request[src_ip,dst_ip]['queue_bind'][dst_p_name] = queue_id
        self.change = True
    
    #Check demadn of a request
    def check_demand(self,path,vni,src_ip,dst_ip,vm_src,vm_dst):
        check_req = True
        for accept_req in self.request_table.values():
            if accept_req['path'] != path:
                continue
            if accept_req['vni'] != vni:
                continue
            if accept_req['src_ip'] != src_ip:
                continue
            if accept_req['dst_ip'] != dst_ip:
                continue
            if accept_req['vm_bind'] != (vm_src,vm_dst):
                continue
    
            check_req = False
            
        return check_req
    
    #regulate config QOS for a specific port in a sw using OVSDB
    def mod_request(self,port,queue_id,request_mod):
        #Create connection vs ovsdb and Open_vSwitch table
        db = libovsdb.OVSDBConnection(ovsdb_server, "Open_vSwitch")
        #Query info from table Port to get uuid and qos of port
        get_port = db.select(table = "Port",
                    columns = ['_uuid',"qos"],
                    where = [["name", "==", port]])
        #Store qos port in port_qos 
        port_qos = get_port[0]['qos']
        #save the configs that need update
        config = []
        #if rq store min_rate append min-rate in list config
        if request_mod.get("min-rate"):
            min_rate_list = ['min_rate',request_mod["min-rate"]]
            config.append(min_rate_list)
        if request_mod.get("max-rate"):
            if int(request_mod["min-rate"]) > int(request_mod["max-rate"]):
                max_rate_list = ['max_rate',request_mod["min-rate"]]
            else:
                max_rate_list = ['max_rate',request_mod["max-rate"]]
            config.append(max_rate_list)

        self.logger.info("configure: %s",config)

        #Query information from the QoS table to get _uuid and queues based on port_qos.
        get_queue = db.select(table = "QoS",
                            columns = ['_uuid',"queues"],
                            where = [["_uuid", "==", ["uuid",port_qos]]])
        # print("select qos result: %s" %(json.dumps(get_queue, indent=4)))
        #Each element in queues is a list with two elements. The first element (queue[0]) is the ID of the queue.
        for queue in get_queue[0]['queues']:
            if queue[0] != queue_id:
                continue
            #queue[1][1] lấy UUID của hàng đợi từ danh sách này. UUID này sẽ được sử dụng để xác định hàng đợi cụ thể cần cập nhật trong bảng Queue.
            queue_uuid = queue[1][1]
            #Cập nhật hàng đợi trong bảng Queue:
            res = db.update(table = "Queue",
                            row = {"other_config": ['map',config]},
                            where = [["_uuid", "==", ["uuid",queue_uuid]]])
   
    #This method is used to delete a specific queue on a network port using OVSDB (Open vSwitch Database).
    def queue_del(self,queue_id,port):
        db = libovsdb.OVSDBConnection(ovsdb_server, "Open_vSwitch")
        get_port = db.select(table = "Port",
                        columns = ['_uuid',"qos"],
                        where = [["name", "==", port]],)
        port_qos = get_port[0]['qos']
        # print(get_port)
        # print("select qos result: %s" %(json.dumps(port_qos, indent=4)))

        get_queue = db.select(table = "QoS",
                columns = ['_uuid',"queues"],
                where = [["_uuid", "==", ["uuid",port_qos]]])
        # print(get_queue)
        # print("select qos result: %s" %(json.dumps(get_queue, indent=4)))

        if not get_queue:
        # self.logger.info("Queue not ref")
            tx = db.transact()
            uuid = port_qos

            tx.delete(table = "QoS",
                    where = [["_uuid", "==", ["uuid",uuid]]])
            tx.mutate(table = "Port",
                        where = [["name", "==", port]],
                        mutations = [tx.make_mutations("qos", "delete", {"uuid": port_qos})])
            response = tx.commit()
            # print(response)

        # Queue table delete
        else:
            del_queue = None
            list_queue = get_queue[0]['queues']
            for queue_key in list_queue:
                if queue_id == queue_key[0]:
                    # print(queue_key)
                    del_queue = queue_key
        
            list_queue.remove(del_queue)
            list_queue = ['map',list_queue]
            res_qos = db.update(table = "QoS",
                                row = {"queues": list_queue},
                                where = [["_uuid", "==", ["uuid",port_qos]]])
            # print(res_qos)
            if del_queue:
                queue_uuid = del_queue[1][1]
                res = db.delete(table = "Queue",
                                where = [["_uuid", "==", ["uuid",queue_uuid]]],
                                referby = ["QoS", port_qos, "queues"])
                # print(res)
    #handle requests to modify QoS (Quality of Service) parameters such as min-rate and max-rate
    def handle_request_mod(self,request_id,request_mod,path_mod):
        resp = "Success modify"
        cond = True
        if not request_mod.get("min-rate") and not request_mod.get("max-rate"):
            return "Wrong rate request", False
        self.logger.info("Request_table: %s",request_id)
        src_ip = request_id["src_ip"]
        dst_ip = request_id["dst_ip"]
        if not request_mod.get("min-rate"):
            # max-rate
            if self.host_request[src_ip,dst_ip]['request']['max-rate'] <= request_mod['max-rate']: #get value with key max-rate request_mod = {'min-rate': 1000,'max-rate': 5000}
                self.host_request[src_ip,dst_ip]['request']['max-rate'] = request_mod['max-rate']
            if request_id["path"] == path_mod:
                for port,queue_id in request_id['queue_bind'].items():
                    self.mod_request(port,queue_id,self.host_request[src_ip,dst_ip]['request'])
                resp = "Success moding (max-rate)"
                return resp, True
            # mod path: delete all qos then add qos again??
            
        min_rate = int(request_mod.get("min-rate"))

        if request_id["min-rate"]:
            temp_min = min_rate + int(self.host_request[src_ip,dst_ip]['request']["min-rate"])
            if temp_min <= DEFAULT_BW:
                self.host_request[src_ip,dst_ip]['request']["min-rate"] = str(temp_min)
            else:
                reject_min = DEFAULT_BW - int(self.host_request[src_ip,dst_ip]['request']["min-rate"])
                resp = "Reject: Minrate %s >= available bw: %s" % (min_rate,reject_min)
                return resp, False
        # else:

        self.logger.info("MOD----------")
        
        for port,queue_id in request_id['queue_bind'].items():
            self.mod_request(port,queue_id,request_mod)

        if request_id["min-rate"] and request_id["path"] == path_mod:
            for i in range(len(path_mod)-1):
                s1 = path_mod[i]
                s2 = path_mod[i+1]
                e1 = self.adjacency[s1][s2]
                self.min_queue_config.setdefault(s1,{})
                self.min_queue_config[s1].setdefault(e1,0)
                self.min_queue_config[s1][e1] += min_rate
        
                    
        return resp,cond
    
    #Handle (QoS) requests between two source IP (src_ip) and destination (dst_ip) addresses on a specific network path
    def handle_request(self,request,path,src_ip,dst_ip,vni,vm_src,vm_dst):
        new_queue = False
    
        self.logger.info("RES: %s"%request)
        req_num = 1
        if not request.get('max-rate') and not request.get('min-rate'):
            resp = "Wrong rate request"
            self.logger.info(resp)
            return resp, False
        
        
        if src_ip not in self.arp_table.keys():
            resp = "Host IP not found: %s" % src_ip
            self.logger.info(resp)
            return resp, False
        
        if dst_ip not in self.arp_table.keys():
            resp = "Host IP not found: %s" % dst_ip
            self.logger.info(resp)
            return resp, False
               
        mac_src = self.arp_table[src_ip]
        mac_dst = self.arp_table[dst_ip]
        #add host have mac add to h1 h2
        h1 = self.hosts[mac_src]
        h2 = self.hosts[mac_dst]
        #assign sw src and dst sw
        src = h1[0]
        dst = h2[0]

        paths,pw = self.get_optimal_paths_qos(src, dst,h1[1],h2[1])
        self.logger.info("paths: %s\npw: %s" %(paths,pw))
        if not path:
            path = paths[0]
        elif path not in paths:
            resp = "Can`t find path: Path seem to be not correct"
            self.logger.info(resp)
            return resp, False
        
        #Check max rate if negative or > physical link respond error message
        if request.get('max-rate'):
            if int(request.get('max-rate')) > DEFAULT_BW:
                resp = "max-rate exceeds link bandwidth: \nThere are %d traffics bind to this demand" % req_num
                self.logger.info(resp)
                return resp, False
           
            if int(request.get('max-rate')) < 0 :
                resp = "request can't be negative"
                self.logger.info(resp)
                return resp, False
        
        # Kiểm tra xem có yêu cầu tương tự tồn tại hay không:
        if not request.get('min-rate'):
            check = self.check_demand(path,vni,src_ip,dst_ip,vm_src,vm_dst)
            
            if check == False:
                # Need to modify old queue/qos
                resp = "Request exist for the same type traffic"
                return resp, False
            
            self.request_table.setdefault(self.request_id,{})
            self.request_table[self.request_id]={'request':request,'path':path,
                                                'vni':vni,'src_ip':src_ip,
                                                'dst_ip':dst_ip,'queue_bind':{},'vm_bind':(vm_src,vm_dst)}
            # if vm_src:
            #     self.request_table[self.request_id]["vm_bind"] = (vm_src,vm_dst)
            self.host_request.setdefault((src_ip,dst_ip),{})
            if not self.host_request[src_ip,dst_ip]:
                self.host_request[src_ip,dst_ip]={'request':request,'path':path,
                                                'queue_bind':{}}
                #Accept the request and update the information.
                self.accept_demand(request,path,h2[1],vni,src_ip,dst_ip)   
                self.request_id += 1   
                resp = "Request accepted"  
                return resp, True
            #If the max-rate in the current request is greater than or equal to the existing max-rate,
            #update the max-rate and call the self.mod_request function to adjust the queues for each port.
            if self.host_request[src_ip,dst_ip]['request']['max-rate'] <= request['max-rate']:
                self.host_request[src_ip,dst_ip]['request']['max-rate'] = request['max-rate']
                
                for port,queue_id in self.host_request[src_ip,dst_ip]['queue_bind'].items():
                    self.mod_request(port,queue_id,self.host_request[src_ip,dst_ip]['request'])
                resp = "Request accepted (SDN mod)"  
                return resp, True
            else:
                resp = "SDN Request unchanged"  
                return resp, True 

        if request.get('max-rate'):
            if int(request.get('min-rate')) > int(request.get('max-rate')):
                resp = "Invalid min request: Minrate > Maxrate"
                self.logger.info(resp)
                return resp, False
            
        if int(request.get('min-rate')) < 0 :
            resp = "request can't be negative"
            self.logger.info(resp)
            return resp, False
            
        index = 0
        min_rate = int(request.get('min-rate'))
        
        # Path was already found in the prev action
        for index in range(len(paths)):
            if paths[index] == path:  
                break
        self.logger.info("BAND:%s",pw)

        #If remain bw < min_rate =>> Reject rq
        for avai_bw in pw[index]:
            if avai_bw < min_rate:
                resp = "Reject: Minrate %s > available bw: %s \
                " % (min_rate,avai_bw)
                self.logger.info(resp)
                return resp, False
       
        check = self.check_demand(path,vni,src_ip,dst_ip,vm_src,vm_dst)
        if check == False:
            # Need to modify old queue/qos
            resp = "Request exist for the same type traffic"
            return resp, False
        
        for i in range(len(path)-1):
            s1 = path[i]
            s2 = path[i+1]
            e1 = self.adjacency[s1][s2] #e1 is the port connecting s1 and s2 in the adjacency table.
            self.min_queue_config.setdefault(s1,{})
            self.min_queue_config[s1].setdefault(e1,0)
            self.min_queue_config[s1][e1] += min_rate

        #Update the minimum queue configuration for the last switch    
        self.min_queue_config[path[-1]][h2[1]] += min_rate
        
        self.request_table.setdefault(self.request_id,{})
        self.request_table[self.request_id]={'request':request,'path':path,
                                            'vni':vni,'src_ip':src_ip,
                                            'dst_ip':dst_ip,'queue_bind':{},'vm_bind':(vm_src,vm_dst)}
        self.host_request.setdefault((src_ip,dst_ip),{})
        if not self.host_request[src_ip,dst_ip]:
            self.host_request[src_ip,dst_ip]={'request':request,'path':path,
                                                'queue_bind':{}}
            self.accept_demand(request,path,h2[1],vni,src_ip,dst_ip)  
            self.request_id += 1    
            resp = "Request accepted"  
            return resp, True
        
        # MOD REQ
        temp_min = min_rate + int(self.host_request[src_ip,dst_ip]['request']["min-rate"])
        if 'max-rate' not in self.host_request[src_ip,dst_ip]['request'].keys():
            self.host_request[src_ip,dst_ip]['request']['max-rate'] = str(DEFAULT_BW)
        # elif temp_min > int(self.host_request[src_ip,dst_ip]['request']['max-rate']):
        #     self.host_request[src_ip,dst_ip]['request']['max-rate'] = str(temp_min)
        # if request.get("max-rate"):
        #     if int(self.host_request[src_ip,dst_ip]['request']['max-rate']) <= int(request['max-rate']):
        #         self.host_request[src_ip,dst_ip]['request']['max-rate'] = request['max-rate']
        self.host_request[src_ip,dst_ip]['request']["min-rate"] = str(temp_min)
        for port,queue_id in self.host_request[src_ip,dst_ip]['queue_bind'].items():
            self.mod_request(port,queue_id,self.host_request[src_ip,dst_ip]['request'])
        resp = "Request accepted (SDN mod)"  
        return resp, True
    
    
    #Handle replace path
    def replace_path(self,src,dst,p,pw):
        #1 switch connect to multiple host -> multiple IPs
        #return dict of IP:host
        src_ips = self.get_ip_from_dpid(src)
        dst_ips = self.get_ip_from_dpid(dst)
        ip_h1 = []
        ip_h2 = []
        p_reverse = []
        for i in p:
            # self.logger.info("PATH %s",i[::-1])
            #Reverse path for add flow
            p_reverse.append(i[::-1])

        for ip_host in src_ips:
            ip_h1.append(ip_host.popitem())
            
        for ip_host in dst_ips:
            ip_h2.append(ip_host.popitem())
        
        for ip_1,h_1 in ip_h1: 
            for ip_2,h_2 in ip_h2:
                self.install_replace_paths(src,self.hosts[h_1][1],dst,self.hosts[h_2][1],ip_1,ip_2,p,pw)              
                self.install_replace_paths(dst,self.hosts[h_2][1],src,self.hosts[h_1][1],ip_2,ip_1,p_reverse,pw)
    

    def setup_new_route_with_qos(self,vm_id, src_ip, dst_ip, old_host_ip, old_host_port, new_host_ip, new_host_port, tos,request, new_src,dst,last_post):
        self.logger.info(f"Setting up new route with QoS for VM {vm_id}")

        path = self.get_optimal_paths_qos(new_src,dst,new_host_port, last_post)  # Tìm đường dẫn mới từ host mới đến đích
        self.accept_demand(request, path, new_host_port, None, src_ip, dst_ip)
        self.logger.info(f"QoS setup complete for new route from {new_host_ip} to {dst_ip}")

    def setup_traffic_for_migration(self,request, new_path, new_src_ip, dst_ip, vni, vm_src, vm_dst):
        """
        Setup traffic on the new path before migrating the VM.
        """
        # Assuming self.handle_request is part of a class managing network state and requests
        resp, success = self.handle_request(request, new_path, new_src_ip, dst_ip, vni, vm_src, vm_dst)
        if not success:
            self.logger.error("Failed to setup traffic on the new path: %s", resp)
            return False
        self.logger.info("Successfully setup traffic on the new path")
        return True
    def live_migrate_vm(self,vm_id, target_host):
        """
        Perform live migration of the VM to the target host.
        """
        # Assuming we're using OpenStack's API to manage VMs
        try:
            # nova_client.servers.live_migrate(server=vm_id, host=target_host, block_migration=True, disk_over_commit=False)
            # self.logger.info("Successfully initiated live migration for VM %s to host %s", vm_id, target_host)
            return True
        except Exception as e:
            self.logger.error("Failed to initiate live migration: %s", e)
            return False
    def cleanup_old_traffic(self,request_id, old_path):
        """
        Clean up traffic on the old path after VM migration.
        """
        try:
            # Assuming self.remove_request is a method that removes the QoS and traffic rules
            self.remove_request(request_id, old_path)
            self.logger.info("Successfully cleaned up traffic on the old path")
            return True
        except Exception as e:
            self.logger.error("Failed to clean up traffic on the old path: %s", e)
            return False

    def migrate_vm_with_traffic_setup(self, vm_id, request, new_path, old_path, src_ip, dst_ip, vni, target_host):
        """
        Migrate a VM with pre-setup and cleanup of traffic rules.
        """
        # Step 1: Setup traffic on the new path
        if not self.setup_traffic_for_migration(request, new_path, src_ip, dst_ip, vni, vm_id, dst_ip):
            return "Failed to setup traffic on the new path", False

        # Step 2: Live migrate the VM
        if not self.live_migrate_vm(vm_id, target_host):
            return "Failed to live migrate VM", False

        # Step 3: Cleanup old traffic rules
        request_id = self.get_request_id_by_vm(vm_id)  # Assuming this function maps VM to request ID
        if not self.cleanup_old_traffic(request_id, old_path):
            return "Failed to clean up old traffic", False

        return "VM migrated successfully with traffic setup and cleanup", True

    @set_ev_cls(event.EventSwitchEnter)
    def get_topology(self, ev):
        switch_list = get_switch(self.topology_api_app, None)
        switches = [switch.dp.id for switch in switch_list]
        self.logger.info("Switches in the network:")
        for switch in switches:
            self.logger.info("Switch ID: %s", switch)
        links_list = list(get_link(self.topology_api_app, None))
        links = [(link.src.dpid,link.dst.dpid,{'port':link.src.port_no}, {'port':link.dst.port_no}) for link in links_list]
		# print(links_list)
        self.logger.info("Links in the network:")
        for link in links_list:
            self.logger.info("Link from switch %s port %s to switch %s port %s",
                             link.src.dpid, link.src.port_no,link.dst.dpid,link.dst.port_no)

