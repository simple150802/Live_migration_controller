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

import json
from ryu.lib.ovs import bridge
from ryu.ofproto import nx_match
from dataclasses import dataclass

# QoS flow direction
SAME_DIRECTION = 1
REVERSE_DIRECTION = 2

# Mark port has QoS meter
PORT_NONE_QOS = 0 
PORT_HAVE_QOS = 1

# Cookie masks
TOS_MASK = 0x00ff
PORT_NO_MASK = 0xff00
QOS_FLOW_MASK = 0x0000ff

# Best-effort meter rate
BE_RATE = 0.01

# Request types
REQUEST_NEW    = 1
REQUEST_MODIFY = 2
REQUEST_DELETE = 3
REQUEST_MAPPING_SUCCESS = 4
REQUEST_MAPPING_FAIL = -1

# Sync result
SYNC_NONE_CHANGE = 0
SYNC_HAVE_CHANGE = 1

# Request modify types
CHANGE_MIN_BW = 1
CHANGE_HOST = 2

NUM_RANDOM = 0.97

DEFAULT_BW = int(10000000/1000) # 100 Mbps => kbps
NSEC         = 1000000000

DEFAULT_TABLE = 100

MAX_PATHS = 10


VERBOSE = 0
DEBUGING = 0
SHOW_PATH = 0

DEFAULT_FLOW_PRIORITY = 0
IDLE_TIMEOUT = 150

@dataclass
class RequestAttr:
    outter_src_ip: int
    outter_dst_ip: int
    min_bw: int 
    status: int = REQUEST_NEW
    change_status: int = 0
    inner_src_ip: int
    inner_dst_ip: int

@dataclass
class PortAttr:
    name: str
    have_qos: bool = PORT_NONE_QOS 
    available_bw: int = DEFAULT_BW
    physical_bw: int = DEFAULT_BW

@dataclass
class MeterAttr:
    meter_id: int = 0
    out_port: int = 0
    guaranteed_bw: int =0
    cr_bw_max: int =0
    cr_bw_need: int =0
    last_byte_in: int =0
    last_sec: int =0
    last_nsec: int =0

class ProjectController(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto.OFP_VERSION]


    def __init__(self, *args, **kwargs):
        super(ProjectController, self).__init__(*args, **kwargs)
        self.mac_to_port = {}
        self.LEARNING = 1
        self.FLAG = 0
        
        self.topology_api_app = self
        self.arp_table = {} #{IP:MAC}
        self.hosts = {} #{MAC:(switch_id, in_port)}
        self.multipath_group_ids = {}
        self.all_group_id = {}
        self.group_id_count =0
        self.group_ids = []
        self.adjacency = defaultdict(dict)
        self.count = 0
        self.path_install_cnt =0

        self.datapath_list = {} #{switch_id:datapath}
        self.sw_port = defaultdict(dict) # {switch_id:{port_no:PortAttr()}}
        self.switches = [] #[switch_id]
        

        self.qos_flows_cookie = defaultdict(int) # {switch_id:cookie}
        self.meter_bands = defaultdict(list) #{switch_id:[MeterAttr(),..]}
        self.request_table = {} #{tos:RequestAttr}
        self.qos_paths = {} #{tos:path}

        
        if DEBUGING == 1:
            self.logger.setLevel(logging.DEBUG)
        else:
            self.logger.setLevel(logging.INFO)
            
        
        # monitor
        self.sleep = 1
        # self.datapaths = {}
        self.monitor_thread = hub.spawn(self._monitor)

    def _connect_to_vim(self):
        '''
        Connect to Openstack
        '''
        pass    

    def _get_qos_table(self):
        '''
        Call Neutron APi to get qos information form Openstack
        '''
        _conn = self._connect_to_vim
        pass

    def _handle_qos_request(self,api_result):
        '''
        Handle API result from OpenStack
        '''
        ret = {} # {tos:RequestAttr()}
        pass
        return ret

    def _compare_request(self,old_request,new_request):
        ret = SYNC_NONE_CHANGE
        if old_request.min_bw != new_request.min_bw:
            new_request.status = REQUEST_MODIFY
            new_request.change_status = CHANGE_MIN_BW
            ret = SYNC_HAVE_CHANGE
            return new_request, ret
        if old_request.outter_src_ip != new_request.outter_src_ip or old_request.outter_dst_ip != new_request.outter_dst_ip:
            new_request.status = REQUEST_MODIFY
            new_request.change_status = CHANGE_HOST
            ret = SYNC_HAVE_CHANGE
            return new_request, ret
        return ret
    
    def _sync_qos(self):
        '''
        Sync qos of virtual network topology from VIMs with request_table
        '''
        result = self._get_qos_table
        qos_table = self._handle_qos_request(result)
        new_request_table = {}
        ret = SYNC_NONE_CHANGE

        for old_tos in self.request_table.items():
            old_request = self.request_table[old_tos]
            if old_tos in qos_table:
                new_request = qos_table[old_tos]
                new_request.status = REQUEST_MAPPING_SUCCESS
                new_request,ret1 = self._compare_request(old_request,new_request)
                if ret1 == SYNC_HAVE_CHANGE:
                    new_request_table[old_tos] = new_request
                else:
                    new_request_table[old_tos] = old_request
                del qos_table[old_tos]
            else:
                old_request.status = REQUEST_DELETE
                new_request_table[old_tos] = old_request
                ret = SYNC_HAVE_CHANGE

        new_request_table = new_request_table | qos_table
        return new_request_table, ret
    
    def sync_qos(self):
        new_request_table, ret = self._sync_qos()
        if ret == SYNC_HAVE_CHANGE:
            self.handle_request_table(new_request_table)
    
    def handle_request_table(self,request_table):
        for tos, request in request_table.items():
            # Giai phong bandwidth cua QoS bi xoa truoc, viec nay luon thanh cong
            if request.status == REQUEST_DELETE:
                self._handle_request(tos, request)
                del request_table[tos]

        for tos, request in request_table.items():
            ret = self._handle_request(tos, request)
            if ret == REQUEST_MAPPING_FAIL:
                del request_table[tos]
            else:
                request.status = REQUEST_MAPPING_SUCCESS
                request.change_status = 0

        self.request_table = request_table
        
    def _handle_request(self, tos, request):
        '''
        Handle a reserve bw request
        '''
        ret = -1
        if request.status == REQUEST_NEW:
            ret = self._handle_new_request(tos, request)
        elif request.status == REQUEST_MODIFY:
            ret = self._handle_modify_request(tos, request)
        elif request.status == REQUEST_DELETE:
            ret = self._handle_delete_request(tos,request)
        return ret
    
    def _handle_new_request(self, tos, request):
        src_mac = self.arp_table[request.outter_src_ip]
        dst_mac = self.arp_table[request.outter_dst_ip]

        src_host = self.hosts[src_mac]
        dst_host = self.hosts[dst_mac]

        path,path_bw = self.find_available_path(src_host,dst_host,request.min_bw); 
        
        if not path or not path_bw:
            return REQUEST_MAPPING_FAIL
        
        self.qos_paths[tos] = path
        self._install_meters_in_path(tos,request,path,dst_host)
        return REQUEST_MAPPING_SUCCESS
    
    def _handle_modify_request(self, tos, request):
        ret = REQUEST_MAPPING_FAIL
        old_path = self.qos_paths[tos]
        dst_mac = self.arp_table[request.outter_dst_ip]
        dst_host = self.hosts[dst_mac]

        if request.change_status == CHANGE_HOST:
            # Thu mapping request vao mot path khac
            self._handle_delete_request(self, tos, request)
            ret = self._handle_new_request(self, tos, request)

        if request.change_status == CHANGE_MIN_BW:
            path_bw = self._get_path_available_bw(old_path,dst_host[1])
            if path_bw >= request.min_bw:
                self._change_min_tos_bw_in_path(tos,request,old_path,dst_host)
            else:
                # Thu mapping request vao mot path khac
                self._handle_delete_request(self, tos, request)
                ret = self._handle_new_request(self, tos, request)    
        return ret
    
    def _handle_delete_request(self, tos, request):
        old_path = self.qos_paths.pop(tos)
        self._delete_meters_in_path(tos, old_path, request)
        return REQUEST_MAPPING_SUCCESS
        
    def _change_min_tos_bw_in_path(self, tos, request, path, dst_host):
        new_min_bw = request.min_bw
        old_min_bw = self.request_table[tos].min_bw
        for i in range(len(path)-1):
            src_sw = path[i]
            dst_sw = path[i+1]
            port_no = self.adjacency[src_sw][dst_sw]
            meter_id = ((port_no << 8) & PORT_NO_MASK) | (tos & TOS_MASK)

            self.sw_port[src_sw][port_no].have_qos = PORT_HAVE_QOS
            self.sw_port[src_sw][port_no].available_bw += old_min_bw - new_min_bw
            self.meter_bands[src_sw].guaranteed_bw = request.min_bw

            self.configure_meter_band(switch=self.datapath_list[src_sw],rate=request.min_bw,
                                      meter_id=meter_id,command=ofproto.OFPMC_MODIFY)
        # Last port connect to dst_host
        src_sw = path[-1]
        port_no = dst_host[1]
        meter_id = ((port_no << 8) & PORT_NO_MASK) | (tos & TOS_MASK)
        self.sw_port[src_sw][port_no].have_qos = PORT_HAVE_QOS
        self.sw_port[src_sw][port_no].available_bw += old_min_bw - new_min_bw
        self.meter_bands[src_sw].guaranteed_bw = request.min_bw

        self.configure_meter_band(switch=self.datapath_list[src_sw],rate=request.min_bw,
                                    meter_id=meter_id,command=ofproto.OFPMC_ADD)
        
    def _install_meters_in_path(self, tos, request, path, dst_host):
        for i in range(len(path)-1):
            src_sw = path[i]
            dst_sw = path[i+1]
            port_no = self.adjacency[src_sw][dst_sw]
            meter_id = ((port_no << 8) & PORT_NO_MASK) | (tos & TOS_MASK)
            match = of_parser.OFPMatch(
                eth_type=0x0800,
                ip_proto=17,
                ipv4_src=request.outter_src_ip,
                ipv4_dst=request.outter_dst_ip, 
                ip_ecn=(tos >> 6) & 0xFF,
                ip_dscp=(tos << 2) & 0xFF
            )
            action = of_parser.OFPActionOutput(port_no)
            instr = [of_parser.OFPInstructionMeter(meter_id)]
            cookie = (meter_id << 8) | (0xff)

            self.sw_port[src_sw][port_no].have_qos = PORT_HAVE_QOS
            self.sw_port[src_sw][port_no].available_bw -= request.min_bw
            self.meter_bands[src_sw] = MeterAttr(meter_id,port_no,request.min_bw)
            
            self.add_flow(switch=self.datapath_list[src_sw], priority=200, match=match,
                          cookie=cookie, actions=action, idle_timeout=3600,insts=instr)
            
            self.configure_meter_band(switch=self.datapath_list[src_sw],rate=request.min_bw,
                                      meter_id=meter_id,command=ofproto.OFPMC_ADD)
        # Last port connect to dst_host
        src_sw = path[-1]
        port_no = dst_host[1]
        meter_id = ((port_no << 8) & PORT_NO_MASK) | (tos & TOS_MASK)
        self.sw_port[src_sw][port_no].have_qos = PORT_HAVE_QOS
        self.sw_port[src_sw][port_no].available_bw -= request.min_bw
        self.meter_bands[src_sw] = MeterAttr(meter_id,port_no,request.min_bw)
        match = of_parser.OFPMatch(
            eth_type=0x0800,
            ip_proto=17,
            ipv4_src=request.outter_src_ip,
            ipv4_dst=request.outter_dst_ip, 
            ip_ecn=(tos >> 6) & 0xFF,
            ip_dscp=(tos << 2) & 0xFF
        )
        action = of_parser.OFPActionOutput(port_no)
        instr = [of_parser.OFPInstructionMeter(meter_id)]
        cookie = (meter_id << 8) | (0xff)
        
        self.add_flow(switch=self.datapath_list[src_sw], priority=200, match=match,
                      cookie=cookie, actions=action, idle_timeout=3600,insts=instr)
        
        self.configure_meter_band(switch=self.datapath_list[src_sw],rate=request.min_bw,
                                    meter_id=meter_id,command=ofproto.OFPMC_ADD)

    def _delete_meters_in_path(self, tos, path, request):
        dst_mac = self.arp_table[request.outter_dst_ip]
        dst_host = self.hosts[dst_mac]
        old_min_bw = self.request_table[tos].min_bw    
        for i in range(len(path)-1):
            src_sw = path[i]
            dst_sw = path[i+1]
            port_no = self.adjacency[src_sw][dst_sw]
            meter_id = ((port_no << 8) & PORT_NO_MASK) | (tos & TOS_MASK)
            self.sw_port[src_sw][port_no].available_bw += old_min_bw
            cookie = cookie = (meter_id << 8) | (0xff)
            
            self.del_flow(datapath=self.datapath_list[src_sw],cookie=cookie, cookie_mask=cookie)
            self.configure_meter_band(switch=self.datapath_list[src_sw],rate=request.min_bw,
                                      meter_id=meter_id,command=ofproto.OFPMC_DELETE)
        # Last port connect to dst_host
        src_sw = path[-1]
        port_no = dst_host[1]
        meter_id = ((port_no << 8) & PORT_NO_MASK) | (tos & TOS_MASK)
        self.sw_port[src_sw][port_no].available_bw += old_min_bw

        self.del_flow(datapath=self.datapath_list[src_sw],cookie=cookie, cookie_mask=cookie)
        self.configure_meter_band(switch=self.datapath_list[src_sw],rate=request.min_bw,
                                    meter_id=meter_id,command=ofproto.OFPMC_DELETE)

    def _get_paths(self, src_node, dst_node):
        '''
        Get all paths from src_node to dst_node using DFS algorithm    
        '''
        if SHOW_PATH == 1:
            print("################################################")
        if src_node == dst_node:
            # host target is on the same switch
            return [[src_node]]
        paths = []
        stack = [(src_node, [src_node])]
        
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
                if next is dst_node:
                    paths.append(path + [next])
                    
                    if VERBOSE == 1:
                        print("-paths",paths)
                else:
                    stack.append((next, path + [next]))
                    
                    if VERBOSE == 1:
                        print("--stack",stack)
        if SHOW_PATH == 1:
            print("################################################")
            print("Available paths from ", src_node, " to ", dst_node, " : ", paths)
        
        return paths

    def _get_shortest_paths(self, src_node, dst_node):
        paths = self._get_paths(src_node, dst_node)
        paths_count = len(paths) if len(
            paths) < MAX_PATHS else MAX_PATHS
        pw = []
        for path in paths:
            pw.append(len(path))
        return self._sorted_path(paths,pw)[0:(paths_count)],sorted(pw[0:(paths_count)])        
    
    def _sorted_path(self,paths,path_weight):
        '''
        Sorting paths based on path_weight
        '''
        zip_list = zip(path_weight,paths)
        sorted_zip_list = sorted(zip_list)
        sorted_list = [e for _, e in sorted_zip_list]
       
        return sorted_list

    def _get_port_bw_available(self, dpid, port_no):
        '''
        Get the bw availbe of a port
        '''
        return self.sw_port[dpid][port_no][1].available_bw    

    def _get_path_available_bw(self, path,last_port):
        '''
        Get the available bandwidth of path
        '''
        port_bw = []
        next_port = None

        for i in range(len(path) - 1):
            next_port = self.adjacency[path[i]][path[i+1]]
            port_bw.append(self._get_port_bw_available(next_port,path[i]))
            
        port_bw.append(self._get_port_bw_available(last_port, path[-1]))
        
        # Available bw of a physical path = minimum bw of physical links belong path
        return min(port_bw)
    
    def find_available_path(self, src_host, dst_host, demand_bw):
        '''
        - Find physical path which is best to map virtual link with demand_bw
        - A best physical path has smallest bandwidth in satisfying paths.
        - Return:
            - available path and their bandwidth.
        '''
        paths = self._get_paths(src_host[0], dst_host[0])
        # paths_count = len(paths) if len(paths) < MAX_PATHS else MAX_PATHS

        path_bw = []
        i = 0
        for path in paths:  
            path_bw = self._get_path_available_bw(path,dst_host[1])
            # Satisfying paths have bandwdith >= demand_bw of virtual link
            if (path_bw >= demand_bw):
                path_bw.append(path_bw)
            else:
                del paths[i]
            i = i + 1
        return self._sorted_path(paths,path_bw)[0],sorted(path_bw[0])

    def get_overload_meters(self, port_meters):  
        ovl_meters = []
        normalize = 0
        excess_bw = DEFAULT_BW/NUM_RANDOM
        for meter in port_meters:
            if meter.cr_bw_need > meter.guaranteed_bw:
                ovl_meters.append(meter)
                normalize += meter.guaranteed_bw
                excess_bw -= meter.guaranteed_bw
            else:
                excess_bw -= meter.cr_bw_need
        return ovl_meters, normalize, excess_bw
    
    def min_bw_algorithm_2(self):
        for sw_id in self.datapath_list.keys():
            # meters = self.meter_bands[sw_id]
            for port_no in self.sw_port[sw_id].keys():
                port_bw_usaged, port_meters = self.get_meters(sw_id,port_no)
                self.logger.info('port_bw_usaged %s',port_bw_usaged)
                
                ovl_meters,norm,excess_bw=self.get_overload_meters(port_meters)
                self.logger.info("excess_bw %s",excess_bw)
                for meter in port_meters:
                    new_bw_max = 0
                    if excess_bw >= 0:
                        if meter in ovl_meters:
                            new_bw_max = meter.guaranteed_bw*(1 + excess_bw/norm)   
                        
                        else:  
                            if meter.cr_bw_need:
                                new_bw_max = meter.cr_bw_need
                            else:
                                new_bw_max = BE_RATE*DEFAULT_BW

                        if not (0.95*meter.cr_bw_max <= new_bw_max <= 1.05*meter.cr_bw_max):
                            meter.cr_bw_max = new_bw_max
                            self.configure_meter_band(switch=self.datapath_list[sw_id],rate=int(meter.cr_bw_max),
                                                    burst=int(meter.guaranteed_bw),meter_id=meter.meter_id, 
                                                    command=ofproto.OFPMC_MODIFY)
                            
    def configure_meter_band(self, switch, rate, meter_id, burst=None, command=ofproto.OFPMC_ADD):

        burst_size = burst if burst else int(2*rate)  # Default burst size = 2 * rate limit
        dropband = of_parser.OFPMeterBandDrop(rate=rate, burst_size=burst_size) # Only use drop band
        request = of_parser.OFPMeterMod(datapath=switch, 
                                   command=command, 
                                   flags=ofproto.OFPMF_KBPS|ofproto.OFPMF_BURST|ofproto.OFPMF_STATS, 
                                   meter_id=meter_id, 
                                   bands=[dropband])
        switch.send_msg(request)

    def _monitor(self):
        while True:
            for switch_id in self.datapath_list.keys():
                dp = self.datapath_list[switch_id]
                # QoS flow has cookie mask 
                self._request_flow_stats(dp,cookie=0xffffff,cookie_mask=QOS_FLOW_MASK)
            hub.sleep(self.sleep)

    def _request_flow_stats(self, datapath, cookie=0, cookie_mask=0):
        match = None
        req = of_parser.OFPFlowStatsRequest(datapath=datapath, cookie=cookie, 
                                            cookie_mask=cookie_mask, match=match)
        datapath.send_msg(req)

    def del_flow(self, datapath, cookie, cookie_mask):
        mod = of_parser.OFPFlowMod(datapath=datapath,command=ofproto.OFPFC_DELETE,
                                cookie=cookie,cookie_mask=cookie_mask)
        datapath.send_msg(mod)

    def add_flow(self, datapath, priority, match, actions, idle_timeout=0, 
                buffer_id=None,insts=None,table_id=0,cookie=0,cookie_mask=0):
        # print "Adding flow ", match, actions
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,
                                             actions)]
        if not cookie_mask:
            cookie_mask = cookie_mask
        if insts:
            inst.append(insts)
        if buffer_id:
            mod = parser.OFPFlowMod(datapath=datapath, buffer_id=buffer_id,idle_timeout=idle_timeout,
                                    priority=priority, match=match,cookie=cookie,cookie_mask=cookie_mask,
                                    instructions=inst,table_id=table_id)

        else:
            mod = parser.OFPFlowMod(datapath=datapath,idle_timeout=idle_timeout, priority=priority,
                                    cookie=cookie,cookie_mask=cookie_mask, match=match, 
                                    instructions=inst,table_id=table_id)
        datapath.send_msg(mod)

    def add_ports_to_paths(self, paths, first_port, last_port):
        '''
        Add the ports that connects the switches for all paths
        '''
        paths_p = []
        for path in paths:
            p = {}
            in_port = first_port
            # print("-----")
            # print(path[:-1],"\n", path[1:])
            for s1, s2 in zip(path[:-1], path[1:]):
                out_port = self.adjacency[s1][s2]
                # print('s',s1,s2,out_port)
                p[s1] = (in_port, out_port)
                in_port = self.adjacency[s2][s1]
            p[path[-1]] = (in_port, last_port)
            paths_p.append(p)

        return paths_p

    def install_paths_arp(self, src, first_port, dst, last_port, ip_src, ip_dst):
        self.LEARNING = 1
        paths,pw = self.get_optimal_paths(src, dst,first_port,last_port)
        pw = pw[0]
        path = paths[0]

        paths_with_ports = self.add_ports_to_paths(paths, first_port, last_port)
        paths_with_ports = paths_with_ports[0]

        if VERBOSE == 1:
            print(paths_with_ports)
            # print(pw)
            print("#adjacency",self.adjacency)

        for node in paths[0]:

            dp = self.datapath_list[node]
            ofp_parser = dp.ofproto_parser

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
                be_meter_id = ((out_ports[0][0] << 8) & PORT_NO_MASK)
                actions = [ofp_parser.OFPActionOutput(out_ports[0][0])]
                # Goto port's BE meter
                instr = [ofp_parser.OFPInstructionMeter(be_meter_id)]
                self.add_flow(dp, 1, match_arp, actions,IDLE_TIMEOUT,insts=instr)
        return paths_with_ports[src][1]
    
    def install_paths(self, src, first_port, dst, last_port, ip_src, ip_dst,ip_proto,tos):
        self.LEARNING = 1
        direction = 0
        if tos:
            paths = self.qos_paths[tos]
            request = self.request_table[tos]
            if (request.outter_src_ip, request.outter_dst_ip) == (ip_src,ip_dst):
                direction = SAME_DIRECTION
            else:
                direction = REVERSE_DIRECTION
        else:
            paths = self._get_shortest_paths(src,dst)

        paths_with_ports = self.add_ports_to_paths(paths, first_port, last_port)
        paths_with_ports = paths_with_ports[0]

        if VERBOSE == 1:
            print(paths_with_ports)
            # print(pw)
            print("#adjacency",self.adjacency)

        for node in paths[0]:
            dp = self.datapath_list[node]
            ofp_parser = dp.ofproto_parser
            ports = defaultdict(list)
            actions = []
      
            if node in paths_with_ports:
                in_port = paths_with_ports[node][0]
                out_port = paths_with_ports[node][1]
                if (out_port) not in ports[in_port]:
                    ports[in_port].append((out_port))
        
            if VERBOSE == 1:
                print("-------------------------------")
                print("\tnode {}: ports{}".format(node,ports) ) 

            for in_port in ports:
                out_ports = ports[in_port]
                actions = [ofp_parser.OFPActionOutput(out_ports[0][0])]
                meter_id = ((out_ports[0][0] << 8) & PORT_NO_MASK) 
                cookie = 0
                if direction == SAME_DIRECTION:
                    meter_id = ((out_ports[0][0] << 8) & PORT_NO_MASK) | (tos & TOS_MASK) 
                    cookie = (meter_id << 8) | (0xff)
                else:
                    meter_id = ((out_ports[0][0] << 8) & PORT_NO_MASK)

                instr = [ofp_parser.OFPInstructionMeter(meter_id)]
                if ip_proto == 1:
                # Ipv4
                    match_icmp = ofp_parser.OFPMatch(
                        eth_type=0x0800,
                        ip_proto=1,
                        ipv4_src=ip_src, 
                        ipv4_dst=ip_dst,
                    )
                    self.add_flow(dp, 3, match_icmp, actions,IDLE_TIMEOUT,insts=instr)        


                    
                if ip_proto == 6: # TCP
                    match_tcp = ofp_parser.OFPMatch(
                        eth_type=0x0800,
                        ip_proto=6,
                        ipv4_src=ip_src, 
                        ipv4_dst=ip_dst,
                    )
                    self.add_flow(dp, 10, match_tcp, actions,IDLE_TIMEOUT,insts=instr)

    
                elif ip_proto == 17: # UDP
                    match_udp= ofp_parser.OFPMatch(
                        eth_type_nxm=0x0800, 
                        ip_proto_nxm=17,
                        ipv4_src=ip_src, 
                        ipv4_dst=ip_dst,
                        ip_ecn=(tos >> 6) & 0xff,
                        ip_dscp=(tos << 2) & 0xff
                    )
                    self.add_flow(dp, 12, match_udp, actions,IDLE_TIMEOUT,insts=instr,cookie=cookie,cookie_mask=cookie)

        # print("Path installation finished in ", time.time() - computation_start )
        # print(paths_with_ports[0][src][1])
        return paths_with_ports[src][1]

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

    @set_ev_cls(event.EventSwitchEnter)
    def switch_enter_handler(self, ev):
        switch = ev.switch.dp
        ports = ev.switch.ports
        
        self.logger.info("ALL_SW: %s",ev.switch)
        
        if VERBOSE == 1:
            print("Switch In: ",switch.id)

        if switch.id not in self.switches:
            self.switches.append(switch.id)
            self.datapath_list[switch.id] = switch

            # Request port/link descriptions, useful for obtaining bandwidth
            req = of_parser.OFPPortDescStatsRequest(switch)
            switch.send_msg(req)

            for port in ports:
                port_name = port.name.decode('utf-8')
                # By default, a port has bandwidth = DEFAULT_BW
                #  and doesn't have meter-band limit
                self.sw_port[switch.id][port.port_no] = PortAttr(port_name)
                # ex: 0x0100 id be meter_id of port 1
                be_meter_id = ((port.port_no << 8) & PORT_NO_MASK)
                self.meter_bands[switch.id] = MeterAttr(be_meter_id,port.port_no,BE_RATE*DEFAULT_BW)
                self.configure_meter_band(switch=switch,rate=DEFAULT_BW, meter_id=be_meter_id)
        
        # self.logger.info("ALL_SW: %s",self.sw_port)

    @set_ev_cls(event.EventLinkAdd, MAIN_DISPATCHER)
    def link_add_handler(self, ev):
        s1 = ev.link.src
        s2 = ev.link.dst
        
        # Set default bandwith for a new link
        self.adjacency[s1.dpid][s2.dpid] = s1.port_no
        self.adjacency[s2.dpid][s1.dpid] = s2.port_no

    @set_ev_cls(ofp_event.EventOFPPortStatus, MAIN_DISPATCHER)
    def port_status_handler(self, ev):
        msg = ev.msg
        dp = msg.datapath

        if msg.reason == ofproto.OFPPR_ADD:
            reason = 'ADD'
        elif msg.reason == ofproto.OFPPR_DELETE:
            reason = 'DELETE'
            
        elif msg.reason == ofproto.OFPPR_MODIFY:
            reason = 'MODIFY'
            
        else:
            reason = 'unknown'
            
        # port = msg.desc.port_no

        port_attr = msg.desc
        
        self.logger.info('OFPPortStatus received: reason=%s desc=%s' ,
                          reason, msg.desc)
        
        out_port = port_attr.port_no
        host_dist = False
        remove_host = []
        if port_attr.state == 1:
            for host in self.hosts:
                if out_port == self.hosts[host][1] and self.hosts[host][0] == dp.id:
                    host_dist = True
                    self.logger.info("Host %s disconnected: dpid:%d port:%d " % (host,self.hosts[host][0],self.hosts[host][1]))
                    # del self.hosts[host]
                    remove_host.append(host)
                    ip = self.get_ip(host)
                    del self.arp_table[ip]
                    # self.logger.info("arp %s  " % (self.hosts)
            if host_dist == False:
            
                #del port flow and group
                self.logger.info("Port sw-sw down")
                for i in self.datapath_list.keys():
                    # self.delete_flow(self.datapath_list[i],0)
                    self.logger.info("Reset Topo And ready to install path")
                    self.delete_group_mod(self.datapath_list[i])
       
                
                self.multipath_group_ids = {}
                self.group_id_count =0
                self.group_ids = []
                # self.arp_table = {}
                self.sw_port = {}
                # self.hosts = {}
                return
                #del flow and group ...    
            else:
                #del host flow and group
                for host in remove_host:
                    del self.hosts[host]
                for i in self.datapath_list.keys():
                    # self.delete_flow(self.datapath_list[i],0)
                    self.logger.info("Reset Topo And ready to install path")
                    self.delete_group_mod(self.datapath_list[i])
                    self.multipath_group_ids = {}
                    self.group_id_count =0
                    self.group_ids = []
                    # self.arp_table = {}
                    self.sw_port = {}
           
        elif port_attr.state == 0:
            pass  

    @set_ev_cls(ofp_event.EventOFPFlowStatsReply, MAIN_DISPATCHER)
    def flow_stats_reply_handler(self, ev):
        flows = []
        msg = ev.msg
        dp = msg.datapath
        meters = self.meter_bands[dp.id]
        
        for stat in ev.msg.body:
            flows.append('table_id=%s '
                        'duration_sec=%d duration_nsec=%d '
                        'priority=%d '
                        'idle_timeout=%d hard_timeout=%d flags=0x%04x '
                        'cookie=%d packet_count=%d byte_count=%d '
                        'match=%s instructions=%s' %
                        (stat.table_id,
                        stat.duration_sec, stat.duration_nsec,
                        stat.priority,
                        stat.idle_timeout, stat.hard_timeout, stat.flags,
                        stat.cookie, stat.packet_count, stat.byte_count,
                        stat.match, stat.instructions)) 
            if stat.cookie & QOS_FLOW_MASK:
                meter_id = (stat.cookie >> 8) & (0xffff)
                for meter in meters:
                    if meter.meter_id == meter_id:
                        arrival_sec = float((stat.duration_sec - meter.last_sec) + (stat.duration_nsec - meter.last_nsec)/NSEC)
                        arival_byte_in = stat.byte_count - meter.last_byte_in

                        meter.cr_bw_need = int(arival_byte_in / arrival_sec)
                        meter.cr_bw_need = int((8*meter.cr_bw_need)/1000)

                        meter.last_byte_in = stat.byte_count
                        meter.last_sec = stat.duration_sec
                        meter.last_nsec = stat.duration_nsec
                        
                        self.logger.info('Meter_id: %s, Meter.cr_bw_need: %s\n',
                                        meter.meter_id, meter.cr_bw_need)

        self.logger.debug('FlowStats: %s', flows)      

    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        msg = ev.msg
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        in_port = msg.match['in_port']


        pkt = packet.Packet(msg.data)
        eth = pkt.get_protocol(ethernet.ethernet)
        arp_pkt = pkt.get_protocol(arp.arp)


        # avoid broadcast from LLDP
        if eth.ethertype == 35020:
            return
        
        # Drop the IPV6 Packets.
        if pkt.get_protocol(ipv6.ipv6):  
            match = parser.OFPMatch(eth_type=eth.ethertype)
            actions = []
            self.add_flow(datapath, 1, match, actions)
            return None


        dst = eth.dst
        src = eth.src
        dpid = datapath.id


        if src not in self.hosts:
            self.hosts[src] = (dpid, in_port)
            if VERBOSE == 1:
                print("-----------------------------------")
                print("\t\tHost_learned: ",self.hosts)
                print("-----------------------------------")
        
        # IPv4, UDP, TCP fields
        out_port = ofproto.OFPP_FLOOD
        ip_pkt = pkt.get_protocol(ipv4.ipv4)
        tos = 0 # default TOS bits
        dst_port = 0
        ip_proto = -1
           
        # Parsing ARP packets
        if arp_pkt:
            self.LEARNING = 1
            # print dpid, pkt
            if VERBOSE == 1:
                print("datapath id: "+str(dpid))
                print("port: "+str(in_port))
                print(("pkt_eth.dst: " + str(eth.dst)))
                print(("pkt_eth.src: " + str(eth.src)))
                print(("pkt_arp: " + str(arp_pkt)))
                print(("pkt_arp:src_ip: " + str(arp_pkt.src_ip)))
                print(("pkt_arp:dst_ip: " + str(arp_pkt.dst_ip)))
                print(("pkt_arp:src_mac: " + str(arp_pkt.src_mac)))
                print(("pkt_arp:dst_mac: " + str(arp_pkt.dst_mac)))
                # dst_mac will be 00:00:00:00:00:00 when host is unknown (ARPRequest)
            
            src_ip = arp_pkt.src_ip
            dst_ip = arp_pkt.dst_ip

            if arp_pkt.opcode == arp.ARP_REPLY:
                # ARP table IP - MAC
                self.arp_table[src_ip] = src
                h1 = self.hosts[src]
                h2 = self.hosts[dst]
                # self.logger.info("VXPORT %s"%vx_dst_port)
                
                #Install path: dpid src, src in_port, dpid dst, dpid in_port, src_ip, dst_ip
                if VERBOSE == 1:
                    print("Installing: Src:{}, Src in_port{}. Dst:{}, Dst in_port:{}, Src_ip:{}, Dst_ip:{}".format(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip,dst_port))
                out_port = self.install_paths_arp(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip,ip_proto,dst_port,src_ip, dst_ip)
                self.install_paths_arp(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip,ip_proto,dst_port,src_ip, dst_ip) # reverse
            elif arp_pkt.opcode == arp.ARP_REQUEST:
                if dst_ip in self.arp_table:
                    # print("dst_ip found in arptable")
                    self.arp_table[src_ip] = src
                    dst_mac = self.arp_table[dst_ip]
                    h1 = self.hosts[src]
                    h2 = self.hosts[dst_mac]
                    out_port = self.install_paths_arp(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip)
                    self.install_paths_arp(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip) # reverse
            if VERBOSE == 1:
                print("--arptable",self.arp_table)

        # Parsing IPv4 packets
        if isinstance(ip_pkt,ipv4.ipv4):
            ip_proto = ip_pkt.proto
            src_ip = ip_pkt.src
            dst_ip = ip_pkt.dst

            if ip_proto == 6: # TCP
                tcp_pkt = pkt.get_protocol(tcp.tcp)
                dst_port = tcp_pkt.dst_port

            elif ip_proto == 17: # UDP
                udp_pkt = pkt.get_protocol(udp.udp)
                dst_port = udp_pkt.dst_port

                # Only get TOS bits in UDP packets
                if ip_pkt.tos:
                    tos =  ip_pkt.tos
                
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