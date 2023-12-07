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

from libovsdb import libovsdb
import json
from ryu.lib.ovs import bridge
from ryu.ofproto import nx_match
import numpy as np
from dataclasses import dataclass

# Mark port has QoS meter
NONE_QOS = 0 
HAVE_QOS = 1

# Cookie mask
COOKIE_MASK = 1 >> 8

# Best-effort meter id
BE_METER_ID = 1000

# Request types
REQUEST_CREATE = 0
REQUEST_MODIFY = 1
REQUEST_DELETE = 2


# HFSC take almost 0.95 of link BW
# DEFAULT_BW = int(1000000000/0.94)
# DEFAULT_BW = 100000000
DEFAULT_BW = 1000000000

DEFAULT_TABLE = 100

MAX_PATHS = 10


VERBOSE = 0
DEBUGING = 0
SHOW_PATH = 0

DEFAULT_FLOW_PRIORITY = 0
IDLE_TIMEOUT = 150

@dataclass
class PortAttr:
    have_qos: bool = NONE_QOS 
    available_bw: int = DEFAULT_BW

class ProjectController(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto.OFP_VERSION]


    def __init__(self, *args, **kwargs):
        super(ProjectController, self).__init__(*args, **kwargs)
        self.mac_to_port = {}
        self.LEARNING = 1
        self.FLAG = 0
        self.request_id = 1
        self.new_request = False
        
        self.topology_api_app = self
        self.datapath_list = {} #{switch_id:datapath}
        self.arp_table = {} #{IP:MAC}
        self.switches = [] #[switch_id]
        self.hosts = {} #{MAC:(switch_id, in_port)}
        self.multipath_group_ids = {}
        self.all_group_id = {}
        self.group_id_count =0
        self.group_ids = []
        self.adjacency = defaultdict(defaultdict(list)) #{src_sw_id:{dst_sw_id:[port_no, PortAttr(have_qos, available_bw)]}}
        self.bandwidths = defaultdict(lambda: defaultdict(lambda: DEFAULT_BW))
        self.sw_port = defaultdict(defaultdict(list)) # {switch_id:{port_no:[port_name,PortAttr(have_qos,available_bw)]}}
        self.count = 0
        self.path_install_cnt =0
        
        self.max_bw = {}
        self.curr_max_bw = {}
        self.sw_reserve_bw = defaultdict(dict)
        self.port_reserve_bw = defaultdict(dict)
        

        self.qos_flows_cookie = defaultdict(int) # {switch_id:cookie}
        self.meter_bands = defaultdict(defaultdict(list)) #{switch_id:{meter_id:[rate,in_port,out_port]}}
        self.request_table = defaultdict(list) #{meter_id:[path,bw]}
        
        self.init_bw_max = defaultdict(defaultdict(int)) #{switch_id:{meter_id:[init_bw_max,in_port,out_port}}
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

    def get_paths(self, src_node, dst_node):
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

    def sorted_path(self,paths,path_weight):
        '''
        Sorting paths based on path_weight
        '''
        zip_list = zip(path_weight,paths)
        sorted_zip_list = sorted(zip_list)
        sorted_list = [e for _, e in sorted_zip_list]
       
        return sorted_list

    def get_port_bw_available(self, dpid, port_no,):
        '''
        Get the bw availbe of a port
        '''
        return self.sw_port[dpid][port_no][1].available_bw
    

    def get_path_available_bw(self, path,first_port,last_port):
        '''
        Get the available bandwidth of path
        '''
        port_bw = []
        next_port = None

        port_bw.append(self.get_port_bw_available(first_port, path[0]))
        for i in range(len(path) - 1):
            next_port = self.adjacency[path[i]][path[i+1]]
            port_bw.append(self.get_port_bw_available(next_port,path[i]))
            
        port_bw.append(self.get_port_bw_available(last_port, path[-1]))
        
        # Available bw of a physical path = minimum bw of physical links belong path
        return min(port_bw)
    
    def find_available_path(self, host1, host2, demand_bw):
        '''
        - Find physical path which is best to map virtual link with demand_bw
        - A best physical path has smallest bandwidth in satisfying paths.
        - Return:
            - available path and their bandwidth.
        '''
        paths = self.get_paths(host1[0], host2[0])
        paths_count = len(paths) if len(paths) < MAX_PATHS else MAX_PATHS

        path_bw = [0]
        i = 0
        for path in paths:  
            path_bw = self.get_path_available_bw(path,host1[1],host1[2])
            # Satisfying paths have bandwdith >= demand_bw of virtual link
            if (path_bw >= demand_bw):
                path_bw.append(path_bw)
            else:
                del paths[i]
            i = i + 1
        return self.sorted_path(paths,path_bw)[0],sorted(path_bw[0])

    def handle_new_reserve_bw_request(self, src_ip , dst_ip, guaranted_bw, request_id):
        pass
    def handle_modify_reserve_bw_request(self, src_ip , dst_ip, guaranted_bw, request_id):
        pass
    def handle_delete_reserve_bw_request(self, src_ip , dst_ip, guaranted_bw, request_id):
        pass

    def handle_reserve_bw_request(self, src_ip , dst_ip, guaranted_bw, request_id, request_type):
        '''
        - Handle a reserve bw request
        - A request will have: 
            - IP address's src and dst host which VMs belong
            - guaranted_bw: Virtual link's guaranted BW
            - Request_id: TOS bits of virtual link
            - Request type: 
        Return:
           - Fail: -1
           - Succeed: positive number
           - If mapping successed: A positive number which will be TOS bits of Virtual link's traffic
           - If mapping fail: -1  
        '''
        ret = -1
        if request_type == REQUEST_CREATE:
                ret = self.handle_new_reserve_bw_request(self, src_ip , dst_ip, guaranted_bw, request_id)
        elif request_type == REQUEST_MODIFY:
            if self.request_table[request_id]:
                ret = self.handle_modify_reserve_bw_request(self, src_ip , dst_ip, guaranted_bw, request_id)
        elif request_type == REQUEST_DELETE:
            ret = self.handle_delete_reserve_bw_request(self, src_ip , dst_ip, guaranted_bw, request_id)
        src_mac = self.arp_table[src_ip]
        dst_mac = self.arp_table[dst_ip]

        host1 = self.hosts[src_mac]
        host2 = self.hosts[dst_mac]

        path,paths_bw = self.find_available_paths(host1,host2,guaranted_bw); 
        if not path or not paths_bw:
            return ret
        
        
        return ret

    def configure_meter_band(self, switch ,rate, burst=0.1, meter_id=BE_METER_ID, command=ofproto.OFPMC_ADD):
        bands = []
        burst_Size = rate * burst # Default burst size = 1/10 rate limit
        dropband = of_parser.OFPMeterBandDrop(rate=rate, burst_size=burst_Size) # Only use drop band
        bands.append(dropband)
        request = of_parser.OFPMeterMod(datapath=switch, 
                                   command=command, 
                                   flags=ofproto.OFPMF_KBPS, 
                                   meter_id=meter_id, 
                                   bands=bands)
        switch.send_msg(request)

    def _monitor(self):
        while True:
            for switch_id in self.datapath_list.keys():
                dp = self.datapath_list[switch_id]
                # Monitor meter in switches
                if self.meter_bands[switch_id]:
                    self._request_meter_stats(dp)
            hub.sleep(self.sleep)

    def _request_meter_stats(self, datapath, meter_id=ofproto.OFPM_ALL):
        self.logger.debug('send meter stats request: %016x', datapath.id)

        #Send MeterStatsRequest
        req = of_parser.OFPMeterStatsRequest(datapath, 0, meter_id=meter_id)
        datapath.send_msg(req)

    @set_ev_cls(ofp_event.EventOFPMeterStatsReply, MAIN_DISPATCHER)
    def meter_stats_reply_handler(self, ev):
        meters = []
        msg = ev.msg
        switch = msg.datapath

        meters = self.meter_bands[switch.id] # Meters in this switch

        for stat in msg.body:
            meters.append('meter_id=0x%08x len=%d flow_count=%d '
                        'packet_in_count=%d byte_in_count=%d '
                        'duration_sec=%d duration_nsec=%d '
                        'band_stats=%s' %
                        (stat.meter_id, stat.len, stat.flow_count,
                        stat.packet_in_count, stat.byte_in_count,
                        stat.duration_sec, stat.duration_nsec,
                        stat.band_stats))
        self.logger.debug('MeterStats: %s', meters) 

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
            self.meter_bands[switch.id][BE_METER_ID] = (DEFAULT_BW, ofproto.OFPP_ANY, ofproto.OFPP_ANY)
            self.init_bw_max[switch.id][BE_METER_ID] = DEFAULT_BW

            # Add a default Best-effort meter-band in every new switch.
            self.configure_meter_band(switch ,DEFAULT_BW)

            # Request port/link descriptions, useful for obtaining bandwidth
            req = of_parser.OFPPortDescStatsRequest(switch)
            switch.send_msg(req)

            for port in ports:
                port_name = port.name.decode('utf-8')
                # By default, a port has bandwidth = DEFAULT_BW
                #  and doesn't have meter-band limit
                self.sw_port[switch.id][port.port_no] = [port_name,PortAttr(NONE_QOS,DEFAULT_BW)]
        
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