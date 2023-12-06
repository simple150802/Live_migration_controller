#!/bin/bash

# Delete all exsited flow 
sudo ovs-ofctl del-flows s1 -O OpenFlow13

# Each port have a max rate
#sudo ovs-ofctl add-flow s1 -O Openflow13 priority=200,table=0,in_port=1,actions=meter:1001,goto_table:1
#sudo ovs-ofctl add-flow s1 -O Openflow13 priority=200,table=0,in_port=2,actions=meter:1002,goto_table:1
sudo ovs-ofctl add-flow s1 -O Openflow13 priority=200,table=0,in_port=1,actions=goto_table:1  
sudo ovs-ofctl add-flow s1 -O Openflow13 priority=200,table=0,in_port=2,actions=goto_table:1 

# FLow for meter 1
#sudo ovs-ofctl add-flow s1 -O OpenFlow13 cookie=0x01,priority=200,table=1,in_port=1,ip,tcp,tcp_dst=1000,actions=meter:1,output:2
#sudo ovs-ofctl add-flow s1 -O OpenFlow13 priority=200,table=1,in_port=2,ip,tcp,tcp_src=1000,actions=meter:1,output:1
sudo ovs-ofctl add-flow s1 -O OpenFlow13 cookie=0x01,priority=200,table=1,in_port=1,ip,udp,udp_dst=1000,actions=meter:1,output:2
#sudo ovs-ofctl add-flow s1 -O OpenFlow13 cookie=0x01,priority=200,table=2,in_port=1,ip,udp,udp_dst=1000,actions=output:2
#sudo ovs-ofctl add-flow s1 -O OpenFlow13 priority=200,table=1,in_port=2,ip,udp,udp_src=1000,actions=meter:1,output:1

# Flow for meter 2
#sudo ovs-ofctl add-flow s1 -O OpenFlow13 cookie=0x02,priority=200,table=1,in_port=1,ip,tcp,tcp_dst=2000,actions=meter:2,output:2
#sudo ovs-ofctl add-flow s1 -O OpenFlow13 priority=200,table=1,in_port=2,ip,tcp,tcp_src=2000,actions=meter:2,output:1
sudo ovs-ofctl add-flow s1 -O OpenFlow13 cookie=0x02,priority=200,table=1,in_port=1,ip,udp,udp_dst=2000,actions=meter:2,output:2
#sudo ovs-ofctl add-flow s1 -O OpenFlow13 cookie=0x02,priority=200,table=2,in_port=1,ip,udp,udp_dst=2000,actions=output:2
#sudo ovs-ofctl add-flow s1 -O OpenFlow13 priority=200,table=1,in_port=2,ip,udp,udp_src=2000,actions=meter:2,output:1

# FLow for meter 3
#sudo ovs-ofctl add-flow s1 -O OpenFlow13 priority=200,table=1,in_port=2,ip,tcp,tcp_src=3000,actions=meter:3,output:1
#sudo ovs-ofctl add-flow s1 -O OpenFlow13 priority=200,table=1,in_port=1,ip,tcp,tcp_dst=3000,actions=meter:3,output:2
#sudo ovs-ofctl add-flow s1 -O OpenFlow13 priority=200,table=1,in_port=2,ip,udp,udp_src=3000,actions=meter:3,output:1
#sudo ovs-ofctl add-flow s1 -O OpenFlow13 priority=200,table=1,in_port=1,ip,udp,udp_dst=3000,actions=meter:3,output:2

# Flow for BE traffic
sudo ovs-ofctl add-flow s1 -O OpenFlow13 cookie=1000,priority=100,table=1,in_port=1,actions=meter:1000,output:2
sudo ovs-ofctl add-flow s1 -O OpenFlow13 cookie=1000,priority=100,table=1,in_port=2,actions=output:1

sudo ovs-ofctl dump-flows s1 -O OpenFlow13
