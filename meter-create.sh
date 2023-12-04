#!/bin/bash

sudo ovs-ofctl del-meters s1 -O OpenFlow13
sudo ovs-ofctl add-meter s1 meter=1,kbps,band=type=drop,rate=10000 -O OpenFlow13
sudo ovs-ofctl add-meter s1 meter=2,kbps,band=type=drop,rate=20000 -O OpenFlow13
sudo ovs-ofctl add-meter s1 meter=3,kbps,band=type=drop,rate=30000 -O OpenFlow13
sudo ovs-ofctl add-meter s1 meter=1000,kbps,band=type=drop,rate=40000 -O OpenFlow13
sudo ovs-ofctl add-meter s1 meter=1001,kbps,band=type=drop,rate=100000 -O OpenFlow13
sudo ovs-ofctl add-meter s1 meter=1002,kbps,band=type=drop,rate=100000 -O OpenFlow13
sudo ovs-ofctl dump-meters s1 -O OpenFlow13
