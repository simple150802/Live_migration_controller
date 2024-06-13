#!/bin/bash

sudo ovs-ofctl del-meters s1 -O OpenFlow13
sudo ovs-ofctl add-meter s1 meter=1,kbps,band=type=drop,rate=3000 -O OpenFlow13
sudo ovs-ofctl add-meter s1 meter=2,kbps,band=type=drop,rate=7000 -O OpenFlow13
#sudo ovs-ofctl add-meter s1 meter=3,kbps,band=type=drop,rate=30000 -O OpenFlow13
sudo ovs-ofctl add-meter s1 meter=1000,kbps,band=type=drop,rate=100 -O OpenFlow13
sudo ovs-ofctl add-meter s1 meter=1001,kbps,burst,band=type=drop,rate=10000,burst_size=10000 -O OpenFlow13
sudo ovs-ofctl add-meter s1 meter=1002,kbps,burst,band=type=drop,rate=10000,burst_size=10000 -O OpenFlow13
sudo ovs-ofctl dump-meters s1 -O OpenFlow13
