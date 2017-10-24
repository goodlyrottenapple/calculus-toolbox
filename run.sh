#!/bin/sh

docker build -t calculus-toolbox .

if [[ "$OSTYPE" == "darwin"* ]]; then
    #ip=$(ifconfig en0 | grep inet | awk '$1=="inet" {print $2}')
    #xhost + $ip
    docker run -ti -v ${PWD}/calculi:/root/calculi calculus-toolbox
else
    docker run -ti -v ${PWD}/calculi:/root/calculi -e DISPLAY=$DISPLAY calculus-toolbox
fi
