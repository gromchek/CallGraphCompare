#!/bin/bash

run_410() {
    python CmpCallGraph.py 335_call_graph.json 410_call_graph.json -j 14 -o 410.txt --grouped
}

run_501() {
    python CmpCallGraph.py 335_call_graph.json 501_call_graph.json -j 14 -o 501.txt --grouped
}

run_053() {
    python CmpCallGraph.py 335_call_graph.json 053_call_graph.json -j 14 -o 053.txt --grouped
}

case "$1" in
    410)
        run_410
        ;;
    501)
        run_501
        ;;
    053)
        run_053
        ;;
    all)
        run_410
        run_501
        run_053
        ;;
    *)
        echo "Usage: $0 {410|501|053|all}"
        exit 1
        ;;
esac