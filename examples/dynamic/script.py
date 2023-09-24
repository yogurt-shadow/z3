import os
import subprocess
import sys


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise OSError("input arguments wrong")
    else:
        destination = "/home/wangzh/z3/examples/dynamic/debug" + sys.argv[1] + "/"
        file_name = "trace" + sys.argv[1] + ".debug"
        error_bench = []
        for line in open(file_name):
            if "system error:" in line:
                for ele in line.strip().split(' '):
                    if ".smt2" in ele:
                        command = "cp -r " + ele + " " + destination
                        error_bench.append(ele)
                        os.system(command)
    print("#error: ", len(error_bench))