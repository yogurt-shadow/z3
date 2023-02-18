import os
import sys

if __name__ == "__main__":
    path = sys.argv[1]
    dir_list = os.listdir(path)
    print("Number of files in '", path, "' :", len(dir_list))

    num_timeout = 0
    num_unsat = 0
    num_sat = 0
    num_unknown = 0
    num_memoryout = 0

    with open("listing.txt", "w") as f2:
        for p in sorted(dir_list):
            with open(path + "/" + p, "r") as f:
                line = f.readline().strip()
                if line == "sat":
                    num_sat += 1
                elif line == "unsat":
                    num_unsat += 1
                elif line == "timeout":
                    num_timeout += 1
                elif line == "unknown":
                    num_unknown += 1
                elif line == "memoryout":
                    num_memoryout += 1
                else:
                    raise NotImplementedError("First line is", line)
                f2.write(p + "\t" + line + "\n")
    print("#SAT     = ", num_sat)
    print("#UNSAT   = ", num_unsat)
    print("#TIMEOUT = ", num_timeout)
    print("#UNKNOWN = ", num_unknown)
    print("#MEMORY  = ", num_memoryout)


