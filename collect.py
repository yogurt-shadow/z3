import os
import sys
import csv

# 20161105-Sturm-MBO/mbo_E10E24.smt2
def process_name(file):
    split_parts = file.split('/')
    family_name, file_name_pre = split_parts[0], split_parts[-1]
    file_name = file_name_pre.rsplit('.', 1)[0]
    return file_name, family_name


'''
benchmark   family    result
'''
def collect_infos(folder, files, data):
    data.append(["benchmark", "family", "result"])
    timeout, total, sat, unsat, unknown = 0, 0, 0, 0, 0
    for file in files:
        total += 1
        file_name, family_name = process_name(file)
        with open(folder + file_name + ".txt", 'r', encoding='utf-8') as f:
            res = f.readline().strip()
            if res == "sat":
                sat += 1
            elif res == "unsat":
                unsat += 1
            else:
                unknown += 1
                if res == "timeout":
                    timeout += 1
        data.append([file_name, family_name, res])
    data.append([])
    data.append(["total", "sat", "unsat", "solved", "timeout", "unsolved"])
    data.append([total, sat, unsat, sat + unsat, timeout, unknown])
    
if __name__ == "__main__":
    folder = sys.argv[1]
    result = sys.argv[2]
    file_names = [line.strip() for line in open("list.txt", "r").readlines()]
    data = []
    collect_infos(folder, file_names, data)
    with open(result, "w") as csvfile:
        writer = csv.writer(csvfile)
        writer.writerows(data)
    
