#include <iostream>
#include <fstream>
#include <vector>
#include <string>

using namespace std;

const string instance_path = "../ls_instance_server.txt";

const string output_path = "z3_nra_newest.csv";
const string input_folder = "z3_nra_newest/"; 

vector<string> instance_vec;

string get_instance_name(string str) {
    int idx1 = -1, idx2 = -1;
    for(int i = str.length() - 1; i >= 0; i--) {
        if(str[i] == '.' && idx2 == -1) {
            idx2 = i;
        }
        if(str[i] == '/') {
            idx1 = i;
            break;
        }
    }
    return str.substr(idx1 + 1, idx2 - idx1 - 1);
}

void read_instances() {
    ifstream inFile(instance_path);
    string line;
    while(getline(inFile, line)) {
        instance_vec.push_back(get_instance_name(line));
    }
}

string get_number(string str) {
    int idx1 = -1, idx2 = -1;
    for(unsigned i = 0; i < str.length(); i++) {
        if(str[i] >= '0' && str[i] <= '9' && idx1 == -1) {
            idx1 = i;
        }
        if(!((str[i] >= '0' && str[i] <= '9') || str[i] == '.') && idx1 != -1 && idx2 == -1) {
            idx2 = i;
            break;
        }
    }
    return idx2 != -1 ? str.substr(idx1, idx2 - idx1) : str.substr(idx1, str.length() - idx1);
}

void write_statistics() {
    unsigned sat = 0, unsat = 0, unknown = 0, total = 0;
    ofstream outFile(output_path);
    outFile << "name, result, bool var, arith var, conflict, decision, stage, learned added\n";
    for(auto curr_instance: instance_vec) {
        total++;
        ifstream inFile(input_folder + curr_instance + ".txt");
        string line;
        unsigned idx = 0;
        string curr_result, curr_bool, curr_arith, curr_conf, curr_dec, curr_stg, curr_added;
        while(getline(inFile, line)) {
            if(idx == 0) {
                curr_result = line;
            }
            else if(line.find(":nlsat-arith-vars") != string::npos) {
                curr_arith = get_number(line);
            }
            else if(line.find(":nlsat-bool-vars") != string::npos) {
                curr_bool = get_number(line);
            }
            else if(line.find(":nlsat-conflicts") != string::npos) {
                curr_conf = get_number(line);
            }
            else if(line.find(":nlsat-decisions") != string::npos) {
                curr_dec = get_number(line);
            }
            else if(line.find(":nlsat-learned-added") != string::npos) {
                curr_added = get_number(line);
            }
            else if(line.find(":nlsat-stages") != string::npos) {
                curr_stg = get_number(line);
            }
            idx++;
        }
        if(curr_result == "sat") {
            sat++;
        }
        else if(curr_result == "unsat") {
            unsat++;
        }
        else {
            unknown++;
        }
        outFile << curr_instance << ", " << curr_result << ", " << curr_bool << ", " << curr_arith
        << ", " << curr_conf << ", " << curr_dec << ", " << curr_stg << ", " << curr_added << endl;
    }
    outFile.close();
    cout << "total: " << total << endl;
    cout << "solved: " << sat + unsat << endl;
    cout << "sat: " << sat << endl;
    cout << "unsat: " << unsat << endl;
    cout << "unknown: " << unknown << endl;
}

int main() {
    read_instances();
    write_statistics();
    return 0;
}