#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <unordered_map>

using namespace std;

const string instance_path = "../ls_instance_server.txt";

const string output_path = "z3_nra_newest.csv";
const string output_label_path = "z3_nra_newest_label.csv";
const string input_folder = "z3_nra_newest/"; 

vector<string> instance_vec;
unordered_map<string, string> m_ins_label;

class label {
public:
    int num, num_arith, num_bool, num_solved, num_sat, num_unsat, num_unsolved;

    label(): num(0), num_arith(0), num_bool(0), num_solved(0), num_sat(0), num_unsat(0), num_unsolved(0)
    {

    }
};

unordered_map<string, label *> m_labels;

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

string get_label_name(string str) {
    // /....../
    int idx1 = -1, idx2 = -1;
    // find QF_NRA2/..../
    for(int i = 0; i < str.length(); i++) {
        if(str[i] == '2') {
            idx1 = i + 1;
            break;
        }
    }
    for(int i = idx1 + 1; i < str.length(); i++) {
        if(str[i] == '/') {
            idx2 = i;
            break;
        }
    }
    return str.substr(idx1 + 1, idx2 - idx1 - 1);
}

int self_stoi(string str) {
    if(str.length() == 0 || !(str[0] >= '0' && str[0] <= '9')) {
        return 0;
    }
    return stoi(str);
}

void read_instances() {
    ifstream inFile(instance_path);
    string line; 
    while(getline(inFile, line)) {
        auto ins_name = get_instance_name(line);
        auto label_name = get_label_name(line);
        instance_vec.push_back(ins_name);
        m_ins_label[ins_name] = label_name;
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

void write_ins_statistics() {
    unsigned sat = 0, unsat = 0, unknown = 0, total = 0;
    ofstream outFile(output_path);
    outFile << "name, result, bool var, arith var, conflict, decision, stage, learned added\n";
    for(auto curr_instance: instance_vec) {
        auto curr_label = m_ins_label[curr_instance];
        if(m_labels.count(curr_label) == 0) {
            m_labels[curr_label] = new label();
        }
        total++;
        m_labels[curr_label]->num++;
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
            m_labels[curr_label]->num_sat++;
            m_labels[curr_label]->num_solved++;
        }
        else if(curr_result == "unsat") {
            unsat++;
            m_labels[curr_label]->num_unsat++;
            m_labels[curr_label]->num_solved++;
        }
        else {
            unknown++;
            m_labels[curr_label]->num_unsolved++;
        }
        outFile << curr_instance << ", " << curr_result << ", " << curr_bool << ", " << curr_arith
        << ", " << curr_conf << ", " << curr_dec << ", " << curr_stg << ", " << curr_added << endl;

        m_labels[curr_label]->num_bool += self_stoi(curr_bool);
        m_labels[curr_label]->num_arith += self_stoi(curr_arith);
    }
    outFile.close();
    cout << "total: " << total << endl;
    cout << "solved: " << sat + unsat << endl;
    cout << "sat: " << sat << endl;
    cout << "unsat: " << unsat << endl;
    cout << "unknown: " << unknown << endl;
}

void write_label_statistics() {
    ofstream outFile(output_label_path);
    outFile << "name, total, bool var, arith var, sat, unsat, solved, unsolved\n";
    for(auto ele: m_labels) {
        outFile << ele.first << ", " << ele.second->num << ", " << ele.second->num_bool << ", " << ele.second->num_arith << ", "
        << ele.second->num_sat << ", " << ele.second->num_unsat << ", " << ele.second->num_solved << ", " << ele.second->num_unsolved << endl;
    }
    outFile.close();
}

int main() {
    read_instances();
    write_ins_statistics();
    write_label_statistics();
    return 0;
}