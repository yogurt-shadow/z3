#include <iostream>
#include <fstream>
#include <string>
#include <unordered_set>
#include <vector>

using namespace std;

const string instance_path = "../instance_server.txt";
const string output_path = "../ls_instance_server.txt";

string csv[] = {
    "../dnlsat/cvc5_orgin.csv",
    "../dnlsat/z3_origin.csv",
};


vector<string> m_instances;
unordered_set<unsigned> m_unsat_instances;

void read_unsat_instances(string str) {
    ifstream inFile(str);
    string line;
    int index = 0;
    while(getline(inFile, line)) {
        if(index == 0) {
            index++;
            continue;
        }
        if(line.find("unsat") != string::npos && m_unsat_instances.count(index - 1) == 0) {
            m_unsat_instances.insert(index - 1);
        }
        index++;
    }
}

void read_csv() {
    m_unsat_instances.clear();
    for(int i = 0; i < 2; i++) {
        read_unsat_instances(csv[i]);
    }
}

void write_instances() {
    m_instances.clear();
    ifstream inFile(instance_path);
    string line;
    while(getline(inFile, line)) {
        m_instances.push_back(line);
    }

    int other = 0;
    ofstream outFile(output_path);
    for(int i = 0; i < m_instances.size(); i++) {
        if(m_unsat_instances.count(i) == 0) {
            outFile << m_instances[i] << endl;
            other++;
        }
    }
    outFile.close();
    std::cout << "overall: " << m_instances.size() << endl;
    cout << "unsat: " << m_unsat_instances.size() << endl;
    cout << "other: " << other << endl;
}

int main() {
    read_csv();
    write_instances();
    return 0;
}