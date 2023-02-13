
#include <bits/stdc++.h>
#include <assert.h>
#include <sys/stat.h>
#include <dirent.h>
#include <unistd.h>
#include <stdlib.h>
#include <sys/wait.h>

// #include "time_tool.h"
// #include "parameters.h"
// #include "random_tool.h"

using namespace std;

// const string instance_list_path = "/home/wangzh/QF_NRA/ls_instance.txt";
const string instance_list_path = "/home/wangzh/QF_NRA/instance.txt";
// const string z3_path = "/home/wangzh/code/z3-9-4/build/z3";
const string z3_path = "/home/wangzh/code/z3-relaxed-nlsat/build/z3";
// const string output_path = "/home/wangzh/nra_ls/ls-version16/";
const string output_path = "/home/wangzh/relaxed-nlsat/bool_only_0.8_vsids_paws/";

const string time_limit = "1200";
const string memory_limit = "30720";

const int max_process_num = 120;

string getPath(const string &str) {
    int start = -1, end = -1;
    for (int i = str.length() - 1; i >= 0; i--) {
        if (str[i] == '.' && end == -1) {
            end = i;
        }
        if (str[i] == '/' && start == -1) {
            start = i;
            break;
        }
    }
    return str.substr(start + 1, end - start - 1);
}

class System_Comand_Helper {
private:
    string cmd;
public:
    bool run() {
        // cout << "## cmd: " << cmd << endl;
        if (system(cmd.c_str()) != 0) {
            cout << "system error: " << cmd << endl;
            // exit(1);
            return false;
        }
        return true;
    }
    void run_mkdir_cmd(const string &dir_path) {
        cmd = "mkdir -p " + dir_path;
        run();
    }
    void run_remove_cmd(const string & str) {
        cmd = "rm -r " + str;
        run();
    }
    void run_echo_string_cmd(const string &str, const string & path) {
        stringstream ss;
        ss << "echo " << str << " >>" + path;
        cmd = ss.str();
        run();
    }

    void run_touch_cmd(const string & str){
        stringstream ss;
        ss << "touch " << str;
        cmd = ss.str();
        run();
    }

    // void run_echo_time_cmd(const string &output_path) {
    //     double run_time = clk.get_time();
    //     stringstream ss;
    //     ss << "echo " << run_time << " >>" + output_path;
    //     cmd = ss.str();
    //     run();
    // }
    void run_z3_cmd(const string &path) {
        // string input_path  = get_input_file_path(sub_path);
        // string output_path = get_instance_output_path(sub_path);
        string rela_path = getPath(path);
        string final_path = output_path + rela_path + ".txt";
        run_touch_cmd(final_path);

        stringstream ss;
        ss << z3_path << " " << path;
        ss << " -T:" << time_limit;
        ss << " -memory:" << memory_limit;
        
        // ss << " nlsat.shuffle_vars=";
        // if (nlsat_shuffle_vars) {
        //     ss << "true";
        // }
        // else {
        //     ss << "false";
        // }
        // ss << " nlsat.seed=" << nlsat_seed;
        ss << " -st > " + final_path;

        cmd = ss.str();

        if (!run()) {
            run_echo_string_cmd("memoryout", final_path);
        }
    }
};

class Z3_Multiprocess_Runner {
private:
    System_Comand_Helper &sch;
    vector<string> &vec_job;
    unsigned ite, siz;
public:
    Z3_Multiprocess_Runner(System_Comand_Helper &_sch, vector<string> &_vec_job)
        : sch(_sch), vec_job(_vec_job), ite(0), siz(_vec_job.size()) {}

    void init() {
        ite = 0;
        siz = vec_job.size();
    }
    bool has_next_job() {
        if (ite >= siz) return false;
        return true;
    }
    unsigned get_cur_job_id() {
        return ite;
    }
    void get_next_job() {
        ++ite;
    }
    // void config_z3_parameters(const int &seed, const int &tl) {
    //     time_limit = tl;
    //     if (seed == -1) {
    //         nlsat_shuffle_vars = false;
    //         nlsat_seed = 0;
    //     }
    //     else {
    //         nlsat_shuffle_vars = true;
    //         nlsat_seed = seed;
    //     }
    // }
    void child_process() {
        const string &job = vec_job[ite];

        stringstream ss;
        ss << "file[" << ite << "] = " << job;
        string tag = ss.str();

        // config_z3_parameters(-1, 1200);
        sch.run_z3_cmd(job);

        cout << "finish: " << tag << endl;
        exit(0);
    }
    void process_finished_child(const unsigned &job_id, const int &sta) {
        if (sta != 0) {
            stringstream ss;
            ss << "file[" << job_id << "] = " << vec_job[job_id];
            string tag = ss.str();
            cout << "error: " << tag << endl;
        }
        else {
            // cout << "main catch finish: " << tag << endl;
        }
    }
};
template<typename T>
class Process_Pool {
private:
    unsigned max_proc_num;
    map<unsigned, pid_t> dict_proc_id;
public:
    Process_Pool(unsigned _max_proc_num = 1234567) : max_proc_num(_max_proc_num) {}
    void handle_finished_process(T &func) {
        pid_t child_pid;
        int sta;
        for (const auto x : dict_proc_id) {
            child_pid = waitpid(x.second, &sta, WNOHANG);
            if (child_pid == 0) { // child process does not finish
                // do nothing
            }
            else { // child process finished
                // assert(child_pid == x.second);
                func.process_finished_child(x.first, sta);
                dict_proc_id.erase(x.first);
                break;
            }
            // else if (child_pid > 0) { // child process finished
            //     assert(child_pid == x.second);
            //     func.process_finished_child(x.first, sta);
            //     dict_proc_id.erase(x.second);
            //     break;
            // }
            // else {
            //     cout << "waitpid error [" << x.first << ", " << x.second << "], child_pid = " << child_pid << endl;
            //     assert(false);
            // }
        }
    }
    void solve(T &func) {
        bool is_parent;
        func.init();
        while (true) {
            is_parent = false;
            if (!func.has_next_job())
                break;
            pid_t pid = fork();
            if (pid == -1) {
                cout << "fork failed" << endl;
                exit(1);
            }
            if(pid == 0) {
                func.child_process();
                exit(0);
            }
            else {
                unsigned job_id = func.get_cur_job_id();

                // stringstream ss;
                // ss << "file[" << job_id << "] = " << vec_job[job_id] << "pid = " << pid;
                // string tag = ss.str();
                // cout << "debug: " << tag << endl;
                
                dict_proc_id[job_id] = pid;
                // sleep(1);
                is_parent = true;
                while (dict_proc_id.size() >= max_proc_num) {
                    handle_finished_process(func);
                    // sleep(1);
                }
            }
            func.get_next_job();
        }
        if (!is_parent) return ;
        while (!dict_proc_id.empty()) {
            handle_finished_process(func);
            // sleep(1);
        }
    }
};

void get_jobs(System_Comand_Helper &sch, vector<string> &vec_job) {

    ifstream ifs(instance_list_path);
    string word;
    while (ifs >> word) {
        vec_job.emplace_back(word);
    }
}
template<typename T>
void shuffle_jobs(T &vec) {
    mt19937 mt(123);
    shuffle(vec.begin(), vec.end(), mt);
}
void solve() {
    System_Comand_Helper sch;
    vector<string> vec_job;
    
    // sch.run_mkdir_cmd(output_dir_pre_path);
    get_jobs(sch, vec_job);

    shuffle_jobs(vec_job);

    // sch.run_mkdir_cmd(output_path);

    cout << "vec file size: " << vec_job.size() << endl;
    
    // output_dir_path = output_dir_pre_path;

    // sch.run_mkdir_cmd(output_dir_path);

    // set<string> vis_set;
    // for (const string &job : vec_job) {
    //     string pre_path = get_file_pre_path(get_instance_output_path(job));
    //     if (vis_set.count(pre_path) == 0) {
    //         sch.run_mkdir_cmd(pre_path);
    //         vis_set.emplace(pre_path);
    //     }
    // }

    Process_Pool<Z3_Multiprocess_Runner> pp(max_process_num);
    Z3_Multiprocess_Runner z3mr(sch, vec_job);
    pp.solve(z3mr);

    // cout << "script run time: " << clk.get_time() << endl;
}
// ../
// ../../
// /home/linxi/smt/z3/instances/
int main(int argc, char **argv) {
    // cout << "test" << endl;
    // init_parameters();
    // return 0;
    solve();
    // const string str = "/ home / wangzh / benchmark / QF_NRA / 20161105 - Sturm - MBO /mbo_E10E11.smt2"; 
    // cout << getPath(str) << endl;
    return 0;
}

/*
*/
