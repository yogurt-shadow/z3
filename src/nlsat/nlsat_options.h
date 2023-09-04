#pragma once

namespace nlsat {
    namespace OPTIONS {
        // vsids
        const double arith_var_decay      =               0.95;
        const double bool_var_decay       =               0.95;
        const bool rand_init_act          =               false;

        // reduce
        const bool enable_reduce          =               true;
        const double clause_decay         =               0.999;
        const double learnt_size_fatcor   =               1.0 / 3.0;
        const double learnt_size_inc      =               1.1;
        const unsigned min_learnt_size    =               1;
        const double reduce_init_conf     =               100;
        const double reduce_conf_inc      =               1.5;

        // rephase
        const bool enable_rephase         =               true;

        // restart
        const bool enable_restart         =               true;
        const bool luby_restart           =               false;
        const int restart_init            =               100;
        const double restart_inc          =               1.5;
    };
};