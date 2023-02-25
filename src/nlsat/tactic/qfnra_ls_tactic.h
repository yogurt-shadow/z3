#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_qfnra_local_search_tactic(ast_manager & m, params_ref const & p = params_ref());
