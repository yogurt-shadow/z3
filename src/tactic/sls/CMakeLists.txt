z3_add_component(sls_tactic
  SOURCES
    sls_tactic.cpp
  COMPONENT_DEPENDENCIES
    bv_tactics
    core_tactics
    normal_forms
    tactic
    ast_sls
  TACTIC_HEADERS
    sls_tactic.h
)
