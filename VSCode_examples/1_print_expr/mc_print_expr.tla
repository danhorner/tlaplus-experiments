
--------- MODULE mc_print_expr --------
EXTENDS TLC, print_expr
CONSTANT module_checker_name


ASSUME PrintT(<<"MODEL CHECK SCRIPT: ", module_checker_name >>)
=======================================