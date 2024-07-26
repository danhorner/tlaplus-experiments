
--------- MODULE print_expr --------
EXTENDS TLC

ASSUME PrintT("Project Architecture:")
ASSUME PrintT("MC File extends main file and queries it")
ASSUME PrintT(" Use multiple MC files to set different parameters in the code")
ASSUME PrintT(" OK to check a model with no SPEC")

================