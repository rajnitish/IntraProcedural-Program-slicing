# IntraProcedural-Program-slicing

Algorithm

CFG – Control Flow Graph
Each program statement is a node
A directed edge will connect between any 2 nodes that represent statements with a possible control flow between them.
Special nodes: Start, Stop
Definitions
                
- There is- a directed path from i to j
                - Set of nodes that are influenced by i
	             - all of the variables that are defined (modified)    	     at statement i.
	             - all of the variables that are referenced (used) 	        
                    at statement i.

