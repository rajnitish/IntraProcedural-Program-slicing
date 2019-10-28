# IntraProcedural-Program-slicing

Algorithm

CFG – Control Flow Graph
Each program statement is a node
A directed edge will connect between any 2 nodes that represent statements with a possible control flow between them.
Special nodes: Start, Stop
Definitions
                
- There is- a directed path from i to j        			
Infl[i]             - Set of nodes that are influenced by i
DEF[i]            - all of the variables that are defined (modified) at statement i.
REF[i]             - all of the variables that are referenced (used) at statement i.
  
  RC0 : Set of variables at statement i whose values can be directly affect what is observed through the window defined by Criteria C
  
  Let C = (p,V)
  p is program node(Instruction in our LLVM pass)
  V is set of Referenced variable at program point p.
  
  RC0[i] : RC0 at statement/program point i
         = for each variables v of entire program ,such that either of following is true, will be included in RC0[i]
	 (1) i == p && v belongs to V
	 (2) i is an immediate predessor of node j such that either of following is true
	    2.A) v belongs to REF[i] && DEF[i]  INTERSECT RC0[j] is not empty
	    2.B) v doesn't belong to DEF[i] && v belongs to RC0[j]
	    
  SC0[i]: Statements included in the slice by RC0	     
