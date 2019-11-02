#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/User.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/Pass.h>
#include <fstream>
#include <llvm/Analysis/CFG.h>
#include <stdio.h>
#include <map>
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include <string>
#include <vector>
#include <iostream>
using namespace llvm;

namespace
{
struct CFGPass : public FunctionPass
{

#define __LLVM_DEBUG__

	struct struct_Inst
	{
		Instruction *ins;
		int ins_id;
	};

	std::map<Instruction *, std::vector<Instruction *>> map_Def;
	std::map<Instruction *, std::vector<Instruction *>> map_Ref;
	std::map<Instruction *, std::vector<Instruction *>> map_Infl;
	std::map<Instruction *, std::vector<Instruction *>> map_RC0;
	std::vector<Instruction *> varList;
	std::map<Instruction *, bool> map_SC0;

	struct Criteria
	{
		Instruction *p;
		std::vector<Instruction *> V;
	};

	Criteria C;

	static char ID;
	std::error_code error;
	std::string str;
	std::map<BasicBlock *, int> basicBlockMap;
	int bbCount; //Block
	CFGPass() : FunctionPass(ID) { bbCount = 0; }

	void setListOfVariables() // currently stored all , we can filter it for alloc only
	{
		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_Def.begin();
		while (itr != map_Def.end())
		{
#ifdef __LLVM_DEBUG__
			std::cout << " Instruction in Listing of variable :: " << std::endl;
			errs() << *itr->first << "\n";
#endif
			std::vector<Instruction *>::iterator itrVec = varList.begin();

			if (itr->second.size() > 0)
			{
				if (itrVec == varList.end())
				{
					Instruction *I = *itr->second.begin();
					if (I->getOpcode() == Instruction::Alloca)
						varList.push_back(I);
				}
				else
				{
					std::vector<Instruction *>::iterator itrSec = itr->second.begin();
					while (itrSec != itr->second.end())
					{
						if (std::find(varList.begin(), varList.end(), *itrSec) == varList.end())
						{

							Instruction *I = *itrSec;
							if (I->getOpcode() == Instruction::Alloca)
								varList.push_back(*itrSec);
						}

						itrSec++;
					}
				}
			}
			itr++;
		}
	}

	void displayVarList()
	{
		std::cout << " DISPLAY VAR LIST " << std::endl;
		for (int i = 0; i < varList.size(); i++)
		{
			errs() << *(varList[i]) << "\n\n\n";
		}
	}
	bool isPresentinVarList(Instruction *I)
	{
		return !(std::find(varList.begin(), varList.end(), I) == varList.end());
	}
	void setCriteria(Instruction *I)
	{
		C.p = I;
		std::map<Instruction *, std::vector<Instruction *>>::iterator itr;
		itr = map_Ref.find(I);

		if (itr == map_Ref.end())
		{
			std::cout << " Wrong Instruction pointer provided" << std::endl;
		}
		else
		{
			errs() << " Criteria Variable set are as follows \n\n";
			for (int i = 0; i < itr->second.size(); i++)
				errs() << " \t\t " << *itr->second[i] << "\n";
			C.V = itr->second;
		}
	}

	bool isVarExistInCriteria(Instruction *i)
	{

		return !(std::find(C.V.begin(), C.V.end(), i) == C.V.end());
	}

	bool isVarExistInRef(Instruction *v, Instruction *i) // is v belongs to Ref(i)
	{
		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_Ref.begin();

		itr = map_Ref.find(i);
		if (itr != map_Ref.end())
		{
			return !(std::find(itr->second.begin(), itr->second.end(), v) == itr->second.end());
		}
		else
		{
			return false;
		}
	}
	bool isVarExistInDef(Instruction *v, Instruction *i) // is v belongs to Def(i)
	{
		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_Def.begin();

		itr = map_Def.find(i);
		if (itr != map_Def.end())
		{
			return !(std::find(itr->second.begin(), itr->second.end(), v) == itr->second.end());
		}
		else
		{
			return false;
		}
	}

	bool isVarExistInRC0(Instruction *v, Instruction *i) // is v belongs to Def(i)
	{
		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_RC0.begin();

		itr = map_RC0.find(i);
		if (itr != map_RC0.end())
		{
			return !(std::find(itr->second.begin(), itr->second.end(), v) == itr->second.end());
		}
		else
		{
			return false;
		}
	}
	bool isCommonExist(std::vector<Instruction *> vec1, std::vector<Instruction *> vec2)
	{
		for (int i = 0; i < vec1.size(); i++)
			for (int j = 0; j < vec2.size(); j++)
			{
				if (vec1[i] == vec2[j])
					return true;
			}

		return false;
	}

	/*std::vector<Instruction *> getSuccessorList(Instruction *ins, Function &F)
	{
		std::vector<Instruction *> SuccList;
		SuccList.clear();

		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{
				std::vector<Instruction *> predList = getPredessorList(F, &I);

				for (int i = 0; i < predList.size(); i++)
				{
					if (predList[i] == ins)
					{
						if (std::find(SuccList.begin(), SuccList.end(), &I) == SuccList.end())
						{
							SuccList.push_back(&I);
						}
					}
				}
			}
		}

		return SuccList;
	}*/

	void displaySuccList(Function &F)
	{

		std::vector<Instruction *> SuccList;
		SuccList.clear();

		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{
				std::vector<Instruction *> SuccList = getSuccessorList(F, &I);

				errs() << "\n\n\n Successor of  :: " << *&I << " is as follows ::\n";
				for (int i = 0; i < SuccList.size(); i++)
				{
					errs() << "\t\t\t" << *SuccList[i] << "\n";
				}
			}
		}
	}
	void displayPredList(Function &F)
	{

		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{
				std::vector<Instruction *> PredList = getPredessorList(F, &I);

				errs() << "\n\n\n Predessor of  :: " << *&I << " is as follows ::\n";
				for (int i = 0; i < PredList.size(); i++)
				{
					errs() << "\t\t\t" << *PredList[i] << "\n";
				}
			}
		}
	}
	int getCountTotalIns(Function &F)
	{
		int count = 0;
		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{
				count++;
			}
		}

		return count;
	}
	void computeRC0(Function &F)
	{
		std::cout << "computeRC0 started " << std::endl;

		int TC = 2; //getCountTotalIns(F);
		for (int k = 0; k < TC; k++)
			for (BasicBlock &B : F)
			{
				for (Instruction &I : B)
				{
					//errs() << " Criteria Point = " << *C.p << " Instruction = " << I << "\n";
					//errs()<<" INS---> "<<I<<" : ::  ";

					errs() << " \n\n\n\n\n\nComputing RC0 for Instruction is :: " << I << "\n\n";
					std::cout << "Total no of variable in Function is " << varList.size() << std::endl;

					for (int i = 0; i < varList.size(); i++)
					{
						errs() << " Variable picked is " << *varList[i] << "\n";
						bool flag1 = false, flag2 = false, flag3 = false;

						if (&I == C.p)
						{
							if (isVarExistInCriteria(varList[i]))
							{
								std::cout << "\n Condition 1) met ---------->\n";

								flag1 = true;
							}
						}
						else
						{
							std::vector<Instruction *> vecSucc;
							vecSucc = getSuccessorList(F, &I);

							std::cout << "Size of SuccessorList of current Instruction " << vecSucc.size() << std::endl;
							if (vecSucc.size() > 1)
								std::cout << " ##########################################################\n\n\n\n\n";
							for (int j = 0; j < vecSucc.size(); ++j)
							{
								errs() << "Successor of current Instruction picked  " << *(vecSucc[j]) << "\n";

								std::vector<Instruction *> Def_I = getDef(&I);
								std::vector<Instruction *> RC0_j = getRC0(vecSucc[j]);

								std::cout << " Def_I size " << Def_I.size() << std::endl;
								std::cout << " RC0_j size " << RC0_j.size() << std::endl;
								errs() << " REF checking " << isVarExistInRef(varList[i], &I) << "\n";

								if (isVarExistInRef(varList[i], &I) && isCommonExist(Def_I, RC0_j))
								{
									std::cout << "\n Condition 2.a) met --------------------------------------------------------------------------------------------------------->\n";
									flag2 = true;
								}

								else if (!isVarExistInDef(varList[i], &I) && isVarExistInRC0(varList[i], vecSucc[j]))
								{
									std::cout << "\n Condition 2.b) met ---------->\n";
									flag3 = true;
								}
							}
						}

						if (flag1 || flag2 || flag3)
						{
							//	errs()<< " VAR--->"<<*varList[i]<<"\n\n";
							insertRC0(&I, varList[i]);
						}
					}
				}
			}

		DisplayRC0();
	}

	void ComputeSC0(Function &F)
	{

		std::cout << "computeRC0 started " << std::endl;

		int TC = 2; //getCountTotalIns(F);
		for (int k = 0; k < TC; k++)
			for (BasicBlock &B : F)
			{
				for (Instruction &I : B)
				{
					errs() << " \n\n\n\n\n\nComputing SC0 for Instruction is :: " << I << "\n\n";

					bool flag = false;
					std::vector<Instruction *> vecSucc;
					vecSucc = getSuccessorList(F, &I);

					for (int j = 0; j < vecSucc.size(); ++j)
					{
						errs() << "Successor of current Instruction picked  " << *(vecSucc[j]) << "\n";

						std::vector<Instruction *> Def_I = getDef(&I);
						std::vector<Instruction *> RC0_j = getRC0(vecSucc[j]);

						std::cout << " Def_I size " << Def_I.size() << std::endl;
						std::cout << " RC0_j size " << RC0_j.size() << std::endl;

						// if (isCommonExist(Def_I, RC0_j))
						// {
						// 	insertSC0(&I, true);
						// }
						// else
						// {
						// 	insertSC0(&I, false);
						// }

						insertSC0(&I, isCommonExist(Def_I, RC0_j));
					}
				}
			}

		DisplaySC0();
	}

	void insertSC0(Instruction *ins, bool flag)
	{

		std::map<Instruction *, bool>::iterator itr = map_SC0.begin();
		itr = map_SC0.find(ins);

		if (itr != map_SC0.end())
		{
			itr->second = flag;
		}
		else
		{

			map_SC0.insert(std::pair<Instruction *, bool>(ins, flag));
		}
	}
	void DisplaySC0()
	{

		std::cout << " Display SC0 started---------------------------->\n\n"
				  << std::endl;
		std::map<Instruction *, bool>::iterator itr = map_SC0.begin();

		while (itr != map_SC0.end())
		{
			errs() << "\n\n Instruction :: " << *(itr->first) << "\n ";

			errs() << "\t\t\t " << (itr->second) << "\n";

			itr++;
		}

		std::cout << " \n\nDisplay SC0 end---------------------------->\n\n"
				  << std::endl;
	}
	void DisplayRC0()
	{
		std::cout << " Display RC0 started---------------------------->\n\n"
				  << std::endl;
		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_RC0.begin();

		while (itr != map_RC0.end())
		{
			errs() << "\n\n Instruction :: " << *(itr->first) << "\n";

			for (int i = 0; i < itr->second.size(); i++)
			{
				errs() << "\t\t\t " << *(itr->second[i]) << "\n";
			}

			itr++;
		}

		std::cout << " \n\nDisplay RC0 end---------------------------->\n\n"
				  << std::endl;
	}
	void insertRC0(Instruction *ins, Instruction *rc0)
	{
		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_RC0.begin();
		itr = map_RC0.find(ins);

		if (itr != map_RC0.end())
		{
			if (std::find(itr->second.begin(), itr->second.end(), rc0) == itr->second.end())
			{
				itr->second.push_back(rc0);
			}
		}
		else
		{
			std::vector<Instruction *> tmp_vec;
			tmp_vec.push_back(rc0);
			map_RC0.insert(std::pair<Instruction *, std::vector<Instruction *>>(ins, tmp_vec));
		}
	}

	void insertDef(Instruction *ins, Instruction *def)
	{
		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_Def.begin();
		itr = map_Def.find(ins);

		if (itr != map_Def.end())
		{
			if (std::find(itr->second.begin(), itr->second.end(), def) == itr->second.end())
			{
				itr->second.push_back(def);
			}
		}
		else
		{
			std::vector<Instruction *> tmp_vec;
			tmp_vec.push_back(def);
			map_Def.insert(std::pair<Instruction *, std::vector<Instruction *>>(ins, tmp_vec));
		}
	}

	std::vector<Instruction *> getDef(Instruction *i)
	{
		std::vector<Instruction *> tmp_vec;
		tmp_vec.clear();

		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_Def.begin();
		itr = map_Def.find(i);

		if (itr != map_Def.end())
		{
			tmp_vec = itr->second;
		}

		return tmp_vec;
	}
	std::vector<Instruction *> getRef(Instruction *i)
	{
		std::vector<Instruction *> tmp_vec;
		tmp_vec.clear();

		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_Ref.begin();
		itr = map_Ref.find(i);

		if (itr != map_Ref.end())
		{
			tmp_vec = itr->second;
		}

		return tmp_vec;
	}
	std::vector<Instruction *> getRC0(Instruction *i)
	{
		std::vector<Instruction *> tmp_vec;
		tmp_vec.clear();

		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_RC0.begin();
		itr = map_RC0.find(i);

		if (itr != map_RC0.end())
		{
			tmp_vec = itr->second;
		}

		return tmp_vec;
	}

	void insertInfl(Instruction *ins, Instruction *Infl)
	{
		//std::cout << "Instruction insert took place " << std::endl;
		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_Infl.find(ins);

		if (itr != map_Infl.end())
		{
			if (std::find(itr->second.begin(), itr->second.end(), Infl) == itr->second.end())
			{
				itr->second.push_back(Infl);
			}
		}
		else
		{
			std::vector<Instruction *> tmp_vec;
			tmp_vec.push_back(Infl);
			map_Infl.insert(std::pair<Instruction *, std::vector<Instruction *>>(ins, tmp_vec));
		}
	}
	bool findVariables(Function &F)
	{

		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{
				if (CallInst *call_inst = dyn_cast<CallInst>(&I))
				{
					Function *fn = call_inst->getCalledFunction();
					StringRef fn_name = fn->getName();
					errs() << fn_name << " : " << call_inst->getArgOperand(0) << "\n";
					for (auto op = I.op_begin(); op != I.op_end(); op++)
					{
						Value *v = op->get();
						StringRef name = v->getName();
					}
				}
				else
				{
					errs() << I.getName() << "\n"
						   << I.getOpcodeName();
				}
			}
		}
	}

	std::vector<Instruction *> getSuccessorList(Function &F, Instruction *I) // there might be multiple Succ
	{
		std::vector<Instruction *> SuccList;

		Instruction *NextIns = NULL;
		Instruction *curIns = NULL;
		Function::iterator B_iter = F.begin();
		while (B_iter != F.end())
		{
			BasicBlock *curBB = &*B_iter;
			std::string name = curBB->getName().str();

			BasicBlock::iterator itrNext;

			for (BasicBlock::iterator I_iter = curBB->begin(); I_iter != curBB->end(); ++I_iter)
			{

				curIns = &*I_iter;

				if (curIns == I && (I->getOpcode() == Instruction::Br))
				{
					for (BasicBlock *SuccBB : successors(curBB))
					{
						SuccList.push_back(&SuccBB->front());
					}
				}
				else if ((I == &*(itrNext)))
				{
					SuccList.push_back(&*I_iter);
				}

				itrNext = I_iter;
			}

			++B_iter;
		}

		return SuccList;
	}

	std::vector<Instruction *> getPredessorList(Function &F, Instruction *I) // there might be multiple pred
	{
		std::vector<Instruction *> PredList;

		Instruction *prevIns = NULL;
		Instruction *curIns = NULL;
		Function::iterator B_iter = F.begin();
		while (B_iter != F.end())
		{
			BasicBlock *curBB = &*B_iter;
			std::string name = curBB->getName().str();
			int fromCountNum;
			int toCountNum;
			if (basicBlockMap.find(curBB) != basicBlockMap.end())
			{
				fromCountNum = basicBlockMap[curBB];
			}
			else
			{
				fromCountNum = bbCount;
				basicBlockMap[curBB] = bbCount++;
			}

			for (BasicBlock::iterator I_iter = curBB->begin(); I_iter != curBB->end(); ++I_iter)
			{
				curIns = &*I_iter;

				if (curIns == I && prevIns)
				{
					PredList.push_back(prevIns);
				}

				prevIns = &*I_iter;
			}
			for (BasicBlock *SuccBB : successors(curBB))
			{
				if (basicBlockMap.find(SuccBB) != basicBlockMap.end())
				{
					toCountNum = basicBlockMap[SuccBB];
				}
				else
				{
					toCountNum = bbCount;
					basicBlockMap[SuccBB] = bbCount++;
				}
			}

			++B_iter;
		}

		return PredList;
	}

	void addEdge(Instruction *u, Instruction *v)
	{
	}
	bool createCFG(Function &F)
	{
		std::map<Instruction *, std::vector<Instruction *>> InsGrph;

		raw_string_ostream rso(str);
		StringRef name(F.getName().str() + ".dot");

		enum sys::fs::OpenFlags F_None;
		raw_fd_ostream file(name, error, F_None);

		file << "digraph \"CFG for'" + F.getName() + "\' function\" {\n";

		Function::iterator B_iter = F.begin();
		while (B_iter != F.end())
		{
			BasicBlock *curBB = &*B_iter;
			std::string name = curBB->getName().str();
			int fromCountNum;
			int toCountNum;
			if (basicBlockMap.find(curBB) != basicBlockMap.end())
			{
				fromCountNum = basicBlockMap[curBB];
			}
			else
			{
				fromCountNum = bbCount;
				basicBlockMap[curBB] = bbCount++;
			}

			file << "\tBB" << fromCountNum << " [shape=record, label=\"{";
			file << "BB" << fromCountNum << ":\\l\\l";
			for (BasicBlock::iterator I_iter = curBB->begin(); I_iter != curBB->end(); ++I_iter)
			{
				file << *I_iter << "\\l";
			}
			file << "}\"];\n";
			for (BasicBlock *SuccBB : successors(curBB))
			{
				if (basicBlockMap.find(SuccBB) != basicBlockMap.end())
				{
					toCountNum = basicBlockMap[SuccBB];
				}
				else
				{
					toCountNum = bbCount;
					basicBlockMap[SuccBB] = bbCount++;
				}

				file << "\tBB" << fromCountNum << "-> BB" << toCountNum << ";\n";
			}

			++B_iter;
		}
		file << "}\n";
		file.close();
	}

	void checkInstruct(Function &F)
	{
		int K = 0;

		for (BasicBlock &BB : F)
		{
			for (Instruction &I : BB)
			{

				if (K == 24)
				{
					errs() << " INSTRUCTion----------------------> " << K << "   -->" << I << "\n";
					//	 Instruction Inst = dyn_cast<Instruction *>(I);
					recSlice(&I);
				}

				for (unsigned i = 0, e = I.getNumOperands(); i != e; i++)
				{
					//I.getOperand(i)->print(errs());
					//errs() << "\n";
				}
				K++;
			}
		}

		int i = 0;
		for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I, i++)
		{
			struct_Inst obj;
			//obj.ins = &I;

			std::vector<struct_Inst> InsList;

			K++;
		}
	}

	void Influenced(Function &F)
	{
		std::vector<Instruction *> vecCompleted;

		int Ki = 0;
		for (BasicBlock &BB : F)
			for (Instruction &I : BB)
			{
				Ki++;
				bool flag = true;
				if (std::find(vecCompleted.begin(), vecCompleted.end(), &I) == vecCompleted.end())
					if (I.getOpcode() == Instruction::Br && I.getNumOperands() == 1)
					{
						for (unsigned i = 0, ei = I.getNumOperands(); i != ei; i++)
						{
							Value *operand1 = I.getOperand(i);

							int Kj = 0;
							for (BasicBlock &BB1 : F)
								for (Instruction &Ii : BB1)
								{
									Kj++;

									if (Kj > Ki && flag)
									{
										for (unsigned j = 0, ej = Ii.getNumOperands(); j != ej; j++)
										{
											Value *operand2 = Ii.getOperand(j);

											if (operand1 == operand2)
											{
												insertInfl(&I, &Ii);
												if (std::find(vecCompleted.begin(), vecCompleted.end(), &Ii) == vecCompleted.end())
												{
													vecCompleted.push_back(&Ii);
												}
												flag = false;
											}
											else
											{
												insertInfl(&I, &Ii);
											}
										}
									}
								}
						}
					}
			}
	}

	void displayInfl()
	{

		std::cout << " Display Infl started---------------------------->\n\n"
				  << std::endl;
		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_Infl.begin();

		while (itr != map_Infl.end())
		{
			errs() << "\n\n Instruction :: " << *(itr->first) << "\n";

			if (itr->second.size() == 0)
				std::cout << "\t\t\t No Infl for this Instruction" << std::endl;
			for (int i = 0; i < itr->second.size(); i++)
			{
				errs() << "\t\t\t " << *(itr->second[i]) << "\n";
			}

			itr++;
		}

		std::cout << " \n\nDisplay Infl end---------------------------->\n\n"
				  << std::endl;
	}

	void setDef(Function &F)
	{
#ifdef __LLVM_DEBUG__
//errs() << " Printing Def Use"
//	   << "\n";
//<< *F;
#endif

		std::vector<Instruction *> Inslist;
		for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I)
		{
			Inslist.push_back(&*I);
		}
		std::vector<Instruction *>::iterator iter = Inslist.begin();

		while (iter != Inslist.end())
		{
			Instruction *instr = *iter;
			//	errs() << "\n\n\ndef: " << *instr << " its address is " << instr << "\n";
			//std::vector<Instruction *> PredList = getPredessorList(F, instr);

			//	for (int i = 0; i < PredList.size(); i++)
			//	{
			//				errs() << "\t\t Predecessor Instruction :: " << *PredList[i] << "\n";
			//	}

			Instruction *vi = dyn_cast<Instruction>(instr);
			if (vi->getOpcode() == Instruction::Store)
			{

				//	errs() << "Ref: " << *instr << "\n";
				for (User::op_iterator i = vi->op_begin(), e = vi->op_end(); i != e; ++i)
				{
					Value *v = *i;
					Instruction *opIns = dyn_cast<Instruction>(*i);
					if (opIns)
					{
						insertDef(instr, opIns);
					}
				}
			}

			else
			{

				for (Value::use_iterator i = instr->use_begin(), ie = instr->use_end(); i != ie; ++i)
				{
					Value *v = *i;

					Instruction *useIns = dyn_cast<Instruction>(*i);
					if (useIns)
					{
						insertDef(instr, useIns);

						//	errs() << "\t\t" << *vi << "\n";
					}
				}
			}
			iter++;
		} // use-def chain for Instruction
	}
	void displayDEF()
	{

		std::cout << " Display DEF started---------------------------->\n\n"
				  << std::endl;
		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_Def.begin();

		while (itr != map_Def.end())
		{
			errs() << "\n\n Instruction :: " << *(itr->first) << "\n";

			if (itr->second.size() == 0)
				std::cout << "\t\t\t No Def for this Instruction" << std::endl;
			for (int i = 0; i < itr->second.size(); i++)
			{
				errs() << "\t\t\t " << *(itr->second[i]) << "\n";
			}

			itr++;
		}

		std::cout << " \n\nDisplay DEF end---------------------------->\n\n"
				  << std::endl;
	}
	void setRef(Function &F)
	{

		std::vector<Instruction *> Inslist;
		for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I)
		{
			Inslist.push_back(&*I);
		}

		for (std::vector<Instruction *>::iterator iter1 = Inslist.begin(); iter1 != Inslist.end(); ++iter1)
		{
			Instruction *instr = *iter1;



			if (instr->op_begin() == instr->op_end())
			{
				std::cout<<" NUM of OPerands is zero "<<std::endl;

				insertRef(instr, NULL);
			}
			else
			{

				for (User::op_iterator i = instr->op_begin(), e = instr->op_end(); i != e; ++i)
				{
					Value *v = *i;
					Instruction *vi = dyn_cast<Instruction>(*i);
					if (vi)
					{
						insertRef(instr, vi);
						//			errs() << "\t\t" << *vi << "\n";
					}
				}
			}
		}
	}
	void insertRef(Instruction *ins, Instruction *ref)
	{

		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_Ref.find(ins);

		if (itr != map_Ref.end())
		{

			if (std::find(itr->second.begin(), itr->second.end(), ref) == itr->second.end())
			{
				if (ref && ref->getOpcode() != Instruction::Store)
				{
					itr->second.push_back(ref);
				}
			}
		}
		else
		{
			if (ref)
			{

				std::vector<Instruction *> tmp_vec;
				tmp_vec.push_back(ref);

				map_Ref.insert(std::pair<Instruction *, std::vector<Instruction *>>(ins, tmp_vec));
			}
			else
			{
				std::cout<<" I am here------------------> "<<std::endl;
				std::vector<Instruction *> tmp_vec;
				tmp_vec.clear();

				map_Ref.insert(std::pair<Instruction *, std::vector<Instruction *>>(ins, tmp_vec));
			}
		}
	}
	/*	void insertRef(Instruction *ins, Instruction *ref)
	{

		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_Ref.find(ins);

		if (itr != map_Ref.end())
		{

			if (std::find(itr->second.begin(), itr->second.end(), ref) == itr->second.end())
			{
				if (ref)
				{
					if (isPresentinVarList(ref))
						itr->second.push_back(ref);

					for (unsigned i = 0, ei = ref->getNumOperands(); i != ei; i++)
					{
						Value *operand1 = ref->getOperand(i);

						if (operand1)
						{
							Instruction *vi = dyn_cast<Instruction>(operand1);
							if (vi)
								if (vi->getOpcode() == Instruction::Load || vi->getOpcode() == Instruction::Alloca)

									if (isPresentinVarList(vi))
										itr->second.push_back(vi);
						}
					}
				}
			}
		}
		else
		{
			if (ref)
			{

				std::vector<Instruction *> tmp_vec;

				if (isPresentinVarList(ref))
					tmp_vec.push_back(ref);

				for (unsigned i = 0, ei = ref->getNumOperands(); i != ei; i++)
				{

					Value *operand1 = ref->getOperand(i);
					if (operand1)
					{

						Instruction *vi = dyn_cast<Instruction>(operand1);

						if (vi)
							if (vi->getOpcode() == Instruction::Load || vi->getOpcode() == Instruction::Alloca)
							{
								std::cout << isPresentinVarList(vi) << std::endl;
								errs() << *vi << " \n";
								//if (isPresentinVarList(vi))
								tmp_vec.push_back(vi);
							}
					}
				}
				map_Ref.insert(std::pair<Instruction *, std::vector<Instruction *>>(ins, tmp_vec));
			}
		}
	}*/
	void displayREF()
	{

		std::cout << " Display REF started---------------------------->\n\n"
				  << std::endl;
		std::map<Instruction *, std::vector<Instruction *>>::iterator itr = map_Ref.begin();

		while (itr != map_Ref.end())
		{
			errs() << "\n\n Instruction :: " << *(itr->first) << "\n";

			if (itr->second.size() == 0)
				std::cout << "\t\t\t No Ref for this Instruction" << std::endl;
			for (int i = 0; i < itr->second.size(); i++)
			{
				errs() << "\t\t\t " << *(itr->second[i]) << "\n";
			}

			itr++;
		}

		std::cout << " \n\nDisplay REF end---------------------------->\n\n"
				  << std::endl;
	}

	void recSlice(Instruction *I)
	{
		for (Use &U : I->operands())
		{
			if (Instruction *Inst = dyn_cast<Instruction>(U))
			{
				recSlice(Inst);

				U->print(errs());
				errs() << " NITISH  \n\n\n";
			}
		}
	}
	bool runOnFunction(Function &F) override
	{

		//checkInstruct(F);
		//findVariables(F);
		//createCFG(F);
		setDef(F);
		displayDEF();
		setListOfVariables();
		setRef(F);
		displayREF();
		Influenced(F);

		int count = 0;
		for (BasicBlock &BB : F)
			for (Instruction &I : BB)
			{
				count++;
				if (17 == count)
				{
					errs() << " Criteria is set for program IR point = " << I << "\n";
					setCriteria(&I);
				}
			}

		////computeRC0(F);
		////displaySuccList(F);
		////ComputeSC0(F);

		//displayPredList(F);
		return false;
	}
};
} // namespace
char CFGPass::ID = 0;
static void registerlinkuse(const PassManagerBuilder &, legacy::PassManagerBase &PM) { PM.add(new CFGPass()); }
static RegisterStandardPasses X(PassManagerBuilder::EP_EarlyAsPossible, registerlinkuse);

/*#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Instruction.h"
#include "llvm/ADT/ilist_node.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/CFG.h"

 
using namespace llvm;

namespace 
{
 	struct linkuse : public FunctionPass 
	{
	static char ID;
	linkuse() : FunctionPass(ID) {}

	bool runOnFunction(Function &F) override 	
	{		
	
      for (auto &B : F) {
        //errs()<<"BLOCK FOUND "<<B<<"\n";
        for (auto &I : B) {
         
          //errs()<<&I<<"\n";
          if(I.getPrevNode())
          errs()<<"Parent of "<<I<<"    ::  "<<*(I.getPrevNode())<<"\n\n\n\n";
          
            
          }
      }
      

      return false;
    }
	
  };
}

 char linkuse::ID = 0;
 //static RegisterPass<linkuse> X("linkuse", "Display of code",false,true);

// Automatically enable the pass.

 static void registerlinkuse(const PassManagerBuilder &
                                 , legacy::PassManagerBase &PM) 
 								{ PM.add(new linkuse());}
 static RegisterStandardPasses X(PassManagerBuilder::EP_EarlyAsPossible,
                                              registerlinkuse);

*/
