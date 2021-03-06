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
#include <llvm/Analysis/LoopInfo.h>

using namespace llvm;

namespace
{
struct PSlicePass : public FunctionPass
{

	//#define __LLVM_DEBUG__

	typedef std::vector<Instruction *> __vecIns_type__;
	typedef std::pair<Instruction *, __vecIns_type__> __pair_map_Ins__;
	typedef std::map<Instruction *, __vecIns_type__> __mapIns_type__;
	typedef std::map<Instruction *, bool> __mapIns_Inc_type__;

	typedef __mapIns_type__::iterator __itr_mapIns_type__;
	typedef __mapIns_Inc_type__::iterator __itr_mapIns_Inc_type__;
	typedef __vecIns_type__::iterator __itr_vecIns_type__;

	__vecIns_type__ varList;
	__mapIns_type__ map_Def;
	__mapIns_type__ map_Ref;
	__mapIns_type__ map_Infl;

	__mapIns_type__ map_RC0;
	__mapIns_type__ map_RCk;
	__mapIns_type__ map_RCkPlus1;

	__mapIns_Inc_type__ map_SC0;
	__mapIns_Inc_type__ map_SCkPlus1;

	__mapIns_Inc_type__ map_BC0;
	__mapIns_Inc_type__ map_BCk;
	__mapIns_Inc_type__ map_BCkPlus1;

	struct Criteria
	{
		Instruction *p;
		__vecIns_type__ V;
	};

	Criteria C;

	static char ID;
	std::error_code error;
	std::string str;
	std::map<BasicBlock *, int> basicBlockMap;
	int bbCount; //Block
	int TC;
	PSlicePass() : FunctionPass(ID)
	{
		bbCount = 0;
	}

	bool isFixedPointConverge(__mapIns_Inc_type__ OLD, __mapIns_Inc_type__ NEW) // Assuming NEW IS SUPERSET OF OLD
	{
		__itr_mapIns_Inc_type__ itr_new = NEW.begin();

		while (itr_new != NEW.end())
		{

			__itr_mapIns_Inc_type__ itr_old = OLD.begin();

			itr_old = std::find(OLD.begin(), OLD.end(), *itr_new);
			if (itr_old == OLD.end())
			{
				return false;
			}
			else
			{
				if (itr_old->second != itr_new->second)
				{

					return false;
				}
			}

			itr_new++;
		}

		return true;
	}

	bool isFixedPointConverge(__mapIns_type__ OLD, __mapIns_type__ NEW) // Assuming NEW IS SUPERSET OF OLD
	{
		__itr_mapIns_type__ itr_new = NEW.begin();

		while (itr_new != NEW.end())
		{

			__itr_mapIns_type__ itr_old = OLD.begin();
			itr_old = std::find(OLD.begin(), OLD.end(), *itr_new);

			if (itr_old == OLD.end())
			{
				return false;
			}
			else
			{

				__itr_vecIns_type__ itrV_new = itr_new->second.begin();

				while (itrV_new != itr_new->second.begin())
				{

					if (std::find(itr_old->second.begin(), itr_old->second.end(), *itrV_new) == itr_old->second.end())
					{
						return false;
					}

					itrV_new++;
				}
			}

			itr_new++;
		}

		return true;
	}
	void computeBCkPlus1(Function &F)
	{
		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{

				bool flag = true;

				__vecIns_type__ vec_Infl = getInfl(&I);

				if (vec_Infl.size() > 0)
				{
					for (int j = 0; j < vec_Infl.size(); ++j)
					{
						if (getSCkPlus1(vec_Infl[j]))
							insertBCkPlus1(&I, true);
					}
				}
				else
				{
					insertBCkPlus1(&I, false);
				}
			}
		}

		map_BCk = map_BCkPlus1;
	}

	bool getSCkPlus1(Instruction *ins)
	{
		__mapIns_Inc_type__::iterator itr = map_SCkPlus1.begin();
		itr = map_SCkPlus1.find(ins);

		if (itr != map_SCkPlus1.end())
		{
			return itr->second;
		}
		else
		{
#ifdef __LLVM_DEBUG__
			std::cout << " This instruction is not present n program, How come getting its SCO" << std::endl;
#endif
			return false;
		}
	}
	void insertBCkPlus1(Instruction *ins, bool flag)
	{
		__mapIns_Inc_type__::iterator itr = map_BCkPlus1.begin();
		itr = map_BCkPlus1.find(ins);

		if (itr != map_BCkPlus1.end())
		{
			itr->second = flag;
		}
		else
		{

			map_BCkPlus1.insert(std::pair<Instruction *, bool>(ins, flag));
		}
	}

	void computeSCkPlus1(Function &F)
	{

		for (int k = 0; k < TC; k++)
		{
			bool success_flag = false;
			for (BasicBlock &B : F)
			{
				for (Instruction &I : B)
				{

					bool flag = false;
					__vecIns_type__ vecSucc;
					vecSucc = getSuccessorList(F, &I);

					for (int j = 0; j < vecSucc.size(); ++j)
					{

						__vecIns_type__ Def_I = getDef(&I);
						__vecIns_type__ RCkPlus1_j = getRCkPlus1(vecSucc[j]);

						if (insertSCkPlus1(&I, isCommonExist(Def_I, RCkPlus1_j)))
							success_flag = true;
					}
				}
			}

			if (!success_flag)
			{
#ifdef __LLVM_DEBUG__

				std::cout << "@computeSCkPlus1::Fixed point achieved at iteration no " << k << std::endl;

#endif
				break;
			}
		}

		__itr_mapIns_Inc_type__ itr = map_BCk.begin();

		while (itr != map_BCk.end())
		{
			if (itr->second == true)
			{
				insertSCkPlus1(itr->first, true);
			}
			itr++;
		}
	}

	bool insertSCkPlus1(Instruction *ins, bool flag)
	{
		bool success_flag = false;
		__mapIns_Inc_type__::iterator itr = map_SCkPlus1.begin();
		itr = map_SCkPlus1.find(ins);

		if (itr != map_SCkPlus1.end())
		{
			itr->second = flag;
			success_flag = true;
		}
		else
		{

			map_SCkPlus1.insert(std::pair<Instruction *, bool>(ins, flag));
			success_flag = true;
		}
	}

	void computeRCkPlus1(Function &F) //Note RCk is intially assined from RC0; base value of RCk
	{
		__mapIns_type__ UnionRBck0 = computeUnionRCb0(F, map_BCk);

		__itr_mapIns_type__ itr = UnionRBck0.begin();

		for (int k = 0; k < TC; k++)
		{
			bool success_flag = false;
			for (BasicBlock &B : F)
			{
				for (Instruction &I : B)
				{
					__vecIns_type__ rck = getRCk(&I);

					if (rck.size() > 0)
					{
						__itr_vecIns_type__ itrRck = rck.begin();

						while (itrRck != rck.end())
						{
							if (insertRCkPlus1(&I, *itrRck))
								success_flag = true;

							itrRck++;
						}
					}

					itr = UnionRBck0.find(&I);

					if (itr != UnionRBck0.end())
					{
						__itr_vecIns_type__ itrSec = itr->second.begin();

						while (itrSec != itr->second.end())
						{
							if (insertRCkPlus1(&I, *itrSec))
								success_flag = true;

							itrSec++;
						}
					}
				}
			}

			if (!success_flag)
			{
#ifdef __LLVM_DEBUG__

				std::cout << "@computeRCkPlus1::Fixed point achieved at iteration no " << k << std::endl;

#endif
				break;
			}
		}

		map_RCk.clear();
		map_RCk = map_RCkPlus1;
	}

	bool insertRCkPlus1(Instruction *ins, Instruction *rck)
	{
		bool success_flag = false;
		__itr_mapIns_type__ itr = map_RCkPlus1.begin();
		itr = map_RCkPlus1.find(ins);

		if (itr != map_RCkPlus1.end())
		{
			if (std::find(itr->second.begin(), itr->second.end(), rck) == itr->second.end())
			{
				itr->second.push_back(rck);
				success_flag = true;
			}
		}
		else
		{
			__vecIns_type__ tmp_vec;
			tmp_vec.push_back(rck);
			map_RCkPlus1.insert(__pair_map_Ins__(ins, tmp_vec));
			success_flag = true;
		}

		return success_flag;
	}
	__vecIns_type__ getRCk(Instruction *I)
	{

		__vecIns_type__ tmp_vec;
		tmp_vec.clear();

		__itr_mapIns_type__ itr = map_RCk.begin();
		itr = map_RCk.find(I);

		if (itr != map_RCk.end())
		{
			tmp_vec = itr->second;
		}

		return tmp_vec;
	}
	__vecIns_type__ getRCkPlus1(Instruction *I)
	{

		__vecIns_type__ tmp_vec;
		tmp_vec.clear();

		__itr_mapIns_type__ itr = map_RCkPlus1.begin();
		itr = map_RCkPlus1.find(I);

		if (itr != map_RCkPlus1.end())
		{
			tmp_vec = itr->second;
		}

		return tmp_vec;
	}

	__mapIns_type__ computeUnionRCb0(Function &F, __mapIns_Inc_type__ BCk)
	{
		__mapIns_type__ map_RCb0;
		map_RCb0.clear();

		__mapIns_Inc_type__::iterator itr_BCk = BCk.begin();

		while (itr_BCk != BCk.end())
		{
			if (itr_BCk->second)
			{
				Criteria Cb_k = setCriteria(itr_BCk->first);

				__mapIns_type__ map_RCb0_k;
				map_RCb0_k.clear();
				map_RCb0_k = computeRCb0(F, Cb_k);

				__itr_mapIns_type__ itr_map_RC0_k = map_RCb0_k.begin();

				while (itr_map_RC0_k != map_RCb0_k.end())
				{

					__itr_mapIns_type__ itr = map_RCb0.begin();
					itr = map_RCb0.find(itr_map_RC0_k->first);

					if (itr != map_RCb0.end())
					{
						for (int i = 0; i < itr_map_RC0_k->second.size(); i++)
						{
							if (std::find(itr->second.begin(), itr->second.end(), itr_map_RC0_k->second[i]) == itr->second.end())
							{
								itr->second.push_back(itr_map_RC0_k->second[i]);
							}
						}
					}
					else
					{
						__vecIns_type__ tmp_vec;
						tmp_vec.clear();
						if (itr_map_RC0_k->second.size() > 0)
						{
							tmp_vec = itr_map_RC0_k->second;
						}
						map_RCb0.insert(__pair_map_Ins__(itr_map_RC0_k->first, tmp_vec));
					}

					itr_map_RC0_k++;
				}
			}
			itr_BCk++;
		}

		return map_RCb0;
	}

	__mapIns_type__ computeRCb0(Function &F, Criteria Cb)
	{
		__mapIns_type__ map_RCb0;

		for (int k = 0; k < TC; k++)
		{
			bool success_flag = false;
			for (BasicBlock &B : F)
			{
				for (Instruction &I : B)
				{

					for (int i = 0; i < varList.size(); i++)
					{
#ifdef __LLVM_DEBUG__
						errs() << " Variable picked is " << *varList[i] << "\n";
#endif
						bool flag1 = false, flag2 = false, flag3 = false;

						if (&I == Cb.p)
						{
							if (isVarExistInCriteria(varList[i], Cb))
							{
#ifdef __LLVM_DEBUG__
								std::cout << "\n Condition 1) met ---------->\n";
#endif

								flag1 = true;
							}
						}
						else
						{
							__vecIns_type__ vecSucc;
							vecSucc = getSuccessorList(F, &I);
							for (int j = 0; j < vecSucc.size(); ++j)
							{
								__vecIns_type__ Def_I = getDef(&I);
								__vecIns_type__ RCb0_j = getRCb0(vecSucc[j], map_RCb0);

								if (isVarExistInRef(varList[i], &I) && isCommonExist(Def_I, RCb0_j))
								{
#ifdef __LLVM_DEBUG__
									std::cout << "\n Condition 2.a) met --------------------------------------------------------------------------------------------------------->\n";
#endif
									flag2 = true;
								}

								else if (!isVarExistInDef(varList[i], &I) && isVarExistInRCb0(varList[i], vecSucc[j], map_RCb0))
								{
#ifdef __LLVM_DEBUG__
									std::cout << "\n Condition 2.b) met ---------->\n";
#endif
									flag3 = true;
								}
							}
						}

						if (flag1 || flag2 || flag3)
						{
							__itr_mapIns_type__ itr = map_RCb0.begin();
							itr = map_RCb0.find(&I);

							if (itr != map_RCb0.end())
							{
								if (std::find(itr->second.begin(), itr->second.end(), varList[i]) == itr->second.end())
								{
									itr->second.push_back(varList[i]);
									success_flag = true;
								}
							}
							else
							{
								__vecIns_type__ tmp_vec;
								tmp_vec.push_back(varList[i]);

								map_RCb0.insert(__pair_map_Ins__(&I, tmp_vec));
								success_flag = true;
							}
						}
					}
				}
			}

			if (!success_flag)
			{
#ifdef __LLVM_DEBUG__

				std::cout << "@computeRCb0::Fixed point achieved at iteration no " << k << std::endl;

#endif
				break;
			}
		}

		return map_RCb0;
	}

	void setListOfVariables() // currently stored all
	{
		__itr_mapIns_type__ itr = map_Def.begin();
		while (itr != map_Def.end())
		{
#ifdef __LLVM_DEBUG__
			std::cout << " Instruction in Listing of variable :: " << std::endl;
			errs() << *itr->first << "\n";
#endif
			__vecIns_type__::iterator itrVec = varList.begin();

			if (itr->second.size() > 0)
			{
				if (itrVec == varList.end())
				{
					Instruction *I = *itr->second.begin();
					varList.push_back(I);
				}
				else
				{
					__vecIns_type__::iterator itrSec = itr->second.begin();
					while (itrSec != itr->second.end())
					{
						if (std::find(varList.begin(), varList.end(), *itrSec) == varList.end())
						{

							Instruction *I = *itrSec;
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
	Criteria setCriteria(Instruction *I)
	{
		Criteria Cb;
		Cb.p = I;
		__itr_mapIns_type__ itr;
		itr = map_Ref.find(I);

		if (itr == map_Ref.end())
		{
#ifdef __LLVM_DEBUG__
			std::cout << " Wrong Instruction pointer provided" << std::endl;
#endif
		}
		else
		{
#ifdef __LLVM_DEBUG__
			errs() << " Criteria Variable set are as follows \n\n";
			for (int i = 0; i < itr->second.size(); i++)
				errs() << " \t\t " << *itr->second[i] << "\n";
#endif
			Cb.V = itr->second;
		}
		return Cb;
	}

	bool isVarExistInCriteria(Instruction *i, Criteria Cb)
	{

		return !(std::find(Cb.V.begin(), Cb.V.end(), i) == Cb.V.end());
	}

	bool isVarExistInRef(Instruction *v, Instruction *i) // is v belongs to Ref(i)
	{
		__itr_mapIns_type__ itr = map_Ref.begin();

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
		__itr_mapIns_type__ itr = map_Def.begin();

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

	bool isVarExistInRCb0(Instruction *v, Instruction *i, __mapIns_type__ mapRC) // is v belongs to Def(i)
	{
		__itr_mapIns_type__ itr = mapRC.begin();

		itr = mapRC.find(i);
		if (itr != mapRC.end())
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
		__itr_mapIns_type__ itr = map_RC0.begin();

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
	bool isCommonExist(__vecIns_type__ vec1, __vecIns_type__ vec2)
	{
		for (int i = 0; i < vec1.size(); i++)
			for (int j = 0; j < vec2.size(); j++)
			{
				if (vec1[i] == vec2[j])
				{
					return true;
				}
			}

		return false;
	}

	void displaySuccList(Function &F)
	{

		__vecIns_type__ SuccList;
		SuccList.clear();

		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{
				__vecIns_type__ SuccList = getSuccessorList(F, &I);

#ifdef __LLVM_DEBUG__
				errs() << "\n\n\n Successor of  :: " << *&I << " is as follows ::\n";
				for (int i = 0; i < SuccList.size(); i++)
				{
					errs() << "\t\t\t" << *SuccList[i] << "\n";
				}
#endif
			}
		}
	}
	void displayPredList(Function &F)
	{

		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{
				__vecIns_type__ PredList = getPredessorList(F, &I);
#ifdef __LLVM_DEBUG__
				errs() << "\n\n\n Predessor of  :: " << *&I << " is as follows ::\n";
				for (int i = 0; i < PredList.size(); i++)
				{
					errs() << "\t\t\t" << *PredList[i] << "\n";
				}
#endif
			}
		}
	}
	void setCountTotalIns(Function &F)
	{
		int count = 0;
		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{
				count++;
			}
		}

		TC = count;
	}
	void computeRC0(Function &F)
	{
#ifdef __LLVM_DEBUG__
		std::cout << "computeRC0 started " << std::endl;
#endif

		for (int k = 0; k < TC; k++)
		{
			bool success_flag = false;
			for (BasicBlock &B : F)
			{
				for (Instruction &I : B)
				{
#ifdef __LLVM_DEBUG__
					errs() << " Criteria Point = " << *C.p << " Instruction = " << I << "\n";
					errs() << " INS---> " << I << " : ::  ";

					errs() << " \n\n\n\n\n\nComputing RC0 for Instruction is :: " << I << "\n\n";
					std::cout << "Total no of variable in Function is " << varList.size() << std::endl;
#endif

					for (int i = 0; i < varList.size(); i++)
					{
#ifdef __LLVM_DEBUG__
						errs() << " Variable picked is " << *varList[i] << "\n";
#endif
						bool flag1 = false, flag2 = false, flag3 = false;

						if (&I == C.p)
						{
							if (isVarExistInCriteria(varList[i], C))
							{
#ifdef __LLVM_DEBUG__
								std::cout << "\n Condition 1) met ---------->\n";
#endif

								flag1 = true;
							}
						}
						else
						{
							__vecIns_type__ vecSucc;
							vecSucc = getSuccessorList(F, &I);

#ifdef __LLVM_DEBUG__
							std::cout << "Size of SuccessorList of current Instruction " << vecSucc.size() << std::endl;
#endif
							for (int j = 0; j < vecSucc.size(); ++j)
							{

#ifdef __LLVM_DEBUG__
								errs() << "Successor of current Instruction picked  " << *(vecSucc[j]) << "\n";
#endif

								__vecIns_type__ Def_I = getDef(&I);
								__vecIns_type__ RC0_j = getRC0(vecSucc[j]);

#ifdef __LLVM_DEBUG__

								std::cout << " Def_I size " << Def_I.size() << std::endl;
								std::cout << " RC0_j size " << RC0_j.size() << std::endl;
								errs() << " REF checking " << isVarExistInRef(varList[i], &I) << "\n";
#endif

								if (isVarExistInRef(varList[i], &I) && isCommonExist(Def_I, RC0_j))
								{
#ifdef __LLVM_DEBUG__
									std::cout << "\n Condition 2.a) met --------------------------------------------------------------------------------------------------------->\n";
#endif

									flag2 = true;
								}

								else if (!isVarExistInDef(varList[i], &I) && isVarExistInRC0(varList[i], vecSucc[j]))
								{
#ifdef __LLVM_DEBUG__
									std::cout << "\n Condition 2.b) met ---------->\n";
#endif

									flag3 = true;
								}
							}
						}

						if (flag1 || flag2 || flag3)
						{
							if (insertRC0(&I, varList[i]))
								success_flag = true;
						}
					}
				}
			}

			if (!success_flag)
			{
#ifdef __LLVM_DEBUG__

				std::cout << "@computeRC0::Fixed point achieved at iteration no " << k << std::endl;

#endif
				break;
			}
		}

		map_RCk = map_RC0;
	}

	void computeBC0(Function &F)
	{

		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{
				bool flag = true;

				__vecIns_type__ vec_Infl = getInfl(&I);

				if (vec_Infl.size() > 0)
				{
					for (int j = 0; j < vec_Infl.size(); ++j)
					{
						if (getSC0(vec_Infl[j]))
							insertBC0(&I, true);
					}
				}
				else
				{
					insertBC0(&I, false);
				}
			}
		}

		map_BCk = map_BC0;
	}

	void insertBC0(Instruction *ins, bool flag)
	{
		__mapIns_Inc_type__::iterator itr = map_BC0.begin();
		itr = map_BC0.find(ins);

		if (itr != map_BC0.end())
		{
			itr->second = flag;
		}
		else
		{

			map_BC0.insert(std::pair<Instruction *, bool>(ins, flag));
		}
	}
	void displayBC0()
	{

		std::cout << " Display BC0 started---------------------------->\n\n"
				  << std::endl;
		__mapIns_Inc_type__::iterator itr = map_BC0.begin();

		while (itr != map_BC0.end())
		{
			errs() << "STATUS = " << (itr->second) << "  Instruction :: " << *(itr->first) << "\n";
			itr++;
		}

		std::cout << " \n\nDisplay BC0 end---------------------------->\n\n"
				  << std::endl;
	}
	void displayBCkPlus1()
	{

		std::cout << " Display BC(k+1) started---------------------------->\n\n"
				  << std::endl;
		__mapIns_Inc_type__::iterator itr = map_BCkPlus1.begin();

		while (itr != map_BCkPlus1.end())
		{

			errs() << "STATUS = " << (itr->second) << "  Instruction :: " << *(itr->first) << "\n";

			itr++;
		}

		std::cout << " \n\nDisplay BC(k+1) end---------------------------->\n\n"
				  << std::endl;
	}
	void computeSC0(Function &F)
	{

		for (int k = 0; k < TC; k++)
		{
			bool success_flag = false;
			for (BasicBlock &B : F)
			{
				for (Instruction &I : B)
				{
#ifdef __LLVM_DEBUG__
					errs() << " \n\n\n\n\n\nComputing SC0 for Instruction is :: " << I << "\n\n";
#endif
					bool flag = false;
					__vecIns_type__ vecSucc;
					vecSucc = getSuccessorList(F, &I);

					for (int j = 0; j < vecSucc.size(); ++j)
					{

#ifdef __LLVM_DEBUG__
						errs() << "Successor of current Instruction picked  " << *(vecSucc[j]) << "\n";
#endif
						__vecIns_type__ Def_I = getDef(&I);
						__vecIns_type__ RC0_j = getRC0(vecSucc[j]);

#ifdef __LLVM_DEBUG__
						std::cout << " Def_I size " << Def_I.size() << std::endl;
						std::cout << " RC0_j size " << RC0_j.size() << std::endl;

#endif

						if (insertSC0(&I, isCommonExist(Def_I, RC0_j)))
							success_flag = true;
					}
				}
			}

			if (!success_flag)
			{
#ifdef __LLVM_DEBUG__

				std::cout << "@computeSC0::Fixed point achieved at iteration no " << k << std::endl;

#endif
				break;
			}
		}
	}

	bool insertSC0(Instruction *ins, bool flag)
	{
		bool success_flag = false;

		__mapIns_Inc_type__::iterator itr = map_SC0.begin();
		itr = map_SC0.find(ins);

		if (itr != map_SC0.end())
		{
			itr->second = flag;
			success_flag = true;
		}
		else
		{

			map_SC0.insert(std::pair<Instruction *, bool>(ins, flag));
			success_flag = true;
		}

		return success_flag;
	}
	void displaySC0()
	{

		std::cout << " Display SC0 started----------------------------------------------------------->\n\n"
				  << std::endl;
		__mapIns_Inc_type__::iterator itr = map_SC0.begin();

		while (itr != map_SC0.end())
		{

			errs() << "STATUS = " << (itr->second) << "  Instruction :: " << *(itr->first) << "\n";

			itr++;
		}

		std::cout << " \n\nDisplay SC0 end------------------------------------------------------------->\n\n"
				  << std::endl;
	}
	void displaySCkPlus1()
	{

		std::cout << "\n Display SC(k+1) started---------------------------->\n\n";
		__mapIns_Inc_type__::iterator itr = map_SCkPlus1.begin();

		while (itr != map_SCkPlus1.end())
		{

			errs() << "STATUS = " << (itr->second) << "  Instruction :: " << *(itr->first) << "\n";

			itr++;
		}

		std::cout << " \n\nDisplay SC(k+1) end---------------------------->\n\n"
				  << std::endl;
	}
	bool getSC0(Instruction *ins)
	{
		__mapIns_Inc_type__::iterator itr = map_SC0.begin();
		itr = map_SC0.find(ins);

		if (itr != map_SC0.end())
		{
			return itr->second;
		}
		else
		{

#ifdef __LLVM_DEBUG__
			std::cout << " This instruction is not present n program, How come getting its SCO" << std::endl;
#endif
			return false;
		}
	}
	void displayRC0()
	{
		std::cout << " Display RC0 started--------------------------------------------------------->\n\n"
				  << std::endl;
		__itr_mapIns_type__ itr = map_RC0.begin();

		while (itr != map_RC0.end())
		{
			errs() << "Instruction :: " << *(itr->first) << "\n";

			for (int i = 0; i < itr->second.size(); i++)
			{
				errs() << "\t\t\t " << *(itr->second[i]) << "\n";
			}

			itr++;
		}

		std::cout << " \n\nDisplay RC0 end---------------------------->\n\n"
				  << std::endl;
	}
	void displayRCkPlus1()
	{
		std::cout << " Display RC(k+1) started---------------------------->\n\n"
				  << std::endl;
		__itr_mapIns_type__ itr = map_RCkPlus1.begin();

		while (itr != map_RCkPlus1.end())
		{
			errs() << "\n\n Instruction :: " << *(itr->first) << "\n";

			for (int i = 0; i < itr->second.size(); i++)
			{
				errs() << "\t\t\t " << *(itr->second[i]) << "\n";
			}

			itr++;
		}

		std::cout << " \n\nDisplay RC(k+1) end---------------------------->\n\n"
				  << std::endl;
	}
	bool insertRC0(Instruction *ins, Instruction *rc0)
	{
		bool success_flag = false;
		__itr_mapIns_type__ itr = map_RC0.begin();
		itr = map_RC0.find(ins);

		if (itr != map_RC0.end())
		{
			if (std::find(itr->second.begin(), itr->second.end(), rc0) == itr->second.end())
			{
				itr->second.push_back(rc0);
				success_flag = true;
			}
		}
		else
		{
			__vecIns_type__ tmp_vec;
			tmp_vec.push_back(rc0);
			map_RC0.insert(__pair_map_Ins__(ins, tmp_vec));
			success_flag = true;
		}
		return success_flag;
	}

	void insertDef(Instruction *ins, Instruction *def)
	{
		__itr_mapIns_type__ itr = map_Def.begin();
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
			__vecIns_type__ tmp_vec;
			tmp_vec.push_back(def);
			map_Def.insert(__pair_map_Ins__(ins, tmp_vec));
		}
	}

	__vecIns_type__ getDef(Instruction *i)
	{
		__vecIns_type__ tmp_vec;
		tmp_vec.clear();

		__itr_mapIns_type__ itr = map_Def.begin();
		itr = map_Def.find(i);

		if (itr != map_Def.end())
		{
			tmp_vec = itr->second;
		}

		return tmp_vec;
	}
	__vecIns_type__ getRef(Instruction *i)
	{
		__vecIns_type__ tmp_vec;
		tmp_vec.clear();

		__itr_mapIns_type__ itr = map_Ref.begin();
		itr = map_Ref.find(i);

		if (itr != map_Ref.end())
		{
			tmp_vec = itr->second;
		}

		return tmp_vec;
	}
	__vecIns_type__ getRCb0(Instruction *i, __mapIns_type__ mapRC)
	{
		__vecIns_type__ tmp_vec;
		tmp_vec.clear();

		__itr_mapIns_type__ itr = mapRC.begin();
		itr = mapRC.find(i);

		if (itr != mapRC.end())
		{
			tmp_vec = itr->second;
		}

		return tmp_vec;
	}

	__vecIns_type__ getRC0(Instruction *i)
	{
		__vecIns_type__ tmp_vec;
		tmp_vec.clear();

		__itr_mapIns_type__ itr = map_RC0.begin();
		itr = map_RC0.find(i);

		if (itr != map_RC0.end())
		{
			tmp_vec = itr->second;
		}

		return tmp_vec;
	}

	void insertInfl(Instruction *ins, Instruction *Infl)
	{
		__itr_mapIns_type__ itr = map_Infl.find(ins);

		if (itr != map_Infl.end())
		{
			if (std::find(itr->second.begin(), itr->second.end(), Infl) == itr->second.end())
			{
				itr->second.push_back(Infl);
			}
		}
		else
		{
			__vecIns_type__ tmp_vec;
			tmp_vec.push_back(Infl);
			map_Infl.insert(__pair_map_Ins__(ins, tmp_vec));
		}
	}
	__vecIns_type__ getInfl(Instruction *ins)
	{

		__itr_mapIns_type__ itr = map_Infl.find(ins);

		if (itr != map_Infl.end())
		{
			return itr->second;
		}
		else
		{
			__vecIns_type__ tmp_vec;
			tmp_vec.clear();
			return tmp_vec;
		}
	}

	__vecIns_type__ getSuccessorList(Function &F, Instruction *I) // there might be multiple Succ
	{
		__vecIns_type__ SuccList;

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

				if (curIns == I && (I->getOpcode() == Instruction::Br)) // Memory comp
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

	__vecIns_type__ getPredessorList(Function &F, Instruction *I) // there might be multiple pred
	{
		__vecIns_type__ PredList;

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

				if (curIns == I && prevIns) // Memory comp
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

	/*void setInfluence(Function &F)
	{
		std::vector<BasicBlock *> vecTmp;
		Function::iterator B_iter = F.begin();
		bool breakFlag = false;
		while (B_iter != F.end())
		{
			BasicBlock *curBB = &*B_iter;
			std::string name = curBB->getName().str();

			for (BasicBlock::iterator I_iter = curBB->begin(); I_iter != curBB->end(); ++I_iter)
			{

				if (I_iter->getOpcode() == Instruction::Br)
				{
					//bool flag = false;
					for (BasicBlock *SuccBB : successors(curBB))
					{
						//if (!flag)
						//{
						if (std::find(vecTmp.begin(), vecTmp.end(), SuccBB) == vecTmp.end())
						{
							vecTmp.push_back(curBB);
							//		flag = true;
							for (Instruction &I : *SuccBB)
							{

								insertInfl(&*I_iter, &I);
								//	errs() << " \t\t\t ::" << *&I << "\n";
							}
						}
						//}
					}
				}
				// 	else if (I_iter->getOpcode() == Instruction::Br)
				// {
				// 	bool flag = false;
				// 	for (BasicBlock *SuccBB : successors(curBB))
				// 	{
				// 		if (!flag)
				// 		{
				// 			if (std::find(vecTmp.begin(), vecTmp.end(), SuccBB) == vecTmp.end())
				// 			{
				// 				vecTmp.push_back(curBB);
				// 				flag = true;
				// 				for (Instruction &I : *SuccBB)
				// 				{

				// 					insertInfl(&*I_iter, &I);
				// 					//	errs() << " \t\t\t ::" << *&I << "\n";
				// 				}
				// 			}
				// 		}
				// 	}
				// }
				Instruction *Ins = dyn_cast<Instruction>(I_iter);
				if (Ins == C.p)
				{
					breakFlag = true;
					break;
				}
			}

			if (breakFlag)
				break;

			++B_iter;
		}
	} */
	// void Influenced(Function &F)
	// {
	// 	__vecIns_type__ vecCompleted;

	// 	int Ki = 0;
	// 	for (BasicBlock &BB : F)
	// 		for (Instruction &I : BB)
	// 		{
	// 			Ki++;
	// 			bool flag = true;
	// 			if (std::find(vecCompleted.begin(), vecCompleted.end(), &I) == vecCompleted.end())
	// 				if (I.getOpcode() == Instruction::Br && I.getNumOperands() == 1)
	// 				{
	// 					for (unsigned i = 0, ei = I.getNumOperands(); i != ei; i++)
	// 					{
	// 						Value *operand1 = I.getOperand(i);

	// 						int Kj = 0;
	// 						for (BasicBlock &BB1 : F)
	// 							for (Instruction &Ii : BB1)
	// 							{
	// 								Kj++;

	// 								if (Kj > Ki && flag)
	// 								{
	// 									for (unsigned j = 0, ej = Ii.getNumOperands(); j != ej; j++)
	// 									{
	// 										Value *operand2 = Ii.getOperand(j);

	// 										if (operand1 == operand2)
	// 										{
	// 											insertInfl(&I, &Ii);
	// 											if (std::find(vecCompleted.begin(), vecCompleted.end(), &Ii) == vecCompleted.end())
	// 											{
	// 												vecCompleted.push_back(&Ii);
	// 											}
	// 											flag = false;
	// 										}
	// 										else
	// 										{
	// 											insertInfl(&I, &Ii);
	// 										}
	// 									}
	// 								}
	// 							}
	// 					}
	// 				}
	// 		}
	// }

	void displayInfl()
	{

		std::cout << " Display Infl started---------------------------->\n\n"
				  << std::endl;
		__itr_mapIns_type__ itr = map_Infl.begin();

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

		__vecIns_type__ Inslist;
		for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I)
		{
			Inslist.push_back(&*I);
		}
		__vecIns_type__::iterator iter = Inslist.begin();

		while (iter != Inslist.end())
		{
			Instruction *instr = *iter;

#ifdef __LLVM_DEBUG__
			errs() << "\n\n\ndef: " << *instr << " its address is " << instr << "\n";
			__vecIns_type__ PredList = getPredessorList(F, instr);

			for (int i = 0; i < PredList.size(); i++)
			{
				errs() << "\t\t Predecessor Instruction :: " << *PredList[i] << "\n";
			}
#endif

			Instruction *vi = dyn_cast<Instruction>(instr);
			if (vi->getOpcode() == Instruction::Store)
			{

#ifdef __LLVM_DEBUG__
				errs() << "Ref: " << *instr << "\n";
#endif

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
#ifdef __LLVM_DEBUG__

						errs() << "\t\t" << *vi << "\n";
#endif
					}
				}
			}
			iter++;
		}
	}
	void displayDEF()
	{

		std::cout << " Display DEF started---------------------------->\n\n"
				  << std::endl;
		__itr_mapIns_type__ itr = map_Def.begin();

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

		__vecIns_type__ Inslist;
		for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I)
		{
			Inslist.push_back(&*I);
		}

		for (__vecIns_type__::iterator iter1 = Inslist.begin(); iter1 != Inslist.end(); ++iter1)
		{
			Instruction *instr = *iter1;
			insertRef(instr, NULL);

			for (User::op_iterator i = instr->op_begin(), e = instr->op_end(); i != e; ++i)
			{
				Value *v = *i;
				Instruction *vi = dyn_cast<Instruction>(*i);
				if (vi)
				{
#ifdef __LLVM_DEBUG__
					errs() << "iter num operands = " << instr->getNumOperands() << "\n";
#endif
					insertRef(instr, vi);
				}
			}
		}
	}
	void insertRef(Instruction *ins, Instruction *ref)
	{

		__itr_mapIns_type__ itr = map_Ref.find(ins);

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

				__vecIns_type__ tmp_vec;
				tmp_vec.push_back(ref);

				map_Ref.insert(__pair_map_Ins__(ins, tmp_vec));
			}
			else
			{
				__vecIns_type__ tmp_vec;
				tmp_vec.clear();

				map_Ref.insert(__pair_map_Ins__(ins, tmp_vec));
			}
		}
	}
	/*	void insertRef(Instruction *ins, Instruction *ref)
	{

		__itr_mapIns_type__ itr = map_Ref.find(ins);

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

				__vecIns_type__ tmp_vec;

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
				map_Ref.insert(__pair_map_Ins__(ins, tmp_vec));
			}
		}
	}*/
	void displayREF()
	{

		std::cout << " Display REF started---------------------------->\n\n"
				  << std::endl;
		__itr_mapIns_type__ itr = map_Ref.begin();

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

	// void basiCBlockInfo(Function &F)
	// {
	// 	std::cout << " NITSHHHHHHHHHHHHHHHH  -------------------->" << std::endl;

	// 	std::vector<BasicBlock *> vecPerformed;
	// 	Instruction *curIns = NULL;
	// 	Function::iterator B_iter = F.begin();
	// 	while (B_iter != F.end())
	// 	{
	// 		BasicBlock *curBB = &*B_iter;
	// 		std::string name = curBB->getName().str();

	// 		for (BasicBlock::iterator I_iter = curBB->begin(); I_iter != curBB->end(); ++I_iter)
	// 		{

	// 			curIns = &*I_iter;

	// 			if (I_iter->getOpcode() == Instruction::Br)
	// 			{

	// 				if (std::find(vecPerformed.begin(), vecPerformed.end(), curBB) == vecPerformed.end())
	// 				{
	// 					errs() << "\t\t This is branch Instruction ::" << *I_iter << "\n";
	// 					bool flag = false;
	// 					for (BasicBlock *SuccBB : successors(curBB))
	// 					{
	// 						if (!flag)
	// 						{
	// 							flag = true;
	// 							vecPerformed.push_back(SuccBB);
	// 							for (Instruction &I : *SuccBB)
	// 							{
	// 								errs() << " \t\t\t ::" << *&I << "\n";
	// 							}
	// 						}
	// 					}
	// 				}
	// 			}
	// 		}

	// 		++B_iter;
	// 	}
	// }

	void computeRcScBcPlus1(Function &F)
	{
		bool successflag = false;
		for (unsigned char i = 0; i < TC; i++)
		{
			__mapIns_type__ map_RCk_old = map_RCk;

			computeRCkPlus1(F);
			//	displayRCkPlus1();

			__mapIns_type__ map_RCk_new = map_RCk;

			__mapIns_Inc_type__ map_SCk_old = map_SCkPlus1;

			computeSCkPlus1(F);
			//displaySCkPlus1();

			__mapIns_Inc_type__ map_SCk_new = map_SCkPlus1;

			__mapIns_Inc_type__ map_BCk_old = map_BCk;

			computeBCkPlus1(F);

			__mapIns_Inc_type__ map_BCk_new = map_BCk;

			if (isFixedPointConverge(map_RCk_old, map_RCk_new) && isFixedPointConverge(map_SCk_old, map_SCk_new) && isFixedPointConverge(map_BCk_old, map_BCk_new))
			{
#ifdef __LLVM_DEBUG__

				errs() << "@computeRcScBcPlus1::Fixed point achieved at iteration no " << (int)i << "\n";

#endif
				break;
			}
		}
	}
	void displayFinalInstruction(Function &F)
	{
		std::cout << " Program Slicing for Given Procedure are as follows :: " << std::endl;
		bool breakFlag = false;
		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{
				if (getSCkPlus1(&I))
					errs() << "\t\t " << *&I << "\n";

				if (C.p == &I)
				{
					breakFlag = true;
					break;
				}
			}
			if (breakFlag)
				break;
		}
	}

	bool isMemorySame(Function &F, Instruction *I1, Instruction *I2)
	{
		__vecIns_type__ vecTmp;
		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{
				vecTmp.push_back(&I);
			}
		}

		__itr_vecIns_type__ itr1 = std::find(vecTmp.begin(), vecTmp.end(), I1);
		__itr_vecIns_type__ itr2 = std::find(vecTmp.begin(), vecTmp.end(), I2);

		if (itr1 == itr2 && itr1 != vecTmp.end())
		{
			return true;
		}
		else
		{
			return false;
		}
	}
	void CheckCriteriaBreak(Function &F, Criteria Cb)
	{

		std::cout << " Program Slicing for Given Procedure are as follows :: " << std::endl;

		__vecIns_type__ vecTmp;
		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{
				vecTmp.push_back(&I);
			}
		}

		__itr_vecIns_type__ itr = std::find(vecTmp.begin(), vecTmp.end(), Cb.p);

		if (itr == vecTmp.end())
		{
			std::cout << " Given crieria point doesn't exist in Program " << std::endl;
		}
		else
		{
			__itr_vecIns_type__ itr1 = vecTmp.begin();
			while (itr1 != itr)
			{
				errs() << " Checking through iterators ::  " << *itr1 << "\n";

				itr1++;
			}
		}

		bool flag = false;
		for (BasicBlock &B : F)
		{
			for (Instruction &I : B)
			{
				errs() << "  NITISH Instruction :: " << &I << "\n";
				errs() << " Crieria Instruction :: " << Cb.p << "\n";
				if (Cb.p == &I)
				{

					std::cout << " Memeory same " << std::endl;
					flag = true;
					break;
				}
			}
			if (flag)
				break;
		}
	}
	void getAnalysisUsage(AnalysisUsage &AU) const override
	{
		AU.setPreservesCFG();
		AU.addRequired<LoopInfoWrapperPass>();
	}
	void setInfluence(Function &F)
	{
		//F.viewCFG();

		LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

		for (BasicBlock &BB1 : F)
		{

			bool isLoop = LI.getLoopFor(&BB1);
			for (Instruction &I : BB1)
			{

				if (I.getOpcode() == Instruction::Br)
				{

					Loop *L = LI.getLoopFor(&BB1);
					if (LI.isLoopHeader(&BB1))
					{

#ifdef __LLVM_DEBUG__
						errs() << "\n\n New Loop Branching detected---> @ ";
						errs() << I << " \n";
#endif

						for (auto *Block : L->getBlocks())
						{
							for (auto &I1 : *Block)
							{
								insertInfl(&I, &I1);
#ifdef __LLVM_DEBUG__
								errs() << *&I1 << "\n";
#endif
							}
						}
					}
					else
					{

						BranchInst *BI = dyn_cast<BranchInst>(BB1.getTerminator());
						if (BI && BI->isConditional())
						{
#ifdef __LLVM_DEBUG__
							errs() << "\n\n New Conditional Branching detected---> @ ";
							errs() << I << " \n";
#endif
							for (auto *Block : successors(&BB1))
							{
								for (auto &I1 : *Block)
								{
									insertInfl(&I, &I1);
#ifdef __LLVM_DEBUG__
									errs() << *&I1 << "\n";
#endif
								}
							}
						}
					}
				}
			}
		}
		errs() << '\n';
	}
	void setProgramPointForCriteria(Function &F, int P)
	{
		int count = 0;
		for (BasicBlock &BB : F)
			for (Instruction &I : BB)
			{
				count++;
				if (P == count)
				{
					errs() << " Criteria is set for program IR point = " << I << "\n";
					C = setCriteria(&I);
				}
			}
	}
	bool runOnFunction(Function &F) override
	{

		setCountTotalIns(F);
		setDef(F);
		displayDEF();
		setListOfVariables();
		setRef(F);
		displayREF();
		setInfluence(F);
		displayInfl();
		setProgramPointForCriteria(F, 34);
		computeRC0(F);
		displayRC0();
		//displaySuccList(F);
		computeSC0(F);
		displaySC0();
		computeBC0(F);
		displayBC0();
		computeRcScBcPlus1(F);
		displayFinalInstruction(F);

		//displayPredList(F);

		std::cout << " CALLS OVER " << std::endl;
		return false;
	}
}; // namespace
} // namespace
char PSlicePass::ID = 0;
static void registerlinkuse(const PassManagerBuilder &, legacy::PassManagerBase &PM) { PM.add(new PSlicePass()); }
static RegisterStandardPasses X(PassManagerBuilder::EP_EarlyAsPossible, registerlinkuse);
