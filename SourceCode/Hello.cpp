#define DEBUG_TYPE "hello"//-hello
#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Pass.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Attributes.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/Support/MathExtras.h>
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <stack>
#include <set>
#include <iostream>
#include <string>
using namespace llvm;

 int NumberofInstinFunction(CallInst* function);
// void Return_Inst_store(CallInst* function);


namespace {
	struct Hello :  public FunctionPass {
		static char ID;                           
		Hello() : FunctionPass(ID) {}
	        //DEFINE_INTPASS_ANALYSIS_ADJUSTMENT(PointerAnalysisPass);
	        /**
	         * @brief Runs this pass on the given function.
	         * @param [in,out] func The function to analyze
	         * @return true if the function was modified; false otherwise
	        */
	        virtual bool runOnFunction(Function &F);

			StringRef get_function_name(CallInst *call);
	};
}


char Hello::ID = 0;
static RegisterPass<Hello> X("hello", "Hello World Pass", false, false);

bool Hello::runOnFunction(Function &F){
// errs()<<'\n';

bool modified = false;

for(Function::iterator block = F.begin(),i=0; block != F.end();i++, block++) {
	//Step 1 iterate over all insturctions

	for(BasicBlock::iterator inst = block->begin(); inst != block->end();++inst) {
		Instruction * Inst = inst;
		bool NonConstArgFlg = false;
		if(isa<CallInst>(Inst)){
			CallInst* callInst = dyn_cast<CallInst>(Inst);
			Function* call = callInst->getCalledFunction();		// func -- call	
			//errs() <<"--------"<<*call<<"-----"<< '\n';
			Function *fun = callInst->getCalledFunction();
			// if stm fun is direct call and is NOT declaration
			// NumberofInstinFunction(callInst);
			if(NumberofInstinFunction(callInst)<10){
				if (fun && !fun->isDeclaration()) {
					StringRef funname = fun->getName(); //here i would take fun and not call!  
					// print funname
					errs() << funname << '\n'; 
					// Function::arg_iterator arg = fun->arg_begin();
					for(int j = 0; j < callInst->getNumArgOperands(); j++){
						Value* number = callInst->getArgOperand(j);
						errs()<<" Printing arguments\n";
						errs()<< *number << "\n";
						if (isa<Constant>(number)){
							errs()<<"Is a constant\n";	
						}
						else{
							errs()<<"Is not a constant\n";
							NonConstArgFlg = true;
							break;
						}
						
					}
					if(!NonConstArgFlg){//if all arg is constant do step 4 - 8
						errs()<<"Start modification\n";//step 4 - 8 code start from here
						int k = 0;//Step 4
						for(Function::arg_iterator argiter=fun->arg_begin(); argiter != fun->arg_end(); argiter++, k++){
							Value* argument = callInst->getArgOperand(k);
							Constant *c = (Constant *) argument;
							const APInt api = c->getUniqueInteger();
							Constant *newC = ConstantInt::get(argiter->getType(), api);
							errs()<< *newC << "...NewC\n";
							errs()<< *c << "...c\n";
							argiter->replaceAllUsesWith(newC);//Step 5
							errs()<< *argiter <<"\n";
							
						}
						// Step 6
						llvm::ValueToValueMapTy vmap;
						if(call != NULL && !call ->isDeclaration()){
							
							for (Function::iterator b = call->begin(), be = call->end(); b != be; ++b) {
                    				for (BasicBlock::iterator i = b->begin(), ie = b->end(); i != ie; ++i) {
                    					if(isa<ReturnInst>(i)) continue;


                    					// step 6 part 1 

                    					Instruction *new_inst = i->clone();
                    					new_inst->insertBefore(Inst);
                    					vmap[i] = new_inst;
                    					llvm::RemapInstruction(new_inst, vmap, RF_NoModuleLevelChanges);                    			

      
						
                    				}
                    				}
						}
						// Step 6 part 2 -- getting return and storing it after call and then deleting call
						if(call != NULL && !call ->isDeclaration()){
							
						for (Function::iterator b = call->begin(), be = call->end(); b != be; ++b) {
                    		for (BasicBlock::iterator i = b->begin(), ie = b->end(); i != ie; ++i) {
						// Step 6 Part 2
						if (ReturnInst *temp_return_inst = dyn_cast<ReturnInst>(&*i)) {
							errs() << "Found return instruction:\n"; // getting void
                            errs() << *temp_return_inst << "\n";

                            Instruction *inst_after_func_call = ++inst;       // getting position after call
                            errs() << "Instruction after function call: " ;
                            errs() << *inst_after_func_call << "\n";
                            Instruction *inst_func_call = --inst;       // getting position of call
                            errs() << "Instruction of function call: " ;
                            errs() << *inst_func_call << "\n";                            


                            //if(isa<StoreInst>(inst_after_func_call)){	// Not going in if return type is  void
                            	if(temp_return_inst->getNumOperands()!=0){ // Go in even if there is no store but not if it is void
                            	// going in only when store is after call instruction
                            	Value *return_value = temp_return_inst->getReturnValue();
                            	errs() << "Return value: " ;
                                errs() << *return_value << "\n";
                                errs() << "Store line detected after call \n";
                                // Now to add a store instruction after call with pointer of return value
                               // errs() << "Trying to insert store instruction after call " ;

                                //inst_after_func_call->replaceAllUsesWith(return_value);
                                // Replace all uses with the return value 
                                callInst->replaceAllUsesWith(vmap[return_value]);
                               // --inst;
                                //step 8
                                // Deleting call from main using erasefromParent
                               // inst_func_call->eraseFromParent();
                             

                            	
                            }
                                --inst;
                                //step 8
                                // Deleting call from main using erasefromParent
                                inst_func_call->eraseFromParent(); // should erase call even if there is no store after call
                              //inst_func_call->eraseFromParent();


						}
					}
				}
			} 


						//step 4 - 8 codes end here
						bool modified = true; //Turn modified to true if modified
					}
						
				}
			}else//else for if(NumberofInstinFunction(callInst)<10)
			{
				errs()<<"Long Functions Have "<<NumberofInstinFunction(callInst)<<" inst\n";
				
			}
		}
		
	}
}
return modified;
}

 

 int NumberofInstinFunction(CallInst* function){
 	int i=0;
 	Function* func = function->getCalledFunction();	
 	if(func!=NULL)
	for(Function::iterator block = func->begin(); block != func->end(); block++) {
		i=i+block->size();
   }
   errs()<<"Number of insturctions"<<i<<"\n";
   return i;
   errs()<<"Number of insturctions"<<i<<"\n";
 }

/*
void Return_Inst_store(){
        for (Function::iterator b2 = function->begin(), be2 = function->end(); b2 != be2; ++b2) {
                for (BasicBlock::iterator i2 = b2->begin(), ie2 = b2->end(); i2 != ie2; ++i2) {
                    if (ReturnInst *temp_return_inst = dyn_cast<ReturnInst>(&*i2)) {	// Detecting return instruction, if detected gointo the loop
                    	errs() << "Found return instruction: ";
                        errs() << *temp_ret_inst << "\n";	// printing if return instruction found
                        Instruction *inst_after_func_call = ++i;
                        errs() << "Instruction after function call: " ;
                                                        errs() << *inst_after_func_call << "\n";


                    }
                }
            }


}*/
