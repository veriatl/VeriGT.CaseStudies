Modular and Reusable Verifier Design through an Intermediate Verification Language
=======

Introduction
------
Previously, we have developed the VerMTLr framework that allows rapid verifier construction for relational model transformation languages. VerMTLr draws on the Boogie intermediate verification language to systematically design modular and reusable verifier. It also includes a modular formalisation of EMFTVM bytecode to ensure verifier soundness. In this work, we will illustrate how to adapt VerMTLr to design a verifier for the SimpleGT graph transformation language, which allows us to soundly prove the correctness of graph transformations. An experiment with the Pacman game demonstrates the feasibility of our approach. This repository contains the experimenting details for VeriGT system.


Overview of Repository
------
1. Libraries
2. The Source Files for ATL Transformation
3. Encoding soundness verification
4. Transformation contracts verification
5. Regression Tests + Driver + Result

Libraries
------
VeriATL system is driven by two essential Boogie Libraries:
- Library for Metamodel & OCL [portal](https://github.com/VeriATL/VeriGT/blob/master/Prelude/LibOCL.bpl)
- Library for EMFTVM bytecode formalisation [portal](https://github.com/VeriATL/VeriGT/blob/master/Prelude/Instr.bpl)

The Source Files for ATL Transformation
------
We demonstrate VeriATL system against ER2REL transformation. The source files of this transformation contain:
- Source (Pacman) metamodels [portal](https://github.com/VeriATL/VeriGT/blob/master/Source/Pacman.ecore)
- Semantics of Pacman in SimpleGT [portal](https://github.com/VeriATL/VeriGT/blob/master/Source/Pacman.simplegt)

Verifying sound encoding of ATL rules
------
We verified the soundness of our encoding for the execution semantics of SimpleGT rules. To perform this verification, both metamodels and ATL specification are encoded in Boogie.
- metamodels [portal](https://github.com/VeriATL/VeriGT/blob/master/Prelude/Metamodels.bpl)
- **SimpleGT rules** [portal](https://github.com/VeriATL/VeriGT/tree/master/Rule_TranslationValidation)


Transformation contracts verification
------
Using the sound encoding of ATL rules, we can verify transformation specification against transformation contracts. We verify Pacman transformation against 3 OCL contracts:

1. GemReachable [portal](https://github.com/VeriATL/VeriGT/blob/master/Pacman_TransformationCorrectness/PacmanP1.bpl)
2. PacmanSurvive [portal](https://github.com/VeriATL/VeriGT/blob/master/Pacman_TransformationCorrectness/PacmanP2.bpl)
3. PacmanMoved [portal](https://github.com/VeriATL/VeriGT/blob/master/Pacman_TransformationCorrectness/PacmanP3.bpl)

To modularize the verification task, the encodings of ATL rules are encapsulated in this file [portal](https://github.com/VeriATL/VeriGT/blob/master/Prelude/ATLRules.whole.bpl).


Performance
------
We also record the **performance** [portal](https://github.com/VeriATL/VeriGT/tree/master/UnitTesting/Benchmark) of regression tests for reader who interested.


------


