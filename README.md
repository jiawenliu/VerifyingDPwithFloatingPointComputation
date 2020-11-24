# Formally Verification of Differential Privacy under Finite Computation
main ideal: Providing verification tools for formally verifiying the differentially privacy algorithms implementated under finite computation and formalizing the verification in Coq.
Steps:
1. having the differentially privacy programs formally verified in ideal real computation. (see in snap-ideal/main.tex)
2. having a transition semantics formally transits the programs from real computation into floating-point computation with relative computation error. Then verifying that the programs trasited into floating-point computation within certain transition error still preserve differential privacy. (see in snap-flopt/main.tex)
3. integrating the logic for verifying the DP of ideal computation together with the transition semantics, which works together to provide the formal verification of the differential privacy of an program in floating-point computation. (see in snap-connect-v3/main.tex)
4. formalizing the new verification method in Coq. (see in implementation/src/\*.v )
5. adding several examples: snapping mehcnaism, exponential mehcanism in base-2 implementation, and discrete gaussian mehcanism. (see in implementation/examples/\*.v )
