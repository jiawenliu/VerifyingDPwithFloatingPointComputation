# Differential Privacy in Floating-Point Computation
main ideal: Formally verifiying the differentially privacy algorithms implementated in flaoting-point computation and implementing the verification in Coq.
Steps:
1. having the differentially privacy programs formally verified in ideal real computation. (seen in snap-ideal/main.tex)
2. having a transition semantics formally transits the programs from real computation into floating-point computation with relative computation error. Then verifying that the programs trasited into floating-point computation within certain transition error still preserve differential privacy. (seen in snap-flopt/main.tex)
3. integrating the logic for verifying the DP of ideal computation together with the transition semantics, directly verifying the differential privacy of an program in floating-point computation. (seen in snap-connect-v3/main.tex)
4. implementating the integral system in Coq. (seen in implementation/src/\*.v )
5. adding several examples: snapping mehcnaism, exponential mehcanism in base-2 implementation. gaussian mehcanism. (seen in implementation/examples/\*.v )
