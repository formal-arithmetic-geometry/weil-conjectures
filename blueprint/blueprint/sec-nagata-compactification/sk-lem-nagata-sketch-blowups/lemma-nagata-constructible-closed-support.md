+++
id = "lemma-nagata-constructible-closed-support"
kind = "lemma"
title = "Property of the constructible-support ideal, [stacks-project]"
order = 172
lean = ["AlgebraicGeometry.Scheme.exists_finiteType_ideal_coe_support_eq_compl"]
uses = ["def-nagata-constructible-closed-support", "def-nagata-extended-ideal", "lemma-nagata-finite-type-ideal-extension-exists", "lemma-nagata-qc-open-complement-ideal"]
+++
The ideal $\mathcal J_U(T)$ is finite type and quasi-coherent, and its
vanishing set is exactly $T$.

## Proof

An open constructible subset of a spectral space is quasi-compact. Apply
[lemma-nagata-qc-open-complement-ideal] to $W=U\setminus T$; its
vanishing set is $U\setminus W=T$.
