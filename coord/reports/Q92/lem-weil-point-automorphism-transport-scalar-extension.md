# Q92: lem-weil-point-automorphism-transport-scalar-extension

## Files written

- `dag/nodes/sec-six-functors/lem-weil-point-automorphism-transport-scalar-extension.json`: statement, split into seven steps; no Mathlib match for the whole item.
- `citations.json`: one verbatim statement quotation for every use in every proof step.
- `report.md`: this report. The sandbox also retains the actual `searches.jsonl` log and the scripts used to write the JSON.

There are **0 new nodes and 0 Mathlib leaves**. All non-elementary inputs already have nodes. The ordinary tensor restriction calculation and the comparison cancellations belong in this item's proof, rather than in new nodes restating its clauses.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the exact item tag and point-automorphism/point-transport names, then for Frobenius transport and sections/scalar concepts. No declaration states the completed integral equation with these specified maps and its rational and tower clauses. I read `SixFunctors/ProEtale/Adic/PadicIntModuleUpperStar.lean`: its integral-to-algebraic-closure pullback comparison does not state this item, which concerns finite valuation-ring extensions and completed derived comparisons. The Weil-sheaf Frobenius/stalk transport hits likewise do not give these clauses. No sorried upstream declaration was treated as a finished proof.

## WANTED

None. The documents used are available. The completed comparison calculation is explicitly agent-written; it is not attributed as a numbered theorem of Deligne.

## Source error

**STATEMENT-DISPUTED: the imported explanatory description of the direction of the sections comparison was ill-typed.** The old wording described phi as “the inverse of sections-tensor followed by Gamma(chi)”. Write A = Gamma(H) tensor O_L, B = Gamma(CH), D = Gamma(TH). Then theta has type A to B and Gamma(chi) has type B to D. Their inverses and composite therefore give the required map D to A as `(Gamma(chi) composed with theta)^(-1) = theta^(-1) composed with Gamma(chi)^(-1)`. Composing theta inverse with Gamma(chi) in the verbally specified order does not type-check: the intermediate objects disagree, whichever order convention is intended.

I replaced only that explanatory phrase by the explicit formula `phi_H = (Gamma(chi_H) composed with theta_H)^(-1)`, introducing theta with its domain and codomain. This is precisely the formula in the already cited statement of `lem-weil-point-sections-scalar-extension`, and agrees with the item's existing arrow direction and equations. No hypothesis or conclusion is weakened. This is an error in the imported wording, not an error in Deligne.

## What changed and what remains

The item was unsplit and had no proof. Steps 1–2 establish the typing and ordinary tensor restriction square; Step 3 conjugates it by the specified chi maps; Step 4 uses the existing specified-kappa comparison equation and naturality of phi. Steps 5–6 check the ordinary and completed unit/tower equations, and Step 7 rationalizes. The completion, kappa, pullback and sections maps remain exactly those named in the statement. I retained the inherited source, ancestry, chapter/unit, creation data, and earlier Mathlib searches.

No unfinished part of this one-level split remains. Its existing unsplit dependencies retain their own proof obligations; I do not claim that the entire closure has been formalized.

## Searches and reuse

No prior sandbox node, report, split, or search log existed at the start. I copied the current repository item. I retained its Q97 searches and ran the Q92 searches recorded verbatim in `searches.jsonl` and appended to `mathlib_searches`: LeanFinder for both the completed point-automorphism square and the more general restriction/sections tensor square, LeanSearch for inverse image and sections tensor compatibility, Loogle for `"sheafTensor"`, and three source greps.

The semantic results include ordinary ring/field restrictions, scheme structure-sheaf evaluation, sheaf-module pullback of free sheaves, and presheaf tensor restriction. I read the returned `PresheafOfModules.Monoidal.tensorObjMap` at `Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean:45` and the free-pullback naturality at `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean:132`. These are relevant ingredients, but neither is the whole completed transport assertion or a one-line specialization to all its clauses. In particular the former defines presheaf tensor restriction rather than proving the specified completion/pullback square. All services used in this attempt answered; none was recorded as unavailable or as a match incorrectly.

The whole DAG was searched for automorphism/scalar compatibility, point sections tensor, restriction tensor and the existing comparison names. Blueprint searches for scalar extension, transport, point transport and point automorphism found no blueprint node stating the item. The exact nearest blueprint ancestor is `def-weil-global-geometric-frobenius`, as returned by `tools/blueprint_refs.py ancestor`. The recorded `same_as` remains empty.

## Not duplicates

There are no new-node/existing-node pairs: no new node was created. I reused the existing sections-tensor, derived descent, ordinary associator, completion, inverse-image tensor-model, specified-kappa, and rationalization nodes. In particular I did not create another “restriction commutes with tensor” lemma or a new version of either equation of the item.

## Review by Q92

I read the full statement of the item and every node cited in its proof. I also read the chapter and inherited unit records, the current blueprint ancestor in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-weil-global-geometric-frobenius.md`, Deligne's (1.1.3) on printed p. 150 and (1.1.7) on pp. 150–151 (PDF pages 15–16), and the sheaf tensor construction in `literature/stacks-project/sites-modules.tex`, Tag 03EK, `section-tensor-product`. Deligne supplies the raw rationalization and point transport context; the blueprint specifies the first arrows whose coefficient compatibility this descendant supplies. The actual proof here is the explicit algebra of the already specified maps. No SGA source or alternative purity route is used. There are no new nodes needing additional sources.

In Step 1 I checked that `lem-weil-isomorphism-derived-pullback` explicitly places G_E K in the bounded constructible category and identifies it with P_E K there. The integral category includes derived completeness. Thus the three uses of chi and phi are valid. The completion node actually supplies a natural isomorphism, and the sections node actually specifies phi as the inverse of Gamma(chi) theta. The derived-descent node explicitly permits ordinary termwise tensor to compute derived tensor and permits all derived morphisms; I am not obtaining these facts merely from a definition of completeness or flatness.

For Step 2, `lem-pc-kflat-resolution` gives precisely a flat-term K-flat resolution. The tensor-model node explicitly makes G_E P K-flat, gives the local formula for b_P, and identifies its derived class with b_K. The finite-free point tensor node gives the pure-tensor formula for theta, including the constant-value coefficient sections. The restriction-natural node gives both the evaluation at V and the constant-coefficient formula using c inverse. Together with the tensor definition's restriction rule, these make both routes send x tensor a to the same sheafification image of x restricted to V tensor a restricted to V. I checked the transported coefficient action rather than assuming it acts as an unspecified identity. The equality is checked on generators of the source ordinary module tensor, so it never asserts that arbitrary sheaf tensor sections are sectionwise tensors. The derived-descent node and naturality of sigma for the resolution transfer this equality to K. I refined the proof to mention the resolution explicitly so that the b representative is covered by the cited statement's actual hypotheses.

For Step 3 I checked that the restriction-natural node states naturality for every derived morphism, with no constructibility assumption. It therefore applies to chi_K even before using any constructibility of CK. The isomorphism-comparison node's *statement* fixes beta as G(chi) b chi inverse, exactly as used; it is not a claim taken from that node's proof. The displayed cancellation then proves the first equation without changing its maps.

In Step 4 the same node states exactly alpha T(kappa_E) = kappa_L beta for the specified kappa, not just an unspecified pullback isomorphism. The definition of kappa makes it a morphism of the required completed-module derived category. Both its endpoints are the complete constructible objects checked in Step 1. Naturality of the sections comparison therefore applies to kappa_E itself. I checked the domains when inverting alpha and beta, and the displayed two-line substitution gives the requested t equation. No naturality of t was assumed.

For Step 5 I checked the tensor-model node and the ordinary tensor-tower node for their chain representative formulas and absence of completeness restrictions on the ordinary tensors. On the K-flat model the two maps on an iterated pure tensor give the same product of the two coefficient factors. This is a short generator computation with those statements, not an extracted lemma hiding the item's conclusion. For Step 6 the sections node explicitly defines the integral associator by conjugation with chi, and the completion node explicitly supplies naturality. Thus the beta tower formula follows by cancelling adjacent inverse comparisons. I wrote the resulting beta and psi tower equations, including the occurrence of beta at the intermediate extended object, and checked that naturality of phi applies to that morphism. The integral-operations scalar-extension node explicitly supplies the unit and tower coherence of alpha. These are the generic tool inputs declared in `split_report.tool_uses`; they supply comparison maps and their algebra, rather than replace any prescribed geometric argument of the inherited unit.

For Step 7 I checked that the coefficient-complex rationalization node is natural for arbitrary derived morphisms, gives exact tensor functors and the displayed fraction-compatible formula, and includes the mixed integral/field associator equation. The rationalization definition keeps integral objects and localizes morphisms without Karoubi completion. Tensoring the actual integral equality with L therefore gives the stated raw rational equation, with the same alpha and sections comparisons and the same composition laws.

I tested the zero complex, g = identity, E = L, a torsion integral complex such as O_E modulo a uniformizer, and a ramified finite extension inside a three-field tower. The pure-tensor equality still holds, the identity maps reduce to the stated multiplication/completeness identifications, and the rational equality is zero for a torsion complex as expected. No step assumes that g fixes k_0, that ramification indices are one, that the uniformizers agree, that K is a bounded flat complex, or that sections commute with an arbitrary inverse limit. The existing completion and resolution theorems carry those issues. None of the seven steps exceeds 2000 characters; the longest is the explicit ordinary tensor calculation. I checked it for a concealed independent lemma and kept the calculation in the item because it is just the restriction formula on pure tensors.

I checked the B–E delivery errors against the written files: the statement dependencies continue to name the notions used, every substantive proof input is a cited statement (with a verbatim quotation in `citations.json`), there is no clause moved to a new node and no citation back to the item or its ancestors, and the one direction/type correction is explicitly reported above. The preliminary server review check passed with zero new nodes. The full required dry run and delivery follow this report.
