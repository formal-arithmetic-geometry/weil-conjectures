# Worker report: lem-trf-valuation-specialization-stalk-model

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-specialization-stalk-model.json`: statement, split; no exact Mathlib match. Eight proof steps, 21 existing proof dependencies, no new nodes and no Mathlib leaves created. The statement and statement dependencies are unchanged.
- `citations.json`: 27 step/node records, with verbatim statements read from the live DAG. Each step's uses is covered and every quote was checked for literal inclusion in its cited statement.
- `report.md`: this report. `searches.jsonl` and the five search-result text files preserve the actual search executions and responses; `write_split.py` is the sandbox-local JSON writer.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact blueprint id and by valuation, specialization, stalk, fibre and local-ring terminology. The general specialization-localization theorems in `WeilConjectures/Mathlib/AlgebraicGeometry/Stalk.lean` cover only ring localizations. They do not state the item, its two module comparisons, its component-induced radical condition or its association clauses. The étale sheaf specialization declarations in `ConstructibleSheaf/LowerStarSpecialization.lean` concern different sheaves and sites and do not attach this item.

## WANTED

None. All sources used below are present in `literature/stacks-project/`. No source was downloaded and no SGA source was used.

## Problems found and changes

The imported item is mathematically correct. It had no proof; I expanded the local setup and calculations of Tag 0GSI into a proof using existing, more general tools. In particular, I did not add the flatness or association hypotheses of the parent theorem: they are unnecessary for this local-stalk model. I did not identify the generally non-Noetherian ring B with a Noetherian ring. Only its closed-fibre quotient is asserted Noetherian.

`lem-trf-finite-presentation-stalk-fibre-data` is not applicable because it requires locally finite presentation and a finitely presented sheaf. `lem-trf-flat-association-stalk-dictionary` also cannot be used because it assumes a flat morphism and a locally Noetherian base. Instead, the split uses the fully general fibre-stalk quotient and module-pullback-stalk lemmas and writes out the localization calculations. The off-unit generic tools are declared, with reasons, in `split_report.tool_uses`; I did not set the maintainer's top-level `tool_uses`.

## Unfinished work

None for this one-level split. No definition, Lean file, unit route or other existing node was changed. The unit's realization fields belong to its key-node worker, so this auxiliary item leaves them untouched.

## Not duplicates

No new node was created. Whole-DAG title, keyword and source-tag searches located the existing fibre quotient, affine germ-localization, canonical local-spectrum, reduced closure, minimal-prime radical, and tensor-localization nodes used here. Blueprint searches for `stalk localization`, `fibre stalk`, and `valuation specialization` found no blueprint node stating this item. The one Proj hit for `stalk localization` concerns a different construction.

## Review by Q39

I read the third proof paragraph of Stacks Tag 0GSI, `more-morphisms.tex`, lines 5206–5252. It explicitly sets B and N, gives the closed-fibre stalk quotients, introduces q by specialization, asserts the radical equality, and gives the final generic-fibre localizations. I also read the applicable source passages: Schemes 01HV (`lemma-spec-sheaves`), 01J7 (`lemma-specialize-points`), 0HA1 (`lemma-local-ring-fibre`), and 01I9 (`lemma-widetilde-pullback`); Sheaves 0098 (`lemma-stalk-pullback-modules`); Algebra 00ES (`lemma-irreducible`), 00DK (`lemma-tensor-localization`) and 00E3 (`lemma-spec-localization`); Divisors 02OJ and 05AT; and the local-algebra setup of More on Morphisms 0GSG. Properties 01PB confirms the distinction between finite type and finite presentation for the sheaf. There are no new nodes requiring an additional source review.

For step 1 I checked the statements of the locally-finite-type and essentially-finite-type definitions, the affine-open stalk localization, locally ringed space morphisms, affine spectrum stalks, and finite-type module stalk finiteness. These respectively supply a finite type chart C, B=C_p, the local stalk map, O_{S,s}=A, and finiteness of N. The point x is over the closed point, so the source of the local stalk map really is A, without replacing A by a different local ring.

For step 2 I checked the full statements of the localization-spectrum embedding and the canonical local-spectrum morphism, together with the spectrum definition. The canonical morphism's statement explicitly gives its image as the generalizations and identifies their local rings. The localization embedding gives uniqueness of q. The argument for q_0 contained in p is written out using D(c), and contraction to A is zero because f(y) is the generic point. The proof does not assume A injects into B.

For step 3 I checked that `lem-sbc-scheme-fibre-stalk-quotient` is for an arbitrary scheme morphism and explicitly states the canonical quotient ring map and its kernel. `lem-weil-pbc-module-stalk-pullback` explicitly supplies the tensor isomorphism and the formula for germs. `lem-weil-pbc-tensor-over-quotient-ring` gives the arbitrary-ideal module quotient, so the proof really has both compatible comparisons, not only a ring isomorphism. Neither quoted theorem needs a flatness or finite-presentation hypothesis.

For step 4 the valuation closed-fibre Noetherian lemma requires a local essentially finite type map and finite N; these have all been proved in step 1. Its statement explicitly asserts Noetherianity of B/m_AB. I only take that part and prove finiteness of L directly by images of generators, without confusing finiteness with finite presentation or assuming B Noetherian.

For step 5 the reduced induced closed-subscheme node explicitly gives the radical ideal and affine quotient. The affine fibre-product node explicitly identifies its projections and tensor coordinate ring; the quotient-tensor node supplies its quotient calculation. The component/minimal-prime node applies to the quotient C/I, not directly to C. I wrote the argument that the chosen global component remains a component in the open chart. The resulting minimality of p over I is exactly the hypothesis of `lem-weil-pbc-minimal-prime-localization-radical`; it gives the radical after localization, without any Noetherian hypothesis. This step proves the item's radical clause; no new lemma merely restates it.

For step 6 the affine germ-localization node explicitly states localization of the actual sheaf germ map for a quasi-coherent module on any affine open, with no Noetherianity or finiteness assumed. The affine-open ring stalk node gives the compatible ring localization. Both x and its generalization y lie in U. I wrote the maps and their inverse fraction formulas for the second localization, including the module formula, instead of relying on an unspecified transport between stalk models.

For step 7 I checked the tensor-localization-over-base statement, specializing its intermediate algebra and first module to A and its second module to B or N. This gives S^{-1}B and S^{-1}N from K tensor B and K tensor N. The previously proved contraction q cap A=0 guarantees that the denominators avoid q; the localization-spectrum node then gives primality of q_K. The second localization maps and inverses are explicit. The affine domain-stalk node supplies O_{S,t}=K, and the arbitrary fibre-stalk quotient and module-pullback-stalk statements at y give O_{X_t,y}=O_{X,y} and (F_t)_y=F_y. Both identifications and their module scalar actions are therefore accounted for. This does not treat the generic fibre as an open subscheme: for higher-rank valuation rings it need not be open.

For step 8 I read both the relative-assassin definition and the element-annihilator associated-prime definition. They use actual annihilators, with no Noetherian condition; the fibre projection is injective on points as in the scheme-fibre definition already present in the item. I wrote why a compatible ring/module isomorphism takes annihilators and maximal ideals to the corresponding ideals. This elementary step thus gives both directions of both equivalences, including when the stalk is zero.

I checked delivery-errors B–E against the actual files: no new statement-only node is needed; no duplicate or clause-renaming node was introduced; the sources use tags and labels; all notions retain their existing statement dependencies; every non-elementary input is a node in that step's uses; and all quoted statements actually say what is used. The new proof-dependency union equals the steps' uses. I also checked that the reused closed-fibre Noetherian, affine-germ localization and pullback-stalk nodes do not have this item in their dependency closures. No statement correction or disputed hypothesis was necessary.

Small cases checked: F=0 gives finite zero stalks and false association on both sides; A a field gives s=t and x=y, with q=m_B, the radical identity and unchanged fibre stalks; if Y_s is empty there is no x and the assertion has no instance. Nonreduced X is allowed because the closure is explicitly reduced, and no argument needs it to define a reduced fibre. Higher-rank/non-Noetherian valuation domains are allowed: generic-fibre calculations use multiplicative localization, while only the closed-fibre quotient is Noetherian. A module of finite type but not finite presentation still satisfies every cited hypothesis. All proof steps are shorter than 2000 characters, and their displayed comparisons are routine fraction computations from the cited general tools, not hidden new geometric lemmas.

The fresh Mathlib searches ran through the required msearch command: LeanFinder twice, Loogle, grep, and LeanSearch. All five were available and their full results are retained. I read the candidate stalk and restriction declarations; they are ingredients already represented by existing nodes, not a one-line specialization giving the whole item. I retained the inherited item searches and appended only searches actually run for Q39.

The server `review_split` check passed with zero new nodes. The final delivery dry run and push are performed after this report is written.
