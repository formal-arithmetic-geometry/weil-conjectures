# Q98 — lem-trf-localized-polynomial-resolution-model

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-localized-polynomial-resolution-model.json`: statement, split; no Mathlib match for the complete augmented simplicial-resolution assertion. Six proof steps. The statement is unchanged. Added its existing module-localization definition to `stmt_deps`.
- `citations.json`: thirteen entries, one for each step/node pair, checked verbatim against the live statements.
- `report.md` and the search command's `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. Reused existing Mathlib leaves for localization of a tensor product over a base, exactness of module localization, and polynomial scalar extension. No repository writes, git commands, Lean edits, compiler calls, or delegation.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, localized polynomial resolutions, and polynomial-resolution terminology. No declaration gives the full item. The existing cotangent-resolution declaration recorded on another node is not an attachment for this item and is used only through that node's natural-language definition of a resolution.

## WANTED

None. The required ring computations are present in the local Stacks source.

## Corrections and source/route observations

The imported item had no proof. Its statement is correct including arbitrary sets of variables and a multiplicative set containing zero, so no statement dispute or correction is needed. Its use of module localization now names `def-weil-pbc-module-localization` explicitly in statement dependencies.

Read chapter `sec-trace-formula`, unit `sk-i-curve-zero`, the three levels in SETUP, and the current latest blueprint (COMMITS: main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345). The latest local-term locality proof uses Varshavsky's contracting-correspondence route; the inherited `blueprint.from` records a historical semistable/dualizing/cotangent auxiliary branch. This delivery supplies precisely the existing algebra item below that branch and does not replace or re-realize a current unit step. The item is not a unit key node, so no unit record is written. Kept the inherited provenance field and explained its present relation in `split_report.blueprint`.

## Searches and not duplicates

The current item is not a Mathlib leaf: the search results offer exactness and scalar-change components but no declaration giving polynomial terms, the augmented simplicial maps, the complex identification and the augmentation together. Ran the mandated grep, LeanSearch, Loogle and LeanFinder commands, plus a second semantic phrasing; read the returned declaration types. The commands' actual summaries are retained in `searches.jsonl` and appended to the inherited `mathlib_searches` without altering earlier searches.

Searched the whole DAG for localization exactness, tensor localization, and polynomial scalar extension, and the whole blueprint through `tools/blueprint_refs.py search` for polynomial resolutions, localization, scalar extension, and the combined concepts. The two broad searches produce many unrelated sheaf-localization and coefficient-extension nodes; none states this item. Crucially the existing nodes `lem-weil-pbc-localization-module-exact`, `lem-weil-pbc-localization-tensor-over-base`, and `lem-weil-pbc-polynomial-scalar-extension` already state the needed generic facts. Reused them instead of creating narrower duplicates. No new node pairs require a `## Not duplicates` section.

## Review by Q98

I read Stacks `cotangent.tex`, Tag 08QI (`remark-resolution`, lines 667–705) for the definition/criterion, and Tag 08QP (`lemma-flat-base-change`, lines 958–980) for the computation with scalar extension of the augmented alternating-face complex. I read `algebra.tex`, Tag 00DK (`lemma-tensor-localization`, lines 2088 onward) for the actual fraction formula and its proof, Tag 00CS (`proposition-localization-exact`, lines 1336 onward) for exactness including its denominator argument, Tag 07JZ and the surrounding fraction construction for module localization, and Tag 00CX for the tensor universal property. There are no new nodes needing additional sources.

For step 1 I opened `lem-weil-pbc-localization-tensor-over-base`: it really supplies the isomorphism on arbitrary multiplicative sets, not only powers of one element. Its specialization is A=R and first module R, second module M. Its isomorphism, combined with the explicit tensor unit maps, gives the requested fraction/tensor isomorphism. I wrote out B-linearity and the naturality calculation instead of assuming an unnamed comparison. The cited tensor definition supplies the balancing relations and generation by pure tensors; the localization definition supplies the induced maps on fractions. I also read the recorded Mathlib source `RingTheory/Localization/BaseChange.lean:244–263`; it handles arbitrary submonoids and has the required naturality. This is a generic Mathlib tool, not a change of unit route.

For step 2 I checked that the tensor definition licenses the factor switch and equality of linear maps on pure tensors, and that `def-weil-module-base-change` explicitly states preservation of composition, identities and linear combinations, as well as extension of bilinear multiplication. Those exact statement clauses establish the simplicial identities and the augmentation. Multiplicativity of the fraction map and its unit are calculated on pure tensors; the maps induced by faces and degeneracies are written on fractions. There is no claim that the chosen polynomial coordinates respect degeneracies; that unnecessary additional requirement would not be justified.

For step 3 I opened `lem-trf-cotangent-resolution-coherence` and `lem-weil-pbc-polynomial-scalar-extension`. The former defines a resolution by polynomial terms, levelwise surjective augmentation and a quasi-isomorphism on the alternating complex. The latter quantifies over an arbitrary set J and states the algebra isomorphism and its coefficient/variable maps. Applying it to R→B after switching factors proves polynomiality of each Q_n. I read `RingTheory/TensorProduct/MvPolynomial.lean:97–113`, including `algebraTensorAlgEquiv`, its formula on pure tensors, and its inverse on variables. No hypothesis of finite variables or a nonzero base ring occurs.

For step 4 the coherence node states exactly what s(P) and its differential mean; the base-change definition states linearity in the map. I checked the equality for every face and their finite signed sum, and wrote the augmentation equality too. The degreewise maps have the inverse from step 1, so this proves an isomorphism of augmented complexes, not merely an agreement of cohomology dimensions. This step is elementary from those cited definitions and the previously proved fraction formula.

For step 5 the coherence node's resolution criterion gives the exact augmented sequence. I checked the cited exact-localization node states exactness for any triple of modules and any multiplicative subset, and read `Algebra/Module/LocalizedModule/Exact.lean:37–59`. It applies to all consecutive triples, including both the degree-zero boundary and surjectivity at the target. The proof separately lifts t/s by choosing a preimage p in each P_n and using p⊗(1/s), so it obtains the levelwise surjectivity required by the definition, not only the degree-zero quasi-isomorphism. No derived tensor theorem or K-flatness is used without citation: the argument is directly through exact localization.

For step 6 I used the localization definition's fraction relation and operations to check the map S^{-1}B→B, both inverse identities, B-linearity and multiplication. The proof explains how an equality of fractions descends by inverting u/1; it does not assume denominators are nonzero. The composite augmentation is explicitly ε(p)b. The tensor definition and fraction relation also show all modules in question vanish if 0∈S, so this case is covered without imposing 0∉S or nontriviality.

Small cases checked: S={1} gives the ordinary tensor unit comparison and recovers P→T; 0∈S gives zero rings/modules and the zero augmented complex; T=B gives the stated product augmentation; P_n=R (empty variable set) gives Q_n=B; infinite E_n is allowed by the scalar-extension node. Zero divisors in R cause no problem since the fraction equivalence uses an extra multiplier u rather than cancellation in R.

Checked delivery-errors B–E against these actual files: no new statement-only nodes to smuggle a proof into, no relabelled clauses or hidden new lemmas, every non-elementary input is an existing cited statement, every citation has a verbatim statement quotation, no definition is cited for an unstated exactness theorem, and all hypotheses used are present. Every proof step is under 1100 characters, so none triggers the >2000-character long-step review. The inherited item provenance is preserved; no SGA source or route is used. The searches were run and their hits read, not reconstructed from names alone.

## Unfinished work

None in the split. The maintainer's independent mathematical review remains the normal next review after delivery.
