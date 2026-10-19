# Stage-1 report: lem-coef-etale-hom-thick-locus

## Files written

- `dag/nodes/sec-six-functors/lem-coef-etale-hom-thick-locus.json`: existing statement node, now split in nine steps. Statement, coefficient categories, hypotheses and blueprint ancestry retained. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim quotation for each step/node citation.
- `searches.jsonl`: actual `msearch.py` log; the item's historical searches are retained and the five new logged queries are recorded in its `mathlib_searches`.

## Attachments

None. Searches by the exact blueprint tag and by scalar extension/internal Hom/triangulated terminology in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration proving this item. In particular, the existing complex and homotopy-category internal Hom adjunctions do not assert the unbounded derived scalar comparison or its shift square. Upstream master is reference material only.

## WANTED

None.

## Issues found and repaired

No statement dispute. This is the ordinary unbounded derived category of constant-coefficient module sheaves on the small étale site. No constructibility, boundedness, Tor-amplitude, coefficient flatness or idempotent-completeness hypothesis has been added.

The source blueprint suppresses the compatibility of its evaluation-defined map with shifts in the sentence “Exactness in the first argument now proves it for K”. The item exists precisely to fill that gap. The main-20261015 version of `thm-coef-finite-hom` is in `sec-smooth-purity/sk-lem-sp-tower` and repeats the relevant master argument; I read both. I retained this item's historical master ancestry and its maintainer-owned unit.

My initial short draft did not make the shift signs explicit and wrote the retract inverse imprecisely. I replaced it with the componentwise signed calculation and a fully typed inverse using the two contravariant functors. I also replaced the initial malformed citation with literal slices of the actual statements. Exactness of scalar extension alone does not specify the correct shift normalization, so Step 1 now cites the existing `lem-sbc-derived-scalar-extension-counit-shift`. The tensor comparison itself now cites the existing ringed-topos tensor-pullback theorem. These corrections required no new nodes.

## Unfinished work

None in the one-level stage-1 split. All generic facts used below it already have DAG nodes, including the Mathlib triangle-isomorphism leaf. No Lean was written and no compiler, Lake or build command was run.

## Review by Q107

I read the item's imported statement, its parent `thm-coef-finite-hom` split and the master source proof, the current main-20261015 statement/proof, the chapter and unit records, and the full delivery-error checklist B–E. The source route is the parent's localization reduction: prove thickness for this particular map, then apply it to generators. I did not replace the unit's geometric route. I searched the whole DAG and imported blueprint for scalar-Hom/shift/thick-locus and triangle-isomorphism statements. `lem-sf-generating-class-determination` assumes shift compatibility, and the rational completed-evaluation node concerns different functors and coefficients, so neither proves this item. The ringed-site Hom calculus and the existing triangle-isomorphism node supply the generic inputs instead. There are no new-node duplicate pairs.

Step 1 uses exactly the ordinary derived change-of-rings theorem, the counit-compatible shift theorem, the ringed-topos tensor-pullback theorem and the total tensor differential. I opened all four statements and checked that the identity topos map with constant ring homomorphism satisfies their hypotheses. I read Stacks `sites-cohomology.tex` Tag 06YY (`lemma-derived-base-change`) and Tag 07A4 (`lemma-pullback-tensor-product`), and `derived.tex` Tags 05SU (`lemma-derived-shift`) and 05SE (`proposition-derived-functor`). The canonical tensor map balances coefficients by `(x tensor b) tensor (y tensor c) -> (x tensor y) tensor bc`, preserving degrees and signs; `B` need not be flat.

Step 2 uses the statement of `lem-weil-pbc-ringed-internal-hom-exact-restriction`: its first clause is the internal currying isomorphism, and its last clause gives triangle and shift behavior with no boundedness hypothesis. Applying `lem-pur-rhom-global-sections` to that isomorphism gives the displayed natural tensor–Hom bijection. The chain normalization is the actual functorial complex isomorphism in `lem-sc-derived-hom-tensor-total`, evaluated on the K-injective model in `def-pur-derived-internal-hom`. I read the corresponding Stacks Tags 08JA (`lemma-section-RHom-over-U`), 08J9 (`lemma-internal-hom`) and 08JC (`lemma-RHom-triangulated`), including the source's “details omitted”. The evaluation identity defines precisely the map from the item; it is not an arbitrarily chosen natural comparison. Step 3 uses only this bijection and the tensor comparison of Step 1: both transposes are displayed, so its naturality assertion includes every derived morphism without asserting every derived map is a chain map.

Step 4 uses the actual statements of `lem-pc-kflat-resolution` and `prop-pur-kinjective-resolutions-exist` to obtain its unbounded models; their small-site hypotheses hold after the universe choice in Step 1. I checked `def-pur-derived-internal-hom` for the representative with any K-injective target and `def-pur-hom-complex` for its explicit differential. Substitution proves the first-variable shift map `f -> (-1)^a f`. The total tensor differential from `def-pc-tensor-complex-sheaves` proves that the expressly defined simultaneous-shift cancellation has the same sign. The model `T[-1] -> Hom(P[1],I)` is obtained from a flat-term K-flat resolution of `Hom(P,I)`; thus both factors in the evaluation tensor are K-flat. `lem-weil-pbc-site-derived-tensor-descent` explicitly supplies the representative isomorphisms and descent, so this step does not assume Hom itself is K-flat. I checked the two differential coefficients and the evaluation on a homogeneous tensor. This is a direct calculation, not an uncited standard identification.

Step 5 writes both transposes of the desired shift square. Substituting Step 4's equality and Step 1's degree-preserving balance identifies those expressions. Injectivity of the bijection from Step 2 proves the square for this `v`, and iteration/inversion proves integer shifts. Step 6 writes the last arrow using `w[-1]` and retains the common reversal sign. Naturality and the shift square give the displayed three-term equality, exactly the last-square convention in `def-weil-triangulated-category`. Hence the connecting square is checked rather than inferred solely from naturality or exactness of the object functors.

Step 7 checks zero, conjugation by isomorphisms and all shifts directly. Step 8 applies precisely `lem-sf-triangle-morphism-iso` (Stacks `derived.tex`, Tag 014A, `lemma-third-isomorphism-triangle`), whose statement permits arbitrary pre-triangulated categories and any two isomorphic components. Step 6 has supplied all its hypotheses. Step 9's inverse is `Phi(i) v_L^{-1} Psi(r)`, which has domain `Psi(K)` and codomain `Phi(K)`. The two inverse equations use contravariant naturality and `r i = 1_K`. The biproduct calculation is additive matrix algebra. No ambient splitting of arbitrary idempotents is assumed.

I tested the zero scheme/zero categories, `K=0`, `M=0`, identity coefficient change, the zero coefficient ring, and the nonflat map `Z -> Z/2` on a point (including the two-term K-flat resolution of `Z/2`). None of the representative arguments replaces derived tensor by underived tensor on a nonflat complex. In characteristic two the signs become equal to one and all equations still hold. Shift and retract closure use no finite generation or finite cohomological amplitude. Every cited node's statement is quoted verbatim in `citations.json`. No step exceeds 2000 characters, and I checked the signed calculation and transposition arguments for hidden subclaims anyway. The initial dry-run citation failures were repaired before the final dry run.
