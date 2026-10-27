# Stage-1 report: lem-trf-space-chart-adjunction-tensor-realization

## Files written

- dag/nodes/sec-trace-formula/lem-trf-space-chart-adjunction-tensor-realization.json: existing statement split into eight steps; not a Mathlib match as a whole.
- citations.json: one verbatim statement quotation for every citation of every proof step.
- searches.jsonl: six newly executed Mathlib searches; their results were read and appended to the existing item search history.

No new DAG nodes and no new Mathlib leaves. The existing statement and its statement dependencies are unchanged. All writes are confined to this item's sandbox.

## Attachments

None. Searches for the exact blueprint tag and chart/tensor notions in lean/WeilConjectures found scheme, abelian-chart and open-cover declarations, but no declaration asserting this item for arbitrary algebraic spaces with its specified all-chart direct images. Mathlib's generic uniqueness result is already the leaf lem-weil-pbc-conjugate-iso-unit-equation. It is cited rather than recreated.

## WANTED

None. All source passages used are in literature/stacks-project. The current blueprint was read through literature/blueprint/latest (main-20261023-1620), including the chapter, unit and nearest imported ancestor. No older blueprint snapshot was used for the proof.

## Problems found and corrected

The item was statement-only, not previously split in this sandbox. Its statement correctly distinguishes local tensor representatives from arbitrary sections. I preserved that distinction. In particular the proof does not use a global pure-tensor description or assert that evaluating a sheaf tensor equals tensoring its section modules. The proof makes the tensor adjunction unit explicit rather than assuming that an abstract left-adjoint isomorphism respects chart units. I expanded Stacks 03D8's “clear from definitions” into actual balancing and inverse calculations. The original source place and imported metadata are preserved.

The generic tensor adjunction node states the natural Hom bijection but its statement does not spell out the unit. Step 2 therefore derives the unit from the separately cited normalized geometric-module Hom bijection, scalar-extension Hom bijection, and the sheafification universal property. It does not use an unstated formula from that node's proof. Similarly, the pro-etale scheme tensor-composition lemma is not cited for algebraic spaces: the argument uses generic inverse-image tensor and generator theorems with the enlarged-space model and writes the scalar calculation itself.

## What remains unfinished

Nothing in this one-level split. Its cited existing unsplit or not-yet-formalized nodes remain their own items. No Lean files were written and no compiler, Lake or build command was run.

## Review by Q113

I read Stacks sites-modules.tex lemma-adjoint-pullback-pushforward-modules (03D7), its ingredients lemma-adjoint-push-pull-modules (03D3) and lemma-adjointness-tensor-restrict (03CZ), the sectionwise tensor and sheafification definitions, lemma-push-pull-composition-modules (03D8), and lemma-tensor-product-pullback (03EL). For the geometric input I read spaces-properties.tex lemma-morphism-ringed-topoi (03G8), lemma-etale-exact-pullback (03LV) and equation-restrict-modules (03LW). For uniqueness I read categories.tex lemma-transformation-between-functors-and-adjoints (0B65). The proof is marked agent-written because the all-chart normalization expands those passages rather than copying a source proof of this exact statement. No SGA route is used.

Step 1 uses the enlarged model's actual equivalence of module sheaves and compatible ringed morphisms, the arbitrary-ringed-topos module adjunction, and the chart-limit comparison's explicit projection-preserving isomorphism. Each cited statement was opened. I checked that no representability, flatness, quasi-compactness or etale hypothesis on f or k is inserted, and that site smallness is relative to the module universe as the item assumes. The comparison is of functors with the same scalar actions, not only of sets of sections.

Step 2 uses the geometric-module transport statement's explicit underlying-mate equation; the scalar-extension Hom statement's formula psi mapped to m mapped to psi(1 tensor m); and the tensor definition and module-sheafification universal property. Together they determine the actual tensor unit by evaluating the identity. The chart-limit node states that projections are restrictions from the enlarged fibre-product object, which is exactly what the projection computation needs. No claim is inferred solely from a definition of flatness or another irrelevant property.

Step 3 uses the existing Mathlib uniqueness leaf, with its orientation checked: R1=D, R2=Q and delta=alpha inverse. Naturality of alpha gives the item's equation with Q(tau), alpha at P(M), and eta. The uniqueness follows in the reverse direction from that same equation.

Step 4 cites the definition of chart projections and unit-defined tensors, the natural chart-cone comparison, and the sheaf tensor definition. Projecting the previous equation and multiplying by b gives the exact requested formula. I explicitly checked chart restriction b mapped by r-sharp and module naturality m mapped by phi, rather than saying only “the comparisons transport”.

Step 5 uses the enlarged model and its ringed-composition/localization theorem for the composite coefficient map, the generic algebraic inverse-image tensor theorem for the middle tensor, and the site inverse-image composition-generators theorem for nested section representatives. The latter applies to continuous base-change site functors whose precomposition gives sheaf direct image; this is part of the enlarged model. The algebraic module lift is the actual inverse image with operations transported by its finite-product comparisons. Enlarged-site module equivalences allow the calculation before return to the small scheme sites. Each cited node states the part used, including the pure-tensor normalization. I checked that these dependencies do not reach the item and hence do not close a cycle.

Step 6 proves the scalar association maps, rather than citing a new node that merely restates composition. I checked the intermediate B relation and the original R relation separately, then the two inverse identities. The inner and outer sheafification universal properties are applied successively; evaluation need not commute with tensor. This is a routine balanced-map argument from the tensor and sheafification definitions, so it is elementary and not a new node.

Step 7 gives the actual four-factor conjugation defining the comparison of P functors. The existing composite-adjunction leaf says exactly that its unit is the first unit followed by the right image of the second. On the displayed local generators this is 1 tensor (1 tensor m), and multiplication gives 1 tensor m. The uniqueness leaf therefore fixes the canonical compositor. The calculation also covers identities.

Step 8 uses the enlarged model's etale localization and its identification of the restricted structure ring, the localized-site definition's sectionwise restriction, and tensor/sheafification. The inverse and multiplication formulas are proved by balancing before sheafification. Scheme objects carry the same regular-function rings, including operations and restrictions; no surjectivity of the etale morphism is required.

I tested the formulas on identity morphisms, an etale map with several components, the empty source, zero modules, zero scalars and non-flat coefficient maps. Identities give the usual unitors; zero/empty cases give the unique maps; balancing uses no flatness. I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the actual files. There are no new nodes to duplicate or restate clauses, no newly introduced notions, and no non-elementary step longer than 2000 characters. Off-unit generic tool uses are declared in split_report.tool_uses, not in a maintainer-owned tool_uses field. Verbatim full-statement citations retain the hypotheses of every cited theorem.

## Mathlib searches read

Both semantic phrasings, Loogle and source grep were run through msearch.py and are in searches.jsonl. I inspected Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean, especially pullbackPushforwardAdjunction and PullbackConstruction.adjunction (lines 55 and 81), pullbackComp and its mate equation (lines 167 and 177). Those are abstract adjoints for continuous site functors, not the specified tensor/chart realization on algebraic spaces. The uniqueness hits are reused through the existing Mathlib leaf. None covers every clause of the item. All searches that returned hits were recorded as successful searches with a no-match verdict for the complete item, not as unavailable.
