# Stage-1 delivery: lem-per-algebraic-local-duality

## Files written

All node paths are under `dag/nodes/sec-deligne-laumon-a1/` in this sandbox.

- `lem-per-algebraic-local-duality.json`: item, statement, split into six steps; original statement and statement dependencies retained. Its inherited five Mathlib search results were read and retained.
- `lem-per-algebraic-dualizing-torsion-hull.json`: new statement, unsplit; no Mathlib match. Local torsion of a normalized dualizing complex realizes a residue-field injective hull.
- `lem-per-algebraic-completion-rhom.json`: new statement, unsplit; no Mathlib match. Generic internal derived Hom and completion comparison, with no dualizing complex hypothesis.
- `lem-per-algebraic-torsion-completion-hom.json`: new statement, unsplit; no Mathlib match. Generic internal Hom comparison under torsion-completion, with no dualizing complex hypothesis.
- Removed the earlier never-delivered `lem-per-algebraic-coherent-completion.json`: the current DAG now supplies `lem-per-derived-completion-finite-cohomology`. Its original searches remain in `searches.jsonl` and its original construction in the saved scratch script.

Also wrote `citations.json` (17 verbatim quotations), `searches.jsonl` (20 searches logged by msearch), and this report. `write_split.py` is sandbox scratch work, not a project file or part of the delivery. Three new nodes, zero Mathlib leaves. No unit record is changed because this auxiliary item is not the key statement of its unit.

## Attachments

None. Searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, the blueprint tag, algebraic local duality, local cohomology, Matlis, injective hulls, dualizing terminology, and completion/Hom terminology. The completion files in `CategoryTheory/DerivedCategory/Complete` concern completeness criteria, integral coefficients, and rationalization, not these two-variable internal Hom comparisons. No project declaration states the item or any of the three retained new statements. The upstream master checkout was not treated as finished evidence.

## WANTED

None: the Stacks sources used are present locally.

## Findings and changes

The imported item had a correct, fully specified completed-Ext statement and no proof. I did not remove the completion or assume the ring complete. Stacks `dualizing.tex`, `lemma-special-case-local-duality` (0AAK), treats all coherent complexes; the item is its finite-module specialization. Its proof invokes the full derived local duality theorem, so I read that proof too and exposed its actual structural inputs instead of creating one node restating the whole local-duality theorem.

The three retained new statements are distinct ingredients: a particular dualizing object's local torsion and two general comparisons independent of any dualizing object. The finite-cohomology completion theorem is now cited from the current DAG. Hull uniqueness is written inside Step 1 from injectivity and essentiality, rather than turned into another node. The exactness/cohomology calculation for Hom into the hull is written inside Step 5, rather than left as an uncited standard assertion or moved into another node.

I used the existing `lem-trf-coherent-rhom-finite-injective-dimension` rather than creating another coherent-RHom theorem. This and the existing bounded-below-injectives/K-injective theorem are declared generic tool uses in `split_report.tool_uses`. The source's dualizing-coherent theorem is not used to claim boundedness that it does not provide. Likewise the existing extended Cech node is cited for the actual complex it defines; its module-only local-cohomology theorem is not misused as an unbounded-complex comparison.

The Cech realization of completion is defined explicitly as RHom from the already defined extended Cech complex, in each new statement that uses it. These statements do not claim that ordinary termwise completion computes derived completion for arbitrary complexes. Stacks 091V identifies this precise model with the derived-completion functor used in 0A6E, 0A6Y and 0A06. In the torsion-completion comparison and the normalized-hull statement, 0955(3) supplies the Noetherian identification between closed-support and derived ideal-torsion cohomology. The new statements cite the K-injective definition for their unbounded right-derived functors, on the one-object ringed site.

## Not duplicates

The earlier whole-DAG searches by tags 0A82, 0A6E, 0A6Y, 0A06 and keywords for Matlis duality, injective hulls, normalized algebraic dualizing complexes, derived completion and derived Hom were retained. On resumption, the dry run found the newly present `lem-per-derived-completion-finite-cohomology`; I removed the overlapping helper and reused it. The remaining three new results still have no existing match. `tools/blueprint_refs.py search` was run for local duality, injective hull, torsion complete, dualizing complex, completion RHom, coherent derived Hom, Matlis, internal Hom comparison, and the four main Stacks tags. No blueprint node states the three retained new facts. The new nodes' ancestor is `lem-per-artin-gabber-affine-curve`, with the item prepended to the inherited via chain and the exact algebraic input added to from.place.

The shared-source-tag comparisons are:

lem-per-algebraic-dualizing-torsion-hull vs lem-per-local-cohomology-flat-base-change: the latter is a tensor/base-change formula for a module; it makes no assertion about local torsion of a normalized dualizing complex or a residue-field injective hull. Both use 0955 for the torsion/support model.

lem-per-algebraic-dualizing-torsion-hull vs lem-per-local-cohomology-cech-bound: the latter identifies module local cohomology with the extended localization complex; it does not identify the local torsion of a dualizing complex with an injective hull.

lem-per-algebraic-dualizing-torsion-hull vs lem-per-local-cohomology-sum-spectral: the latter is a first-quadrant spectral sequence for sums of ideals on modules, not a dualizing-complex concentration or injectivity statement.

lem-per-algebraic-dualizing-torsion-hull vs lem-per-algebraic-local-duality: the new node identifies one dualizing complex's torsion and supplies a hull; the item instead identifies completed Ext of every finite module with the dual of its local cohomology. The item still needs both generic comparisons, finite-generation and completion-cohomology inputs, and the explicit injective Hom calculation.

lem-per-algebraic-torsion-completion-hom vs lem-per-local-cohomology-flat-base-change: the new node compares internal Hom of two completed complexes with internal Hom of their local torsion; the existing node compares module local cohomology with tensor after a flat ring map.

lem-per-algebraic-torsion-completion-hom vs lem-per-local-cohomology-cech-bound: the existing module Cech computation does not assert the two-variable derived internal Hom comparison, even for a single fixed ring.

lem-per-algebraic-torsion-completion-hom vs lem-per-local-cohomology-sum-spectral: the existing spectral sequence concerns iterated torsion of modules for two ideals, rather than internal Hom and completion for two arbitrary complexes and one ideal.

lem-per-algebraic-torsion-completion-hom vs lem-per-algebraic-local-duality: the generic new comparison has no normalized dualizing complex or injective hull, no finiteness of K or L, and no formula about ordinary completed Ext; Step 3 must combine it with the other inputs.

lem-per-algebraic-completion-rhom vs lem-per-algebraic-torsion-completion-hom: both cite 091V to specify completion, but the first moves completion inside derived Hom whereas the second compares complete and torsion objects; neither supplies the other's assertion.

lem-per-algebraic-dualizing-torsion-hull vs lem-per-affine-support-cech-localization: the existing node identifies derived ideal torsion with affine supported sections and a localization tensor complex for arbitrary input; it never asserts that the torsion of a normalized dualizing complex is concentrated in degree zero and is a residue-field injective hull.

lem-per-algebraic-torsion-completion-hom vs lem-per-affine-support-cech-localization: the existing node computes torsion and localization triangles, whereas the new node identifies the internal derived Hom between two completed objects with internal derived Hom between their torsions; no such two-variable Hom comparison is in the existing statement.

The removed lem-per-algebraic-coherent-completion vs lem-per-derived-completion-finite-cohomology: these are the same finite-cohomology completion result after identifying their models. It is a duplicate and is not delivered. The saved search log is retained intact.

## What remains unfinished

No part of the item's one-level split is omitted. The three new nodes deliberately remain statement-only and unsplit, as the brief requires. No Lean was written or compiled; no shared repository or launcher file was edited, and no git command was run in the shared repository.

## Review by Q104

I read Stacks `dualizing.tex` at `lemma-special-case-local-duality` (0AAK), `theorem-local-duality`, `lemma-local-cohomology-of-dualizing` (0A82), `lemma-injective-hull-unique` (08Y4), `lemma-local-cohomology-noetherian` (0955), and `lemma-compare-RHom` (0A6Y). I read `more-algebra.tex` at `lemma-completion-RHom` (0A6E), `lemma-derived-completion` (091V), and `lemma-derived-completion-pseudo-coherent` (0A06). These are the sources for the item and respectively the new hull, two generic Hom-comparison nodes; the coherent-completion theorem is reused from the current DAG. The local normalization is exactly RHom from the residue field equal to that field in degree zero, so there is no omitted dimension shift.

For Step 1 I opened the new hull statement: it gives both an actual embedding of the residue field in E0 and the derived isomorphism, not just an unspecified injective module. I checked that the arbitrary E in the item is reached by extending the fixed residue-field embeddings. Essentiality kills ker(u) and ker(v), and the written splitting shows surjectivity. This proves the item for every hull, not only the one constructed from omega. The injection definition node states precisely the extension property used twice.

For Step 2 I opened `def-per-algebraic-normalized-dualizing` and `lem-trf-coherent-rhom-finite-injective-dimension`. The former really gives finite cohomology and a bounded injective representative; the latter really asserts finite cohomology of RHom for arbitrary coherent input K, and its ring is Noetherian. K=M[0] meets every hypothesis because M is finitely generated; no finite projective dimension of M is assumed.

For Step 3 I read the Noetherian definition (every ideal finitely generated) and the extended Cech statement, which explicitly defines the actual alternating complex C. I then read the two new comparison formulas: the first gives precisely Lambda(RHom(K,L)) versus RHom(Lambda K,Lambda L), and the second precisely the same middle object versus RHom of the two derived ideal torsions. Both use the same fixed generating list and completion model. They require only the stated Noetherian ring, not completeness, a regular sequence, perfection or boundedness. `def-pur-derived-internal-hom` explicitly supplies its functor and its action on isomorphisms; this is all the last substitution uses. The hidden support-versus-ideal comparison is included in the new theorem's statement and its 0955 source, rather than attributed to a Cech definition that does not state it.

For Step 4 I opened the newly available `lem-per-derived-completion-finite-cohomology`: it allows all integers and unbounded complexes, but uses a quotient-tower model, so a bare substitution would not suffice. I opened `lem-weil-pbc-extended-cech-completion-model`, whose statement makes the RHom model a reflector, and the final paragraph of `lem-weil-pbc-constant-completion-equivalence`, which gives exactly the same reflection condition and quotient-tower unit on any small site over a Noetherian ring. The one-object identity-cover site has module category exactly A-modules and meets their hypotheses. I read algebraization.tex 099F and 0A0E and proetale.tex 099M to check this use. The written unit-preserving maps u and v are inverse by uniqueness, a routine two-line universal-property argument. I also opened `lem-weil-pbc-ringed-strict-tower-homotopy-limit`: its product-fibre triangle aligns total derived inverse limit with the finite-cohomology node's model. These three generic tools are declared in split_report.tool_uses. No additional finite quotient, torsion coefficient, regularity or completeness hypothesis is imposed. Step 2 supplies exactly the finite cohomology needed by the existing theorem; degree -i gives the stated ordinary completion.

For Step 5 I opened the ideal-torsion definition, the bounded-below-injectives/K-injective theorem, the derived internal Hom definition and the injective extension definition. The torsion node computes the module-derived functors by injective resolutions, as used here. E[0] is bounded below with injective terms, so the K-injective theorem applies. The Hom differential gives the written cycles, and injective extension gives both surjectivity of restriction to cycles modulo boundaries and its kernel equal to the boundaries of the Hom complex. I checked the degree reversal and sign explicitly; nothing is inferred from injectivity in the first variable. Step 6 just composes these already obtained linear isomorphisms. All seventeen step/node pairs have verbatim quotes in citations.json.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the files. No new node contains proof text or proof dependencies; all introduce their own rings, modules, ideals and complexes, with definition dependencies or explicit formulas. Every source uses the correct tag and literal .tex label. The searches are the exact twenty queries in searches.jsonl, five per original helper (fifteen belonging to the three retained new nodes, five for the removed candidate), and their actual returned declarations were read. Both semantic phrasings were tried before concluding no match. In particular, Mathlib's local-cohomology file explicitly lists the derived-functor and Cech comparisons as future work; ordinary completion exactness is not the unbounded derived result needed here. No match is claimed and no unavailable service is recorded as a negative result.

For small cases I checked a field (m=0, C=A[0], omega=k[0], E=k, ordinary finite-dimensional duality in degree zero and both sides zero in higher degrees); Artinian local rings (torsion is the identity and omega is its injective hull in degree zero); the noncomplete DVR k[t]_(t) with normalized omega=A[1] (M=A and i=1 require completed A, not A); M=0; and M=k over a DVR (the degree-zero formula has the residue field on each side, verifying the negative-degree shift). For the generic comparison nodes I checked I=0, r=0, I=A, and a generating list containing a unit: these give identity or zero completion and torsion consistently. The finite-cohomology condition in 0A06 is retained; no arbitrary-module exactness of ordinary completion is asserted. No statement dispute arose. Every proof step is below 2,000 characters and the two elementary arguments are written in full, with no hidden standard comparison or compatibility lemma. The earlier corrections during self-review were explicitly declaring the K-injective notion in the two new unbounded-torsion statements and spelling out the model of derived completion to avoid conflating it with ordinary completion.


On resumption I ran the dry run before edits. It returned three duplicate-tag diagnostics: one real overlap and two distinct uses of 0955. I removed the real duplicate rather than defending a different model as a different theorem, wrote the model comparison in Step 4 using existing nodes, added the two explicit nonduplicate comparisons above, and updated all citation quotes and counts. I compared the saved item with the current repository: its statement, source, statement dependencies, creation metadata and blueprint provenance still agree; only its authorized split fields differ. The original proof, citations and logged searches were retained except where the duplicate repair required updating them. The repaired Step 4 is under 2,000 characters and its only inline subargument is uniqueness of a reflector; the non-elementary model identifications are all cited.
