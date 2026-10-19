# Q16: lem-trf-ind-etale-local-henselian-integral

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-ind-etale-local-henselian-integral.json`: statement node, now split into seven steps; no Mathlib match for the whole theorem.
- `citations.json`: one exact statement quotation for each node cited by each proof step.
- `searches.jsonl`: actual msearch results for the item, retained with their query text.

No new nodes, no new Mathlib leaves, and no unit changes. The sandbox was empty of node files and reports at the start; the current unsplit repository item was copied before editing. The imported statement, source, ancestry, and its four prior Mathlib search records are retained. Four searches run during this work were appended.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id/docstring tag and for ind-etale, henselization, henselian and integral found no declaration stating this result. The relevant existing IndEtale and QuasiFinite files provide other properties, not this ordinary-henselization integrality theorem. No upstream sorry declaration is used as evidence of a finished proof.

## WANTED

WANTED: archive Hübner–Schmidt, *The tame site of a scheme*, https://www.mathi.uni-heidelberg.de/~schmidt/papers/algebraic_tame_site.pdf, printed p. 13, sentence between Theorems 6.3 and 6.4, for lem-trf-ind-etale-local-henselian-integral. The PDF was read online, including the preceding theorem's henselization convention and the following ind-etale statement; it is not present under the repository literature paths searched. No literature file was downloaded or written. The expanded proof is marked `proof_origin.by = agent` and uses the available Stacks source.

## Corrections and route

The item is true as written; there is no STATEMENT-DISPUTED correction. The paper asserts the integrality reduction without expanding its proof. Its prime is made precise by the item's existing contraction formula, and ordinary henselization remains ordinary henselization throughout. No Noetherian, injective-transition, finite-residue-field, or strictly henselian hypothesis was added.

The chapter `sec-trace-formula` and unit `sk-i-curve-zero` were read, together with the current main-20261015 blueprint locality node. This item is an auxiliary commutative-algebra input along the existing normal-cone/nearby-cycle/Artin-join ancestry, not a replacement of the unit's contracting-local-term argument. The existing blueprint.from place already describes that role and was retained; the whole-blueprint searches for henselian, ind-etale and integral over yielded no statement duplicate, so same_as remains empty. No SGA source is used.

Two off-unit statements are declared in split_report.tool_uses: etale maps are quasi-finite, and henselian finite-type algebras have a finite local product part. These are generic ring-theoretic tools below the specified unit route. The other statement inputs are existing Mathlib leaves.

## Not duplicates

There are no newly created nodes. In particular I reused `lem-weil-pbc-henselian-finite-type-product-decomposition` (04GJ), rather than creating an etale special case or another node restating the conclusion. DAG searches by the relevant henselian tags and statement keywords also found the existing etale base-change, quasi-finiteness, finite-algebra-integrality and filtered-colimit-representative nodes. Their statements were opened and checked before use. No separate nodes were made for local idempotent selection or the elementary localization at a coordinate idempotent.

## Review by Q16

I read delivery-errors B–E in full and reviewed the written proof against the actual cited statements, not their titles. For the item I read the online Hübner–Schmidt PDF, printed p. 13. For the inputs I read algebra.tex: 00U2 (lemma-etale, in this version its base-change clause is (3)), 00U5 (lemma-etale-quasi-finite), 04GJ (lemma-mop-up), 00GK (lemma-finite-is-integral), the henselization construction and functoriality around 04GN/04GQ, and the colimit discussion. I also opened the localization, ind-etale, henselian, quasi-finite-at-prime and algebra-colimit DAG statements. There are no new statements whose source needs a separate review.

1. Step 1 uses `def-weil-pbc-localization-at-prime` for fractions and the local maximal ideal, and `def-weil-pbc-henselian-terminology` for the local hypotheses. The fraction formula extends f because precisely the elements outside the contracted prime map to units. Its maximal-ideal inverse image is checked explicitly. H is already defined by its initial local-map property in the item's statement, so applying that defining property gives the canonical local h; no independent theorem about a different construction of H is being smuggled in. This step does not assert that H maps injectively into D.
2. Step 2 uses `def-weil-pbc-ind-etale-algebra` for a filtered presentation by etale A-algebras, and `lem-weil-pbc-filtered-colimit-algebras-elementwise`, whose clause (2) explicitly gives an element representative in the category of commutative A-algebras. It is not the special residue-triple presentation theorem. The chosen diagram is small in the universe used for its colimit, and no elementwise surjectivity of an individual transition map is required.
3. Step 3 uses `lem-weil-pbc-etale-ring-base-change` with R=A, its A-algebra replaced by E_i, and S=H. Its conclusion is exactly the etaleness of H to H tensor_A E_i. `lem-weil-pbc-etale-ring-map-quasi-finite` supplies both finite type and quasi-finiteness at every prime. The map g is given on pure tensors, with balancing supplied by h eta=f; the image of 1 tensor e is checked explicitly.
4. Step 4 uses the entire statement of `lem-weil-pbc-henselian-finite-type-product-decomposition`. Its H-henselian hypothesis holds by the meaning of H in the item, and its finite-type hypothesis was established in step 3. The node gives finite *modules* F_j and a residual factor with no quasi-finite closed-fibre primes, precisely the two properties later used. I do not claim here that the finite factors are etale or invoke an unstated equivalence of finite-etale categories.
5. Step 5 needs no further theorem: in a local ring an idempotent and its complement cannot both be nonunits; their product is zero. Applying this to the finitely many coordinate idempotents proves there is exactly one selected factor and gives the actual factor map z to g(e_*z). This includes n=0, where the residual factor would have to be selected, and excludes selecting a zero factor because its idempotent is zero.
6. Step 6 cites `def-weil-pbc-ring-map-quasi-finite-at-prime`, which really defines quasi-finiteness by an isolated point of the fibre spectrum. If the residual factor were selected, its contracted prime lies over the closed point of H because h is local. In the fibre, localization at the coordinate idempotent kills the other factors and is exactly the residual fibre ring. Thus an isolated point of the full fibre stays isolated in this open part. This is a direct coordinate localization, not a general component comparison or an unproved transfer theorem. Finite type of B is also checked using the surjective product projection. The contradiction uses precisely the negative assertion in step 4. I corrected the tempting shortcut “all etale algebras over H are finite”: only the factor selected by D is forced to be finite, and the residual factor can remain nonzero away from the closed fibre.
7. Step 7 uses `lem-weil-pbc-finite-algebra-is-integral`, whose hypothesis is finiteness as an H-module and whose conclusion is an actual monic equation for each element. It applies to F_j, not to D. Applying the selected H-algebra map to that polynomial equality gives the displayed equation for d. This justifies integrality under a potentially noninjective map without a separate permanence lemma or a claim that D itself is finite.

I tested the reasoning on A a field with D an arbitrary algebraic separable extension (D can be infinite), on henselian A with D=A, and on a localization at a nonmaximal prime followed by henselization. The third case explains why one must use A_p^h rather than claim D is integral over A. I also checked product stages with an additional factor supported away from the closed point; the proof discards precisely that factor. D is nonzero because its specified maximal ideal is proper; the argument allows zero and empty finite parts in the intermediate decomposition, whose impossible selection is then excluded. Nilpotents, non-Noetherian bases and noninjective stage maps do not enter any cancellation. Every step is below 2000 characters; the two elementary product arguments are written out, and no long step hides another lemma. All citations.json quotations are copied verbatim from node statements, including their hypotheses.

Mathlib searches were actually run with msearch.py: LeanFinder's first phrasing returned standard-etale/locus/localization results; LeanSearch's second phrasing returned henselian predicates and root criteria; Loogle returned zero hits for HenselianLocalRing, Algebra.IsIntegral; grep returned no henselization or ind-etale/integral theorem. I read Henselian.lean and Etale/Basic.lean to rule out treating the root predicates or base-change instance as the whole theorem. The logged searches and old records are preserved. No Lean files were changed and no compiler or Lake command was run.

## Unfinished work

None within this one-level split. The existing cited nodes remain their own work items according to their current states; no new subnode was necessary. Server dry-run validation and direct delivery are recorded by the delivery tool.
