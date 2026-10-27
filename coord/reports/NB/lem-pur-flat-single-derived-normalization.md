# Worker report: lem-pur-flat-single-derived-normalization

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-flat-single-derived-normalization.json`: statement node, now split into eight steps. Statement unchanged; no full Mathlib match.
- `citations.json`: 17 entries, one for every step/node citation, quoting the cited statement verbatim with its hypotheses.
- `searches.jsonl`: the five searches actually run with msearch.py for this item, supplementing the inherited searches in the node.
- `report.md`: this report and direct-delivery review.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this item is not the statement of sk-prop-an.

## Attachments

None. Searched project Lean by the exact blueprint tag and by flat/single/termwise/derived concepts. In particular `CochainComplex.kFlat_single_obj_iff_flat` in `WeilConjectures/FromJoel/CategoryTheory/Abelian/Flat/KFlat.lean:243` covers K-flatness only. `DerivedCategory.QObjTensorSingleFunctorObjIso` in `WeilConjectures/CategoryTheory/DerivedCategory/FlatModel.lean:202` assumes the varying complex P is K-flat; that is explicitly not an assumption of this item. `mapHomologicalComplexTensorRightIso` in `TorAmplitudeMapDerivedCategory.lean:74` concerns an exact monoidal functor applied to termwise tensor. None states the complete normalized, shift-compatible flat-sheaf comparison here. No partial result is submitted as an attachment.

## WANTED

None. The local Stacks sources and current blueprint contain the required arguments.

## Findings and corrections

The item had a statement and searches but no proof. Its seeded dependencies already contain the substantive general tools. I retained its statement, source, blueprint provenance, inherited searches and other metadata, and supplied the argument rather than moving its clauses into new lemmas. The current blueprint source is `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/sk-def-sp-tate-twist-locally-free.proof.md`, proof (3), ending with flatness and termwise derived tensor. This item provides just that generic flat-sheaf argument for its parent `lem-pur-line-unbounded-derived-tensor`; invertibility is not needed here.

I checked the chapter and unit records and the three blueprint levels in SETUP. This is a generic algebra tool supporting the Tate-twist calculation, with no change to affine-space purity or its route. The additional localization tool and explicit integer-shift leaf are existing nodes. Generic tool uses are declared in split_report; no maintainer-owned tool_uses field is set.

A source-reference typo in the existing definition node `def-weil-triangulated-category` identifies Tag 05QL with the definition of an exact functor. The local tag map identifies 05QL as `derived-equation-rotate`; the definition actually used here is Tag 014V, `derived-definition-exact-functor-triangulated-categories`, followed by the paragraph on natural transformations. I used the correct reference in proof step 7 and did not edit that other node. This does not alter the statement.

The inherited brief mentions `coord/dag-sync.md`, which is absent in this read clone; the current user brief and specified read-only source paths were followed.

## Searches and reuse

Whole-DAG keyword/tag searches included flat degree-zero, fixed tensor, exact-functor-derived, 06YU, 015F and 010N. Whole-blueprint searches with `tools/blueprint_refs.py search` included `flat degree-zero`, `normalized flat degree-zero`, `derived tensor by a flat`, `termwise` and `K-flat`; the ancestor command confirms `det-def-sp-tate-twist-locally-free`. No blueprint node states this full normalization in another form, so same_as remains empty. The hits with generic exact-functor content are already the cited nodes. No node is created, so there are no new/existing same-tag pairs requiring a Not duplicates entry.

All five new Mathlib query texts are recorded exactly from searches.jsonl. LeanFinder was run with two different phrasings; LeanSearch and Loogle also worked. Semantic searches returned ordinary module-flatness declarations, Tor and total-complex infrastructure. I read `Mathlib/RingTheory/Flat/CategoryTheory.lean:41-65`: these declarations concern ModuleCat over one ring, not sheaves on an arbitrary ringed site or the normalized unbounded comparison. Loogle returned `CategoryTheory.Functor.mapDerivedCategory` and its factorization/shift/triangulated API; I read `Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:36-105`. Those support the existing Mathlib leaf `lem-weil-pbc-exact-functor-derived-factorization`, not the complete item. The grep query found only four unrelated Finsupp tensor formulas in RepresentationTheory/Equiv.lean. The integer tensor-shift leaf was checked at `Mathlib/Algebra/Homology/BifunctorShift.lean:95-110`, confirming the unsigned first-factor convention. No search that failed was recorded as no match, and no unrun query was added.

## Review by NB

I read Stacks `sites-cohomology.tex`, Tag 06YN (`definition-K-flat`), the construction immediately preceding Tag 06YU (`definition-derived-tor`), and the fixed-factor quasi-isomorphism argument preceding it. They allow arbitrary unbounded varying complexes; a flat-term K-flat fixed factor is sufficient. I also read `sites-modules.tex` Tag 03ER (`definition-flat`, item (3)), where flatness is exactness of tensor on sheaves, and the tensor/Hom discussion at 03EK/03EO. I read `derived.tex` Tag 015F (`lemma-right-derived-exact-functor`), which explicitly says every complex computes the derived functor of an exact functor, and `homology.tex` Tag 010N (`lemma-exact-functor`). These agree with all hypotheses of the unchanged item: a module-universe-small site, a commutative ring sheaf, and a flat sheaf L; neither constructibility nor invertibility occurs. No new node requires a separate source check.

For step 1 I opened `def-weil-sheaf-of-modules-category`, `def-pc-flat-sheaf-modules`, and `lem-pc-sheaf-modules-tensor-closed`. Their statements respectively give the abelian module-sheaf category under exactly our size condition, exactness of tensor by L as the definition of flatness, and additivity in both variables. Thus the use of the flatness definition here is legitimate: I do not silently derive any acyclicity theorem from it. The zero-object argument is written out and is elementary.

Step 2 uses the actual statement of `def-pc-tensor-complex-sheaves`: direct-sum terms and differential with the sign on the second differential. Since that differential is zero for L[0], projection/inclusion of the single surviving summand are inverse chain maps; the maps on a chain morphism are explicitly f^r tensor 1. This is a calculation from the definition, not a new normalization lemma. Even an unbounded C has only one surviving summand per degree.

Step 3 cites the statement of `lem-weil-pbc-exact-functor-complex-cohomology`, not merely a definition of flatness: it supplies the comparison induced on cycles and boundaries for any exact additive functor between abelian categories. Applied to the exact T_L from step 1, it proves acyclicity after tensoring; `def-pc-kflat-complex` then supplies precisely the quantifier over all acyclic complexes needed to conclude K-flatness. Flat terms follow from L in degree zero and the proved flatness of zero, without assuming C has flat terms.

For step 4 I read `lem-weil-pbc-exact-functor-derived-factorization` in full. It states preservation of quasi-isomorphisms, an exact derived functor, the factorization phi on every complex and its compatibility with all integer shifts. No resolving or boundedness assumption has been smuggled into this application.

For step 5 I opened `lem-weil-pbc-kflat-fixed-tensor-triangulated` and `lem-weil-pbc-localization-universal-property`. The former expressly gives right tensor by a fixed flat-term K-flat factor on arbitrary complexes, canonically identified with the specified derived tensor; step 3 verifies both of its fixed-factor hypotheses for L[0]. The latter states existence, uniqueness and invertibility for transformations descending through the localization. I use exactly those clauses to extend phi inverse composed with Q(theta) composed with chi. That displayed formula fixes the comparison on every representative, rather than asserting the existence of an unrelated isomorphism. No node's proof is being used for information absent from its statement.

For step 6 I also opened `lem-weil-pbc-total-tensor-integer-shifts`: the first-factor map is unsigned for every integer. Since C is the first factor, its unsigned comparison and the degreewise identity for T_L have the same components and differential (-1)^n(d_C tensor 1). This proves the square on complexes. The fixed-factor and exact-functor statements explicitly describe their localized shift structures, and faithfulness of restriction in the localization node proves equality on D(R). I checked negative as well as positive n: the parity formula is unchanged. This avoids an unjustified claim that an arbitrary natural isomorphism of exact functors automatically respects their shift constraints.

Step 7 uses only naturality of the constructed eta at w:Z to X[1] and the shift square just proved. I checked the definition node's exact-functor clause and the correct Stacks definition 014V: their connecting map is the composite with the functor's specified shift comparison. Composing the two squares proves precisely compatibility with that third arrow, not only with the first two arrows of the triangle.

For step 8 the cohomology node states the required cycle-and-boundary normalization and naturality on complexes. `def-weil-abstract-derived-category` states that H^i factors through Q; the localization node then extends the comparison and its inverse uniquely. This gives naturality for all derived morphisms, not merely chain maps. Its value on QC is the formula used to define the family, so the required representative normalization is preserved.

I tested L=0, the zero complex, a complex concentrated in an arbitrary degree, n=0 and n=-1, and a complex unbounded in both directions. In the first case both tensor functors are zero and all maps are the unique maps of zero objects; no nonzero-rank assumption is used. For a single complex in degree j the surviving summand is exactly (j,0); the n=-1 test changes the differential by -1 on both sides. No infinite-product totalization or convergence assertion is used. These checks expose no statement error, so STATEMENT-DISPUTED is not needed. Every proof step is below 2000 characters; the substantive descent and cohomology facts are existing cited nodes, and the remaining short calculations are explicit. B--E review found no new unsplit node, duplicate, clause relabeling, cycle-producing dependency, or uncited substantive lemma.

## Unfinished work

None in the one-level split. Existing dependencies retain their own stage states. Required dry run and push follow this review.
