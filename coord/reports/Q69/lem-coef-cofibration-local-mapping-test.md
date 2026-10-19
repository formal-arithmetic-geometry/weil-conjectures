## Worker report

`Sheaf.CategoryTheory.CofibrationLocalMappingTest` states
`CategoryTheory.cofibration_local_mapping_test`, with one postponed proof and
no new definitions. The node's statement is unchanged. The theorem docstring
contains all eight proof steps and their DAG references. No repair note exists
for this item.

Hypothesis and clause correspondence:

- The model-category convention of
  `lem-coef-simplicial-model-nerve-localization` is expressed by
  `{M : Type u} [Category.{v} M] [ModelCategory M] [HasLimits M]
  [HasColimits M]` and the two `HasFunctorialFactorization` instances for
  `(cofibrations, trivialFibrations)` and `(trivialCofibrations, fibrations)`.
  Mathlib's model structure supplies the lifting, retract, factorization and
  two-out-of-three axioms; limits, colimits and functoriality retain the
  additional conventions explicitly required by that dependency.
- Simplicial enrichment, tensors/cotensors, and SM7 are exactly
  `[SimplicialCategory M]`, `_T : SimplicialTensorCotensor M`, and
  `_hSM7 : SimplicialModelLocalization.SatisfiesSM7 M`. These are the
  dependency's recorded interfaces, not private copies.
- Left properness is `_leftProper`: for a weak equivalence `w : A ⟶ B`
  and cofibration `i : A ⟶ C`, the pushout map
  `pushout.inr w i : C ⟶ pushout w i` is a weak equivalence. There are
  no cofibrancy restrictions in this quantifier.
- The class is `tests : ObjectProperty M`. `_fibrant` says every member is
  fibrant. `_closed` says that a weak equivalence between fibrant `X,Y`
  gives `tests X ↔ tests Y`, retaining closure in both directions.
- The derived mapping-space convention is expressed using
  `Q : M ⥤ M`, `_ε : Q ⟶ 𝟭 M`, and `_hQ`: each `Q.obj X` is
  cofibrant and each augmentation is a trivial fibration. These describe
  any functorial cofibrant replacement, which exists by the stipulated
  functorial weak factorization system. They are representative data for
  the node's derived-map convention, not an additional mathematical
  restriction on `M`. For a fibrant `Z`, the dependency identifies
  `sHom (Q.obj X) Z` with `Map^h(X,Z)`; `Q.map i` and naturality of the
  augmentation identify the actual precomposition map. Hence the first
  predicate, `∀ Z, tests Z → IsWeakHomotopyEquivalence
  (eHomWhiskerRight SSet (Q.map i) Z)`, is precisely `i ∈ W_tests`.
  No arbitrary derived-mapping functor is supplied. Fibrant replacement of
  `Z` is unnecessary because `_fibrant` already applies to each test.
- The tested map is `{A B : M} (i : A ⟶ B) (_hi : Cofibration i)`.
  Neither `IsCofibrant A` nor `IsCofibrant B` is assumed.
- The strict mapping map is Mathlib's
  `eHomWhiskerRight SSet i Z : sHom B Z ⟶ sHom A Z`, with the node's
  stated direction and the original objects `A,B`.
- The conclusion is an iff with
  `∀ Z, tests Z → SSet.modelCategoryQuillen.I.rlp
  (eHomWhiskerRight SSet i Z)`. `I` is the existing family of *all*
  boundary inclusions, indexed by `ℕ`, and `rlp` is the existing right
  diagonal-lifting predicate. The dimension-zero boundary is included.

Dependencies inspected and used:

- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `CategoryTheory.simplicial_model_nerve_localization`,
  `CategoryTheory.SimplicialModelLocalization.SatisfiesSM7` and its actual
  `cornerMap`, `MappingPresentation`, and `MappingFormulas`. Its
  `MappingFormulas` quantifies over exactly the replacement functors and
  augmentations used here. The tensor/cotensor interface is
  `CategoryTheory.SimplicialTensorCotensor` from
  `Sheaf.CategoryTheory.SimplicialTensorCotensor`, publicly imported by
  the recorded module.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen`. Its trivial-fibration clause
  is equality with `modelCategoryQuillen.I.rlp`. The actual definition of
  `SSet.modelCategoryQuillen.I` at
  `Mathlib/AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean`
  was read, as was `CategoryTheory.MorphismProperty.rlp` in
  `Mathlib/CategoryTheory/MorphismProperty/LiftingProperty.lean`.
- Available proof dependencies are imported nonpublicly:
  `Sheaf.AlgebraicTopology.KanFibrationFiberCriterion`
  (`SSet.Enhanced.kan_fibration_fiber_criterion`) and
  `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`
  (the lifting-class closure instances recorded by
  `lem-coef-lifting-class-closure`). The proof-only node
  `lem-coef-simplicial-undercategory-model` has no recorded declaration
  yet, so its future module cannot be imported; no statement notion is
  missing from this delivery. Its future proof-only import is left for
  the maintainer when it lands.

Edge cases checked before the final statement: the test class can be empty,
so both predicates are vacuous; identity cofibrations give identity maps on
both strict and derived mapping spaces; both endpoints can be noncofibrant;
the base `sHom A Z` need not be Kan; empty mapping spaces are allowed, and
nonempty-to-empty or empty-to-nonempty boundary-lifting issues are retained;
`n=0` is included in `I`. For fibrant test objects it is valid to use `Z`
without a further fibrant replacement. The independent universes `u,v`
match the dependency's object/hom universes; the enrichment takes values
in `SSet.{v}`, with no imposed equality of those universes.

Searches (all via the prescribed wrapper or read-only source searches):

- LeanFinder: “cofibration local equivalence detected by strict mapping
  spaces in a left proper simplicial model category” returned eight
  general cofibrant-localization and homotopy-class declarations, including
  `RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence`.
  That result assumes an original weak equivalence and only gives a
  bijection on homotopy classes; it does not state this enriched test.
- LeanSearch: “A cofibration in a left proper simplicial model category is
  a local equivalence precisely when strict mapping spaces into all
  fibrant local test objects give trivial Kan fibrations” returned eight
  cofibration/model axiom declarations, none this assertion.
- Loogle: the initial unqualified query with `Cofibration` failed identifier
  resolution. The corrected query
  `HomotopicalAlgebra.Cofibration, HomotopicalAlgebra.WeakEquivalence`
  returned twelve standard trivial-cofibration, lifting, replacement and
  right-homotopy-class declarations. No exact match.
- `msearch.py` grep:
  `localEquivalence|mapping.*trivial|eHomWhiskerRight|SatisfiesSM7` in
  `Mathlib/AlgebraicTopology/ModelCategory` gave no hits. Direct reads of
  enriched ordinary-category definitions confirm that
  `eHomWhiskerRight` is the actual precomposition map.
- `rg` with that pattern in upstream `WeilConjectures` found enriched
  whiskering formulas only; `grep -rn` for the item id found no upstream
  declaration. The corresponding search in `lean/Sheaf` found existing
  SM7/enrichment interfaces and unrelated mappingwise assertions, but no
  local-mapping-test theorem. Name search for
  `cofibration_local_mapping_test` in upstream names, Mathlib, upstream
  source and `lean/Sheaf` found no collision.

Source check: HTT A.3.7.1 and its full proof were opened online, PDF pages
923--925. The generalization from fibrant S-local objects to the node's
weak-equivalence invariant class uses precisely the same proof: its test
replacements remain fibrant and belong to the class by `_closed`. The
source's cofibrant-source/fibrant-target mapping convention is on PDF page
923 immediately before the lemma. No statement correction is needed.

The final module compiles cleanly through `scompile.py`, both as the sandbox
file and at its library module path. All variable and universe binders are
explicit (`autoImplicit false`). No `STATEMENT-DISPUTED` issue or node fault
remains. The second reading is intentionally reserved for the second worker.

## Second reading by Q69

I independently opened the item node and sandbox module together, the two statement-dependency
nodes and their actual modules, the tensor/cotensor module, the recorded fiber criterion, and
Mathlib's model axioms, enriched precomposition and lifting predicates. I also opened HTT
A.3.7.1 with the preceding mapping convention and the entire proof, PDF pages 923--925
(printed 906--908), at https://people.math.harvard.edu/~lurie/papers/HTT.pdf. This item has
no Stacks source, no repair note, no statement correction, no new nodes and no dependency
modules. Comparing the sandbox node with the repository node found only the `lean` field
changed. No citer audit is required for an unchanged mathematical statement.

Independent inventory, Lean correspondence and verdicts:

1. The category M and its model structure are `{M : Type u} [Category.{v} M]
   [ModelCategory M]`. I read Mathlib's `ModelCategory`: it contains the three morphism
   classes, two-out-of-three, retract closure, both lifting axioms and both factorizations.
   The additional `[HasLimits M] [HasColimits M]` and both
   `MorphismProperty.HasFunctorialFactorization` instances supply precisely the completeness
   and functoriality explicitly stipulated by the nerve-localization dependency's node.
   They are inherited conventions, not extra properness or combinatorial hypotheses. Pass.
2. Simplicial enrichment is `[SimplicialCategory M]`; chosen tensors and cotensors are
   `_T : SimplicialTensorCotensor M`; SM7 is `_hSM7 : SatisfiesSM7 M`. I read the universal
   tensor/cotensor elements and their enriched representing isomorphisms. I read `cornerMap`
   and `SatisfiesSM7`: they use actual enriched pre/postcomposition, horn lifting, and weak
   equivalence if either input is trivial. Together with the Kan--Quillen dependency this
   is the source's simplicial model axiom. These are the recorded notions. Pass.
3. Left properness is `_leftProper`, universally quantifying over every weak equivalence
   `w : A ⟶ B` and cofibration `i : A ⟶ C`. The map `pushout.inr w i` is the induced map
   from C to the pushout. This is the pushout of w along i, in the correct orientation.
   No cofibrancy or fibrancy restriction occurs in this quantifier. Pass.
4. The class of tests is `tests : ObjectProperty M`, an arbitrary predicate on objects.
   `_fibrant : ∀ Z, tests Z → IsFibrant Z` says exactly that its members are fibrant.
   `_closed` states `tests X ↔ tests Y` for every weak equivalence between fibrant X and Y.
   Both directions are present, with no closure asserted for nonfibrant objects. Pass.
5. The derived-map convention is realized by `Q : M ⥤ M`, `_ε : Q ⟶ 𝟭 M` and `_hQ`.
   Each QX is cofibrant and its augmentation is both a fibration and a weak equivalence.
   These data are available from the stipulated functorial factorization system. They are
   universally supplied representative data, not an assumed conclusion or arbitrary map.
   I read `MappingPresentation`, its enriched comparison and composition fields, and
   `MappingFormulas` in the recorded nerve module. Its quantifiers cover these very
   replacement functors and augmentations. With Z already fibrant, `sHom (Q.obj X) Z`
   computes the derived mapping space without replacing Z. Naturality of the augmentation
   identifies `Q.map i` with i in the localized variables. Thus the left predicate
   `∀ Z, tests Z → SSet.Enhanced.IsWeakHomotopyEquivalence
   (eHomWhiskerRight SSet (Q.map i) Z)` is precisely membership in W_tests. I also read
   `Enhanced.IsWeakHomotopyEquivalence`: it tests realization components and every positive
   based homotopy group, rather than only components or an arbitrary equivalence relation.
   Pass.
6. The tested arrow is `{A B : M} (i : A ⟶ B) (_hi : Cofibration i)`. There are no
   `IsCofibrant A` or `IsCofibrant B` hypotheses. The source's cofibration may have either
   endpoint noncofibrant, exactly as here. Pass.
7. The strict mapping arrow is `eHomWhiskerRight SSet i Z`. Mathlib's definition gives
   `sHom B Z ⟶ sHom A Z` by composition with the actual i. It uses the original A and B,
   not Q replacements. Pass.
8. The conclusion is an iff with `∀ Z, tests Z → SSet.modelCategoryQuillen.I.rlp
   (eHomWhiskerRight SSet i Z)`. I read `I`, the family of boundary inclusions indexed by
   all natural numbers, and `rlp`, the diagonal lifting property against each member.
   This is exactly trivial Kan fibration as defined by the node. It includes n = 0.
   Both predicates quantify over the same entire class, in the stated order. Pass.

The source specializes its tests to fibrant local objects. The node's generalization is
valid: inspection of the proof shows that replacement of tests needs only invariance under
weak equivalences between fibrant objects. No further closure, smallness or combinatorial
assumption is used. I checked the eight-step docstring against the node, including both
relative fiber comparisons through the undercategory and the specified base vertices.
The docstring retains the non-Kan strict base case, and the recorded fiber criterion really
allows an arbitrary base. The proof-only undercategory node still has no Lean attachment;
its future import remains a maintainer task. All currently recorded proof modules are
imported nonpublicly, and the two statement-dependency modules are imported publicly.

Edge cases: an empty test class makes both sides vacuous and is permitted. A zero object,
when present, and initial/terminal objects are unrestricted objects of M. Identity
cofibrations are covered; enrichment sends them to identity maps. Noncofibrant endpoints
remain allowed, and the strict base `sHom A Z` need not be Kan. Empty mapping simplicial
sets are permitted; the component condition in the derived predicate and the dimension-zero
boundary condition in the strict predicate retain nonemptiness information. There is no
ring, characteristic, scheme or positive-dimensional restriction. Independent object and
morphism universes u,v are explicitly bound, and mapping simplicial sets live in v as in
the recorded enrichment. No equality of these universes or extra size instance is imposed.

Independent searches, using words different from the first worker's main searches:

- LeanFinder through `msearch.py`: "Derived orthogonality detected by boundary lifting of
  enriched precomposition into fibrant objects". Eight hits, including the right-homotopy
  class bijection for an already weak equivalence. I opened that declaration in
  `Mathlib/AlgebraicTopology/ModelCategory/Homotopy.lean`: it assumes the original weak
  equivalence and concludes only a bijection of homotopy classes. It is not this theorem.
- Loogle through `msearch.py`: `"eHomWhiskerRight", "Cofibration"`. Zero hits.
- LeanSearch through `msearch.py`: "Strict simplicial mapping objects detect derived
  orthogonality of cofibrations without cofibrant endpoints". Eight hits consisting of
  `sHom` and basic cofibrancy/simplicial-set declarations; no matching theorem.
- Direct `rg -i` searches for local cofibration/mapping combinations, boundary
  precomposition/enrichment combinations and fibrant orthogonality in upstream
  `WeilConjectures`, project `lean/Sheaf`, and Mathlib's category-theory and algebraic-topology
  directories. The hits concern other localization interfaces or ordinary model axioms;
  none has the iff being delivered. Exact declaration-name search in those libraries and
  `dag/lean_names_upstream.json` also found no collision.

No mathematical mismatch or convention defect was found. I left the correct Lean module
and node unchanged and appended this independent second reading only. There is one named
postponed theorem, with proof `by sorry`, no new definition, no hollow construction and
nothing proved. Source and blueprint docstrings are present. Every line is within 100
characters. By direct string comparison, `lean.statement` equals the module signature
verbatim. Every variable and universe is explicitly bound with `autoImplicit false`.
The prescribed `scompile.py` compile passed for both the sandbox and library module paths,
with no warnings or errors. No disputed-statement issue remains.
