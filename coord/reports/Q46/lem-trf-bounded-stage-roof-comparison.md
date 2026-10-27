## Worker report

Module: `Sheaf.Algebra.Homology.BoundedStageRoofComparison`.
Main declaration: `CategoryTheory.Functor.bounded_stage_roof_comparison`.
Per-degree declaration: `CategoryTheory.Functor.bounded_stage_roof_comparison_homology`.
Both proofs are `sorry`; there are no definitions, instances, or additional nodes.
Only the item's `lean` field changes. No statement correction is needed.

The source was read in `literature/stacks-project/derived.tex`, Tag 0794,
`proposition-left-derived-exists`, especially the first paragraph and the
bounded-stage roof argument before passage to colimits (lines 9397--9433).
The live Q30 PASS concerns the stage-1 split, not Lean: the base item has no
`lean` or `reviewed_lean` field. Thus that review does not complete this stage-2 task.
No repair note exists for the item.

The convention of brief-stage2 §3, dated 2026-10-21, requires a derived
isomorphism as the main result even when the node only spells out cohomology.
Accordingly the main declaration supplies derived isomorphisms `Θ k`, with
both compatibility equations in `DerivedCategory B`. The second declaration
spells out exactly the node's per-degree conclusion. The common resolving
roof in proof steps 7--8 gives the derived augmentation square as well: F
preserves the homotopy, and localization inverts its two quasi-isomorphism
legs. Applying derived cohomology and its natural comparison with complex
cohomology gives the second declaration and both of its equations. Neither
proof is implemented in stage 2. The main docstring contains all eight steps
of the DAG proof, adapted to the derived form; the corollary docstring explains
its deduction. Both declarations belong to this node, as required by that convention.

Hypothesis and clause correspondence (the same hypotheses occur in both declarations):

- Abelian categories: `{A : Type uA} [Category.{vA} A] [Abelian A]` and the B
  counterparts. All four universes are independent. Cochain complexes are
  `CochainComplex A ℤ`, with Mathlib's cohomological `ComplexShape.up ℤ`.
- The derived main declaration uses `[HasDerivedCategory.{wB} B]` for the
  chosen category appearing in its conclusion. This imposes no equality on
  object or morphism universes. The per-degree corollary has no derived-category
  choice in its hypotheses. The A localization and the corollary's B localization
  can be chosen with `HasDerivedCategory.standard` inside the future proofs,
  exactly as instructed in Mathlib DerivedCategory/Basic.lean. The common larger
  universe in the node is a size convention for the auxiliary localizations,
  not an assumption of small derived Homs in the original Hom universe.
- The class is `(P : A → Prop)`; no second notion of resolving class is defined.
- Contains zero: `hzero : P (0 : A)`.
- Isomorphism closure: `hiso : ∀ (M N : A), (M ≅ N) → P M → P N`.
- Finite biproduct closure: `hsum` is closure under the binary biproduct `M ⊞ N`.
  Together with `hzero` and `hiso`, this is equivalent to closure under arbitrary
  finite biproducts: iterate the binary operation and transport along the canonical
  finite-biproduct isomorphism. The empty biproduct is covered by `hzero` and `hiso`.
  Abelian categories already have binary biproducts; no extra instance is assumed.
- Every object is an epimorphic image of a P-object: `hcover` supplies an actual
  object `N`, map `p : N ⟶ M`, membership `P N`, and `Epi p`, for every M.
- Additive functor: `(F : A ⥤ B) [F.Additive]`.
- Bounded-above quasi-isomorphism preservation: `hF` quantifies over arbitrary
  complexes K,L and f, their separate termwise upper bounds, all their termwise
  P-memberships, and `QuasiIso f`. Its conclusion is `QuasiIso` of the actual
  map `(F.mapHomologicalComplex (ComplexShape.up ℤ)).map f`. Bounds are existential
  integers and need not be equal or positive. There is no global preservation
  hypothesis on F, and no exactness or right-exactness premise.
- Positive stage indices: `E G : ℕ → CochainComplex A ℤ` use k for the source
  index n=k+1. This is a bijective reindexing of all positive integers, not a
  restriction or extra stage. In particular k=0 is precisely source stage 1.
- Stages are bounded above: `hEbound` and `hGbound` give a separate integer bound
  for each k. They do not require terms to vanish above k+1; only cohomology has
  that stronger bound. `hEterms` and `hGterms` give membership at every integer degree.
- Transitions are the supplied `u : ∀ k, E k ⟶ E (k+1)` and the analogous `v`.
- X,Y are arbitrary `CochainComplex A ℤ`, with no boundedness or membership premises.
  The maps e,g are the supplied augmentations from every stage to those complexes.
- Compatible augmentations are exactly `he : u k ≫ e (k+1) = e k` and the analogous hg.
- Vanishing in degrees j>n: `hEvanish` and `hGvanish` say `IsZero` of the actual
  homology objects when `(k : ℤ)+1 < j`. Zero means a categorical zero object,
  not equality with a particular implementation of the zero object.
- Isomorphisms for every j≤n: `heiso` and `hgiso` assert `IsIso` of
  `HomologicalComplex.homologyMap (e k) j` and of the corresponding g map.
  This includes all negative degrees and includes the endpoint j=k+1.
- Every quasi-isomorphism alpha: `(α : X ⟶ Y) (hα : QuasiIso α)` is arbitrary;
  no chain map between the supplied towers is required or assumed.
- Per-degree isomorphisms: the existential `θ : ∀ (k : ℕ) (i : ℤ), ... ≅ ...`
  is between the actual homology objects of the termwise images F(E k), F(G k).
  The existential is outside both universal compatibility clauses, giving a
  single simultaneous choice, and i is entirely unrestricted.
- Transition equation: `homologyMap (F(u k)) i ≫ (θ (k+1) i).hom =
  (θ k i).hom ≫ homologyMap (F(v k)) i`. Lean composition reads left to right,
  so this is exactly the node's theta_(n+1) H(F(u_n)) = H(F(v_n)) theta_n.
- Augmentation equation: `(θ k i).hom ≫ homologyMap (F(g k)) i =
  homologyMap (F(e k)) i ≫ homologyMap (F(α)) i`, with the same composition convention.
  It uses the actual e,g,alpha, not arbitrarily chosen maps on cohomology.
- The derived main conclusion is the same pair of equations with Q.map in place
  of homologyMap, and `Θ k` between `Q.obj F(E k)` and `Q.obj F(G k)`.
- The module assumes no colimits or preservation of colimits.

Dependency declarations used, with source signatures and docstrings read:

- Statement dependency `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (mathlib_match, no Lean record required).
- Statement dependency `def-weil-abstract-derived-category`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`. This module is publicly imported.
- `CategoryTheory.Functor.mapHomologicalComplex`, `Mathlib.Algebra.Homology.Additive`:
  real termwise action on objects, differentials and maps; transitively public.
- `HomologicalComplex.homology`, `HomologicalComplex.homologyMap`, `QuasiIso`,
  `Mathlib.Algebra.Homology.HomologicalComplex` / `QuasiIso`: existing cohomology and
  quasi-isomorphism interfaces supplied by the recorded derived-category dependency.
- `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`,
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: the corollary's plan.
- Proof dependency `lem-pc-quasi-isomorphisms-multiplicative-system`:
  the left/right fraction instances for `HomotopyCategory.quasiIso`,
  `Mathlib.Algebra.Homology.DerivedCategory.Fractions`.
- `lem-pc-right-fraction-representation`: `CategoryTheory.Localization.exists_rightFraction`;
  `lem-pc-right-fraction-common-refinement`:
  `CategoryTheory.MorphismProperty.RightFraction.map_eq_iff`,
  both in `Mathlib.CategoryTheory.Localization.CalculusOfFractions`.
- `lem-weil-pbc-truncation-cohomology`: `CochainComplex.quasiIsoAt_ιTruncLE`,
  `Mathlib.Algebra.Homology.Embedding.CochainComplex`.
- `lem-sfb-subcategory-left-resolution`:
  `CochainComplex.exists_subcategory_left_resolution`,
  `Sheaf.Algebra.Homology.SubcategoryLeftResolution`.
- `lem-trf-right-fraction-dense-subcategory`: `CategoryTheory.rightFractionDenseSubcategory`,
  `Sheaf.CategoryTheory.RightFractionDenseSubcategory`.
- `lem-weil-pbc-homotopic-maps-equal-cohomology`:
  `CategoryTheory.Functor.mapHomotopy` and `Homotopy.homologyMap_eq`,
  `Mathlib.Algebra.Homology.Homotopy`.
- `lem-weil-pbc-localization-universal-property`: `CategoryTheory.Localization.lift`
  and `fac`, `Mathlib.CategoryTheory.Localization.Predicate`.
- `lem-weil-pbc-truncation-descends`: `DerivedCategory.truncation_descends`,
  `Sheaf.CategoryTheory.TruncationDescends`.

Every already stated proof dependency's module is imported without `public`.
There is no missing or unusable dependency and no import cycle.

Edge cases checked before writing:

1. Zero class in a zero category, zero complexes, and the zero additive functor:
   all conclusions reduce to zero-object isomorphisms, with meaningful equations.
2. Empty finite sum: hzero supplies it; hiso covers other choices of zero object.
3. Initial positive stage 1 is k=0, and the first transition is u 0, v 0.
4. At j=k+1 augmentation isomorphy is required, but vanishing is not; j=k+2
   requires vanishing. Negative j and i remain included with no truncation of indices.
5. A stage may have a nonzero acyclic tail above k+1, or any negative termwise
   upper bound. Bounded-above terms and the separate cohomology bound are not confused.
6. X,Y may be unbounded in both directions and need not have terms in P; F need
   not preserve their quasi-isomorphism alpha. The conclusion only compares their
   supplied stage models and imposes the augmentation square.
7. Alpha=id and identical towers admit the identity comparisons. Different towers
   and arbitrary alpha are allowed; no lift of alpha to a tower map is added.
8. F=- tensor Z/2 on abelian groups with P the free groups is additive but not
   exact, while it preserves quasi-isomorphisms between bounded-above free complexes.
   Such an example is allowed; arbitrary-complex preservation is not smuggled in.
9. All category object, category Hom, and derived Hom universes remain independent;
   no assumption identifies site-style object and morphism universes.

Searches for an existing statement (msearch.py Q46, 2026-10-22):

- leanfinder: "Compatible cohomology isomorphisms between bounded above resolving
  class approximations to quasi-isomorphic unbounded complexes under an additive functor".
  Eight hits including mapHomologicalComplexUpToQuasiIsoFactors(h),
  injective/projective resolution comparisons, and DerivedCategory's Q.map instance.
  These do not compare supplied towers with transitions and actual unbounded-target
  augmentation squares under preservation only on bounded-above P-complexes.
- loogle: `Functor.mapHomologicalComplex, HomologicalComplex.homologyFunctor`
  returned zero hits and unknown identifier Functor.mapHomologicalComplex.
  Retried with quoted substring query `"mapHomologicalComplex", "homologyMap"`:
  successful zero hits.
- grep: `IsClosedUnderFiniteBiproducts|IsClosedUnderIsomorphisms` in CategoryTheory:
  25 hits on object-property closure interfaces, not the desired theorem.
- grep: `bounded.*roof|roof.*comparison|stage.*comparison|mapHomologicalComplexUpToQuasiIso`
  in Algebra/Homology: 15 hits, on Localization and derived exact-functor interfaces.
  These global derived-map constructions assume preservation of homology and do
  not give the resolving-class tower comparison here.
- rg in lean/WeilConjectures and lean/Sheaf for
  `bounded.stage|stage.roof|roof.comparison|lem-trf-bounded-stage-roof-comparison`:
  unrelated geometric roof comparisons and the docstring of the parent
  UnboundedLeftDerivedCriterion; no declaration of this statement.
- grep -rn of the exact node id in lean/WeilConjectures: no matches.
- rg of `boundedStageRoofComparison|bounded_stage_roof_comparison` in both source
  roots before writing: no matches. Existing declaration names do not collide.

Compilation: scompile.py compiled the final module in both sandbox and library
contexts on the server with no errors or warnings (2.1 s and 1.7 s, 60 s limit).
All universes are declared and `set_option autoImplicit false` is set.

## Second reading by Q46

A separate in-session manual pass reread the live node, all binders, and both
conclusions after compiling. This is not a claim to an independent subagent review;
none was started, as required by the dispatcher brief. The maintainer supplies
independent delivery review.

The pass checked each correspondence above against the file: hzero/hiso/hsum/hcover,
additivity, the four domain conditions in hF, termwise boundedness and P-membership
of both towers, both transition maps, both augmentations and their equations,
the strict cohomology cutoff and inclusive augmentation cutoff, and arbitrary
quasi-isomorphism alpha. All are present with no new mathematical hypothesis.
It recomputed the source/target of every composite: both transition composites
start at H^i(F(E k)) and end at H^i(F(G(k+1))); both augmentation composites start
at H^i(F(E k)) and end at H^i(F(Y)). The derived composites have exactly the same
endpoints after Q. The two clauses share one existential family, not separate
choices. The k+1 reindexing keeps every positive source stage and no others.
The only enhancement found necessary was the dated derived-isomorphism convention;
it was implemented by adding the derived main declaration while keeping the exact
cohomology statement as a second declaration. No fault or STATEMENT-DISPUTED flag remains.
