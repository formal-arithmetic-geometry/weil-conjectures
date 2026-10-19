## Worker report

The module `Sheaf.Algebra.Homology.KFlatRoosRepresentativeInvariance` states
`SheafOfModules.KFlatRoos.representativeInvariance`. Nothing is proved in this
stage: all seven named theorems have `sorry` proofs. Definitions contain real data.
The node's statement, dependencies and proof are unchanged; only `lean` is added.

The earlier stale-dispatch diagnosis confused a stage-1 completion with a stage-2
completion. The NC landing recorded a reviewed proof split but no `lean` field.
This delivery supplies the absent Lean statement and does not repeat the split.

Hypotheses and objects, clause by clause:

- The site is `C : Type u`, `[Category.{v} C]`, `J : GrothendieckTopology C`.
  `[EssentiallySmall.{r} C]` means small in the module/coefficient universe.
  The three explicit sheaf-composition, abelian sheafification and local-bijection
  instances supply the standard sheaf machinery; they impose no flatness,
  completeness, geometry or ring restriction. Site object, morphism, coefficient
  and derived morphism universes `u`, `v`, `r`, `w` remain independent.
- `R : Sheaf J CommRingCat.{r}` is the commutative ring sheaf. `Modules R` is a
  transparent abbreviation of the recorded `CategoryTheory.ringedSiteModules`
  applied to its underlying ring sheaf, with module universe `r`.
- `[HasCountableProducts (Modules R)]` supplies the products whose existence is
  part of having exact countable products; the main theorem additionally takes
  `[HasExactLimitsOfShape (Discrete ℕ) (Modules R)]`, their exactness.
- `B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r}` is the given tower. Lean index `n`
  denotes the natural-language positive level `n+1`, using exactly the recorded
  inverse-system encoding. `ι : (Functor.const ℕᵒᵖ).obj R ⟶ B` supplies every
  structure map R to B_n and exactly its compatibility with transitions.
  No structure or transition map is assumed flat, epi, mono or surjective.
- `[HasDerivedCategory.{w} (Modules R)]` chooses the unbounded derived category
  and localization `DerivedCategory.Q`, in the chosen morphism universe.
- `P P' : CochainComplex (Modules R) ℤ` are the two complexes. `hP`, `hP'`
  use the dependency's precise `CochainComplex.IsKFlatIndependentCoefficients`
  predicate. `hflat`, `hflat'` assert the dependency's `IsFlatOnSite` in every
  integer degree, with no boundedness hypothesis.

Constructions in the statement:

- `algebraModule` is the existing `SheafOfModules.restrictScalars` applied to
  `SheafOfModules.unit` of B. Thus its sections really are B with its given
  R-action. `algebraModuleMap` is uniquely specified by the original ring map
  on every section; its defining uniqueness theorem supplies only linearity,
  naturality and uniqueness, not unspecified data. `levelModule` and `levelMap`
  apply these constructions to the given tower; `structure_compatible` is the
  consecutive naturality equation for `ι`.
- `level B ι n` is the existing `siteSheafTensorRight` mapped termwise to
  cochain complexes: precisely P tensor_R B_n, considered over R. `transition`
  is `NatTrans.mapHomologicalComplex` of the recorded
  `siteSheafTensorRightMap` for the actual algebra transition.
- `product` is the categorical product in cochain complexes. By the imported
  Mathlib `HomologicalComplexLimits` interface these are termwise products,
  exactly V(P). `oneSubShift` is `Pi.lift` of
  `pr_n - pr_(n+1) ≫ transition_n`, hence exactly 1-s.
- `roosX P i` is V(P)^i biproduct V(P)^(i-1), in the node's actual order.
  `roosD P i` is the biproduct lift `(dx, (1-s)x - dy)`. Its `eqToHom` merely
  identifies `(i+1)-1` with `i`; there is no additional isomorphism chosen.
  `roos` uses `CochainComplex.of` and the named square-zero theorem. It has
  precisely the displayed objects and differential, not an arbitrary cone.
- `tensorUnit` is uniquely prescribed by
  `siteSheafTensorTmul M (algebraModule ι) U p (1 : B(U))` on every local
  section. `unitProduct` takes its product termwise; `augmentation` is the
  actual biproduct lift of this map and zero. Its chain-map proof is the
  named theorem `augmentation_comm`. Thus it is the stated eta_P.
- `productMap a` is `Limits.Pi.map` of `(level n).map a`. `roosMap a` has the
  explicit component `biprod.map (productMap a).f i (productMap a).f (i-1)`;
  its chain-map proof is named `roosMap_comm`. This is exactly the strict L(a).

Conclusions, clause by clause:

- The first conjunct quantifies every `a : P ⟶ P'` and assumes exactly
  `QuasiIso a`. It asserts `QuasiIso (roosMap B ι a)` and the strict equality
  `augmentation P ≫ roosMap a = a ≫ augmentation P'`. Lean composition
  is written from left to right, so this is L(a) eta_P = eta_P' a.
- The second conjunct quantifies **every** derived isomorphism
  `e : Q.obj P ≅ Q.obj P'`. It produces an actual isomorphism
  `v : Q.obj (roos P) ≅ Q.obj (roos P')` satisfying
  `Q.map (augmentation P) ≫ v.hom = e.hom ≫ Q.map (augmentation P')`.
  This includes the identity and arbitrary derived isomorphisms not represented
  by a direct chain map between P and P'. No arbitrary comparison map is a
  hypothesis.
- The final conjunct assumes only `Nonempty (Q.obj P ≅ Q.obj P')` and states
  `QuasiIso (augmentation P) ↔ QuasiIso (augmentation P')`. This is precisely
  dependence only on the derived isomorphism class.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparently Mathlib `SheafOfModules`.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence` and
  `NatTrans.ofOpSequence` establish the recorded natural-number tower encoding;
  the statement uses that functor category directly, since B is already a tower.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory` and `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`:
  `siteSheafTensorRight`, `siteSheafTensorRightMap`, `siteSheafTensorTmul` and
  the zero-preservation instance, retaining the recorded tensor construction.
- Proof-plan imports: `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
  (`exists_isKFlatResolutionIndependentCoefficients`),
  `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`
  (`SheafOfModules.changeOfRings_kFlat_quasiIso`),
  `Sheaf.CategoryTheory.StrictRoosComparison` (`CategoryTheory.strictRoosComparison`),
  `Mathlib.Algebra.Homology.DerivedCategory.Fractions` (both calculus instances),
  `Mathlib.CategoryTheory.Localization.CalculusOfFractions`
  (`Localization.exists_rightFraction`), and
  `Mathlib.CategoryTheory.Abelian.FunctorCategory`
  (`Abelian.functorCategoryAbelian`). These are ordinary proof-only imports.

The helper theorems, all listed in `lean.declarations`, are
`algebraModuleMap_existsUnique`, `tensorUnit_existsUnique`,
`structure_compatible`, `roosD_sq`, `augmentation_comm`, `roosMap_comm` and
`representativeInvariance`, all in namespace `SheafOfModules.KFlatRoos`.
Each has its source, owning blueprint tag and complete natural-language proof.
The helper laws are the proof fields of the node's displayed constructions;
no independent extra mathematical notion or DAG node is introduced.

Sources checked: local Stacks `sites-cohomology.tex`, the full statements and
proofs around `lemma-K-flat-resolution` (06YS),
`lemma-derived-tor-quasi-isomorphism-other-side` (06YT),
`lemma-derived-base-change` (06YY); local `derived.tex`,
`definition-derived-limit` (08TC) and `lemma-products` immediately following it;
the current main-20261015 `sk-def-pe-derived-completion/_section.md` and
`def-weil-derived-complete.md`. The node supplies the augmented strict model
needed to make the completeness display independent of representatives.

Edge cases checked before construction: zero complexes and zero ring sheaves;
the empty site; constant and identity-transition towers; arbitrary nonsurjective
and nonflat coefficient maps; complexes unbounded in both directions; negative
and zero cochain degrees; the identity derived isomorphism; a derived isomorphism
with only a roof representative. The index set is the specified countably
infinite positive tower, never an extra nonempty finite index set. Integer
transport in the differential holds in every degree. No edge case is omitted.
No statement dispute or statement correction was needed.

Searches made:

- `msearch.py ... leanfinder "K flat quasi-isomorphism invariance of augmented
  Roos cones of a tower of tensor scalar extensions"`: eight hits, including
  `Module.Flat.rTensor_shortComplex_exact`,
  `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`, and
  `ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat`; none states
  augmented K-flat Roos representative invariance.
- `msearch.py ... loogle '"Roos"'`: twelve unrelated `Std.DTreeMap` RooSlice
  results, no relevant mathematical declaration.
- `msearch.py ... grep 'Roos|roos|KFlat' Algebra/Homology`: zero Mathlib hits.
- `msearch.py ... leansearch "Augmented Roos tensor tower is invariant under
  K-flat quasi-isomorphisms"`: eight hits concerning quasi-isomorphisms,
  K-projective/injective transport and ordinary flat tensor, none the statement.
- `rg` on the upstream `WeilConjectures` and project's `lean/Sheaf` for
  Roos/roos/scalar towers, this node id, and the proposed declaration names:
  no existing statement or colliding names. Read the generic Roos construction
  in `Sheaf.Paper.IntegralOperationsWellDefined` and the specific augmentation
  in `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`.
  The former is a generic shifted-cone model, the latter an isomorphism-of-sites
  pullback comparison; neither gives this arbitrary algebra-tower augmented
  invariance statement. The required direct coordinates here are constructed
  explicitly (the node's proof specifies the signed interchange with that
  shifted-cone presentation), retaining Mathlib products and biproducts.

Validation: `scompile.py Q69 lem-pe-kflat-roos-representative-invariance` compiled
both the sandbox source and its actual library module path cleanly, approximately
nine seconds each, within the unchanged sixty-second per-file limit.

## Second reading by Q69

Independent maintainer reading of immutable delivery
`aaea74d30f8a6c04680ecfc7fbb397db95c9f535`, performed on 2026-10-17.
This replaces the delivered disclaimer that no second reading occurred. The reviewer
read the item node, all six statement-dependency nodes, the delivered module and
worker report, the exact dependency declarations, and the cited local Stacks sources.
No mathematical statement, Lean declaration, or dependency record was changed.

Hypotheses and conclusions checked against the node:

- `C`, `Category.{v} C`, `J`, and `EssentiallySmall.{r} C` express a site small
  relative to the module universe. `R : Sheaf J CommRingCat.{r}` is the ring
  sheaf. `Modules R` unfolds to the recorded `ringedSiteModules` and Mathlib
  `SheafOfModules`; it creates no new category or abelian structure. The explicit
  sheafification, locally bijective equivalence, and sheaf-composition instances
  provide the standard machinery, with independent site universes `u`, `v`.
- `HasCountableProducts` supplies existence and `HasExactLimitsOfShape
  (Discrete ℕ)` supplies exactly the assumed exactness. `HasDerivedCategory.{w}`
  chooses the unbounded localization and its morphism universe, as the dependency
  prescribes. No boundedness, geometric, flat-ring-map, or surjectivity assumption
  was introduced.
- `B : ℕᵒᵖ ⥤ Sheaf J CommRingCat` and the natural transformation `ι` encode
  the compatible algebra tower. Index zero is positive level one; consecutive
  arrows have the correct direction. `P`, `P'`, `hP`, `hP'`, `hflat`, and
  `hflat'` are precisely the two unbounded K-flat complexes with flat terms.
- `algebraModule` uses restriction of scalars on the existing unit module.
  `algebraModuleMap_existsUnique` prescribes every section value of the original
  algebra morphism. `tensorUnit_existsUnique` prescribes every value as
  `siteSheafTensorTmul ... p 1`. Both choices determine the maps uniquely;
  neither is an arbitrary-map or hollow-definition construction.
- `level` uses the recorded sheafified sectionwise tensor functor termwise;
  `transition` uses its recorded second-factor natural transformation.
  `product` is termwise by Mathlib's evaluation/limit construction.
  `oneSubShift` has coordinate `pr_n - pr_(n+1) ≫ transition_n`.
- `roosX` and `roosD` give exactly `(V^i,V^(i-1))` and
  `(dx,(1-s)x-dy)`. The integer transport identifies `(i+1)-1` with `i`.
  `augmentation` is precisely `(product of tensor units,0)` and `roosMap`
  applies the product tensor map diagonally in the two degrees.
- The first conjunct quantifies every quasi-isomorphism `a` and asserts both
  quasi-isomorphism of the strict `roosMap` and the exact augmentation equation.
  The second quantifies every derived isomorphism `e`, including ones without a
  direct chain representative, and produces an augmentation-compatible actual
  isomorphism `v`. Composition order matches the node after reversing Lean's
  left-to-right notation. The third conjunct is exactly the quasi-isomorphism
  criterion for augmentations whenever the representatives are derived-isomorphic.

Dependency/source checks: read `RingedSiteModules`, `KFlat` (the independent
coefficient predicate), `FlatOnSite`, `SiteTensorFunctoriality`, and its
`TensorProductOfUniverses` tensor definitions in the group clone. Read Mathlib's
`DerivedCategory.Q`, `HasDerivedCategory`, `Functor.ofOpSequence`,
`NatTrans.ofOpSequence`, restriction of scalars, termwise limits, and right
fraction representation. Stacks `sites-cohomology.tex` at 06YS, 06YT, 06YY,
`derived.tex` at 08TC and the following exact-product lemma, and
`sites-modules.tex` at 03EK and 03ER(3) agree with the mathematics.
The specialized change-of-rings and strict-Roos proof imports have narrower
universe interfaces than the main statement; they need transport/generalization
if used directly in stage 3. They impose no hidden binder here. The direct
06YT total-tensor argument and exact-product/cone argument stated in the proof
plan establish the claimed generality without those specializations.

Independent searches with `rg` for Roos, augmented constructions, and K-flat
representative invariance in Mathlib, upstream `WeilConjectures`, and group
`lean/Sheaf` found no existing theorem with all these clauses. Read
`integralOperationsRoos`, `integralOperationsRoosMap`, `strictRoosComplex`,
and `inverseImageRoosComparisonComplex`: these are shifted-cone or particular
pullback constructions, not this arbitrary algebra-tower theorem with its
prescribed direct coordinates and augmentation. Existing tensor and module
notions are reused, not replaced.

Edge cases: zero ring and zero complexes, empty site, constant/identity towers,
nonflat and nonsurjective algebra maps, all integer degrees, complexes unbounded
in both directions, identity derived isomorphisms, and roof-only derived
isomorphisms remain covered. The index set is the specified infinite positive
sequence, so no empty-index assumption is applicable. No universe equality
between site objects, site morphisms, coefficients, and derived morphisms is added.

Mechanical audit: all 24 declarations are listed in `lean.declarations`; the
main signature is verbatim equal to `lean.statement`; every declaration has its
source/blueprint docstring; all seven theorem bodies are exactly `by sorry`;
no definition contains a sorry data field; no line exceeds 100 characters.
The helper laws belong to the displayed construction of this node.

Compiler reproduction: ran only
`scompile.py Q69 lem-pe-kflat-roos-representative-invariance
snapshot/lean/Sheaf/Algebra/Homology/KFlatRoosRepresentativeInvariance.lean`.
The installed wrapper uses the server side overlay (its implementation was
updated on 2026-10-17), and returned exit 0: sandbox 12.0 s, library path 11.6 s,
no errors or warnings. No global build, live Lean write, direct SSH command,
repository edit, delivery, or Git mutation was performed by the reviewer.

Finding fixed: H11, the original second-reading section was a disclaimer rather
than a reading. This independently performed reading supplies the required
clause-by-clause audit. No substantive mathematical defect found.
