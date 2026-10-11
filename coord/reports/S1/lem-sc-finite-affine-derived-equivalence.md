## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence` states
`AlgebraicGeometry.finite_affine_derived_equivalence`, with its sole proof `sorry`.
The original node statement is unchanged. One definition node supplies the canonical
ringed space and the unbounded direct-image-algebra quasi-coherent derived category.
All definitions have complete data and contain no postponed proof.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes X and Y and their morphism: `{X Y : Scheme.{v}} (f : X ⟶ Y)`.
- Affineness, with no finiteness, separation, or Noetherian assumption:
  `[IsAffineHom f]`. The word “finite” in the node ID supplies no hypothesis.
- The chosen derived localizations are explicit `HasDerivedCategory` binders
  on the shared `SheafOfModules (moduleRings ...)` carriers, with independently
  chosen morphism universes `wX`, `wY`, and `wA`. These are localization choices,
  not restrictions on the schemes or complexes.
- The algebra is the sheaf `(TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf`.
  Its O_Y-algebra structure is exactly f.c; scalar restriction uses the existing
  `SheafOfModules.restrictScalars` applied to
  `⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩`.
  This is the same expression as the recorded affine module correspondence, with
  the shared moduleRings carrier. No new algebra action is postulated.
- The source is precisely `schemeDerivedQCohCategory X`.
- The target is `directImageAlgebraDerivedQCohCategory f`: a full subcategory of
  `DerivedCategory (SheafOfModules (moduleRings (directImageAlgebraSpace f)))`.
  Its property is `∀ n : ℤ, ((DerivedCategory.homologyFunctor ... n).obj K).IsQuasicoherent`,
  over the algebra itself. This is the local-presentation sense of the affine
  module correspondence, without a bounded-below condition.
- The equivalence is `∃ E : schemeDerivedQCohCategory X ≌
  directImageAlgebraDerivedQCohCategory f`.
- “Rf_* induces” this equivalence is specified by the first natural isomorphism:
  after including the target in its ambient derived category, `E.functor` agrees
  with the recorded `RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)`.
  This is the source's Rg_*, retaining the direct-image-algebra module structure.
- The restriction functor between the two quasi-coherent subcategories is `S`.
  Its ambient comparison identifies it with the existing scalar-restriction
  functor's `rightDerivedFunctor`. Scalar restriction is exact, since it leaves
  the underlying abelian sheaves and their kernels/cokernels unchanged. Thus
  this derived functor is the ordinary termwise restriction on derived categories.
- The final comparison `E.functor ⋙ S ⋙ (schemeDerivedQCohProperty Y).ι ≅
  (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f` states that its
  composite is Rf_*. Including into the ambient category expresses this without
  choosing a second copy of the restricted Rf_* functor. Existence of S also
  records that scalar restriction lands in D_QCoh(Y).

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`, the specialization of
  `RingedSpace.derivedModuleDirectImage` from
  `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; cohomology is `DerivedCategory.homologyFunctor`.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules`; general ringed-space
  carriers use the node's `SheafOfModules` form and Mathlib's abelian instance.
- `Sheaf.AlgebraicGeometry.AffineModuleCorrespondence`:
  `Scheme.Modules.affine_module_correspondence`, especially its algebra ring sheaf,
  scalar-restriction expression, and the `IsQuasicoherent` notion on algebra modules.
  Its underived equivalence is the proof's input, not a replacement for this theorem.

The source was read at https://stacks.math.columbia.edu/tag/0AVW because the local
literature file is absent. It states the affine equivalence and final Rf_* comparison,
and constructs Phi as the restriction of Rg_* using the same K-injective complex.
The declaration docstring carries all four proof steps, including the scalar
restriction comparison used before the affine cohomology formula.

Edge cases checked: the empty scheme and empty inverse images cause no nonemptiness
binder; zero rings and zero module sheaves are permitted; f can be the identity;
all integer cohomology degrees occur, including negative degrees, with no boundedness
condition; no characteristic or finite-type assumption appears. IsAffineHom is a
real geometric hypothesis, not automatic for arbitrary scheme morphisms. Standard
localizations witness the HasDerivedCategory choices. No statement dispute or
statement correction was needed.

Searches for the item:

- msearch LeanFinder, “affine morphism derived category quasi coherent pushforward
  equivalence”: eight generic pushforward/sheaf-adjunction results, no equivalence.
- msearch Loogle, `AlgebraicGeometry.IsAffineHom, DerivedCategory`: zero hits.
- msearch LeanSearch, “affine morphism derived equivalence of quasi coherent modules”:
  service unavailable, Internal Server Error.
- msearch grep, `affine.*equivalence|Derived.*Affine`, AlgebraicGeometry: five hits,
  about affine etale sites, affine schemes, or elliptic-curve point coordinates.
- rg over WeilConjectures for `affine.*derived|derived.*affine` found only unrelated
  etale/adic/Fourier statements; grep for the node ID found none. Searches of
  lean/Sheaf found the source definitions, underived relative correspondence,
  and absolute affine/Spec statements, not this relative equivalence.
- rg of proposed declaration names in Mathlib, WeilConjectures, lean/Sheaf, and
  dag/lean_names_upstream.json found no collision.

Local compilation of both modules together is clean, with auto-implicit binding
disabled and all universes explicit. The server compile and preflight are run by
`deliver2.py --no-push`; the second reader owns the independent reading and delivery.

## New nodes

`def-sc-direct-image-algebra-derived-category` defines `(Y,f_*O_X)`, the canonical
ringed-space morphism from X with identity map on f_*O_X, and the unbounded
D_QCoh(f_*O_X), with the ring-sheaf category and cohomology supplied by Mathlib.
Source: Stacks Tag 0AVW, the displayed target and the paragraph introducing g.
`directImageAlgebraSpace`, `toDirectImageAlgebraSpace`,
`directImageAlgebraDerivedQCohProperty`, and `directImageAlgebraDerivedQCohCategory`
are all full definitions, not chosen data from existence assertions.

The new node records the actual LeanSearch (unavailable), LeanFinder (eight generic
ringed-space/pushforward declarations), and Mathlib grep (zero exact-name hits)
results. DAG and blueprint searches found no node for this canonical ringed space
or its unbounded category. The existing `def-pc-derived-category-qcoh-algebra`
(`DerivedCategoryQCoherentAlgebra.lean`) was opened: its quasi-coherent property
includes a bounded-below conjunct, so using it would drop the unbounded cases of
0AVW. Its carrier D(B) is Mathlib's same DerivedCategory; this module also uses
that construction, rather than introducing another derived category. Its
quasi-coherence via O_Y agrees, for affine f, with quasi-coherence over f_*O_X by
the recorded affine module correspondence, but its boundedness is not appropriate
here. `Scheme.Hom.toRingCatSheafHom` was also examined: it lands in the RingCat
pushforward of X.ringCatSheaf, whereas the shared algebra carrier forgets the
CommRingCat pushforward; the latter is the carrier fixed by the dependency.
The theorem therefore directly uses the already established whiskerRight expression.
No second definition of that scalar map was added.


## Second reading by S1

I read the node statement, its source (Stacks Tag 0AVW, Lemma 36.5.4), the two
delivered modules, and the dependency declarations. The correspondence is as follows.

- The objects `X`, `Y`, and `f : X ⟶ Y` are the binders `{X Y : Scheme.{v}}`
  and `(f : X ⟶ Y)`; `[IsAffineHom f]` is the sole geometric hypothesis, matching
  “affine morphism” in the source.
- The source category `D_QCoh(O_X)` is `schemeDerivedQCohCategory X`, and the
  target `D_QCoh(f_* O_X)` is `directImageAlgebraDerivedQCohCategory f`, whose
  property quantifies over every `n : ℤ` and requires quasi-coherent homology over
  the direct-image algebra. The three `HasDerivedCategory` binders choose derived
  localizations and add no geometric finiteness, Noetherian, separation,
  characteristic, or boundedness assumptions.
- The existential equivalence `E` is followed by a comparison with
  `RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)`, exactly the
  source's construction of `Phi` as the restriction of `Rg_*`.
- The existential `S` is the restriction-of-scalars functor to
  `schemeDerivedQCohCategory Y`; its displayed isomorphism identifies it with the
  right-derived scalar-restriction functor. The final displayed isomorphism says
  `E ⋙ S` is `schemeDerivedDirectImage f`, precisely the source's composition
  with restriction of scalars being `Rf_*`.

No mismatch was found and no Lean or node change was needed. The source and Lean
both allow the identity morphism, empty schemes, zero sheaves, every integer degree
(including negative and zero), and arbitrary characteristics. No nonemptiness,
finite-type, Noetherian, or universe restriction is introduced. Searches for an
existing declaration were rechecked with LeanFinder/Loogle and grep in Mathlib,
`WeilConjectures`, and `lean/Sheaf`; only the delivered declarations were found.
