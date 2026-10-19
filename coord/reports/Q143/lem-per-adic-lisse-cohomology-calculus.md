## Worker report

The module states `AlgebraicGeometry.Scheme.adic_lisse_cohomology_calculus`.
It asserts existence of the complete normalized calculation bundle, with the exact
pbc common-stage category as its category of complexes. The bundle is a way to
state all of the comparisons simultaneously, rather than to choose unspecified
realization, cohomology, fibre, or tensor maps. No definition chooses data from
the theorem's `Nonempty` conclusion. The only postponed proof is this theorem.
Its docstring includes all ten proof steps of the DAG node and the descent of
the specified coefficient-presentation comparison.

Hypotheses and clauses:

- The prime is `(l : ℕ) [Fact l.Prime]`. The coefficient closure is
  `Qbar : Type (u + 1)` with `Field`, `Algebra ℚ_[l]`, and `IsAlgClosure`.
- The scheme is `X : Scheme.{u}`, with `IsNoetherian`, `X.IsSeparated`, the
  finite-Krull-dimension `Fact`, and the stalk-unit `Fact` prescribed by the
  scheme conventions. `adicCalculusPrimeInvertible` derives the residue-field
  interface used by lisse sheaves from these units; it is not a further hypothesis.
- Complexes are literally `pbcQbarCategory l Qbar X`. Its integral stages retain
  derived completeness, uniform constructible normalized reductions, and the
  compatible étale-origin witnesses. `model_mem` and the natural isomorphism `comparison_integral`
  compare this presentation with the recorded completed-operation presentation
  using exactly `purCoefficientModel`, not a discrete étale coefficient category.
- `adicCalculusIntegralRealization` is the inverse limit of the existing
  comparison-inverse-image finite-level functor, followed by `singleFunctor _ 0`.
  `realization_mem` asserts membership in the exact integral category.
  `realization_integral` and `realization_map` prescribe realization of every
  integral model and every rational pure-tensor map. Thus `L` ranges over the
  recorded `LisseAlgebraicSheaf`, with no constant-rank, positive-rank, or
  globally free hypothesis. `realization_cohomology` and `realization_vanishing`
  state placement in degree zero.
- `adicCalculusTensor` is canonical transport of `commonStageDerivedTensor`.
  Its codomain is the same `pbcQbarCategory`, expressing tensor closure for
  every `K` and every `L`.
- `cohomology_integral` prescribes every integer-degree cohomology functor by
  integral standard-t-structure cohomology and localization. Its values are
  cohomology sheaves embedded as degree-zero objects in the derived category.
  `tensor_cohomology` is a natural isomorphism on the product category of all
  complexes and all lisse coefficients. Its right side has the same tensor
  restricted to degree-zero objects, hence the ordinary sheaf tensor.
- Geometric points use `(k : Type u) [Field k] [IsAlgClosed k]` and
  `x : Spec (.of k) ⟶ X`. `fiber_integral` specifies completed derived pullback,
  cohomology at the point, point sections, and scalar extension to `Qbar`.
  `fiber_lisse` identifies this with the already recorded lisse fibre functor.
- `tensor_fiber` is the natural isomorphism with ordinary `ModuleCat` tensor
  over `Qbar`. `tensor_fiber_induced` identifies its map with the image of
  `tensor_cohomology` followed by `ordinary_tensor_fiber`, so these are the
  induced fibre identifications.
- Independence of common finite fields and finite-extension compatibility are
  expressed by functors and natural comparisons on the *coefficient-localized*
  categories, with normalization at every finite field. Their naturality ranges
  over all arrows, including coefficient-change isomorphisms, not merely arrows
  of a single finite stage. Functor laws include identity and tower coherence.
- `dual` takes values in the same finite-rank lisse category, so its realization
  is also in degree zero. `dual_fiber` gives `Module.Dual Qbar` and
  `dual_fiber_naturality` states precomposition by the original fibre map.
  `dual_permitted` supplies the exact constructible-domain condition of the
  recorded common-stage internal Hom. `dual_realization` identifies the result
  with `commonStageDerivedInternalHom` into realization of the recorded lisse
  coefficient unit. `dual_realization_naturality` includes the coefficient-change
  arrows and hence the required finite-extension compatibility.

Dependency declarations used:

- `def-weil-pbc-scheme-conventions`: Mathlib / inline conventions; None.
- `def-weil-l-adic-coefficient-extension`: Sheaf.NumberTheory.Padics.CoefficientExtensionFinite; Padic.finite_coefficientExtensionRing.
- `def-weil-pbc-qbar-category`: Sheaf.Paper.PbcQbarCategory; AlgebraicGeometry.Scheme.pbcQbarCategory.
- `def-weil-derived-pullback-tensor-hom`: Sheaf.Paper.DerivedPullbackTensorHom; WeilConjectures.commonStageDerivedInternalHom_existsUnique.
- `def-pod-lisse-l-adic-sheaves`: Sheaf.Paper.LisseAdicSheaves; AlgebraicGeometry.Scheme.LisseIntegralSheaf.
- `def-weil-derived-cohomology-sheaves`: Mathlib / inline conventions; {'declaration': 'DerivedCategory.homologyFunctor', 'file': 'Mathlib/Algebra/Homology/DerivedCategory/HomologySequence.lean', 'how': 'specializes in one line: `(DerivedCategory.homologyFunctor (SheafOfModules.{v} R) r).obj K` for `R : Sheaf J RingCat` (abelian by `SheafOfModules` instance in Mathlib/Algebra/Category/ModuleCat/Sheaf/Abelian.lean:40, with `HasDerivedCategory.standard`), equal to the homology of a representing complex by `DerivedCategory.homologyFunctorFactors`; the t-structure statement is `DerivedCategory.isLE_iff` / `isGE_iff` for `DerivedCategory.TStructure.t`; for A_Y take `J = Scheme.ProEt.topology Y`, `R = (constantSheaf J RingCat).obj (RingCat.of A)` (universe-lifted as in def-weil-pbc-constant-sheaf) Re-check 2026-10-09: types read; `homologyFunctor C r` applies to any abelian C with `HasDerivedCategory C`, here C = `SheafOfModules R` (abelian by `SheafOfModules.instAbelian` under HasSheafify J AddCommGrpCat and J.WEqualsLocallyBijective AddCommGrpCat); for the pro-etale site J = `Scheme.ProEt.topology Y` (Mathlib/AlgebraicGeometry/Sites/Proetale.lean:156), whose objects live one universe up, so the modules are taken universe-lifted as the node says.'}.
- `def-weil-geometric-point`: Mathlib.FieldTheory.IsAlgClosed.Basic; IsAlgClosed.
- `def-pod-lisse-adic-fibre-functors`: Sheaf.Paper.LisseAdicFiberFunctors; AlgebraicGeometry.Scheme.lisseIntegralFiberFunctor.

Universe convention: the scheme has universe `u`; the small finite coefficient models
have universe `u`; the algebraic closure and coefficient-module sections have universe
`u + 1`. The small pro-étale site retains object universe `u + 1` and morphism
universe `u`. No equality between the two site universes is imposed.

Additional existing interfaces used are `purCoefficientModel` for the specified
coefficient-ring restriction equivalence, `pbcIntegralTStructure` for integral
standard cohomology, `middleExtensionLevelFunctor` specialized to `𝟙 X` for
finite-level comparison inverse image and coefficient transport, and
`pointCompletedSections` for sections after completed pullback to the point.
These are reused, with their existing normalizations, rather than redefined.

Edge cases checked: the empty scheme, rank zero, different ranks on different
components, all integer cohomological degrees, torsion integral models (which
can rationalize to zero), the zero complex, identity coefficient inclusions,
ramified extensions, and chains of finite coefficient extensions. No assertion
of integral tensor exactness for an arbitrary torsion integral model is made;
the proof passes to a finite-free stable lattice for the rational lisse object.
The point construction never commutes an ordinary pro-étale stalk with a limit.

Searches: `msearch.py` LeanFinder for adic lisse tensor/cohomology and for the
coefficient dual returned light-condensed tensor instances and generic homology
or module-dual facts; Loogle for `Functor.preservesHomologyOfExact` returned
six general exact-functor/homology declarations; `grep` for
`IsAdicLisse|adic.*cohomology|lisse.*dual|Lisse` returned the finite-level
ell-adic site file and unrelated names. LeanSearch returned ordinary module
tensor exactness and duality, not this common-stage calculation. Project and
upstream `rg` searches found the recorded lisse, coefficient-presentation,
t-structure, completed tensor/internal-Hom, and point-sections constructions.
The upstream pro-étale lisse evaluation pairing uses a different coefficient
category and is not an existing match. No declaration states the whole item.

Exact search ledger (2026-10-17):

- LeanFinder: `Cohomology of tensoring an adic constructible derived complex with
  a finite rank lisse l-adic sheaf and its coefficient dual`. Eight hits included
  `CategoryTheory.Sheaf.cohomologyPresheaf`, `CategoryTheory.Sheaf.H`, and the
  `LightCondensed` monoidal/closed instances; no completed-adic calculation.
- Loogle: `CategoryTheory.Functor.preservesHomologyOfExact`. Six hits included
  that theorem, `ShortComplex.quasiIso_iff_evaluation`, the joint-reflection
  criterion for short-complex quasi-isomorphisms, and group (co)homology facts; no adic realization or dual comparison.
- Mathlib grep: `adic.*cohomology|lisse.*dual|Lisse|IsAdicLisse`, restricted to
  `AlgebraicGeometry/`. The ell-adic site finite-coefficient construction was
  found; there was no statement of this common-stage calculation.
- LeanSearch: `Adic constructible cohomology sheaves tensor finite rank lisse
  coefficient sheaf dual`. The returned ordinary module-duality, finite-module
  adic-completion, locally constant condensed, and generic tensor facts do not
  state this node.
- Project/upstream `rg` for lisse realization, dual, integral cohomology,
  completed coefficient transport, common-stage tensor/Hom, and point sections
  located the interfaces discussed above. An exact node-ID upstream grep found
  no existing implementation of this item.
- Final duplicate-name search: `adicCalculus|AdicLisseCohomologyCalculus|
  adic_lisse_cohomology_calculus` over the project, upstream sources, and upstream
  declaration index found no existing declaration with any delivered name.

No statement correction, disputed statement, new DAG node, or replacement of a
dependency declaration is needed. The helpers interpret only the notions already
used in this item and are all listed in `lean.declarations`.

Validation: the normalized-model and calculation records compiled cleanly through
`scompile.py`. The final packet passed repeated per-file compilation with no
errors or warnings and the server preflight (`OK (dry run)`, 207abd430b).
The records separate normalized model data from the comparisons to keep elaboration
within the fixed 60-second per-file limit. No global library build was run.

## Second reading by Q143

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
