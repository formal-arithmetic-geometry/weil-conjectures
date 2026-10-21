## Worker report

The delivery states `AlgebraicGeometry.ProEtale.constructible_exact_scalar_triangulation`
in `Sheaf.AlgebraicGeometry.ConstructibleExactScalarTriangulation`. The sole postponed
proof is this named theorem, with all eight DAG proof steps in its docstring. The two
supporting data declarations are real specializations of existing canonical constructions:
`constructibleScalarExactComparison` is the existing counit-normalized uniqueness
isomorphism, and `constructibleScalarExactCommShift` transports the exact termwise shift
structure along its inverse using `Functor.CommShift.ofIso`. Neither contains `sorry`.
The item's natural-language statement, dependencies and proof are unchanged.

Hypotheses and objects, clause by clause:

- A prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The field Ω is the existing `PadicAlgCl ℓ`;
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)` is exactly a finite intermediate field
  containing `ℚ_[ℓ]`, with its inherited norm topology. No field completeness or other
  coefficient hypothesis is introduced.
- The scheme is `X : Scheme.{u}`, for arbitrary explicit `u`; its underlying-space
  Noetherian hypothesis is `[TopologicalSpace.NoetherianSpace X]`. This does not assume
  scheme-theoretic Noetherianity, separatedness or any base field.
- `padicSubfieldRingObj X ℓ E` and `padicAlgClRingObj X ℓ` are the recorded pullbacks
  from the point of the norm-topology finite-field coefficient and the finite-subfield-valued
  condensed algebraic closure. The latter is not the sheaf of all continuous Ω-valued maps.
  `padicSubfieldRingObjToPadicAlgCl X ℓ E` is the recorded coefficient inclusion.
- `PadicSubfieldConstructible X ℓ E` is the recorded full subcategory of the ordinary
  unbounded derived internal-module category. Its underlying predicate is exactly
  `boundedConstructible (padicSubfieldRingObj X ℓ E)`: bounded cohomology with the recorded
  finite-stratification/local-finite-presentation predicate, with ambient morphisms and no
  completeness condition. The delivered statement does not substitute the discrete
  constant-ring variant also exported by the dependency's module.
- The first conjunct states this predicate's `ObjectProperty.IsTriangulated`. Mathlib's
  full-subcategory `Pretriangulated` instance is the inherited structure, with distinguished
  triangles defined as the inverse image under the inclusion of ambient distinguished
  triangles. Thus this conjunct supplies the stated inherited pretriangulation rather than
  asserting existence of an arbitrary unrelated triangle structure.
- The second conjunct quantifies over every `n : ℤ` and states additivity of the inherited
  `shiftFunctor (PadicSubfieldConstructible X ℓ E) n`. The third states triangulatedness
  of the existing full inclusion `(boundedConstructible ...).ι`.
- Conjuncts four through six state exactly additivity, preservation of finite limits and
  preservation of finite colimits of `Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl ...)`.
  This is the ordinary relative coequalizer tensor extension between the two abelian
  internal-module categories.
- `derivedExtendScalarsToPadicAlgCl X ℓ E` is the recorded total left derived extension.
  The supporting real comparison has this functor as source and the ordinary extension's
  `mapDerivedCategory` as target. That target, by its Mathlib definition and
  `mapDerivedCategoryFactors`, is precisely localization of termwise scalar extension on
  any representing complex, with its canonical integer-shift comparison. The comparison
  is defined by `leftDerivedFunctorIsoMapDerivedCategory`, whose `hom_fac` equation
  normalizes it against the two specified counits; it is not a bare existence of an iso.
- The global `constructibleScalarExactCommShift` is precisely transport along that
  comparison. If `a : T ≅ D(F)`, its hom at `K,n` is
  `a.hom.app (K[n]) ≫ (D(F).commShiftIso n).hom.app K ≫ (a.inv.app K)[n]`.
  It has coherent unit and addition identities by the real `CommShift.ofIso` construction.
- The seventh conjunct is `NatTrans.CommShift` for this canonical comparison's hom;
  the eighth states that `T` with this transported structure is triangulated.
- The ninth states that the composite of the inherited full inclusion with `T` is
  triangulated, using the canonical composite shift structure. The last conjunct states
  `NatTrans.CommShift` for `Functor.isoWhiskerLeft` of the same canonical comparison
  by that inclusion. Its target is exactly the restriction of exact termwise extension,
  so it gives the final canonical shift-compatible identification.
- Every target here is the ambient derived category over Ω. The signature never uses
  `PadicAlgClConstructible` or its triangulation.

Dependency declarations read and used:

- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicSubfieldCondensedRing`, `Profinite.padicAlgClCondensedRing` and their
  underlying continuous-function and finite-subfield-valued ring objects; these are publicly
  reached through the coefficient framework.
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`:
  `AlgebraicGeometry.ProEtale.sfbPullbackFromPoint` (the existing `upperStarFromPoint`).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`:
  `padicSubfieldRingObj`, `padicAlgClRingObj`, `padicSubfieldRingObjToPadicAlgCl`, and
  `CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`:
  `PadicSubfieldConstructible`, `derivedExtendScalarsToPadicAlgCl`.
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale` publicly retains
  `boundedConstructible`, `BoundedConstructible` and `mem_boundedConstructible_iff` from
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`; those original
  general internal-module declarations are the ones used here.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`:
  `CategoryTheory.ObjectProperty.IsTriangulated`, the inherited pretriangulation and
  triangulated full inclusion. `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, the ordinary unbounded localization.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `CategoryTheory.Mod.extendScalars`, its additive structure and extension/restriction
  adjunction. No relative tensor or coefficient inclusion is constructed again.
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact`:
  the recorded exact-left-derived comparison API is publicly imported unchanged. The actual
  recorded coefficient functor is the upstream `leftDerivedFunctor`, so its comparison uses
  `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory`'s
  `CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory`, the same canonical
  uniqueness construction on that functor, rather than replacing the coefficient functor
  by `leftDerivedFunctorFromTotalTensor`. All required structural instances are inherited;
  no new assumption is added to the theorem.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: `mapDerivedCategory`,
  `mapDerivedCategoryFactors`, their integer-shift structures and triangulatedness;
  `Mathlib.CategoryTheory.Shift.CommShift`: `Functor.CommShift.ofIso`.

Recorded proof modules with usable declarations are imported non-publicly when not already
reached by the public dependency imports: `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`,
`Sheaf.Paper.CohomologyInWeakSerreSubcategory`, and
`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`. The proof dependency
`lem-sfb-condensed-coefficient-presentation-identification` has no current Lean declaration;
no proof of it is assumed as a new binder and no non-existent module is imported. This stage
only states the present item, and its proof docstring retains that dependency for stage 3.

Edge cases checked before drafting: empty `X` (zero presentations remain valid), the zero
complex and acyclic representatives, `E = ℚ_ℓ`, all primes including 2, negative shifts and
shift zero. The statement includes all these cases and imposes no boundedness on the ambient
source of `T`. The finite-coefficient constructible source alone has bounded cohomology.
The small-site object universe and morphism universe remain those of `Scheme.{u}.ProEt`,
with coefficients in `Ab.{u+1}`; no site-universe equality is imposed.

Searches (2026-10-21):

- `msearch.py leanfinder`, query: "Bounded constructible finite l-adic coefficient complexes
  inherit triangulation and extension to the condensed algebraic closure is exact triangulated
  termwise". Eight generic results: homological functor exactness, derived triangulation and
  related homology sequences. None states this coefficient-specific combined theorem.
- `msearch.py loogle`, query:
  `CategoryTheory.Functor.mapDerivedCategory, CategoryTheory.ObjectProperty.IsTriangulated`.
  Zero hits.
- `msearch.py leansearch`, query: "Exact scalar extension to condensed algebraic closure on
  bounded constructible derived categories is triangulated". Eight generic results including
  `Functor.instIsTriangulatedDerivedCategoryMapDerivedCategory` and triangulated localization;
  none has the present coefficient and constructibility clauses.
- `msearch.py grep`, query:
  `isTriangulated.*boundedConstructible|leftDerivedFunctorIsoMapDerivedCategory|CommShift.ofIso`.
  Generic transport matches in Mathlib's derived basic module; no complete statement match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `leftDerivedFunctorIsoMapDerivedCategory|constructible.*[Ee]xact.*[Ss]calar|lem-sfb-constructible-exact-scalar-triangulation`:
  found the generic canonical exact-derived comparison and several specializations. The
  upstream-extra TwoColimit module has private `algClDerivedIso`, `algClCommShift` and
  `algClTriangulated`; these private implementation details do not export the node's
  combined statement and cannot be used as its recorded declaration. The current server
  `TwoColimit` source was also read using `scompile.py --source`.
- The item id has no match in the upstream Lean; the three new declaration names have no
  match in upstream, Sheaf, Mathlib or `dag/lean_names_upstream.json`.

No new DAG notion, dependency repair, statement correction or mathematical dispute is needed.

Validation: `scompile.py` compiled both the sandbox and final module successfully, with no
errors or warnings (47.4 s and 37.6 s respectively, each below the 60 s limit). The first
compile diagnosed the missing standard `CategoryTheory.Obj` scope for transported monoid
instances; opening the framework standard scopes fixed it without any new assumptions,
instances for coefficients or changes to the inherited tensor. Only the item's `lean` field
changes; the stored signature is copied verbatim from the final theorem.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
