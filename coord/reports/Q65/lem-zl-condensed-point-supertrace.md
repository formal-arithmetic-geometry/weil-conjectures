## Worker report

The module `Sheaf.Paper.CondensedPointSupertrace` states the entire comparison as
`AlgebraicGeometry.ProEtale.condensed_point_supertrace`. Its conclusion is the
existence of `CondensedPointSupertraceData`. Its six linked components
(`CondensedPointRealizationData`, `CondensedPointScalarData`,
`CondensedPointMatrixData`, `CondensedPointTensorModelData`,
`CondensedPointCohomologyData`, and
`CondensedPointDualityData`) spell out the realization, its matrix description
and every comparison. The tensor matrix and descent equations are separate
Prop-valued definitions asserted in the outer package. All components share
the very same realization and scalar data.
Splitting this large dependent record avoids repeated elaboration of its long
category instances; it changes none of the mathematical clauses. The only postponed proof is this
named theorem. No object or functor is defined by choosing from its existence
proof. No statement correction or dependency repair is required.

Hypotheses and clauses, matched with Lean:

- Prime ℓ is `(l : ℕ) [Fact l.Prime]`. The algebraically closed base is
  `(k : Type u) [Field k] [IsAlgClosed k]`; positive prime characteristic p and
  p ≠ ℓ are `(p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)`.
- The finite subextension inside the fixed algebraic closure is
  `E : PadicAlgCl.FiniteIntermediateField l`. Its carrier is `E.val`, its
  inclusion is `a.val`, and its finiteness instance is part of this existing
  subtype. Ω is exactly `PadicAlgCl l`.
- The point is always `Spec (.of k)`. `PointCondensedModules k l` is an alias for
  internal modules over the recorded `padicAlgClRingObj (Spec (.of k)) l`;
  this is the pullback of `Profinite.padicAlgClRingObj l`, NOT the sheaf of all
  continuous Ω-valued functions. `PointCondensedCategory k l` aliases the
  existing `BoundedConstructible` full subcategory of its ordinary derived
  category. No completeness condition is added.
- The tensor units are `𝟙_ (PointCondensedModules k l)` and the corresponding
  derived/full-subcategory unit. The existing
  `DerivedCategory.singleFunctorObjUnitIso` identifies the former placed in
  degree zero with the latter. `sourceMonoidal`, `targetMonoidal`,
  `sourceTriangulated`, and `targetTriangulated` are CONCLUSIONS in the data
  package, not added assumptions. They equip the existing full subcategories
  with the inherited operations. In particular their tensor is literally the
  ambient derived tensor on underlying objects and morphisms, as in the
  recorded `ObjectProperty.lift` restriction. No replacement tensor is defined.
- `baseScalar` is normalized by `baseScalar_apply` on EVERY section and every
  profinite test point: the resulting function is a·x. This makes it actual
  multiplication by constant Ω-scalars. `scalar_pullback` specifies its actual
  pullback through `upperStarFromPoint`. `subfieldScalar` and
  `coefficient_map_scalar` explicitly commute with the recorded
  `padicSubfieldRingObjToPadicAlgCl`, rather than replacing that coefficient map.
  The latter equality determines subfield multiplication through the canonical
  injective coefficient inclusion.
- `PointSupertraceFrame` contains any bounded finite-dimensional complex with
  any chosen finite basis in each degree. Its finite-support rank allows empty
  bases and all finite bounds, with no fixed interval. `model` and `termIso`
  realize each term as the indicated finite biproduct of regular modules.
  `differential_matrix` fixes EACH matrix entry using the original basis
  coefficient and the specified scalar inclusion.
- `modelMap` and `chain_map_matrix` fix every entry of EVERY chain map, including
  identity maps between different basis choices. `modelIso` and
  `chain_map_descent` identify this construction with `rho` on the actual
  cohomologically defined full subcategory `pointFiniteDimensional E.val`.
  Thus basis changes are the canonical scalar matrices, and they compose by
  functoriality. `quasi_iso` explicitly says that quasi-isomorphisms become
  isomorphisms in the derived target. The domain is not replaced by an
  unquotiented category of finite complexes.
- `rho` is the requested functor, with `braided : rho.Braided` (which includes
  strong monoidality), `additive`, `commShift`, and `exact`. `source_symmetry`
  and `target_symmetry` explicitly record symmetry of the existing Koszul
  braidings. Their instances reuse the existing
  `DerivedCategory.perfectTraceCanonicalBraiding`; they do not choose a
  braiding from a bare Nonempty assertion.
- `tensorModel`, `tensor_matrix`, and `tensor_descent` pin the monoidal
  comparisons on EVERY pure pair of basis labels in every total degree. The
  right-hand coefficient is exactly that of the original total tensor followed
  by the supplied source identification t. The left-unit identification of
  U⊗U with U is explicit. These equations specify the canonical comparisons,
  rather than only the existence of unrelated tensor isomorphisms. The unit
  comparison of the strong monoidal structure identifies ρ(E[0]) with U;
  the tensor normalization and the unit coherence fix its normalization.
- `cohomology_mem` allows the degree-zero cohomology object in the specified
  source full subcategory; `cohomologyIso` states
  Hⁱ(ρC)[0] ≅ ρ(Hⁱ(C)[0]) in the ambient derived category, which is the
  well-typed interpretation of the node's cohomology-module assertion.
- `pointSupertraceSectionRing` is the existing recovered section ring at the
  identity pro-etale object of Spec k. `pointRingIso_apply` normalizes its Ω
  identification by multiplication on the section 1. `pointSupertraceEvaluation`
  is the existing internal/sectionwise equivalence followed by evaluation and
  restriction of scalars along this normalized ring identification.
  `cohomology_evaluation` identifies this actual module with Ω⊗_E Hⁱ(C) as an
  Ω-vector space. This is Hⁱ(C)⊗_E Ω via the canonical swap of tensor factors.
  It does not assert any equivalence of all condensed modules with vector spaces.
- `dual_mem` puts the ACTUAL derived internal Hom `(ihom C.obj).obj (𝟙_ _)`
  into the source full subcategory. `pairing` gives the right dual ρ(RHom(C,E))
  via `ExactPairing`, which contains both triangle identities. Its evaluation
  is fixed by `pairing_evaluation`: apply ρ to the actual internal-Hom
  evaluation with the canonical Koszul swap, then use the specified tensor/unit
  comparisons. Coevaluation is uniquely determined by this evaluation and the
  two triangle identities; thus it is the signed finite-free dual pairing,
  not an arbitrary pairing on the same objects.
- `epsilon` is a ring homomorphism to End of the actual unit, and
  `epsilon_injective` states its injectivity. `epsilon_eq` fixes it to the
  degree-zero derived image of the just-specified scalar multiplication.
- `conjugate_trace` quantifies over every C, every P, every isomorphism
  `w : P ≅ rho.obj C`, and every intertwining pair v,f. The equation
  `v ≫ w.hom = w.hom ≫ rho.map f` is precisely w∘v=ρ(f)∘w in diagrammatic
  composition order. The transported pairing is explicitly fixed on BOTH
  evaluation and coevaluation. Its trace uses the recorded `MonoidalCategory.trace`
  with this right-dual datum. Its value is epsilon applied to the finite-support
  sum `∑ᶠ i, i.negOnePow • LinearMap.trace ... (Hⁱ(f))`, in the actual End(U).
- `unit_trace` states both existence of a right dual of U and
  trace(1_U)=epsilon(1), using the same recorded categorical trace.

The helper colimit, complex tensor and totalization instances apply existing
canonical declarations with fixed parameters. This avoids expensive instance
search; none adds an assumption, selects arbitrary data, or postpones a new theorem.

Dependency declarations read and reused:

- Mathlib `Padic`, `AlgebraicGeometry.Spec`, `LinearMap.trace`, and
  `CategoryTheory.ObjectProperty.lift`/the standard full monoidal subcategory.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, importing the coefficient notion.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`:
  `padicAlgClRingObj`, `padicSubfieldRingObj`,
  `padicSubfieldRingObjToPadicAlgCl`.
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`, together with the
  existing `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`:
  `boundedConstructible`, `BoundedConstructible` and the inherited structures.
- `Sheaf.Paper.PointFdComplexes`: `DerivedCategory.pointFiniteDimensional`.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided`:
  `CategoryTheory.MonoidalCategory.trace`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace`:
  `DerivedCategory.perfectTraceCanonicalBraiding`, already recorded with the
  trace definition used by the existing chain-supertrace proof dependency.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionRingSheaf`, `sectionModuleEquivalence`; and
  `Sheaf.CategoryTheory.InternalSectionTensorComparison`:
  `comparison_internalColimits`, `comparison_internalTotalExists`.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`:
  `monoidalCategoryCochainComplex`; existing `singleFunctorObjUnitIso` and
  derived `Functor.LaxMonoidal.μ` describe localization/unit comparisons.

All recorded proof-dependency modules are imported (proof-only imports are plain
`import`). The theorem docstring supplies the eleven-step natural-language proof:
scalar faithfulness; finite matrices; projective representatives; homotopy descent;
cohomology splitting and constructibility; evaluation; flat total tensor; shifts
and cones; signed duality; matrix supertrace; transport across w.

Edge cases checked before writing: zero rank in every degree and the empty
biproduct; a single E in degree zero; an odd shift (negative supertrace); a
contractible two-term complex (zero cohomology trace); arbitrary basis changes;
identity and arbitrary w; p=2, still with characteristic-zero coefficient field;
and arbitrary base universe u with the small pro-etale site's object universe u+1
and coefficient universe u+1. No equality of distinct site universes is assumed.

Searches before writing:

- `msearch.py ... leanfinder "realization finite dimensional complexes condensed
  coefficients categorical trace supertrace"`: eight hits, including
  `Condensed.finFree`, Lie-module traces and the ordinary linear trace. None
  states this internal-module realization/comparison.
- `msearch.py ... loogle "CategoryTheory.MonoidalCategory.trace, LinearMap.trace"`:
  zero hits; Loogle does not index the project's categorical trace identifier.
  The recorded project trace and Mathlib linear trace were opened directly.
- `msearch.py ... grep "realiz|supertrace" CategoryTheory`: sixteen unrelated
  Mathlib comments/declarations; no comparison theorem.
- `rg` of the item id and point-realization/condensed-supertrace names in the
  upstream WeilConjectures tree and `lean/Sheaf`: no existing theorem for this
  node. Existing `pointFdQbarRealization` concerns ordinary coefficient-stage
  complexes in D(Ω), not internal modules over the specified condensed ring.
- Direct `rg` for `BraidedCategory`, `braiding`, and
  `nonempty_braidedCategory` located the canonical-braiding declaration already
  present in `PerfectCategoricalTrace`; the implementation reuses it.
- Direct declaration-name searches in `dag/lean_names_upstream.json`, upstream
  and `lean/Sheaf` found no collisions for the new owning-node helper names.

No STATEMENT-DISPUTED issue was found.

Validation: the final file passed `scompile.py Q65
lem-zl-condensed-point-supertrace` both as a sandbox module and under its final
library module name, with no errors or warnings. The only sorry is the theorem's
whole proof. The node copy differs from the read-only base only in `lean`; its
main signature and complete declaration list were compared with the file.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
