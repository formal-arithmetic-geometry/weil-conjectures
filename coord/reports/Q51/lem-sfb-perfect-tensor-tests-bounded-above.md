## Worker report

Module: `Sheaf.AlgebraicGeometry.PerfectTensorTestsBoundedAbove`.
Declaration: `AlgebraicGeometry.isBoundedAbove_of_perfect_tensor_tests`.
This states the assigned node, with `sorry` as its only proof. It introduces no definitions.

Source read: `literature/stacks-project/perfect.tex`,
`proposition-detecting-bounded-above` (Tag 0GEN), especially condition (7)(b),
condition (1), and the affine-open-induction proof, lines 10500 onward.
The source equivalence implies exactly this all-perfect-test consequence; the chosen
perfect generator used to state other conditions is not data required by this implication.
The accepted node statement and proof are unchanged.

Clause-by-clause reading:

- A scheme X: `(X : Scheme.{u})`, using Mathlib's actual locally ringed-space scheme.
- Quasi-compact: `[CompactSpace X]`. This is compactness of the underlying topological
  space, with no Hausdorff or separation condition implicit in `CompactSpace`.
- Quasi-separated: `[QuasiSeparatedSpace X]`, the standard absolute scheme convention
  whose affine-open-intersection formulation is in Mathlib's QuasiSeparated module.
- K belongs to D_QCoh(O_X): `(K : schemeDerivedCategory X)` with
  `(hK : schemeDerivedQCohProperty X K)`. The latter requires every integer-degree
  cohomology sheaf to be quasi-coherent; K is not assumed bounded in either direction.
- Every perfect object P in all of D(O_X):
  `∀ P : schemeDerivedCategory X, Scheme.IsPerfect X P → ...`.
  The predicate uses actual local strictly-perfect representatives. The quantifier is
  not restricted to a chosen generator or an arbitrary collection of test objects.
- There is an integer b_P for each P: `∃ bP : ℤ` occurs inside the preceding universal
  quantifier and after the perfectness hypothesis. Thus bounds can depend on P.
- For every i > b_P: `∀ i : ℤ, bP < i → ...`, with strict inequality, and all integers.
- Tensor: `(P ⊗ K)` uses the global `schemeDerivedTensorMonoidal X` instance,
  computed by the recorded K-flat construction. No additional tensor structure is bound.
- RΓ: `(schemeDerivedGlobalSections X).obj (P ⊗ K)`, the existing unbounded derived
  section functor with values in D(Γ(X,O_X)), computed by K-injective resolutions.
- Vanishing of its degree-i cohomology: `IsZero` of the degree-i
  `DerivedCategory.homologyFunctor` in `ModuleCat` of the actual global section ring.
  Vanishing as a module is precisely vanishing of its underlying abelian group.
- Conclusion: `∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ...` of the cohomology sheaf of K,
  using `DerivedCategory.homologyFunctor` on the shared O_X-module category.
  This is one global upper cohomological bound, with no added lower bound or finiteness.
- The `HasDerivedCategory` binders supply the shared localization constructions for
  O_X-modules, localized open-site modules (required by recorded perfectness), and
  global-section modules. Their hom universes `wX` and `wΓ` are independent. They impose
  no geometric or boundedness hypothesis. Every variable and universe is explicitly
  bound, and `set_option autoImplicit false` enforces this.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, `AlgebraicGeometry.schemeDerivedQCohProperty`.
- `def-pc-morphism-conventions` is explicitly a convention node (no declaration);
  the absolute qcqs notions use Mathlib's `CompactSpace` and `QuasiSeparatedSpace`,
  with the scheme criterion in `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `WeilConjectures.AlgebraicGeometry.PerfectComplex`:
  `AlgebraicGeometry.Scheme.IsPerfect`, with `Scheme.IsStrictlyPerfect` in its definition.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage` and `schemeHigherDirectImage` are the
  recorded direct-image framework; the sections specialization is supplied by the
  next node rather than by a new definition.
- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  `AlgebraicGeometry.schemeDerivedTensorMonoidal`, the global derived tensor instance.
- `WeilConjectures.AlgebraicGeometry.GlobalDerivedHom`:
  `AlgebraicGeometry.schemeDerivedGlobalSections`. Its owning, already-stated node
  `def-pc-global-derived-rhom` was added to `stmt_deps` under the permission to add landed
  nodes. It was already a proof dependency. No new or repaired dependency module is needed.

The theorem docstring records all eight steps of the node's proof and their dependencies.
All recorded statement modules and stated proof dependency modules are imported. Proof-only
imports are non-public. The complete proof dependency module list read from the node records:

- `def-pc-derived-pullback`: `WeilConjectures.AlgebraicGeometry.DerivedPullback`, `AlgebraicGeometry.derivedPullback`.
- `def-pc-global-derived-rhom`: `WeilConjectures.AlgebraicGeometry.GlobalDerivedHom`, `AlgebraicGeometry.schemeGlobalDerivedHom`.
- `def-pc-perfect-complex`: `WeilConjectures.AlgebraicGeometry.PerfectComplex`, `AlgebraicGeometry.Scheme.IsPerfect`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`, `CategoryTheory.ordinaryModuleDerivedInternalHom`.
- `lem-pc-affine-koszul-geometric-properties`: `WeilConjectures.AlgebraicGeometry.AffineKoszulGeometricProperties`, `AlgebraicGeometry.affine_koszul_geometric_properties`.
- `lem-pc-affine-qcoh-derived-equivalence`: `WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence`, `AlgebraicGeometry.exists_affineQCohDerivedEquivalence`.
- `lem-pc-derived-direct-image-preserves-qcoh`: `WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`, `AlgebraicGeometry.schemeDerivedDirectImage_preserves_QCoh`.
- `lem-pc-derived-direct-image-uniform-truncation-bound`: `WeilConjectures.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound`, `AlgebraicGeometry.exists_schemeDerivedDirectImage_uniform_truncation_bound`.
- `lem-pc-derived-open-unit-restriction-iso`: `WeilConjectures.AlgebraicGeometry.DerivedOpenUnitRestrictionIso`, `AlgebraicGeometry.derived_open_unit_restriction_isIso`.
- `lem-pc-open-immersion-restriction-derived-properties`: `WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties`, `AlgebraicGeometry.openImmersion_restriction_derived_properties`.
- `lem-pc-perfect-rhom-tensor-comparison`: `WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparison`, `AlgebraicGeometry.perfect_rhom_tensor_comparison`.
- `lem-pc-restrict-derived-direct-image-open`: `WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction`, `AlgebraicGeometry.schemeDerivedDirectImage_openRestriction`.
- `lem-pc-ringed-spaces-derived-adjoint`: `WeilConjectures.AlgebraicGeometry.DerivedAdjoint`, `AlgebraicGeometry.nonempty_derivedPullbackAdjunction`.
- `lem-pc-supported-open-pushforward`: `WeilConjectures.AlgebraicGeometry.SupportedOpenPushforward`, `AlgebraicGeometry.Scheme.supported_open_pushforward`.
- `lem-pc-supported-qcoh-triangulated`: `WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated`, `AlgebraicGeometry.supported_qcoh_isTriangulated`.
- `lem-sc-derived-internal-hom-adjunction`: `WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction`, `AlgebraicGeometry.scheme_derivedInternalHom_adjunction`.
- `lem-sc-derived-open-restriction-adjunction-exact`: `WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact`, `AlgebraicGeometry.open_restriction_adjunction_exact`.
- `lem-sc-derived-open-shriek-derived-adjunction`: `WeilConjectures.Algebra.Homology.DerivedOpenShriekAdjunction`, `AlgebraicGeometry.derived_open_shriek_adjunction`.
- `lem-sc-invert-s-cohomology-induction`: `WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction`, `AlgebraicGeometry.quasiCompactOpen_induction`.
- `lem-sc-perfect-ext-bounded-qcoh-vanishing`: `WeilConjectures.AlgebraicGeometry.PerfectHomGap`, `AlgebraicGeometry.Scheme.exists_subsingleton_hom_of_isPerfect`.
- `lem-sc-perfect-support-map-lift`: `WeilConjectures.AlgebraicGeometry.PerfectSupportedMapLift`, `AlgebraicGeometry.Scheme.exists_perfect_supported_map_lift`.
- `lem-sc-restricted-global-hom-shifted-equiv`: `WeilConjectures.AlgebraicGeometry.RestrictedGlobalHomShiftedEquiv`, `AlgebraicGeometry.restrictedGlobalHom_shiftedHom_equiv`.
- `lem-sf-derived-homology-long-exact`: `Mathlib/Algebra/Homology/DerivedCategory/HomologySequence.lean`, `DerivedCategory.HomologySequence.exact₂`.
- `lem-sfb-affine-koszul-upper-localization`: `Sheaf.AlgebraicGeometry.AffineKoszulUpperLocalization`, `AlgebraicGeometry.affine_koszul_upper_localization`.
- `lem-weil-pbc-hom-into-triangle-exact`: `Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean`, `CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂`.
- `lem-weil-pbc-open-immersion-module-pullback-restriction`: `Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction`, `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoTensorPullback_unit`.
- `lem-weil-pbc-qcqs-finite-affine-open-cover`: `Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean`, `AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens`.
- `lem-weil-pbc-qcqs-morphism-permanence`: `Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean`, `AlgebraicGeometry.quasiCompact_of_compactSpace, AlgebraicGeometry.QuasiSeparated.of_quasiSeparatedSpace, AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace, AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated, quasiCompact_isStableUnderBaseChange, quasiSeparated_isStableUnderBaseChange, locallyOfFinitePresentation_isStableUnderBaseChange`.
- `lem-weil-pbc-quasi-separated-affine-cover-criterion`: `Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean`, `AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens, AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isOpenCover`.
- `new-affine-derived-tilde-homology-comparison`: `WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison`, `AlgebraicGeometry.affineDerivedTilde_homology_comparison`.

Edge cases checked before writing:

- The empty scheme is allowed; its sheaf category is zero, so every cohomology sheaf
  vanishes. Neither a point nor a nonempty affine cover is bound in the statement.
- K = 0 satisfies the tests and conclusion. P = 0 is allowed among the perfect tests
  and imposes no extra constraint.
- On an affine scheme, P = O_X[0] detects the eventual vanishing of the cohomology
  modules of K, as in the source affine case.
- Bounds can be negative; integer shifts do not get excluded by a natural-number bound.
  The vanishing clause omits i = bP (respectively i = b), as the node requires.
- For a perfect P shifted by any integer the bound can change. No uniform bound is
  hidden outside the quantifier. There is no Noetherian, separated, proper, finite-type,
  characteristic, or additional quasi-coherence assumption on the test objects.
- K can have nonzero cohomology arbitrarily far below zero: only an upper bound follows.

Searches actually run for this assignment:

1. `msearch.py ... leanfinder` with query
   "On a quasi compact quasi separated scheme perfect tensor cohomology tests detect
   bounded above quasi coherent complexes": 8 hits, generic derived t-structure lemmas
   (`DerivedCategory.isGE_iff`, `isLE_iff`, `IsGE`, `isGE_Q_obj_iff`,
   `exists_iso_Q_obj_of_isGE`, and related instances) and a condensed-module abelian
   instance. None states this qcqs perfect-tensor detection theorem.
2. `msearch.py ... loogle` with query `"IsPerfect", "IsLE"`: 0 hits.
3. `msearch.py ... grep` with regex `perfect.*[Bb]ound|[Bb]ound.*perfect` in
   `AlgebraicGeometry`: 0 Mathlib hits.
4. `msearch.py ... leansearch` with query
   "If all perfect tensor derived global sections on a qcqs scheme are bounded above
   then the quasi coherent complex is bounded above": 8 hits, generic derived
   fractions, Ext/t-structure lemmas and quasi-coherent-data declarations. No exact match.
5. `rg` in the project's `WeilConjectures` and `Sheaf` sources for derived global
   sections and perfect/bounded tensor combinations located the existing
   `GlobalDerivedHom.lean` section functor and the consumer
   `PerfectTestsDetectPseudoCoherence.lean`. Related perfect-tensor bounded-coherent
   and relative Tor bounds do not assert the present detection theorem.
6. `grep -rn "lem-sfb-perfect-tensor-tests-bounded-above" lean/WeilConjectures`:
   no hits. A corresponding source search in `lean/Sheaf` found only the consumer's
   proof-docstring citation, not a declaration for this node.
7. `rg` for `isBoundedAbove_of_perfect_tensor_tests` in Mathlib, WeilConjectures,
   Sheaf and `dag/lean_names_upstream.json`: no existing declaration with this name.
   The upstream-name index also has no `schemeDerivedGlobalSections` entry; reading
   the actual module and the node's recorded declarations supplied the canonical functor.

No statement correction or STATEMENT-DISPUTED flag is needed. No new nodes are introduced.

Validation: `scompile.py Q51 lem-sfb-perfect-tensor-tests-bounded-above` compiled the
single delivered module in sandbox and library form with no errors or unexpected warnings
(4.8 s and 6.5 s). The only postponed proof is the assigned theorem.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
