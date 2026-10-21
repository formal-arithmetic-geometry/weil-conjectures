## Worker report

The module `Sheaf.Paper.ProperIntegralRationalScalarComparison` states
`AlgebraicGeometry.ProEtale.CondensedRing.properIntegralRationalScalarComparison_isIso`.
The theorem has exactly one postponed proof (`sorry`). Its four helper declarations
are constructions or transparent aliases belonging to this same canonical comparison;
none supplies arbitrary data, an existential comparison, or a new coefficient notion.
The copied node changes only in `lean`; its statement, proof, and dependencies are unchanged.

Clause-by-clause reading:

- Prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Finite extensions in the fixed algebraic closure are
  `{F E : PadicAlgCl.FiniteIntermediateField ℓ}`. Their inclusion is `(i : F ≤ E)`.
  These are the existing finite intermediate fields in `PadicAlgCl ℓ`, with the
  induced norm topologies, including equality F = E.
- A = O_F is the existing `Profinite.padicIntegersRingObj ℓ F.1` and Lambda = E is
  `Profinite.continuousMapRingObj E.1`. These are continuous functions into the actual
  norm-topological rings. In particular, no finite-subextension-valued algebraic-closure
  ring and no discrete topology has been substituted.
- The coefficient inclusion is `integralRationalCoefficientMap ℓ i`, literally the
  composite of the published O_F → F and F → E condensed ring homomorphisms.
  `coefficientMap ... W` pulls it back by `upperStarFromPoint W`, so the ring objects
  are exactly A_W = p_W^* A and E_W = p_W^* E.
- The schemes and morphism are `{U V : Scheme.{u}} (h : U ⟶ V)`. Properness is
  `[IsProper h]`, Mathlib's definition recorded by the proper-morphism dependency.
  The four `CompactSpace` and `QuasiSeparatedSpace` binders say that U and V are qcqs.
  They impose no separatedness over a field or finite-presentation condition.
- The ordinary ambient unbounded module-object categories are `DerivedCategory
  (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj ... W))`.
  Pushforward and pullback use exactly the dependency's
  `moduleObjectDerivedPushforward` and `moduleObjectDerivedPullback`.
- `integralRationalScalarExtension ℓ i W` is an abbreviation for the existing total
  left derived `Mod.extendScalars` along that pulled-back inclusion, hence T_W.
  No completion or bounded derived category replaces this ambient category.
- The input `(J : ConstantModelConstructibleFiniteTor
  (Profinite.padicIntegersRingObj ℓ F.1) U)` uses the recorded definition of Dctf:
  bounded cohomology with finite constant scalar models, and finite Tor amplitude.
  The ambient object used in the conclusion is `J.obj`.
- `properIntegralRationalScalarComparison ℓ i h J.obj` has exactly source
  T_V (Rh_{*,A} J) and target Rh_{*,E} (T_U J).
- The comparison is real data. Its body applies `.homEquiv _ _` of the specified
  `derivedUpperStarLowerStarAdjunction` at E to
  `(integralRationalScalarPullIso ℓ i h).inv.app (Rh_{*,A} J)` followed by
  `T_U.map` of `.counit.app J` of that same published adjunction at A. Thus the
  displayed counit in the node, including its orientation, is part of the definition.
- The scalar/pullback comparison uses the existing `derivedPullIso`. This is the
  canonical conjugate of `derivedComapLowerStarIso`, whose underived restriction
  square is identity on underlying sections. Equivalently, by the adjunction
  triangle identities it is the scalar-adjunction mate of the action square.
  `kflat_scalar_comparison_normalization` identifies that mate with the inverse
  balanced comparison; `internal_module_operations_transport`,
  `sectionDerivedPushpullNormalization`, and `internal_section_scalar_adjunction`
  preserve these adjunctions, units, counits, and balanced generators. This is the
  specified comparison, with no free choice or scalar twist. The named K-flat and
  internal transport dependency modules are publicly imported.
- The published `derivedPullIso` interface requires exact scalar extension. Its
  structural argument is constructed within the helper: `padicIntegers_invertEll`
  gives exactness for O_F → F; `cartesianCoefficients_finiteFree` gives exactness
  for F → E; `Mod.extendScalarsComp` and `coefficientMap_comp` transport exactness
  of the composite to the direct map. These are proof fields, not additional
  hypotheses or choices of a coefficient object. The proof uses no boundedness
  of Rh_*J to construct the map.
- The conclusion `IsIso (...)` says precisely that this morphism is an isomorphism.
  There are no geometric base-change, Noetherian, characteristic, dimension or
  ell-invertibility assumptions or conclusions. The sentence excluding the
  algebraic-closure extrapolation is scope information, not an extra theorem.
- The size convention is represented by the explicit universe `u`, the actual
  small pro-etale site (object universe u+1, Hom universe u), and Ab.{u+1}.
  Derived categories use the published module-object instances. No equality of
  independent site universes has been imposed.

Dependency declarations read and used (the first eight entries are stmt_deps):

1. `Sheaf.Paper.CondensedConstantConstructibility`:
   `AlgebraicGeometry.ProEtale.ConstantModelConstructibleFiniteTor`, together with
   `IsConstantModelConstructible`, finite constant local models and the bounded
   constructible predicate.
2. `Sheaf.Paper.CondensedModuleDerivedPushpull`:
   `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`,
   `moduleObjectDerivedPullback`; its public upstream interface provides
   `derivedUpperStarLowerStarAdjunction`.
3. `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
   `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`, whose finite field
   and integer-ring branches use the exact same coefficient objects as this file.
4. `def-weil-size-convention` is a metatheoretic convention with no Lean declaration;
   explicit universe levels implement it as its recorded `lean.note` directs.
5. `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public imports:
   `Padic.coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`, and
   `finite_coefficientExtensionRing`; finite subfields with the induced norm give
   the same valuation-ring notion used by `Profinite.padicIntegersRingObj`.
6. `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
   extending `IsSeparated`, `UniversallyClosed`, `LocallyOfFiniteType`.
7. `Sheaf.Paper.KFlatScalarComparisonNormalization`:
   `SheafOfModules.ScalarPullback.θ_h` and
   `kflat_scalar_comparison_normalization`, with its full balanced-generator,
   ordinary-unit, K-flat-representative and invertibility clauses.
8. `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`:
   `AlgebraicGeometry.ProEtale.InternalModuleOperations.equivalence`,
   `upperComparison`, `lowerComparison`, `adjunction`, and
   `internal_module_operations_transport`, including the unit/counit identities.

All recorded proof dependency modules are imported. Their relevant declarations are
`cartesianCoefficients_finiteFree` (also needed by the construction),
`ModuleRingedComparison.sectionDerivedPushpullNormalization`,
`CategoryTheory.Mod.sheaf_finiteFreeScalarCoordinates`,
`CategoryTheory.InternalAbelianSheafModule.internal_section_scalar_adjunction`,
`Padic.exists_integral_basis`, `localizedDirectImageComparison_isIso`,
`CategoryTheory.pasted_mates_counit_normalization`,
`AlgebraicGeometry.Scheme.proEtaleRingSheafChangeAdjunction`,
`SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
and `AlgebraicGeometry.proper_basic`. The theorem docstring carries all five proof
steps of the node, naming the inputs and explaining the two coefficient factors
and their identification with the specified counit mate.

Edge cases checked before drafting and again against the signature: F = E (degree-one
second extension), J = 0, empty U or V when a morphism exists, h an identity,
ramified E/F, schemes of characteristic ell, non-Noetherian qcqs schemes, and
unbounded Rh_*J. No binder excludes any of these. Dctf remains the given input
condition; it was not replaced with a chosen K-flat representative or extra resolution.
The finite-extension statement agrees with the node's already reviewed correction.
No new STATEMENT-DISPUTED claim is made about it. The historical split-report dispute
concerns only the excluded all-continuous algebraic-closure extrapolation.

Searches for reuse:

- `msearch.py ... leanfinder "Extension of integral ell adic coefficients to a finite
  rational local field commutes with proper derived pushforward of constructible complexes"`:
  eight unrelated p-adic completion/perfectoid hits, beginning with `BDeRhamPlus`;
  none is this comparison theorem.
- `msearch.py ... loogle '"derivedPushHom", "IsProper"'`: zero hits.
- `msearch.py ... grep 'proper.*scalar|scalar.*proper|projectionFormula'`: fifteen
  Mathlib hits concerning scalar algebra and topology; no derived coefficient theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for integral/rational and proper/scalar
  comparisons found the usable general `derivedPullIso`, `derivedPushHom`, and the
  special O_F → F `localizedDirectImageComparison`. No theorem for O_F → E on Dctf
  was present. The section-ring `integralRationalCoefficientMap` in
  `ContinuousCoefficientPullback.lean` is in a different namespace and concerns the
  single-field section-ring realization; our condensed point map is the composite
  of existing maps, not a replacement for that definition.
- `rg` for the five proposed full-name suffixes in the source/project and
  `dag/lean_names_upstream.json` found no collision with their full namespace.
  `grep -rn` for this item id in `lean/WeilConjectures` found no upstream attachment.

Validation: every compile used the prescribed `scompile.py`, on this one delivered file.
The sandbox and actual library module were both checked. Initial line-continuation
syntax errors were repaired; a 100-character style warning was then repaired.
Final dry-run and delivery outcomes are recorded below.

## Second reading by Q26

Reopened the node and completed module and read the displayed source and target,
all theorem binders, the inverse pullback comparison, and the adjunction counit in
order. Checked that the field supplying O_F is F, the rational target is E, and the
inclusion runs F ≤ E, rather than accidentally rationalizing E's own integer ring.
Checked that `.inv.app` has source h_E^* T_V Rh_{*,A}J and that the following
`T_U.map (counit.app J)` lands in T_U J before transposition. Checked all four qcqs
scheme hypotheses, properness, the actual constant-model Dctf dependency, and that
no extra flatness hypothesis leaked from the published comparison interface.
No mathematical mismatch found. Line splitting was the only final source change.
This is a second pass by the same dispatcher worker; the explicit instruction not
to start other agents was followed. The maintainer's independent delivery review
remains the independent reading required by the dispatch brief.
