## Worker report

The module `Sheaf.Algebra.Homology.KoszulRoosProjectionComparison` states
`CategoryTheory.KoszulRoos.koszulRoosProjectionComparison`, with `sorry` as its entire
proof. Its conclusion unfolds through `Conclusion`, `Models`, `Normalization`, and
`Compatibility`. These records package comparison data and its equations; no object
or map is defined by choosing data from a sorried existence assertion. All helper
constructions are actual composites of existing functors and morphisms.

The source read is the whole first paragraph of
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/sk-lem-sp-tower.proof.md`,
and the item's complete thirteen-step proof. The theorem docstring contains all
thirteen steps, including the explicit signs, finite-prefix and constant-tower
contractions, K-flat adjoint roof, and quotient-coherence argument.

Hypotheses and objects:

- The arbitrary scheme is `T : AlgebraicGeometry.Scheme.{t}`. The site is exactly
  `T.ProEt` with `Scheme.ProEt.topology T`, from Mathlib's Proetale module, the
  recorded match for `sk-def-pe-site`. There is no quasi-compactness assumption.
- `R` is an arbitrary sheaf of commutative rings, rather than a constant ring.
  Its coefficient universe is `max z (t + 1)`, containing the site's object
  universe `t+1` and morphism universe `t`. `EssentiallySmall.{t+1} T.ProEt`
  is the inherited site-size convention. The derived-category instance family
  and the tower instance choose localization morphism sizes in `w`.
- The global section is `s : (R.obj ⋙ forget CommRingCat).sections`.
  `_hs : Mono (globalSectionMultiplication R (unitSection R s))` is injectivity
  of multiplication on the unit module sheaf, equivalently sectionwise injectivity.
- Positive indices are represented by predecessors. Thus Lean `m` represents
  paper `m+1`, and tail `h` represents paper `h+1`. `K` is the existing
  `principalKoszul R (unitSection R s) m`, and `B` is the existing sheafified
  `principalPowerRingQuotient R s (m+1)`. `quotient` is its recorded projection.
- `Modules` is a transparent abbreviation for the recorded `ringedSiteModules`.
  `tensor` uses Mathlib's `curriedTensor.map₂CochainComplex`, the total tensor
  construction of `def-pc-tensor-complex-sheaves`. It is written `K_m ⊗ X`,
  identified with the paper's `X ⊗ K_m` by canonical tensor symmetry; the sign
  in `chi_first` explicitly accounts for this order. No new tensor is defined.
- Strict unbounded towers are `CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ`.
  `RF`, `eta`, and `Normalization.universal` give actual total right derived
  inverse limit; `norm` with `norm_unit` fixes its normalized strict Roos
  realization. `Models.projection` is that realization's coordinate projection.
  `scalar m` is the dependency's existing `DerivedChangeOfRingsCochainModel`.

Every conclusion clause:

- `Normalization.exactProducts` asserts exact countable products.
  `products` says that localizing the termwise product cone is a limit cone,
  with the actual localized product projections.
- `tail`, `deletionProduct`, and `delete_coordinates` specify prefix deletion
  on both Roos coordinates. `delete_quasiIso` proves the requested finite-tail
  assertion, `delete_projection` retains each coordinate, and `delete_natural`
  gives strict-map naturality.
- `tensorProduct` is defined by the tensor images of product projections.
  `tensor_product` asserts it is invertible. `chi` is a natural chain isomorphism;
  `chi_first` and `chi_second` specify all total-tensor summands and both Roos
  coordinates. The previous-degree coordinate has sign `(-1)^a` for Koszul
  degree `a`; the current-degree coordinate has no sign.
- `aug_unit` and `aug_zero` pin the augmentation on the degree-zero unit and
  on every other Koszul summand. `A` and `A_kflat` give the natural two-term
  derived-scalar comparison with exactly this augmentation on K-flat models.
- `Models.comparison` is literally the composite of inverse normalized Roos
  realization, inverse `A`, localized `chi`, localized prefix deletion, and
  normalized Roos realization of the remaining tensor tower.
  `Compatibility.isIso` and `natural` make this the requested natural isomorphism.
  `projection` identifies each retained projection with derived scalar extension
  of `p_n`, followed by inverse `A`.
- For paper `h=m`, `Compatibility.adjoint` quantifies over an arbitrary complex
  of `B_m`-modules and a natural transformation from the extended tail to its
  constant tower. This is exactly a strict compatible family of `B_m`-linear
  chain maps, with no K-flatness imposed on the original tower or the target.
  `Models.familyMap` is the strict augmentation followed by that family. The
  left-hand side is the stated derived-limit composite. The right-hand side is
  restriction of the derived adjoint of `p_m` followed by the ordinary adjunct
  of `f_m`. `ordinary_unit` fixes `x ↦ 1 ⊗ x`, and `derived_adjunction` fixes
  the derived adjunction by its K-flat counit, rather than an arbitrary adjunction.
- `constant_identification` supplies evaluation inverse to the actual diagonal,
  pins that diagonal by both Roos coordinates, and gives both inverse identities.
  `Normalization.reflects` asserts precisely that derived scalar restriction
  detects isomorphisms, without a faithfulness or fullness assertion.
- `koszul_transition` identifies the existing power-tower map with the cone map
  having degree `-1` component `t^(m-k)` and degree-zero component the identity.
  `coefficients` supplies the coefficient quotient map characterized by the
  quotient projections, the ordinary transition characterized on pure tensors,
  the derived transition normalized on K-flat models, and the augmentation,
  two-term-comparison, and full derived-limit comparison squares. Its tail `h`
  is arbitrary, so it includes comparison on the maximum of two chosen tails.
- `bounded` quantifies over all integral endpoints `a,b` and all tower levels,
  with vanishing outside `[a,b]`, and concludes vanishing for `RF(X)` outside
  `[a,b+1]`. It uses `IsZero` in the actual module-sheaf category and has no
  quasi-compactness or boundedness condition on complexes as chain objects.

Dependency declarations used, with recorded modules read:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
  The normalized universal presentation uses ordinary limits in complexes,
  canonically the termwise-limit presentation of that dependency.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  the actual functorial totalization is `Functor.map₂CochainComplex`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, through `restrictedTensorScalars` from
  `Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification`.
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`:
  `Adjunction.exists_derived_adjunction_of_essentially_constant` (proof import).
- `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`:
  `principalKoszul`, `principalKoszulTower`, `globalSectionMultiplication`,
  `koszulRepresentativeAugmentation`, `koszulTowerComplex`, `koszulTowerComplexMap`.
- `Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients`:
  `principalPowerRingQuotient`, `principalPowerRingProjection`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` supplies the
  existing tensor and its size-independent total-tensor infrastructure.
- `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosP`, `roosχ`,
  `roosEval`, `roosι`, and `roosLimitFunctor`.

All already stated proof dependency modules are imported. The four Mathlib proof
leaves are available through HomologySequence, ExactFunctor, and the triangulated
imports. `lem-cbc-regular-quotient-cone-augmentation` has no usable recorded Lean
module on the read base; its mathematical proof is retained in the main docstring,
without inventing a private definition of derived scalar extension.

Searches actually run:

- `msearch.py ... leanfinder "Koszul complex tensor with homotopy inverse limit Roos complex preserves projections and derived scalar adjunction"`:
  eight hits, including `HomologicalComplex.unit_tensor_d₁`; no full match.
- `msearch.py ... loogle "CochainComplex.mapBifunctor, SheafOfModules.restrictScalars"`:
  zero hits for the combined query.
- `msearch.py ... grep "[Rr]oos|[Kk]oszul" Algebra/Homology`:
  one hit in `Mathlib/Algebra/Homology/LocalCohomology.lean`, not this statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item ID and
  `Koszul.*Roos|Roos.*Koszul|koszul.*roos|roos.*koszul`: no exact theorem;
  found existing completed-adic comparison statements, which require constant
  complete coefficient data and do not state this arbitrary ring-sheaf lemma.
- Further source/DAG searches found the principal-power quotient, principal
  Koszul tower, strict Roos model, and independent-size tensor/restriction APIs
  used above. Their five already landed node IDs are added to `stmt_deps`.

Edge cases checked before and during the statement audit: paper `h=1` is Lean
`h=0`, giving empty-prefix deletion; paper `m=1` is Lean `m=0`; equal coefficient
indices give exponent zero and identity components; a unit section makes all
quotients zero and Koszul complexes contractible; the zero ring is admitted;
constant and zero-transition towers are admitted; the empty scheme is admitted;
`a=b` allows the usual one-degree gain, and `a>b` imposes vanishing on every
level. No finiteness, Noetherian, completeness, torsion, or K-flatness hypothesis
was added to the input tower. The size of coefficients can exceed the site's
object size. No statement correction and no mathematical dispute were found.

## Second reading by Q128

I reread the full node against the final definitions, its theorem, and every
normalization field. The dispatcher explicitly prohibits starting another agent;
this is a separate self-audit, not a claim of an independent worker review.
The maintainer's independent delivery review remains the independent check.

This reading checked all clauses listed above. It corrected an initially shadowed
module variable in `ordinary_unit`, made the Roos degree transports explicit,
added the pure-tensor characterization of coefficient transitions, and verified
that the adjoint equality uses the whole strict Roos map. It also checked that
`Conclusion` asserts existence of ring sheafification inside its definition,
rather than adding that available structure as a mathematical hypothesis.
Importing the general small-site sheafification infrastructure increased
elaboration time throughout the module; packaging its existence avoids that
import and keeps the compile under the prescribed limit.
The helper data and proof fields are separate records to avoid expensive Lean
structure projection generation; this does not change any proposition.
