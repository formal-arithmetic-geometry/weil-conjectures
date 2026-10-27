## Worker report

Item: `lem-pd-section-derived-representative-square`, group Q154, stage 2.
Module: `Sheaf.Paper.SectionDerivedRepresentativeSquare`.
Main declaration:
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.DerivedRepresentativeSquare.section_derived_representative_square`.

The delivery states the specified-map representative square, unit, naturality,
inverse-denominator compatibility and the two paths of each constraint diagram.
The theorem has `sorry` as its entire proof. All fifteen helper definitions contain
actual composites or fully expanded propositions; none has postponed data or a
new arbitrary map. Every helper belongs to this node and is recorded in
`lean.declarations`. No statement correction, dependency replacement or new node
is required. The repository and library were read only; sandbox compilation and
delivery use the prescribed wrappers.

Hypotheses and clauses, checked with the node and Lean source open:

- An arbitrary commutative condensed ring is the explicit
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `MonObj Λ` and
  `IsCommMonObj Λ`. This is the unbundled presentation underlying the recorded
  `Profinite.CondensedRing`, not a restriction to topological coefficient rings.
- The schemes and morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`. There is no
  smoothness, properness, nonemptiness or flatness assumption on `f` or Λ.
- `modules Λ T`, `ring Λ T`, `internalModules Λ T`, `equivalence Λ T` and
  `pullback Λ f` are the exact operations of SectionModuleOperationsData. Thus
  the site is `Scheme.ProEt.topology T`, its ring is the reconstructed section
  ring of `condensedRingObj Λ T`, and E is `sectionModuleEquivalence`.
  The site object universe is u+1, Hom universe u, and coefficient/module
  section universe u+1. None is identified with u.
- The binder `∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)` is
  the existing chosen derived-localization size convention of the dependency
  interfaces, not a new mathematical finiteness hypothesis.
- `CochainComplex ... ℤ`, the existing cochain monoidal tensor `⊗`,
  `totalSectionPull`, `qTensor`, and `tensor` retain the signed direct-sum
  totalization and the relative derived tensor over the pulled-back ring.
  `DerivedCategory.Q` is the composite complex localization; it is the same
  q in the node evaluated after the homotopy quotient.
- Resolving membership is exactly the existing
  `KFlatSectionComparison.sectionResolving Λ Y`, whose definition specializes
  `TensorFlatRepresentative`: `IsKFlatIndependentCoefficients` together with
  `∀ i : ℤ, IsFlatOnSite ... (P.X i)`. The full-subcategory objects in the
  theorem therefore introduce precisely P,Q in the node's resolving class.
- LF is the specified `derivedPullback Λ f`; its epsilon is
  `(pullback Λ f).mapDerivedCategoryFactors.hom.app A`, since this particular
  coefficient pullback is exact. The node asks for this specified LF and does
  not quantify over an additional arbitrary derived functor.
- Gamma is `derivedPullComparison`, theta is `tensorComparison`, and the
  fixed equivalence unit/counit is `derivedEquivalence`. `actualTensor` first
  passes M,N to their fixed internal preimages by the equivalence counit,
  reverses theta_Y and gamma, applies the actual `internalDelta`, then theta_X
  and gamma on the factors and the counit back. Its source is LF(M tensor N)
  and target LF(M) tensor LF(N), exactly as in the node. It never mentions
  `tensorPullComparison` or `TensorPullRepresentativeCondition`.
- `input` is LF(qTensor_Y) followed by epsilon at P tensor Q. By
  `TensorRepresentativeCondition` and the representative normalization of
  `section_kflat_tensor_comparison`, qTensor is the inverse r on resolving
  pairs. `NativeComparisonCondition` identifies it with the fixed ringed
  site descent comparison, rather than an independently chosen iso. Thus
  `input` is exactly a in the node.
- `output` is tensor(epsilon_P,epsilon_Q) followed by qTensor_X on FP,FQ,
  hence exactly c. The theorem asserts both `IsIso (input ...)` and
  `IsIso (output ...)` for every resolving pair; invertibility is a conclusion,
  not an extra assumption or an implicit typeclass used to define the maps.
- The square is `actualPath ... = cochainPath ...`, where the former is
  `actualTensor ... ≫ output ...` and the latter is
  `input ... ≫ DerivedCategory.Q.map (sectionTotalIso ...).hom`.
  Composition is left to right in Lean. The common source is
  LF(qP tensor qQ); the common target is q(FP tensor FQ). The cochain map is
  the fixed b from the existing total oplax comparison.
- `Naturality` writes the naturality equation for this same actual path under
  arbitrary maps a and b of resolving complexes. The square identifies the
  cochain path with it, so it asserts naturality of the equality, not just
  existence of some natural family.
- `InverseNaturality` states the same naturality equation with localized
  inverse maps s,t and the inverse v of the pulled-back total map. It
  quantifies the inverses with both defining inverse equations, which uniquely
  determine them; no arbitrary replacement comparison is assumed. QuasiIso
  hypotheses are precisely the denominators being inverted. The usual
  localization and K-flat tensor/pullback preservation give existence of
  these inverses. Identity maps include inversion in either variable alone;
  ordinary naturality and this inverse formula include composites of roofs.
- `regular` is e, namely kappa at the internal regular degree-zero complex
  followed by localization of `totalUnitComparison`. `actualUnit` is obtained
  from LF(e_Y inverse), gamma inverse, the actual internal
  `leftDerivedUpperStarUnitIso`, then e_X. The unit conjunct says exactly
  `actualUnit = epsilon_regular ≫ Q.map (sectionTotalUnit ...)`.
- `AssociatorNormalization` has two conjuncts for each resolving triple.
  The first actual derived path uses the transported source associator then
  the two actual tensor arrows; the second uses those arrows in the other
  order then the transported target associator. Each is followed by the
  same `tripleOutput` and equated to `tripleInput` followed by Q of the
  corresponding actual cochain path in SectionTotalNormalization.
  `tripleInput` and `tripleOutput` iterate precisely qTensor and epsilon
  from a,c. Nested total tensors are allowed by the cited K-flat-total tool.
- `UnitorNormalization` gives four equalities, one for each of the two
  paths of each unitor diagram. `regularLeftUnitor` and
  `regularRightUnitor` replace the transported unit with the regular
  degree-zero representative using exactly e. The actual tensor/unit path
  and the direct derived-unitor path both become the corresponding localized
  cochain paths through `input` and epsilon_P. Their equality is the ordinary
  cochain unitor equation already recorded by SectionTotalNormalization.
- No equality with the independent ringed derived tensor-pullback map is a
  hypothesis or a definition. All map constructors precede the single theorem
  and are independent of its representative equality.

Dependency declarations used, with the recorded module names:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj` in `AlgebraicGeometry.ProEtale`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`.
- `Sheaf.Paper.SectionModuleOperationsData`: `modules`, `ring`, `equivalence`,
  `internalModules`, `pullback`, all in ModuleRingedComparison.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`, `Qh`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` and its
  public Tensor import: `CondensedRing.derivedTensor` and `derivedHom`.
- `Sheaf.Paper.SectionDerivedRealization`: `internalDelta`, `qTensor`,
  `derivedPullComparison`; its SectionDerivedTensorData import provides
  `derivedEquivalence`, `tensor`, `tensorComparison`, `derivedPullback`,
  `sectionLocalizationComparison`.
- `Sheaf.Paper.SectionDerivedPushpullNormalization`:
  `sectionDerivedPushpullNormalization` (resolution compatibility).
- `Sheaf.Paper.SectionKFlatTensorComparison`: `section_kflat_tensor_comparison`,
  `sectionResolving`, `RepresentativeCondition`, `NativeComparisonCondition`,
  `UnitCondition`, `ConstraintCondition` in `KFlatSectionComparison`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients`.
- `Sheaf.Paper.SectionOplaxTotalComparison`: `section_oplax_total_comparison`,
  `SectionTotalNormalization`; its public SectionTotalOplaxComparisonData
  import supplies `sectionTotalIso`, `sectionTotalUnit`, `totalUnitComparison`
  and `totalSectionPull`.
- `Sheaf.Paper.ProEtaleSectionModuleFunctors`: `ordinaryTensorComparison`,
  the actual ordinary oplax structures and signed total comparison.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPullback` and `moduleObjectDerivedPushforward`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`:
  `CondensedRing.leftDerivedUpperStarUnitIso`.
- Proof imports retain the recorded
  `ringedTopoiCanonicalDerivedTensorPullback` in
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
  `derivedPullback_kflat_tensor_computation` in
  `Sheaf.Paper.DerivedPullbackRepresentativeComputation`,
  `kFlat_total_tensor_model` in `Sheaf.Algebra.Homology.KFlatTotalTensorModel`,
  and `Localization.lift`, `liftNatTrans_app`, `natTrans_ext` in
  `Mathlib.CategoryTheory.Localization.Predicate`.

Source and edge checks: read sites-cohomology.tex at lemma-pullback-K-flat
(Tag 0G7E) and lemma-pullback-tensor-product (07A4). These supply preservation
and the resolving total arrow; the node explicitly records the internal/section
normalization as an agent extraction. Checked f = identity, Λ the zero ring,
empty schemes, the zero complex, the regular degree-zero unit, negative/odd
degrees, and complexes unbounded in both directions. No nonzero, nonempty,
bounded or degree-sign restriction is present. Both cochain paths use the
existing signed tensors, so no sign is replaced. There is no statement dispute.

Searches performed on 2026-10-23:

- msearch leanfinder: "The actual internal derived pullback tensor
  transformation satisfies the K-flat representative comparison square under
  the section module equivalence"; eight ordinary scalar/tensor hits, no match.
  A second query "Actual internal derived tensor pullback representative square
  section module equivalence" returned ordinary invertible-module tensor maps.
- msearch loogle: `CategoryTheory.Localization.lift₂NatTrans_app_app`;
  one exact generic component-formula hit. This is a proof tool, not this
  equality between the specified internal and section constructions.
- msearch grep: `derived.*representative|representative.*square`,
  subdirectory CategoryTheory; no match. `leftDerivedTensorComparison` in
  Mathlib CategoryTheory also returned none (the generic map is upstream).
- msearch leansearch: "The internal derived tensor pullback map equals its
  localized ordinary tensor pullback map on K-flat representatives under an
  exact section equivalence"; eight hits, including mapDerivedCategoryFactors,
  none this statement.
- rg across `lean/WeilConjectures` and `lean/Sheaf` for the node id, internalDelta,
  conjugated tensor maps, representative squares and the chosen declaration
  names. The node id has no existing declaration. SectionDerivedTensorNormalization
  is the downstream comparison to the independent ringed map, not this square;
  it is neither imported nor assumed. SectionKFlatTensorComparison and
  SectionOplaxTotalComparison give exactly the dependencies used here.
- rg of `dag/lean_names_upstream.json`, Mathlib, upstream and Sheaf for
  `sectionDerivedRepresentative|DerivedRepresentativeSquare`: no preexisting
  declaration. No duplicate notion was introduced.

Validation: scompile compiled both sandbox and library module names after writing
all definitions and the theorem. The final module with explicit public statement
imports compiled in 13.3 s and 19.0 s. No errors or non-sorry warnings.
The delivery dry run and final push are recorded by the prescribed tool.

## Second reading by Q154

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
