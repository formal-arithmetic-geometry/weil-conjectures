# SheafOfModules scalar tensor and comparison definitions

## Reason

Move the six existing data definitions and structures from
`Sheaf.Paper.InvertibleTensorScalarExtension` into
`Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions`, publicly imported by the original module.
This permits the binary and dual construction modules to use those types while the original
module imports their proofs, without a cycle. Every name, universe, binder, field and definition
body stays identical. The original theorem signature stays identical.

## Old

In `Sheaf.Paper.InvertibleTensorScalarExtension`:

```lean
/-- The tensor power with the unit in degree zero.
Source: Stacks Project, Tag 03EK (blueprint: lem-sp-invertible-tensor-scalar-extension).
Positive powers are left associated, with degree one equal to `M` as in the dependency. -/
noncomputable def scalarTensorPower (R : Sheaf J CommRingCat.{u}) (M : Mod R) : ℕ → Mod R
  | 0 => 𝒪 R
  | 1 => M
  | n + 2 => 𝒯 (scalarTensorPower R M (n + 1)) M

/-- The map on tensor powers induced by a module morphism.
Source: Stacks Project, Tag 03EK (blueprint: lem-sp-invertible-tensor-scalar-extension). -/
noncomputable def scalarTensorPowerMap
    (R : Sheaf J CommRingCat.{u}) {M N : Mod R} (f : M ⟶ N) :
    ∀ r : ℕ, scalarTensorPower R M r ⟶ scalarTensorPower R N r
  | 0 => 𝟙 _
  | 1 => f
  | n + 2 =>
      (siteSheafTensorRight M).map (scalarTensorPowerMap R f (n + 1)) ≫
        siteSheafTensorSecondMap (scalarTensorPower R N (n + 1)) f

/-- The image of a pure scalar-extension tensor under the module sheafification unit.
The module universe may exceed the coefficient universe, as happens for internal Hom.
Source: Stacks, Tag 03EK (blueprint: lem-sp-invertible-tensor-scalar-extension). -/
noncomputable def scalarExtensionSection
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}]
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (M : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (changeOfRingsOfUniverses α M).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
      (changeOfRingsPresheafOfUniverses α M)).app U)
        (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)

/-- Canonical associators and unitors for the actual sheafified tensor product.
Each isomorphism is specified by its action on local pure tensors, rather than an
unspecified monoidal structure. Source: Stacks, Tag 03EK
(blueprint: lem-sp-invertible-tensor-scalar-extension). -/
structure ScalarTensorCoherence (R : Sheaf J CommRingCat.{u}) where
  associator : ∀ (N P Q : Mod R), 𝒯 (𝒯 N P) Q ≅ 𝒯 N (𝒯 P Q)
  associator_tmul : ∀ (N P Q : Mod R) (U : Cᵒᵖ)
      (x : N.val.obj U) (y : P.val.obj U) (z : Q.val.obj U),
    ((associator N P Q).hom.val.app U)
        (siteSheafTensorTmul (𝒯 N P) Q U (siteSheafTensorTmul N P U x y) z) =
      siteSheafTensorTmul N (𝒯 P Q) U x (siteSheafTensorTmul P Q U y z)
  leftUnitor : ∀ N : Mod R, 𝒯 (𝒪 R) N ≅ N
  leftUnitor_tmul : ∀ (N : Mod R) (U : Cᵒᵖ) (a : R.obj.obj U) (x : N.val.obj U),
    ((leftUnitor N).hom.val.app U) (siteSheafTensorTmul (𝒪 R) N U a x) = a • x
  rightUnitor : ∀ N : Mod R, 𝒯 N (𝒪 R) ≅ N
  rightUnitor_tmul : ∀ (N : Mod R) (U : Cᵒᵖ) (x : N.val.obj U) (a : R.obj.obj U),
    ((rightUnitor N).hom.val.app U) (siteSheafTensorTmul N (𝒪 R) U x a) = a • x

/-- Scalar-extension tensor comparisons, with explicit associator and unitor squares.
The pure-tensor normalizations determine the comparisons and hence their canonicity.
Source: Stacks, Tag 03EK (blueprint: lem-sp-invertible-tensor-scalar-extension). -/
structure ScalarExtensionTensorComparison
    (R S : Sheaf J CommRingCat.{u}) (α : R ⟶ S) where
  sourceCoherence : ScalarTensorCoherence R
  targetCoherence : ScalarTensorCoherence S
  unitComparison : changeOfRingsOfUniverses α (𝒪 R) ≅ 𝒪 S
  unit_tmul : ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (a : R.obj.obj U),
    (unitComparison.hom.val.app U) (scalarExtensionSection α (𝒪 R) U s a) =
      s * α.hom.app U a
  tensorComparison : ∀ (N P : Mod R),
    changeOfRingsOfUniverses α (𝒯 N P) ≅
      𝒯 (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P)
  tensor_tmul : ∀ (N P : Mod R) (U : Cᵒᵖ) (s : S.obj.obj U)
      (x : N.val.obj U) (y : P.val.obj U),
    ((tensorComparison N P).hom.val.app U)
        (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y)) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U s x) (scalarExtensionSection α P U 1 y)
  associator_compat : ∀ (N P Q : Mod R),
    changeOfRingsHomOfUniverses α _ (sourceCoherence.associator N P Q).hom ≫
        (tensorComparison N (𝒯 P Q)).hom ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N)
          (tensorComparison P Q).hom =
      (tensorComparison (𝒯 N P) Q).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α Q)).map
          (tensorComparison N P).hom ≫
        (targetCoherence.associator (changeOfRingsOfUniverses α N)
          (changeOfRingsOfUniverses α P) (changeOfRingsOfUniverses α Q)).hom
  leftUnitor_compat : ∀ (N : Mod R),
    (tensorComparison (𝒪 R) N).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α N)).map unitComparison.hom ≫
        (targetCoherence.leftUnitor (changeOfRingsOfUniverses α N)).hom =
      changeOfRingsHomOfUniverses α _ (sourceCoherence.leftUnitor N).hom
  rightUnitor_compat : ∀ (N : Mod R),
    (tensorComparison N (𝒪 R)).hom ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N) unitComparison.hom ≫
        (targetCoherence.rightUnitor (changeOfRingsOfUniverses α N)).hom =
      changeOfRingsHomOfUniverses α _ (sourceCoherence.rightUnitor N).hom
  power : ∀ (N : Mod R) (r : ℕ),
    changeOfRingsOfUniverses α (scalarTensorPower R N r) ≅
      scalarTensorPower S (changeOfRingsOfUniverses α N) r
  power_zero : ∀ N : Mod R, (power N 0).hom = unitComparison.hom
  power_one : ∀ N : Mod R, (power N 1).hom = 𝟙 _
  power_succ : ∀ (N : Mod R) (r : ℕ),
    (power N (r + 2)).hom = (tensorComparison (scalarTensorPower R N (r + 1)) N).hom ≫
      (siteSheafTensorRight (changeOfRingsOfUniverses α N)).map (power N (r + 1)).hom
  power_natural : ∀ (N P : Mod R) (f : N ⟶ P) (r : ℕ),
    changeOfRingsHomOfUniverses α _ (scalarTensorPowerMap R f r) ≫ (power P r).hom =
      (power N r).hom ≫ scalarTensorPowerMap S (changeOfRingsHomOfUniverses α N f) r

/-- The scalar-extension comparisons for tensor powers and internal duals, including
commuting diagrams for iterated ring maps. The larger sheafification universe is the
one required by the recorded internal Hom, with no equality of site universes imposed.
Source: Stacks, Tags 03EK, 03EM and 04TT
(blueprint: lem-sp-invertible-tensor-scalar-extension). -/
structure InvertibleTensorScalarExtensionData
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
    [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]
    (R S : Sheaf J CommRingCat.{u}) (α : R ⟶ S) (M : Mod R)
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [M.IsInvertible] extends ScalarExtensionTensorComparison R S α where
  dual : ∀ (N : Mod R) [N.IsInvertible],
    changeOfRingsOfUniverses α (homObj N (𝒪 R)) ≅
      homObj (changeOfRingsOfUniverses α N) (𝒪 S)
  dual_tmul : ∀ (N : Mod R) [N.IsInvertible] (U : Cᵒᵖ)
      (s t : S.obj.obj U) (f : (homObj N (𝒪 R)).val.obj U) (x : N.val.obj U),
    ((((dual N).hom.val.app U) (scalarExtensionSection α (homObj N (𝒪 R)) U s f)).app
        (Opposite.op (Over.mk (𝟙 U.unop))))
        (scalarExtensionSection α N U t x) =
      s * t * α.hom.app U ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)
  dual_natural : ∀ (N P : Mod R) [N.IsInvertible] [P.IsInvertible] (f : N ⟶ P),
    changeOfRingsHomOfUniverses α _ (homObjMap f (𝟙 (𝒪 R))) ≫ (dual N).hom =
      (dual P).hom ≫ homObjMap (changeOfRingsHomOfUniverses α N f) (𝟙 (𝒪 S))
  after : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T),
    ScalarExtensionTensorComparison S T β
  composite : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T),
    ScalarExtensionTensorComparison R T (α ≫ β)
  tower : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) (N : Mod R),
    changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N) ≅
      changeOfRingsOfUniverses (α ≫ β) N
  tower_tmul : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) (N : Mod R)
      (U : Cᵒᵖ) (a : T.obj.obj U) (s : S.obj.obj U) (x : N.val.obj U),
    ((tower T β N).hom.val.app U)
        (scalarExtensionSection β (changeOfRingsOfUniverses α N) U a
          (scalarExtensionSection α N U s x)) =
      scalarExtensionSection (α ≫ β) N U (a * β.hom.app U s) x
  tower_power : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) (r : ℕ),
    changeOfRingsHomOfUniverses β (changeOfRingsOfUniverses α (scalarTensorPower R M r))
        (power M r).hom ≫
        ((after T β).power (changeOfRingsOfUniverses α M) r).hom ≫
        scalarTensorPowerMap T (tower T β M).hom r =
      (tower T β (scalarTensorPower R M r)).hom ≫ ((composite T β).power M r).hom
  dual_after : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T),
    changeOfRingsOfUniverses β (homObj (changeOfRingsOfUniverses α M) (𝒪 S)) ≅
      homObj (changeOfRingsOfUniverses β (changeOfRingsOfUniverses α M)) (𝒪 T)
  dual_after_tmul : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) (U : Cᵒᵖ)
      (a b : T.obj.obj U)
      (f : (homObj (changeOfRingsOfUniverses α M) (𝒪 S)).val.obj U)
      (x : (changeOfRingsOfUniverses α M).val.obj U),
    ((((dual_after T β).hom.val.app U)
        (scalarExtensionSection β (homObj (changeOfRingsOfUniverses α M) (𝒪 S)) U a f)).app
        (Opposite.op (Over.mk (𝟙 U.unop))))
        (scalarExtensionSection β (changeOfRingsOfUniverses α M) U b x) =
      a * b * β.hom.app U ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)
  dual_composite : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T),
    changeOfRingsOfUniverses (α ≫ β) (homObj M (𝒪 R)) ≅
      homObj (changeOfRingsOfUniverses (α ≫ β) M) (𝒪 T)
  dual_composite_tmul : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) (U : Cᵒᵖ)
      (a b : T.obj.obj U) (f : (homObj M (𝒪 R)).val.obj U) (x : M.val.obj U),
    ((((dual_composite T β).hom.val.app U)
        (scalarExtensionSection (α ≫ β) (homObj M (𝒪 R)) U a f)).app
        (Opposite.op (Over.mk (𝟙 U.unop))))
        (scalarExtensionSection (α ≫ β) M U b x) =
      a * b * (α ≫ β).hom.app U ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)
  dual_tower : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T),
    changeOfRingsOfUniverses β (changeOfRingsOfUniverses α (homObj M (𝒪 R))) ≅
      changeOfRingsOfUniverses (α ≫ β) (homObj M (𝒪 R))
  dual_tower_tmul : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) (U : Cᵒᵖ)
      (a : T.obj.obj U) (s : S.obj.obj U) (f : (homObj M (𝒪 R)).val.obj U),
    ((dual_tower T β).hom.val.app U)
        (scalarExtensionSection β (changeOfRingsOfUniverses α (homObj M (𝒪 R))) U a
          (scalarExtensionSection α (homObj M (𝒪 R)) U s f)) =
      scalarExtensionSection (α ≫ β) (homObj M (𝒪 R)) U (a * β.hom.app U s) f
  tower_dual : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T),
    changeOfRingsHomOfUniverses β _ (dual M).hom ≫ (dual_after T β).hom =
      (dual_tower T β).hom ≫ (dual_composite T β).hom ≫
        homObjMap (tower T β M).hom (𝟙 (𝒪 T))
```

## New

The identical declarations above, verbatim, now reside in
`Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions`. The original module has:

```lean
public import Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions
```

Its public declaration names, elaborated types, data and visibility are preserved. Proof-only
imports provide binary and dual comparison construction statements. The new binary core excludes
power fields and constructs its unit comparison explicitly by sheafifying sectionwise
multiplication and composing with the sheafification counit. Its normalized formula is proved
through the adjunction, without any existence choice. Its `withPowers` construction supplies those fields by explicit recursion and a
proved naturality induction. The new dual/tower core excludes powers and supplies unit and binary
tower squares; the original theorem derives the full power tower square by induction.

## Users

The current `tools/downstream.py` scan reports 602 transitive downstream modules. A current whole-library name search
finds short-name matches in the original item and in `CoefficientExtensionReductionModel`,
`TowerClassDiagonal`, `SemilinearSystemModels`, and `DiagonalTowerTraceCoefficients`.
Inspection of the latter four shows that they refer to the different declaration
`SemilinearSections.scalarExtensionSection`, rather than the relocated declaration. All transitive importers continue receiving the same public
declarations and identical definition bodies through the public reexport. No target uses a
changed definition: this is a relocation with identical bodies. The rows below include every
module from the current downstream scan; no existing downstream module needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.InvertibleTensorScalarExtension | T1 | Publicly reexports the unchanged definitions; proves the original existence theorem by power and tower induction. |
| Sheaf.Paper.TowerClassDiagonal | unchanged, adaptation not needed | Uses the distinct declaration `SemilinearSections.scalarExtensionSection`; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unchanged, adaptation not needed | Uses the distinct declaration `SemilinearSections.scalarExtensionSection`; no adaptation. |
| Sheaf.Paper.SemilinearSystemModels | unchanged, adaptation not needed | Uses the distinct declaration `SemilinearSections.scalarExtensionSection`; no adaptation. |
| Sheaf.Paper.CoefficientExtensionReductionModel | unchanged, adaptation not needed | Uses the distinct declaration `SemilinearSections.scalarExtensionSection`; no adaptation. |
| Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions | new, T1 | Holds the six unchanged definitions and structures. |
| Sheaf.Paper.ScalarExtensionBinaryCoherence | new, T1 | Uses the data types and supplies recursive powers and proved naturality. |
| Sheaf.Paper.ScalarExtensionDualEvaluation | new, T1 | Constructs the evaluation map and its naturality from slice sheafification. |
| Sheaf.Paper.ScalarExtensionDualLocalIso | new, T1 | Proves rank-one preservation and invertibility of the explicit dual map. |
| Sheaf.Paper.ScalarExtensionDualTowerCore | new, T1 | Constructs the ring-tower maps and assembles the dual and tower data. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.DeligneLaumon.GenericDualityModel | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.DeligneLaumon.Reduction.Composition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicExceptionalBase | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicExceptionalCoherence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicExceptionalComposition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicExceptionalOperations | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicExceptionalProjection | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicExceptionalProjectionData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicExceptionalScalars | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicPurityFiniteTensor | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicPurityObjects | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicPurityRootComparisons | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicPuritySourceReduction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicPurityTwistReduction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicSectionClosedSupport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AffineCurveHcZero | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AffineSpaceRationalInduction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ArithmeticRoots | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.BoundaryDualizingComposition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.BoundaryQFoundation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.BoundaryQMaps | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.BoundaryQTransport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.BrownExceptionalAdjoint | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CartierClassAgreement | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ChernFlagFormula | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ClopenStrictSystemComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CoefTowerCoaugmentation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CohomologicalSmoothComposition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CommonStageFourierTransform | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CommonStageWeilShriek | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactFiberStalk | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactSupportCoefficientAction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactSupportCondensedRealization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactSupportFiniteAction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactSupportLerayFiltration | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactSupportPerfectness | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactSupportReductionTower | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactSupportUniformTorBound | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactificationLocalizing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ConnectedConstantH0 | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ConstructibleHomComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CoprojectionCompositionMate | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CurveIntermediateExtension | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.DerivedTruncationCoproducts | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.DirectImagesConstructible | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.DlConstantFieldCharts | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.DlConstructibleFibresExact | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.DualizingObjectPurity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ExceptionalFiniteRealization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ExceptionalSiteRealization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ExtensionByZeroPunctual | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FieldShriekLowerBound | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FieldWeilShriekShiftData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteBoundaryWeights | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteClosedShriek | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteCoefficientHomChange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteConstructibleHom | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteEtaleDescent | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteProductCompactification | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteProperLocalizing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteReductionChartCalculus | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteReductionComparisons | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteReductionOfPurity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteReductionRootCharts | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteTorStability | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FlagPullbackInjective | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FourierKernelConvolution | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FourierTraceFormula | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FrobeniusGeometricExchange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FrobeniusSquareExchange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.GlobalGeometricFrobenius | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralDirectImageTower | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralProperBaseChange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralProperDirectSums | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralProperProjectionFormula | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.InterchangeProperPasting | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.InternalHomPullback | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IteratedWeilCocycle | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.IteratedWeilMap | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.LisseDenseOpenRecovery | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.LisseExtensionInertia | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.LocalizedTopChern | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.MateOpenRestriction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.MiddleExtensionHcZero | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.MixedReductionUnit | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ModelCompactComparisonUnit | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.OpenImmersionLocalizing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.OrdinaryCompactCohomology | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PoincarePointFiniteness | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PointCompletedEvaluation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProjectiveBundleFormula | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProperBaseChangeRational | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProperCompactCoincidence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProperExceptionalRestriction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProperHeartBound | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProperUnboundedCoproducts | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProperUnboundedWindow | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ProperUnboundedWindowIso | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PuncturedDerivedCompletionSections | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurAdicReconstruction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityAffineLineOrientation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityChernClasses | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityCompositionCoherence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityCoprojection | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityDivisorClass | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityDncComparisons | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityDncInvariance | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityFrameIndependence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityGysinStructure | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PuritySourceTransports | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PurityTwistCancellation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.QbarMiddleTStructure | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.QbarPerverseSubcategories | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.QbarPerverseSupportCondition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.QcqsCompactSupportRealization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RationalExceptionalRestriction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RationalPurityPresentation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RationalRestrictionGlue | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RationalStalkExact | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RegularImmersionCancellation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RegularImmersionClassData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RegularImmersionExteriorClass | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RegularImmersionPurity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RegularImmersionPurityComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RelativeSupportBottomDescent | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RestrictionLocal | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SfBidualityClass | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SfPreservationClass | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SmoothMateCounitCancellation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SmoothPurityMap | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SmoothPurityQbar | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SmoothPurityTowerBound | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SmoothTrace | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SupportedProjectionSplitting | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SystemOperationExchangeRealization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TateTwistSupportCondition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TensorTraceTranspose | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TraceBaseChangeSecond | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TraceCompactificationCohomology | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TraceFixedScheme | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TraceFormulaAdicSystem | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TraceGraphCorrespondence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TraceTransposeBaseChange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TrfDevissageGeneration | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TwConventions | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TwFrobeniusAction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TwistFrobeniusScalar | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.VaryingRingGraphSummand | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.VectorBundleThomClass | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.VerdierExchange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.WeilCompactSupportCohomology | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.WeilFourierInversion | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.WeilFourierPlancherel | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.WeilMixedUpperBounds | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.WeilOne | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.WeilOpenImageDelta | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ZlShriekComposition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.CoefQbarVerdier | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.CompositionProjectionMate | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.FiniteDualizing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralDualizing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralSystemOperations | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.IntegralVerdier | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.InternalHomPullback | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.OpenFactorCoherence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.OpenFactorPullModel | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.QbarDualRecollement | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.RationalOperations | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.RationalVerdier | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SmoothPurity.NormalizedWitness | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Targets.AffineSpaceRationalLine | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Targets.PoincareUncurry | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Targets.SmoothPurityQbar | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.ZetaWeil.WeightPurityRoots | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| TargetsCheck | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.PoincareDuality.Poincare | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.PoincareDuality.Verdier | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.Adic.Reduction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.SmoothPurity.Defs | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.Statement | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.TraceFormula.Basic | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.TraceFormula.Slop.Basic | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.TraceFormula.Slop.Main | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.TraceFormula.Slop.Stalk | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.TraceFormula.Statement | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.CohomologyZero | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.Curve | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.EulerProduct | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.Finiteness | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.FourierInversion | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.FourierStalk | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.FourierTrace | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.LFunction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.LocalizationRational | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.PoincareDuality | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.RealPurity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.VerdierDual | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.Examples | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.FinalTheorems | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.HasseWeil | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.IntegralFactors | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.LissePurity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.Rationality | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.RelativePurity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.SmoothProper | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.TraceFormula | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.WeightSeparation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.ZetaFunction.Weights | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |

| Sheaf.Paper.CompactSupportReductionTowerConstruction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.LocalizedFlagProduct | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SixFunctorOperationDatum | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |

| Sheaf.AlgebraicGeometry.FormalPuncturedSections | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdicSectionCanonicalModels | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.AdmissibleVerdierExchange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CommonAdicOpenSectionData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CommonAdicSectionData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompactificationRefinementIdentity | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.CompletedTensorHomTranspose | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.DiagonalTowerTrace | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.DiagonalTowerTraceModels | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.DualStalkFrobenius | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteAdicImageNormalization | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteAdicProperSectionData | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteFreeCompactComposition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.FlagLocalComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.NonrationalCompositionSeed | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.PfRefinementCompatibility | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SixFunctorDatum | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SmoothPurityTowerClasses | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TowerClassChern | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TowerClassCoefficients | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TowerClassFinite | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TowerClassProjective | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TowerClassPullback | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TowerClassReduction | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TowerClassSystems | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.Paper.TowerClassTwisting | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.RingTheory.CompleteLocalConnectednessBound | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.RingTheory.NormalPuncturedHypersurfaceConnected | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.FiniteExceptional | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unchanged, adaptation not needed | Public reexport preserves names, signatures and bodies. |

## Status

landed 20261020T144304-L-2261825 2026-10-20 (merge of deliver/T1/Sheaf.Paper.InvertibleTensorScalarExtension)
