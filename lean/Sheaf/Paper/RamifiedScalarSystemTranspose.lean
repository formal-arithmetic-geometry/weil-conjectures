/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.FiniteFreeCoefficientExtension
public import Sheaf.SixFunctors.FiniteExceptional
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.ProEtaleCommRingSheafification
public import Sheaf.Paper.ProEtaleRingSheafification
public import Sheaf.Paper.FiniteFreeCompactComposition
public import Sheaf.CategoryTheory.ConstantScalarRestrictionTensor
import Sheaf.Paper.FiniteFreeTensorCtf
import Sheaf.Paper.ScalarSystemsNormalized
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Module.Submodule.Equiv
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.CategoryTheory.ConstantScalarGeometricAdjunctions
public import Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars
public import Sheaf.Paper.SystemCompatibleCompositorNormalization
public import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.NormalizedOriginScalarComparisons
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations

/-! # Ramified scalar extension and the ordinary system transpose

Source: blueprint, finite scalar-extension paragraph of lem-coef-rational-operations,
first and third sentences (blueprint: lem-coef-ramified-scalar-system-transpose).

Index n denotes the positive exponent n+1. The upper tower is the actual quotient
by the image of the base uniformizer, hence retains exponents e(n+1), not n+1.
Every category below is a full subcategory of an ordinary unbounded derived category
of strict semilinear systems. Boundedness and Tor intervals are levelwise.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 64
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
open AlgebraicGeometry.FiniteCoefficientAdjoints
open WeilConjectures.FiniteFreeCompactComposition
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
namespace WeilConjectures.RamifiedScalarSystemTranspose

attribute [local irreducible] HasDerivedCategory.standard
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] CategoryTheory.sfbSheafTensor_hasWeakSheafify

/-- Standard localization for constant ring-sheaf modules, with the prescribed size.
Source: Stacks 05RU (blueprint: lem-coef-ramified-scalar-system-transpose). -/
instance constantDerived (W : Scheme.{u}) (B : CommRingCat.{u + 1}) :
    HasDerivedCategory.{u + 2}
      (ConstantScalarRestriction.Modules (Scheme.ProEt.topology W) B) :=
  SemilinearSections.hasDerived.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).obj B)

/-- Cache the existing category structure on the ordinary derived systems.
Source: Zheng 4.1 and the canonical localization category
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
@[instance_reducible]
def systemCategory (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (W : Scheme.{u}) : Category.{u + 2} (Derived C τ W) := inferInstance

attribute [local instance] systemCategory

/-- The simultaneous system calculus on the given actual ring tower.
Source: Zheng 4.1 and 4.10; blueprint finite scalar-extension paragraph
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
def calculus (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (W : Scheme.{u}) :=
  (semilinearDerivedSections.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients C W) (transition C τ W)).some.systems

/-- The canonical derived constant-scalar realization at its two localization sizes.
Source: Stacks 03CY and 05RT
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
def realize (W : Scheme.{u}) (B : CommRingCat.{u + 1}) :=
  @ConstantScalarRestriction.onDerived.{u + 1, u, u + 2, u + 1}
    W.ProEt inferInstance (Scheme.ProEt.topology W) B inferInstance
    (SemilinearSections.hasDerived.{u + 1, u, u + 1}
      (Scheme.ProEt.topology W)
      ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).obj B))
    inferInstance

/-- Evaluation in the existing fixed-coefficient presentation.
Source: Stacks 03CY, 06YY; blueprint finite evaluations
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
def level (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (W : Scheme.{u}) (n : ℕ) :=
  e.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients C W) (transition C τ W) n ⋙ realize W (C n)

private theorem uniqueAdjunctionSquare
    {A A' D D' : Type*} [Category A] [Category A'] [Category D] [Category D']
    (F : A ⥤ A') (G : D ⥤ D') [F.Full] [F.Faithful]
    [G.Full] [G.Faithful] [G.EssSurj]
    {L : A ⥤ D} {R : D ⥤ A} {L' : A' ⥤ D'} {R' : D' ⥤ A'}
    (a : L ⊣ R) (b : L' ⊣ R') (β : R ⋙ F ≅ G ⋙ R') :
    ∃! α : L ⋙ G ≅ F ⋙ L',
      ∀ M N (f : L.obj M ⟶ N),
        b.homEquiv _ _ (α.inv.app M ≫ G.map f) =
          F.map (a.homEquiv M N f) ≫ β.hom.app N := by
  obtain ⟨α, he, _, _⟩ := adjunctionSquare F G a b β
  refine ⟨α, he, ?_⟩
  intro σ hσ
  have h : σ.symm = α.symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    have hh := (hσ M (L.obj M) (𝟙 _)).trans (he M _ (𝟙 _)).symm
    exact (cancel_mono (G.map (𝟙 (L.obj M)))).mp ((b.homEquiv _ _).injective hh)
  exact congrArg Iso.symm h

private theorem uniqueMateSquare
    {A A' D D' : Type*} [Category A] [Category A'] [Category D] [Category D']
    (F : A ⥤ A') (G : D ⥤ D') [F.Full] [F.Faithful]
    [G.Full] [G.Faithful] [G.EssSurj]
    {L : A ⥤ D} {R : D ⥤ A} {L' : A' ⥤ D'} {R' : D' ⥤ A'}
    (a : L ⊣ R) (b : L' ⊣ R') (β : R ⋙ F ≅ G ⋙ R') :
    ∃! δ : F ⋙ L' ≅ L ⋙ G,
      (mateEquiv a b (TwoSquare.mk _ _ _ _ δ.hom)).natTrans = β.hom := by
  obtain ⟨α, he, _, _⟩ := adjunctionSquare F G a b β
  have hα : (mateEquiv a b (TwoSquare.mk _ _ _ _ α.inv)).natTrans = β.hom := by
    apply mateEquiv_eq_of_unit
    intro M
    simpa [Adjunction.homEquiv_unit] using
      (he M _ (𝟙 _)).symm
  refine ⟨α.symm, hα, ?_⟩
  intro σ hσ
  apply Iso.ext
  exact (mateEquiv a b).injective (hσ.trans hα.symm)

private theorem constantRingSection (W : Scheme.{u}) (B : CommRingCat.{u + 1})
    (V : W.ProEtᵒᵖ) (a : B) :
    (((constantCommuteCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app B).hom.app V)
      ((toSheafify (Scheme.ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of B))).app V a) =
    (toSheafify (Scheme.ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj B)).app V a := by
  let J := Scheme.ProEt.topology W
  let : HasWeakSheafify J CommRingCat.{u + 1} := inferInstance
  let : HasWeakSheafify J RingCat.{u + 1} := inferInstance
  have h := sheafComposeIso_hom_fac J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    ((Functor.const W.ProEtᵒᵖ).obj B)
  change ((sheafifyComposeIso J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    ((Functor.const W.ProEtᵒᵖ).obj B)).hom.app V)
      (((presheafToSheaf J RingCat.{u + 1}).map
        ((Functor.compConstIso W.ProEtᵒᵖ
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app B)).hom.app V
            ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of B))).app V a)) = _
  have hi : ((Functor.compConstIso W.ProEtᵒᵖ
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app B) = 𝟙 _ := rfl
  rw [hi]
  erw [CategoryTheory.Functor.map_id]
  exact congrArg (fun f ↦ f.app V a) h

/-- Constant-scalar realization and geometric direct image have a unique comparison
which is the identity on every section. Source: Stacks 03CY, 03DA; node proof step 6
(blueprint: lem-coef-ramified-scalar-system-transpose).
Proof: both functors evaluate the input on the same base-changed test object. The
constant-section structure maps give the same scalar action. Thus the identity on
sections is a module-sheaf isomorphism, natural in the input. A sheaf map is determined
by its sections, proving uniqueness. -/
theorem directOrdinary_existsUnique (B : CommRingCat.{u + 1})
    {U W : Scheme.{u}} (g : U ⟶ W) :
    ∃! ρ : ProEtale.StrictTower.moduleDirectImage B g ⋙
        ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) B ≅
      ConstantScalarRestriction.restriction (Scheme.ProEt.topology U) B ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} B) g,
      ∀ (M : ProEtale.StrictTower.Modules B U) (V : W.ProEtᵒᵖ),
        HEq (fun x ↦ (ρ.hom.app M).hom.app V x)
          (id : ((ProEtale.StrictTower.moduleDirectImage B g).obj M).val.obj V →
            ((ProEtale.StrictTower.moduleDirectImage B g).obj M).val.obj V) := by
  let J := Scheme.ProEt.topology W
  let : HasWeakSheafify J CommRingCat.{u + 1} := inferInstance
  let : HasWeakSheafify J RingCat.{u + 1} := inferInstance
  let K := Scheme.ProEt.topology U
  let : HasWeakSheafify K CommRingCat.{u + 1} := inferInstance
  let : HasWeakSheafify K RingCat.{u + 1} := inferInstance
  let d := Scheme.proEtaleRingDirectImageMap g
    (ProEtale.StrictTower.coefficients B W) (ProEtale.StrictTower.coefficients B U)
    (ProEtale.StrictTower.constantRingIso B g)
  have hd : d = Scheme.proEtaleConstantDirectImageMap g CommRingCat.{u + 1} B := by
    change (Scheme.proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app _ ≫
      (Scheme.proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
        ((Scheme.proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
          (Scheme.proEtaleConstantDirectImageMap g CommRingCat.{u + 1} B) ≫
            (Scheme.proEtaleSheafAdjunction g CommRingCat.{u + 1}).counit.app _) = _
    exact (Scheme.proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (Scheme.proEtaleConstantDirectImageMap g CommRingCat.{u + 1} B)
  have hr : toSheafify J ((Functor.const W.ProEtᵒᵖ).obj B) ≫
      (Scheme.proEtaleConstantDirectImageMap g CommRingCat.{u + 1} B).hom =
      Functor.whiskerLeft (Scheme.proEtaleBaseChange g).op
        (toSheafify K ((Functor.const U.ProEtᵒᵖ).obj B)) :=
    Equiv.apply_symm_apply ((sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv
      ((Functor.const W.ProEtᵒᵖ).obj B)
      ((Scheme.proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
        ((constantSheaf K CommRingCat.{u + 1}).obj B))) _
  let κ (T : Scheme.{u}) := (constantCommuteCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app B
  have hs (V : W.ProEtᵒᵖ) (a : B) :
      d.hom.app V ((κ W).hom.app V
        ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of B))).app V a)) =
      (κ U).hom.app ((Scheme.proEtaleBaseChange g).op.obj V)
        ((toSheafify K ((Functor.const U.ProEtᵒᵖ).obj (RingCat.of B))).app
          ((Scheme.proEtaleBaseChange g).op.obj V) a) := by
    rw [constantRingSection, constantRingSection, hd]
    exact congrArg (fun f ↦ f.app V a) hr
  let F := ProEtale.StrictTower.moduleDirectImage B g ⋙
    ConstantScalarRestriction.restriction J B
  let G := ConstantScalarRestriction.restriction K B ⋙
    ProEtale.lowerStar (ModuleCat.{u + 1} B) g
  let ρ : F ≅ G := NatIso.ofComponents (fun M ↦
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun V ↦
      (LinearEquiv.ofBijective
        (show (F.obj M).obj.obj V →ₗ[B] (G.obj M).obj.obj V from
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := by
              intro a x
              exact congrArg (fun b ↦ b • (show M.val.obj
                  ((Scheme.proEtaleBaseChange g).op.obj V) from x)) (hs V a) })
        (by exact Function.bijective_id)).toModuleIso)
      (by intros; ext x; rfl))) (by intros; ext V x; rfl)
  refine ⟨ρ, fun _ _ ↦ HEq.rfl, ?_⟩
  intro σ hσ
  apply Iso.ext
  ext M V x
  exact congrFun (eq_of_heq (hσ M V)) x

/-- The section-normalized direct-image comparison before localization.
Source: Stacks 03DA (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def directOrdinary (B : CommRingCat.{u + 1}) {U W : Scheme.{u}} (g : U ⟶ W) :=
  (directOrdinary_existsUnique B g).choose

/-- Inverse image is fixed by the mate of that same section-normalized direct image.
Source: Stacks 03CY, 03EK; node proof step 6
(blueprint: lem-coef-ramified-scalar-system-transpose).
Proof: conjugate the geometric adjunction through the exact constant-scalar
equivalences. Its right adjoint is identified with fixed-scalar direct image by
`directOrdinary`. Uniqueness of left adjoints gives an invertible mate. The mate
bijection and the fixed right-hand comparison give uniqueness. -/
theorem pullOrdinary_existsUnique (B : CommRingCat.{u + 1})
    {U W : Scheme.{u}} (g : U ⟶ W) :
    ∃! δ : ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) B ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} B) g ≅
      ProEtale.StrictTower.modulePullback B g ⋙
        ConstantScalarRestriction.restriction (Scheme.ProEt.topology U) B,
      (mateEquiv
        (Scheme.proEtaleRingModuleAdjunction g (ProEtale.StrictTower.coefficients B W)
          (ProEtale.StrictTower.coefficients B U) (ProEtale.StrictTower.constantRingIso B g))
        (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) g)
        (TwoSquare.mk _ _ _ _ δ.hom)).natTrans = (directOrdinary B g).hom := by
  let a := Scheme.proEtaleRingModuleAdjunction g
    (ProEtale.StrictTower.coefficients B W) (ProEtale.StrictTower.coefficients B U)
    (ProEtale.StrictTower.constantRingIso B g)
  let b := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) g
  let := ConstantScalarRestriction.isEquivalence (Scheme.ProEt.topology W) B
  let := ConstantScalarRestriction.isEquivalence (Scheme.ProEt.topology U) B
  exact uniqueMateSquare
    (ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) B)
    (ConstantScalarRestriction.restriction (Scheme.ProEt.topology U) B)
    a b (directOrdinary B g)

/-- The uniquely normalized ordinary inverse-image comparison.
Source: Stacks 03EK (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def pullOrdinary (B : CommRingCat.{u + 1}) {U W : Scheme.{u}} (g : U ⟶ W) :=
  (pullOrdinary_existsUnique B g).choose

/-- Extension by zero is fixed by its ordinary adjunction unit, including the empty open.
Source: Stacks 03DI; node proof step 6
(blueprint: lem-coef-ramified-scalar-system-transpose).
Proof: conjugate the open adjunction through constant-scalar realization and use the
already normalized inverse-image comparison. Uniqueness of left adjoints supplies
an isomorphism whose inverse mate is the displayed map. Mate bijectivity proves
uniqueness. This argument uses the ordinary open adjunction also for the empty open. -/
theorem openOrdinary_existsUnique (B : CommRingCat.{u + 1})
    {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j] :
    ∃! δ : ProEtale.StrictTower.moduleJ B j ⋙
        ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) B ≅
      ConstantScalarRestriction.restriction (Scheme.ProEt.topology U) B ⋙
        ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j,
      (mateEquiv (ProEtale.StrictTower.moduleJAdj B j)
        (ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
        (TwoSquare.mk _ _ _ _ δ.inv)).natTrans = (pullOrdinary B j).inv := by
  let a := ProEtale.StrictTower.moduleJAdj B j
  let b := ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let := ConstantScalarRestriction.isEquivalence (Scheme.ProEt.topology U) B
  let := ConstantScalarRestriction.isEquivalence (Scheme.ProEt.topology W) B
  obtain ⟨α, hα, hu⟩ := uniqueMateSquare
    (ConstantScalarRestriction.restriction (Scheme.ProEt.topology U) B)
    (ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) B)
    a b (pullOrdinary B j).symm
  refine ⟨α.symm, hα, ?_⟩
  intro σ hσ
  exact congrArg Iso.symm (hu σ.symm hσ)

/-- The ordinary open comparison determined by the specified unit.
Source: Stacks 03DI (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def openOrdinary (B : CommRingCat.{u + 1})
    {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j] :=
  (openOrdinary_existsUnique B j).choose

/-- Canonical derived geometric direct-image transport at the two localization sizes.
Source: Stacks 05RT, 07A4 (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def directRealization (B : CommRingCat.{u + 1}) {U W : Scheme.{u}} (g : U ⟶ W) :
    (ProEtale.StrictTower.moduleDirectImage B g).rightDerivedFunctor ⋙ realize W B ≅
      realize U B ⋙ (ProEtale.lowerStar (ModuleCat.{u + 1} B) g).rightDerivedFunctor :=
  haveI := ConstantScalarRestriction.additive (Scheme.ProEt.topology U) B
  haveI : PreservesFiniteLimits
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology U) B) :=
    (ConstantScalarRestriction.exact (Scheme.ProEt.topology U) B).1
  haveI : PreservesFiniteColimits
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology U) B) :=
    (ConstantScalarRestriction.exact (Scheme.ProEt.topology U) B).2
  haveI := ConstantScalarRestriction.additive (Scheme.ProEt.topology W) B
  haveI : PreservesFiniteLimits
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) B) :=
    (ConstantScalarRestriction.exact (Scheme.ProEt.topology W) B).1
  haveI : PreservesFiniteColimits
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) B) :=
    (ConstantScalarRestriction.exact (Scheme.ProEt.topology W) B).2
  haveI := ConstantScalarRestriction.isEquivalence (Scheme.ProEt.topology U) B
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (directOrdinary B g) ≪≫
    Functor.rightDerivedFunctorCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorIsoMapDerivedCategory
        (ConstantScalarRestriction.restriction (Scheme.ProEt.topology U) B)) _

/-- Canonical exact localization of the unit-normalized open comparison.
Source: Stacks 03DI, 05RT (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def openRealization (B : CommRingCat.{u + 1})
    {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j] :
    (ProEtale.StrictTower.moduleJ B j).mapDerivedCategory ⋙ realize W B ≅
      realize U B ⋙
        (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  haveI := ConstantScalarRestriction.additive (Scheme.ProEt.topology U) B
  haveI : PreservesFiniteLimits
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology U) B) :=
    (ConstantScalarRestriction.exact (Scheme.ProEt.topology U) B).1
  haveI : PreservesFiniteColimits
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology U) B) :=
    (ConstantScalarRestriction.exact (Scheme.ProEt.topology U) B).2
  haveI := ConstantScalarRestriction.additive (Scheme.ProEt.topology W) B
  haveI : PreservesFiniteLimits
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) B) :=
    (ConstantScalarRestriction.exact (Scheme.ProEt.topology W) B).1
  haveI : PreservesFiniteColimits
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) B) :=
    (ConstantScalarRestriction.exact (Scheme.ProEt.topology W) B).2
  Functor.mapDerivedCategorySquareIso (openOrdinary B j)

/-- The canonical proper/open transport, retaining both normalized factors.
Source: Stacks 03DI, 07A4; node proof step 6
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
def lowerRealization (B : CommRingCat.{u + 1})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    ((ProEtale.StrictTower.moduleJ B c.i).mapDerivedCategory ⋙
      (ProEtale.StrictTower.moduleDirectImage B c.g).rightDerivedFunctor) ⋙ realize Y B ≅
    realize X B ⋙ lower B c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (directRealization B c.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openRealization B c.i) _ ≪≫
    Functor.associator _ _ _

/-- Evaluating a constant strict diagram at zero recovers precisely the input level.
The comparison is induced by the identity ordinary evaluation, before localization.
Source: Zheng 4.1, 4.10 (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def levelPresentation (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (W : Scheme.{u}) (n : ℕ) :
    compositorLevel C τ W n ⋙ realize W (C n) ≅ level C τ W n :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryCompIso (levelTower C τ n W)
      ((CategoryTheory.evaluation ℕᵒᵖ (ProEtale.StrictTower.Modules (C n) W)).obj (op 0))).symm _

/-- Canonical support evaluation, obtained from evalJ/evalR and their strict-tower
counterparts, transported by identity level evaluation and the normalized proper/open
constant-scalar comparison. Source: Zheng 4.10; node proof steps 3 and 6
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
def canonicalSupportEvaluation
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    support C τ c ⋙ level C τ Y n ≅ level C τ X n ⋙ lower (C n) c :=
  Functor.isoWhiskerLeft _ (levelPresentation C τ Y n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (compositorSupportEvaluation C τ c.i c.g n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (lowerRealization (C n) c) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (levelPresentation C τ X n) _

attribute [local irreducible] canonicalSupportEvaluation

/-- The identity-on-sections ordinary coefficient restriction square is unique.
Source: Stacks 03CY, 03CZ; scalar realization in node proof steps 1 and 6
(blueprint: lem-coef-ramified-scalar-system-transpose).
Proof: restrict along the constant section maps on both paths. Naturality of the
sheafification unit identifies the two coefficient actions. The identity on sections
therefore defines inverse module-sheaf maps, natural in the input. A sheaf map is
uniquely determined by these section functions. -/
theorem restrictionOrdinary_existsUnique (W : Scheme.{u})
    {A B : CommRingCat.{u + 1}} (φ : A ⟶ B) :
    ∃! ρ :
      res.{u + 1, u, u + 1}
          ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).map φ) ⋙
          ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) A ≅
        ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) B ⋙
          Sheaf.restrictScalars (Scheme.ProEt.topology W) φ.hom,
      ∀ (M : ConstantScalarRestriction.Modules (Scheme.ProEt.topology W) B)
        (V : W.ProEtᵒᵖ),
        HEq (fun x ↦ (ρ.hom.app M).hom.app V x)
          (id : M.val.obj V → M.val.obj V) := by
  let J := Scheme.ProEt.topology W
  let : HasWeakSheafify J CommRingCat.{u + 1} := inferInstance
  let : HasWeakSheafify J RingCat.{u + 1} := inferInstance
  let κ (C : CommRingCat.{u + 1}) :=
    (constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app C
  have hs (V : W.ProEtᵒᵖ) (a : A) :
      ((constantSheaf J CommRingCat.{u + 1}).map φ).hom.app V
          ((κ A).hom.app V ((toSheafify J
            ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of A))).app V a)) =
        (κ B).hom.app V ((toSheafify J
          ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of B))).app V (φ a)) := by
    have hκ := congrArg (fun f ↦ f.hom.app V)
      ((constantCommuteCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.naturality φ)
    have hη := congrArg (fun f ↦ f.app V)
      (toSheafify_naturality J
        ((Functor.const W.ProEtᵒᵖ).map (RingCat.ofHom φ.hom)))
    have hc := congrArg (fun f ↦ f ((toSheafify J
      ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of A))).app V a)) hκ
    have he := congrArg (fun f ↦ f a) hη
    change (κ B).hom.app V
        (((constantSheaf J RingCat.{u + 1}).map (RingCat.ofHom φ.hom)).hom.app V
          ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of A))).app V a)) =
      ((constantSheaf J CommRingCat.{u + 1}).map φ).hom.app V
        ((κ A).hom.app V ((toSheafify J
          ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of A))).app V a)) at hc
    change (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of B))).app V (φ a) =
      ((constantSheaf J RingCat.{u + 1}).map (RingCat.ofHom φ.hom)).hom.app V
        ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of A))).app V a) at he
    exact hc.symm.trans (congrArg (fun x ↦ (κ B).hom.app V x) he.symm)
  let F := res.{u + 1, u, u + 1} ((constantSheaf J CommRingCat.{u + 1}).map φ) ⋙
    ConstantScalarRestriction.restriction J A
  let G := ConstantScalarRestriction.restriction J B ⋙ Sheaf.restrictScalars J φ.hom
  let ρ : F ≅ G := NatIso.ofComponents (fun M ↦
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun V ↦
      (LinearEquiv.ofBijective
        (show (F.obj M).obj.obj V →ₗ[A] (G.obj M).obj.obj V from
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := by
              intro a x
              exact congrArg (fun b ↦ b • (show M.val.obj V from x)) (hs V a) })
        (by exact Function.bijective_id)).toModuleIso)
      (by intros; ext x; rfl))) (by intros; ext V x; rfl)
  refine ⟨ρ, fun _ _ ↦ HEq.rfl, ?_⟩
  intro σ hσ
  apply Iso.ext
  ext M V x
  exact congrFun (eq_of_heq (hσ M V)) x

/-- The ordinary square fixed on every section, before deriving.
Source: Stacks 03CY (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def restrictionOrdinary (W : Scheme.{u}) {A B : CommRingCat.{u + 1}} (φ : A ⟶ B) :=
  (restrictionOrdinary_existsUnique W φ).choose

/-- Exact localization of the identity-on-sections restriction square.
Source: Stacks 05RT (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def restrictionRealization (W : Scheme.{u}) {A B : CommRingCat.{u + 1}} (φ : A ⟶ B) :
    resD.{u + 1, u, u + 1}
        ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).map φ) ⋙
        realize W A ≅
      realize W B ⋙ Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W) φ.hom :=
  haveI := ConstantScalarRestriction.additive (Scheme.ProEt.topology W) A
  haveI := ConstantScalarRestriction.additive (Scheme.ProEt.topology W) B
  haveI : PreservesFiniteLimits
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) A) :=
    (ConstantScalarRestriction.exact (Scheme.ProEt.topology W) A).1
  haveI : PreservesFiniteColimits
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) A) :=
    (ConstantScalarRestriction.exact (Scheme.ProEt.topology W) A).2
  haveI : PreservesFiniteLimits
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) B) :=
    (ConstantScalarRestriction.exact (Scheme.ProEt.topology W) B).1
  haveI : PreservesFiniteColimits
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology W) B) :=
    (ConstantScalarRestriction.exact (Scheme.ProEt.topology W) B).2
  Functor.mapDerivedCategorySquareIso (restrictionOrdinary W φ)

/-- Scalar realization is uniquely normalized by the tensor/restriction adjunctions.
It applies equally to finite-free inclusions and all quotient maps.
Source: Stacks 06YY; node proof steps 1, 6, 7
(blueprint: lem-coef-ramified-scalar-system-transpose).
Proof: the identity restriction square localizes exactly. Conjugate it through the
constant-scalar equivalences and take its left-adjoint mate. Uniqueness of adjoints
makes this mate invertible and gives the stated Hom-equivalence equation. That
same equation determines it uniquely, since realization is an equivalence. -/
theorem scalarRealization_existsUnique (W : Scheme.{u})
    {A B : CommRingCat.{u + 1}} (φ : A ⟶ B)
    (s : ScalarData.{u + 1, u, u + 1}
      ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).map φ)) :
    ∃! δ : s.T ⋙ realize W B ≅ realize W A ⋙ tensor φ.hom W,
      ∀ (M : SemilinearSections.D.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
          ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).obj A))
        (N : SemilinearSections.D.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
          ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).obj B))
        (g : s.T.obj M ⟶ N),
        (realize W A).map ((s.adjunction.homEquiv _ _) g) ≫
            (restrictionRealization W φ).hom.app N =
          ((Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W) φ.hom)).homEquiv _ _)
              (δ.inv.app M ≫ (realize W B).map g) := by
  let a := s.adjunction
  let b := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W) φ.hom)
  let : (realize W A).IsEquivalence :=
    ConstantScalarRestriction.derived_isEquivalence (Scheme.ProEt.topology W) A
  let : (realize W B).IsEquivalence :=
    ConstantScalarRestriction.derived_isEquivalence (Scheme.ProEt.topology W) B
  obtain ⟨α, he, hu⟩ := uniqueAdjunctionSquare (realize W A) (realize W B)
    a b (restrictionRealization W φ)
  refine ⟨α, fun M N g ↦ (he M N g).symm, ?_⟩
  intro σ hσ
  exact hu σ (fun M N g ↦ (hσ M N g).symm)

/-- The scalar comparison fixed by the actual tensor adjunction, hence basis independent.
Source: Stacks 06YY (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def scalarRealization (W : Scheme.{u}) {A B : CommRingCat.{u + 1}} (φ : A ⟶ B)
    (s : ScalarData.{u + 1, u, u + 1}
      ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).map φ)) :=
  (scalarRealization_existsUnique W φ s).choose

/-- The actual composite quotient homomorphism, including equal indices.
Source: node coefficient towers (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def quotientMap (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {m n : ℕ} (h : n ≤ m) : C m ⟶ C n :=
  (Functor.ofOpSequence τ).map (homOfLE h).op

/-- Forming the constant ring sheaf commutes with every composite quotient map.
Source: node actual quotient transitions
(blueprint: lem-coef-ramified-scalar-system-transpose).
Proof: induction on m-n, using functoriality of the constant-sheaf functor and
Functor.ofOpSequence on each successor; the zero difference is the identity law. -/
theorem quotientMap_constant (C : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    SemilinearSections.coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
        (coefficients C W) (transition C τ W) h =
      (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).map
        (quotientMap C τ h) := by
  change (Functor.ofOpSequence (transition C τ W)).map (homOfLE h).op =
    (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).map
      ((Functor.ofOpSequence τ).map (homOfLE h).op)
  induction m, h using Nat.le_induction with
  | base => (simp; rfl)
  | succ m h ih =>
    have he : (homOfLE (Nat.le.step h)).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := rfl
    rw [he, Functor.map_comp, Functor.map_comp,
      Functor.ofOpSequence_map_homOfLE_succ,
      Functor.ofOpSequence_map_homOfLE_succ, ih, Functor.map_comp]

/-- The system's own transition, in the fixed-coefficient presentation.
Source: node strict semilinear transitions
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
def fixedTransition (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) (M : Derived C τ W) :
    (level C τ W m).obj M ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W)
        (quotientMap C τ h).hom).obj ((level C τ W n).obj M) :=
  (realize W (C m)).map
      ((derivedTransition.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
        (coefficients C W) (transition C τ W) h).app M) ≫
    (eqToIso (congrArg (fun φ ↦ resD.{u + 1, u, u + 1} φ ⋙ realize W (C m))
      (quotientMap_constant C τ W h))).hom.app
        ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
          (coefficients C W) (transition C τ W) n).obj M) ≫
    (restrictionRealization W (quotientMap C τ h)).hom.app _

/-- Its actual quotient-tensor adjunct, not a separately chosen finite arrow.
Source: node normalization definition
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
def red (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) (M : Derived C τ W) :=
  ((Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W)
      (quotientMap C τ h).hom)).homEquiv _ _).symm (fixedTransition C τ W h M)

/-- Composite quotient homomorphisms satisfy the actual tower cocycle.
Source: node quotient cocycles (blueprint: lem-coef-ramified-scalar-system-transpose).
Proof: apply functoriality of Functor.ofOpSequence to the composable order arrows. -/
theorem quotientMap_comp (C : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) {r m n : ℕ} (h : m ≤ r) (k : n ≤ m) :
    (quotientMap C τ (k.trans h)).hom =
      (quotientMap C τ k).hom.comp (quotientMap C τ h).hom := by
  change (quotientMap C τ (k.trans h)).hom =
    (quotientMap C τ h ≫ quotientMap C τ k).hom
  congr 1
  exact (Functor.ofOpSequence τ).map_comp (homOfLE h).op (homOfLE k).op

/-- The identity quotient really is the identity ring map.
Source: node equal-index case (blueprint: lem-coef-ramified-scalar-system-transpose).
Proof: Functor.ofOpSequence preserves the identity order arrow. -/
theorem quotientMap_id (C : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) (n : ℕ) :
    (quotientMap C τ (le_refl n)).hom = RingHom.id (C n) := by
  exact congrArg CommRingCat.Hom.hom ((Functor.ofOpSequence τ).map_id (op n))

/-- The full normalized domain, using the dependency's bounded constructible finite-Tor
predicate at each level. In particular no interval is chosen before the quantifier n.
Source: the first paragraph of the node; Zheng 4.10
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
def domain (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (W : Scheme.{u}) : ObjectProperty (Derived C τ W) :=
  fun M ↦ Normalized.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients C W) (transition C τ W) (calculus C τ W).scalar M ∧
      ∀ n : ℕ, ctf (C n) W ((level C τ W n).obj M)

/-- Evaluation on the full normalized domain, retaining its finite-Tor proof.
Source: node first paragraph and finite-evaluation clauses
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
def evaluation (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (W : Scheme.{u}) (n : ℕ) :=
  (ctf (C n) W).lift ((domain C τ W).ι ⋙ level C τ W n) (fun M ↦ M.property.2 n)

attribute [local irreducible] realize calculus level
attribute [local irreducible] domain
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Presentation of the stipulated system adjunction with its fixed proper/open left
functor and its actual finite adjunctions. The left comparison is the canonical
proper/open evaluation, with both evaluation equations using the same finite unit
and counit. Thus the adjunction and its evaluation cannot be simultaneously twisted.
Source: node first paragraph; lem-coef-cartesian-section-adjoint-mates and its
retention at the base-uniformizer levels
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
structure SystemAdjunctionData
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) [∀ n : ℕ, Finite (C n)] where
  support_preserves : ∀ M, domain C τ X M →
    domain C τ Y ((support C τ c).obj M)
  G : (domain C τ Y).FullSubcategory ⥤ (domain C τ X).FullSubcategory
  adjunction : (domain C τ Y).lift ((domain C τ X).ι ⋙ support C τ c)
    (fun M ↦ support_preserves M.obj M.property) ⊣ G
  finite : ∀ n : ℕ, AdjointDatum (C n) c
  left : ∀ n : ℕ,
    (domain C τ Y).lift ((domain C τ X).ι ⋙ support C τ c)
      (fun M ↦ support_preserves M.obj M.property) ⋙ evaluation C τ Y n ≅
        evaluation C τ X n ⋙ restrict (lower (C n) c) (finite n).lower_preserves
  right : ∀ n : ℕ, G ⋙ evaluation C τ X n ≅
    evaluation C τ Y n ⋙ restrict (upper (C n) c) (finite n).upper_preserves
  quotient : ∀ {m n : ℕ} (h : n ≤ m),
    Change (quotientMap C τ h).hom c (finite m) (finite n)

/-- The original eight coherence equations, separated from the adjunction data.
Source: Zheng 4.10; the stipulated finite adjunction and quotient coherences
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
structure SystemAdjunctionLaws
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) [∀ n : ℕ, Finite (C n)]
    (d : SystemAdjunctionData C τ c) : Prop where
  left_canonical : ∀ (n : ℕ) (M : (domain C τ X).FullSubcategory),
    ((d.left n).hom.app M).hom = (canonicalSupportEvaluation C τ c n).hom.app M.obj
  unit : ∀ (n : ℕ) (M : (domain C τ X).FullSubcategory),
    (evaluation C τ X n).map (d.adjunction.unit.app M) ≫
      (d.right n).hom.app _ ≫
        (restrict (upper (C n) c) (d.finite n).upper_preserves).map ((d.left n).hom.app M) =
      (d.finite n).adjunction.unit.app ((evaluation C τ X n).obj M)
  counit : ∀ (n : ℕ) (N : (domain C τ Y).FullSubcategory),
    (d.left n).hom.app (d.G.obj N) ≫
      (restrict (lower (C n) c) (d.finite n).lower_preserves).map ((d.right n).hom.app N) ≫
        (d.finite n).adjunction.counit.app ((evaluation C τ Y n).obj N) =
      (evaluation C τ Y n).map (d.adjunction.counit.app N)
  exceptionalTransition : ∀ {m n : ℕ} (h : n ≤ m)
    (N : (domain C τ Y).FullSubcategory),
    red C τ X h (d.G.obj N).obj ≫ ((d.right n).hom.app N).hom =
      (tensor (quotientMap C τ h).hom X).map (((d.right m).hom.app N).hom) ≫
        (d.quotient h).mate.hom.app ((evaluation C τ Y m).obj N) ≫
        (upper (C n) c).map (red C τ Y h N.obj)
  supportTransition : ∀ {m n : ℕ} (h : n ≤ m)
    (M : (domain C τ X).FullSubcategory),
    red C τ Y h
        (((domain C τ Y).lift ((domain C τ X).ι ⋙ support C τ c)
          (fun K ↦ d.support_preserves K.obj K.property)).obj M).obj ≫
        ((d.left n).hom.app M).hom =
      (tensor (quotientMap C τ h).hom Y).map (((d.left m).hom.app M).hom) ≫
        (d.quotient h).projection.hom.app ((evaluation C τ X m).obj M) ≫
        (lower (C n) c).map (red C τ X h M.obj)
  projection_comp : ∀ {r m n : ℕ} (h : m ≤ r) (k : n ≤ m)
    (M : (ctf (C r) X).FullSubcategory),
    (tensor (quotientMap C τ k).hom Y).map ((d.quotient h).projection.hom.app M) ≫
        (d.quotient k).projection.hom.app
          ⟨(tensor (quotientMap C τ h).hom X).obj M.obj,
            (d.quotient h).tensor_preserves_X M.obj M.property⟩ ≫
        (lower (C n) c).map
          ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
            (quotientMap C τ h).hom (quotientMap C τ k).hom
            (quotientMap C τ (k.trans h)).hom (quotientMap_comp C τ h k)).hom.app M.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
          (quotientMap C τ h).hom (quotientMap C τ k).hom
          (quotientMap C τ (k.trans h)).hom (quotientMap_comp C τ h k)).hom.app
            ((lower (C r) c).obj M.obj) ≫
        (d.quotient (k.trans h)).projection.hom.app M
  quotient_comp : ∀ {r m n : ℕ} (h : m ≤ r) (k : n ≤ m)
    (N : (ctf (C r) Y).FullSubcategory),
    (tensor (quotientMap C τ k).hom X).map ((d.quotient h).mate.hom.app N) ≫
        (d.quotient k).mate.hom.app
          ⟨(tensor (quotientMap C τ h).hom Y).obj N.obj,
            (d.quotient h).tensor_preserves_Y N.obj N.property⟩ ≫
        (upper (C n) c).map
          ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
            (quotientMap C τ h).hom (quotientMap C τ k).hom
            (quotientMap C τ (k.trans h)).hom (quotientMap_comp C τ h k)).hom.app N.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
          (quotientMap C τ h).hom (quotientMap C τ k).hom
          (quotientMap C τ (k.trans h)).hom (quotientMap_comp C τ h k)).hom.app
            ((upper (C r) c).obj N.obj) ≫
        (d.quotient (k.trans h)).mate.hom.app N
  quotient_id : ∀ (n : ℕ) (N : (ctf (C n) Y).FullSubcategory),
    (d.quotient (le_refl n)).mate.hom.app N ≫
        (upper (C n) c).map
          ((ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology Y)
            (quotientMap C τ (le_refl n)).hom (quotientMap_id C τ n)).hom.app N.obj) =
      (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X)
        (quotientMap C τ (le_refl n)).hom (quotientMap_id C τ n)).hom.app
          ((upper (C n) c).obj N.obj)

/-- The stipulated system adjunction, with its unchanged data and coherence laws.
Source: Zheng 4.10; node first paragraph and finite adjunction clauses
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
structure SystemAdjunction
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) [∀ n : ℕ, Finite (C n)] where
  data : SystemAdjunctionData C τ c
  laws : SystemAdjunctionLaws C τ c data

/-- The original adjunction accessor, with the same data or predicate.
Source: node system adjunction (blueprint: lem-coef-ramified-scalar-system-transpose). -/
theorem SystemAdjunction.support_preserves
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c) :
    ∀ M, domain C τ X M →
    domain C τ Y ((support C τ c).obj M) :=
  sys.data.support_preserves

/-- The original adjunction accessor, with the same data or predicate.
Source: node system adjunction (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.G
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c) :=
  sys.data.G

/-- The original adjunction accessor, with the same data or predicate.
Source: node system adjunction (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.adjunction
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c) :=
  sys.data.adjunction

/-- The original adjunction accessor, with the same data or predicate.
Source: node system adjunction (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.finite
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c) :=
  sys.data.finite

/-- The original adjunction accessor, with the same data or predicate.
Source: node system adjunction (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.left
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c) :=
  sys.data.left

/-- The original adjunction accessor, with the same data or predicate.
Source: node system adjunction (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.right
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c) :=
  sys.data.right

/-- The original adjunction accessor, with the same data or predicate.
Source: node system adjunction (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.quotient
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c) {m n : ℕ} (h : n ≤ m) :=
  sys.data.quotient h

/-- The original coherence accessor, projected from the proof package.
Source: node system coherence (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.left_canonical
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c)
    (n : ℕ) (M : (domain C τ X).FullSubcategory) :=
  sys.laws.left_canonical n M

/-- The original coherence accessor, projected from the proof package.
Source: node system coherence (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.unit
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c)
    (n : ℕ) (M : (domain C τ X).FullSubcategory) :=
  sys.laws.unit n M

/-- The original coherence accessor, projected from the proof package.
Source: node system coherence (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.counit
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c)
    (n : ℕ) (N : (domain C τ Y).FullSubcategory) :=
  sys.laws.counit n N

/-- The original coherence accessor, projected from the proof package.
Source: node system coherence (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.exceptionalTransition
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c)
    {m n : ℕ} (h : n ≤ m)
    (N : (domain C τ Y).FullSubcategory) :=
  sys.laws.exceptionalTransition h N

/-- The original coherence accessor, projected from the proof package.
Source: node system coherence (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.supportTransition
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c)
    {m n : ℕ} (h : n ≤ m)
    (M : (domain C τ X).FullSubcategory) :=
  sys.laws.supportTransition h M

/-- The original coherence accessor, projected from the proof package.
Source: node system coherence (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.projection_comp
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c)
    {r m n : ℕ} (h : m ≤ r) (k : n ≤ m)
    (M : (ctf (C r) X).FullSubcategory) :=
  sys.laws.projection_comp h k M

/-- The original coherence accessor, projected from the proof package.
Source: node system coherence (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.quotient_comp
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c)
    {r m n : ℕ} (h : m ≤ r) (k : n ≤ m)
    (N : (ctf (C r) Y).FullSubcategory) :=
  sys.laws.quotient_comp h k N

/-- The original coherence accessor, projected from the proof package.
Source: node system coherence (blueprint: lem-coef-ramified-scalar-system-transpose). -/
abbrev SystemAdjunction.quotient_id
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (sys : SystemAdjunction C τ c)
    (n : ℕ) (N : (ctf (C n) Y).FullSubcategory) :=
  sys.laws.quotient_id n N

/-- The stipulated compact-support functor, with its actual action on all system maps.
Source: node compactification f=pj
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
def SystemAdjunction.F
    {C : ℕ → CommRingCat.{u + 1}} {τ : ∀ n, C (n + 1) ⟶ C n}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} [∀ n : ℕ, Finite (C n)]
    (r : SystemAdjunction C τ c) :=
  (domain C τ Y).lift ((domain C τ X).ι ⋙ support C τ c)
    (fun M ↦ r.support_preserves M.obj M.property)

variable (l : ℕ) [Fact l.Prime] (E L : Type (u + 1)) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)

attribute [local semireducible] level

/-- Scalar extension evaluates to the canonical finite derived tensor, with its
normalization inherited from the two tensor/restriction adjunctions.
Source: node first conclusion (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def scalarEvaluation (W : Scheme.{u}) (n : ℕ) :
    (scalarData l E L i W).scalar.T ⋙
        level (upperRings l E L i) (upperMaps l E L i) W n ≅
      level (lowerRings l E) (lowerMaps l E) W n ⋙ tensor (inclusion l E L i n) W :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((scalarData l E L i W).evaluation n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (scalarRealization W (CommRingCat.ofHom (inclusion l E L i n))
        ((scalarData l E L i W).levels n)) ≪≫
    (Functor.associator _ _ _).symm

attribute [local irreducible] scalarData scalarEvaluation

private theorem arrow_finite_free (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (s t : Stage l E) (a : Arrow s t)
    (h : s.exponent = t.exponent) : a.IsFiniteFree := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let k₀ := ULift.{u} (ZMod p)
  let d : FiniteFieldDatum.{u} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := le_rfl
      cardinality_eq := (pow_one p).symm
      k₀ := k₀
      card_base := by rw [Nat.card_ulift, Nat.card_zmod]
      k := AlgebraicClosure k₀ }
  have hl : l ≠ d.p := Nat.ne_of_lt (lt_of_lt_of_le (Nat.lt_succ_self l) hp)
  exact (FiniteFreeCoefficients.finite_free_coefficient_extension d l hl E).2.1 s t a h

attribute [local semireducible] domain

/-- Finite-free tensor preserves normalization and every individual finite-Tor
constructible level, without a common interval.
Source: node proof steps 1--2 (blueprint: lem-coef-ramified-scalar-system-transpose).
Proof: construct scalar extension on the ringed sequence site by semilinear derived
sections. Transpose its strict transitions: reduction is tensor reassociation followed
by scalar extension of the input reduction. A single integral basis reduces at every
level, giving B_m tensor^L_A_m A_n = B_n. Hence normalized reductions stay invertible.
The fully proved finiteFreeTensorCtf preserves bounded constructibility and the Tor
interval of each input level separately. No uniform choice of interval is made. -/
theorem scalar_preserves (W : Scheme.{u})
    (M : Derived (lowerRings l E) (lowerMaps l E) W)
    (hM : domain (lowerRings l E) (lowerMaps l E) W M) :
    domain (upperRings l E L i) (upperMaps l E L i) W
      ((scalarData l E L i W).scalar.T.obj M) := by
  classical
  refine ⟨?_, ?_⟩
  · exact scalarSystems_normalized (Scheme.ProEt.topology W)
      (coefficients (lowerRings l E) W) (coefficients (upperRings l E L i) W)
      (transition (lowerRings l E) (lowerMaps l E) W)
      (transition (upperRings l E L i) (upperMaps l E L i) W)
      (coefficientInclusion l E L i W) (coefficientInclusion_commutes l E L i W)
      (calculus (lowerRings l E) (lowerMaps l E) W)
      (calculus (upperRings l E L i) (upperMaps l E L i) W)
      (scalarData l E L i W) M hM.1
  · intro n
    let a : Arrow (lowerStage l E n) (upperStage l E L i n) :=
      { embedding := i, over_base := AlgHom.comp_id i, level := le_rfl }
    let : Algebra (lowerRings l E n) (upperRings l E L i n) :=
      (inclusion l E L i n).toAlgebra
    let : Module (lowerRings l E n) (upperRings l E L i n) := Algebra.toModule
    obtain ⟨hf, hg⟩ := arrow_finite_free l E _ _ a rfl
    have : Module.Finite (lowerRings l E n) (upperRings l E L i n) := hf
    have : Module.Free (lowerRings l E n) (upperRings l E L i n) := hg
    exact (ctf (upperRings l E L i n) W).prop_of_iso ((scalarEvaluation l E L i W n).app M).symm
      (finiteFreeTensorCtf W (lowerRings l E n) (upperRings l E L i n)
        _ ((Module.Free.chooseBasis _ _).reindex (Fintype.equivFin _)) _ (hM.2 n))

/-- Restriction of the canonical derived scalar extension to the full normalized domains.
Source: node displayed functor T (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def T (W : Scheme.{u}) :=
  (domain (upperRings l E L i) (upperMaps l E L i) W).lift
    ((domain (lowerRings l E) (lowerMaps l E) W).ι ⋙ (scalarData l E L i W).scalar.T)
    (fun M ↦ scalar_preserves l E L i W M.obj M.property)

attribute [local irreducible] domain level

/-- Every finite-free inclusion commutes with every actual quotient map.
Source: node coefficient squares (blueprint: lem-coef-ramified-scalar-system-transpose).
Proof: quotient induction on an element of O_E gives the same residue of its image
in O_L on both paths. This includes equality of indices and the retained ramified powers. -/
theorem inclusion_quotient {m n : ℕ} (h : n ≤ m) :
    (quotientMap (upperRings l E L i) (upperMaps l E L i) h).hom.comp
        (inclusion l E L i m) =
      (inclusion l E L i n).comp
        (quotientMap (lowerRings l E) (lowerMaps l E) h).hom := by
  let η : Functor.ofOpSequence (lowerMaps l E) ⟶
      Functor.ofOpSequence (upperMaps l E L i) :=
    NatTrans.ofOpSequence (fun n ↦ CommRingCat.ofHom (inclusion l E L i n)) (by
      intro n
      simp only [Functor.ofOpSequence_map_homOfLE_succ]
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)
  exact congrArg CommRingCat.Hom.hom (η.naturality (homOfLE h).op).symm

/-- Canonical tensor reassociation for a finite-free coefficient square.
Source: node s_W in proof steps 1 and 7
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
def reassociate (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    tensor (inclusion l E L i m) W ⋙
        tensor (quotientMap (upperRings l E L i) (upperMaps l E L i) h).hom W ≅
      tensor (quotientMap (lowerRings l E) (lowerMaps l E) h).hom W ⋙
        tensor (inclusion l E L i n) W :=
  ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology W)
      (inclusion l E L i m)
      (quotientMap (upperRings l E L i) (upperMaps l E L i) h).hom
      ((quotientMap (upperRings l E L i) (upperMaps l E L i) h).hom.comp
        (inclusion l E L i m)) rfl ≪≫
    (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology W)
      (quotientMap (lowerRings l E) (lowerMaps l E) h).hom (inclusion l E L i n)
      ((quotientMap (upperRings l E L i) (upperMaps l E L i) h).hom.comp
        (inclusion l E L i m)) (inclusion_quotient l E L i h)).symm

/-- The transition-adjoint of scalar extension is reassociation followed by tensor
of the input transition-adjoint, as an equality of the constructed morphisms.
Source: node proof step 1 (blueprint: lem-coef-ramified-scalar-system-transpose).
Proof: transpose both sides through scalar restriction. The evaluation comparison
is normalized by precisely this transpose. Both sides are therefore the same
strict transition of the derived coefficient-system extension. -/
theorem scalar_transition (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (M : Derived (lowerRings l E) (lowerMaps l E) W) :
    red (upperRings l E L i) (upperMaps l E L i) W h
        ((scalarData l E L i W).scalar.T.obj M) ≫
        (scalarEvaluation l E L i W n).hom.app M =
      (tensor (quotientMap (upperRings l E L i) (upperMaps l E L i) h).hom W).map
          ((scalarEvaluation l E L i W m).hom.app M) ≫
        (reassociate l E L i W h).hom.app ((level (lowerRings l E) (lowerMaps l E) W m).obj M) ≫
        (tensor (inclusion l E L i n) W).map
          (red (lowerRings l E) (lowerMaps l E) W h M) := by
  sorry

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  {f : X ⟶ Y} (c : Compactification f)

/-- The canonical proper/open coefficient comparison, restricted without changing
its underlying system map. This definition uses no finite evaluations.
Source: node alpha (blueprint: lem-coef-ramified-scalar-system-transpose).
Proof of naturality: the ambient coefficientComparison is already natural; full
subcategory inclusion preserves its maps and reflects equality. -/
theorem comparison_naturality
    (rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c)
    (rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c)
    {M N : (domain (lowerRings l E) (lowerMaps l E) X).FullSubcategory} (g : M ⟶ N) :
    ((rR.F ⋙ T l E L i Y).map g).hom ≫
        (coefficientComparison l E L i c).app N.obj =
      (coefficientComparison l E L i c).app M.obj ≫
        ((T l E L i X ⋙ rS.F).map g).hom := by
  exact (coefficientComparison l E L i c).naturality g.hom

/-- The proper coefficient projection followed by open tensor balancing, in the
ordinary derived-system category, before evaluation.
Source: node alpha (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def comparison
    (rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c)
    (rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c) :
    rR.F ⋙ T l E L i Y ⟶ T l E L i X ⋙ rS.F where
  app M := ObjectProperty.homMk ((coefficientComparison l E L i c).app M.obj)
  naturality {_ _} g :=
    ObjectProperty.hom_ext _ (comparison_naturality l E L i c rR rS g)

/-- The finite coefficient comparison is the fixed proper/open scalar-adjunction mate.
Its source and target are ambient fixed-module derived categories.
Source: node canonical finite alpha_n
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
def finiteComparison (n : ℕ) :
    lower (lowerRings l E n) c ⋙ tensor (inclusion l E L i n) Y ⟶
      tensor (inclusion l E L i n) X ⋙ lower (upperRings l E L i n) c :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (inclusion l E L i n)))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) (inclusion l E L i n)))).symm
        (TwoSquare.mk _ _ _ _
          (ProEtale.compactSupportRestrictionIso (inclusion l E L i n) c).hom)).natTrans

/-- The exceptional transpose is the ordinary mate of the inverse comparison.
Source: node b and lambda (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def transpose
    (rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c)
    (rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c)
    (α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F) :
    rR.G ⋙ T l E L i X ⟶ T l E L i Y ⋙ rS.G :=
  (mateEquiv rR.adjunction rS.adjunction (TwoSquare.mk _ _ _ _ α.inv)).natTrans

/-- The lambda arrow is an entire-system arrow made from the same system counit.
Source: node displayed lambda (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def lambda
    (rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c)
    (rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c)
    (α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F)
    (N : (domain (lowerRings l E) (lowerMaps l E) Y).FullSubcategory) :=
  α.inv.app (rR.G.obj N) ≫ (T l E L i Y).map (rR.adjunction.counit.app N)

/-- The counit identity holds in the ordinary derived category of entire systems.
Source: node third conclusion (blueprint: lem-coef-ramified-scalar-system-transpose).
Proof: expand the ordinary mate as E_S(lambda) after eta_S. Naturality of epsilon_S
moves lambda outside; its triangle identity cancels F_S(eta_S) with epsilon_S.
Naturality of the same three factors also proves that these are the components of
the natural transformation transpose. No evaluation or inverse limit is used. -/
theorem transpose_counit
    (rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c)
    (rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c)
    (α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F)
    (N : (domain (lowerRings l E) (lowerMaps l E) Y).FullSubcategory) :
    rS.F.map ((transpose l E L i c rR rS α).app N) ≫
        rS.adjunction.counit.app ((T l E L i Y).obj N) = lambda l E L i c rR rS α N := by
  exact mateEquiv_counit rR.adjunction rS.adjunction
    (TwoSquare.mk _ _ _ _ α.inv) N

/-- A finite-sum leg in scalar extension is the tensor unit followed by multiplication
by the indicated coefficient. This fixes the reduced-basis coordinates canonically.
Source: node finite-sum distributivity
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
def basisLeg (W : Scheme.{u}) (n : ℕ)
    (K : AlgebraicGeometry.FiniteCoefficientAdjoints.D (lowerRings l E n) W)
    (b : upperRings l E L i n) :=
  (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W)
        (inclusion l E L i n))).unit.app K ≫
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W) (inclusion l E L i n)).map
      (b • 𝟙 ((tensor (inclusion l E L i n) W).obj K))

/-- The finite coordinate of the actual system transpose, with both exceptional and
scalar evaluation comparisons included explicitly.
Source: node finite b formula (blueprint: lem-coef-ramified-scalar-system-transpose). -/
def evaluatedTranspose
    (rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c)
    (rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c)
    (α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F) (n : ℕ)
    (N : (domain (lowerRings l E) (lowerMaps l E) Y).FullSubcategory) :=
  (tensor (inclusion l E L i n) X).map (((rR.right n).inv.app N).hom) ≫
    (scalarEvaluation l E L i X n).inv.app (rR.G.obj N).obj ≫
    (level (upperRings l E L i) (upperMaps l E L i) X n).map
      (((transpose l E L i c rR rS α).app N).hom) ≫
    ((rS.right n).hom.app ((T l E L i Y).obj N)).hom ≫
    (upper (upperRings l E L i n) c).map
      ((scalarEvaluation l E L i Y n).hom.app N.obj)


attribute [local irreducible] red reassociate comparison finiteComparison
attribute [local irreducible] transpose lambda basisLeg evaluatedTranspose

/-- All finite-coordinate conclusions, for the actual system comparison and mate.
The Change records fix the finite projection maps by their etale-origin witnesses;
their mate and both adjunction equations use those same finite adjunctions.
Source: node finite comparison, transpose, and quotient-square clauses
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
structure FiniteCompatibilityLaws
    (rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c)
    (rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c)
    (α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F)
    (change : ∀ n : ℕ,
      Change (inclusion l E L i n) c (rR.finite n) (rS.finite n)) : Prop where
  /-- The finite comparison is the specified proper/open map, on every finite input. -/
  canonical : ∀ (n : ℕ) (K : (ctf (lowerRings l E n) X).FullSubcategory),
    (change n).projection.hom.app K = (finiteComparison l E L i c n).app K.obj
  /-- Evaluation of the whole-system map is precisely this finite comparison. -/
  comparison_evaluation : ∀ (n : ℕ)
    (M : (domain (lowerRings l E) (lowerMaps l E) X).FullSubcategory),
    (level (upperRings l E L i) (upperMaps l E L i) Y n).map
        ((α.hom.app M).hom) ≫
        ((rS.left n).hom.app ((T l E L i X).obj M)).hom ≫
        (lower (upperRings l E L i n) c).map
          ((scalarEvaluation l E L i X n).hom.app M.obj) =
      (scalarEvaluation l E L i Y n).hom.app (rR.F.obj M).obj ≫
        (tensor (inclusion l E L i n) Y).map (((rR.left n).hom.app M).hom) ≫
        (change n).projection.hom.app
          ((evaluation (lowerRings l E) (lowerMaps l E) X n).obj M)
  /-- Evaluation is the finite exceptional counit transpose, with no faithfulness claim. -/
  transpose_evaluation : ∀ (n : ℕ)
    (N : (domain (lowerRings l E) (lowerMaps l E) Y).FullSubcategory),
    evaluatedTranspose l E L i c rR rS α n N =
      (change n).mate.hom.app
        ((evaluation (lowerRings l E) (lowerMaps l E) Y n).obj N)
  /-- Every finite coefficient square commutes, including its specified quotient maps. -/
  comparison_quotient : ∀ {m n : ℕ} (h : n ≤ m)
    (K : (ctf (lowerRings l E m) X).FullSubcategory),
    (tensor (quotientMap (upperRings l E L i) (upperMaps l E L i) h).hom Y).map
        ((change m).projection.hom.app K) ≫
        (rS.quotient h).projection.hom.app
          ⟨(tensor (inclusion l E L i m) X).obj K.obj,
            (change m).tensor_preserves_X K.obj K.property⟩ ≫
        (lower (upperRings l E L i n) c).map
          ((reassociate l E L i X h).hom.app K.obj) =
      (reassociate l E L i Y h).hom.app ((lower (lowerRings l E m) c).obj K.obj) ≫
        (tensor (inclusion l E L i n) Y).map ((rR.quotient h).projection.hom.app K) ≫
        (change n).projection.hom.app
          ⟨(tensor (quotientMap (lowerRings l E) (lowerMaps l E) h).hom X).obj K.obj,
            (rR.quotient h).tensor_preserves_X K.obj K.property⟩
  /-- In every reduction of a single integral basis, the underlying finite map is
  finite-sum distributivity, characterized on each canonical summand inclusion. -/
  finite_sum : ∀ (d : ℕ) (b : Fin d → Padic.coefficientExtensionIntegers l L),
    Function.Bijective (fun a : Fin d → Padic.coefficientExtensionIntegers l E ↦
      ∑ j, integralScalarIntegerInclusion l E L i (a j) * b j) →
    ∀ (n : ℕ) (K : (ctf (lowerRings l E n) X).FullSubcategory) (j : Fin d),
      basisLeg l E L i Y n ((lower (lowerRings l E n) c).obj K.obj)
          (Ideal.Quotient.mk (upperStage l E L i n).ideal (b j)) ≫
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y)
            (inclusion l E L i n)).map ((change n).projection.hom.app K) =
        (lower (lowerRings l E n) c).map
            (basisLeg l E L i X n K.obj
              (Ideal.Quotient.mk (upperStage l E L i n).ideal (b j))) ≫
          (ProEtale.compactSupportRestrictionIso (inclusion l E L i n) c).hom.app
            ((tensor (inclusion l E L i n) X).obj K.obj)
  /-- The full explicit quotient square, with the retained upper quotient maps. -/
  quotient_square : ∀ {m n : ℕ} (h : n ≤ m)
    (N : (domain (lowerRings l E) (lowerMaps l E) Y).FullSubcategory),
    (tensor (quotientMap (upperRings l E L i) (upperMaps l E L i) h).hom X).map
        (evaluatedTranspose l E L i c rR rS α m N) ≫
        (rS.quotient h).mate.hom.app
          ⟨(tensor (inclusion l E L i m) Y).obj
              ((level (lowerRings l E) (lowerMaps l E) Y m).obj N.obj),
            (change m).tensor_preserves_Y _
              (((evaluation (lowerRings l E) (lowerMaps l E) Y m).obj N).property)⟩ ≫
        (upper (upperRings l E L i n) c).map
          ((reassociate l E L i Y h).hom.app
              ((level (lowerRings l E) (lowerMaps l E) Y m).obj N.obj) ≫
            (tensor (inclusion l E L i n) Y).map
              (red (lowerRings l E) (lowerMaps l E) Y h N.obj)) =
      (reassociate l E L i X h).hom.app
          ((upper (lowerRings l E m) c).obj
            ((level (lowerRings l E) (lowerMaps l E) Y m).obj N.obj)) ≫
        (tensor (inclusion l E L i n) X).map
          ((rR.quotient h).mate.hom.app
              ((evaluation (lowerRings l E) (lowerMaps l E) Y m).obj N) ≫
            (upper (lowerRings l E n) c).map
              (red (lowerRings l E) (lowerMaps l E) Y h N.obj)) ≫
        evaluatedTranspose l E L i c rR rS α n N

/-- Finite comparison data together with all six proof-only compatibility laws.
Source: the finite-coordinate clauses of the node
(blueprint: lem-coef-ramified-scalar-system-transpose).
The proof-only package changes only the representation: its projections are the
same equalities, with exactly the same finite comparison data. -/
structure FiniteCompatibility
    (rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c)
    (rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c)
    (α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F) where
  change : ∀ n : ℕ,
    Change (inclusion l E L i n) c (rR.finite n) (rS.finite n)
  laws : FiniteCompatibilityLaws l E L i c rR rS α change

variable {l E L i c}

/-- The `canonical` law of the finite comparison package. -/
abbrev FiniteCompatibility.canonical
    {rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c}
    {rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c}
    {α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F}
    (fc : FiniteCompatibility l E L i c rR rS α)
    (n : ℕ) (K : (ctf (lowerRings l E n) X).FullSubcategory) :=
  fc.laws.canonical n K

/-- The `comparison_evaluation` law of the finite comparison package. -/
abbrev FiniteCompatibility.comparison_evaluation
    {rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c}
    {rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c}
    {α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F}
    (fc : FiniteCompatibility l E L i c rR rS α)
    (n : ℕ)
    (M : (domain (lowerRings l E) (lowerMaps l E) X).FullSubcategory) :=
  fc.laws.comparison_evaluation n M

/-- The `transpose_evaluation` law of the finite comparison package. -/
abbrev FiniteCompatibility.transpose_evaluation
    {rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c}
    {rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c}
    {α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F}
    (fc : FiniteCompatibility l E L i c rR rS α)
    (n : ℕ)
    (N : (domain (lowerRings l E) (lowerMaps l E) Y).FullSubcategory) :=
  fc.laws.transpose_evaluation n N

/-- The `comparison_quotient` law of the finite comparison package. -/
abbrev FiniteCompatibility.comparison_quotient
    {rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c}
    {rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c}
    {α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F}
    (fc : FiniteCompatibility l E L i c rR rS α)
    {m n : ℕ} (h : n ≤ m)
    (K : (ctf (lowerRings l E m) X).FullSubcategory) :=
  fc.laws.comparison_quotient h K

/-- The `finite_sum` law of the finite comparison package. -/
theorem FiniteCompatibility.finite_sum
    {rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c}
    {rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c}
    {α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F}
    (fc : FiniteCompatibility l E L i c rR rS α) :
    ∀ (d : ℕ) (b : Fin d → Padic.coefficientExtensionIntegers l L),
    Function.Bijective (fun a : Fin d → Padic.coefficientExtensionIntegers l E ↦
      ∑ j, integralScalarIntegerInclusion l E L i (a j) * b j) →
    ∀ (n : ℕ) (K : (ctf (lowerRings l E n) X).FullSubcategory) (j : Fin d),
      basisLeg l E L i Y n ((lower (lowerRings l E n) c).obj K.obj)
          (Ideal.Quotient.mk (upperStage l E L i n).ideal (b j)) ≫
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y)
            (inclusion l E L i n)).map ((fc.change n).projection.hom.app K) =
        (lower (lowerRings l E n) c).map
            (basisLeg l E L i X n K.obj
              (Ideal.Quotient.mk (upperStage l E L i n).ideal (b j))) ≫
          (ProEtale.compactSupportRestrictionIso (inclusion l E L i n) c).hom.app
            ((tensor (inclusion l E L i n) X).obj K.obj) :=
  fc.laws.finite_sum

/-- The `quotient_square` law of the finite comparison package. -/
abbrev FiniteCompatibility.quotient_square
    {rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c}
    {rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c}
    {α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F}
    (fc : FiniteCompatibility l E L i c rR rS α)
    {m n : ℕ} (h : n ≤ m)
    (N : (domain (lowerRings l E) (lowerMaps l E) Y).FullSubcategory) :=
  fc.laws.quotient_square h N

variable (l E L i c)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [xb : X.Over (Spec (.of D.k))] [yb : Y.Over (Spec (.of D.k))]
  [xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [xs : IsSeparated (X ↘ Spec (.of D.k))] [ys : IsSeparated (Y ↘ Spec (.of D.k))]
  [fb : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]

include D hl xb yb xft xqc yft yqc xs ys fb fs fft fqc in
/-- Ramified scalar systems have the canonical compact-support comparison and its
coherent ordinary exceptional transpose. The displayed natural isomorphism is fixed
by the ambient proper/open map; it is never selected from its finite evaluations.
The system realizations retain the specified finite adjunctions, quotient cocycles,
and both units and counits, on the individual bounded finite-Tor levels.
Source: node all clauses; current blueprint det-prop-scalar-six-compact-support and
 det-prop-scalar-six-exceptional, definition and formal-properties paragraph
(blueprint: lem-coef-ramified-scalar-system-transpose).
Proof: use the actual semilinear ring-system extension. Scalar transition is tensor
reassociation followed by the input reduction, so finite freeness and the one reduced
integral basis give normalization and preserve each level's own constructible Tor
interval. The system proper projection followed by open balancing is the scalar mate
of the section-normalized restriction comparison. In the fixed reduced basis its
restriction is finite-sum distributivity, hence it is invertible, independently of
the basis. Construct the stipulated system adjunctions by cartesian adjoint descent;
for S retain the cofinal exponents en with their composite quotient maps, using the
cofinality clause of etaleCoefficientSystemAdjoint. Their simultaneous realizations
preserve finite units and counits. Their left evaluation is compositorSupportEvaluation
transported by the section-normalized constant-scalar comparisons and the identity
constant-diagram evaluation; this gives left_canonical and excludes support twists.
Define b by the ordinary mateEquiv, equivalently
E_S(lambda) after eta_S. Its system counit equation follows from naturality and the
triangle identity before evaluation. Evaluate this constructed word using the same
finite units and counits: it is exactly the finite counit transpose. Substitute the
exceptional-transition and scalar-transition formulas into transition naturality of
this actual b to obtain quotient_square. The finite quotient cocycle, identity, and
unit/counit laws are retained by the same substitution, including m=n. Nothing is
reconstructed from finite evaluations, and no bound is chosen uniformly in n. -/
theorem ramifiedScalarSystemTranspose (ramification : ℕ) (_he : 0 < ramification)
    (_hram : Associated
      (integralScalarIntegerInclusion l E L i (Padic.coefficientExtensionUniformizer l E))
      (Padic.coefficientExtensionUniformizer l L ^ ramification)) :
    ∃ (rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c)
      (rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c)
      (α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F),
      (∀ n : ℕ, (upperStage l E L i n).ideal =
        Padic.coefficientExtensionIdeal l L (ramification * (n + 1))) ∧
      α.hom = comparison l E L i c rR rS ∧
      Nonempty (FiniteCompatibility l E L i c rR rS α) ∧
      (∀ N : (domain (lowerRings l E) (lowerMaps l E) Y).FullSubcategory,
        rS.F.map ((transpose l E L i c rR rS α).app N) ≫
          rS.adjunction.counit.app ((T l E L i Y).obj N) =
            lambda l E L i c rR rS α N) := by
  sorry

end WeilConjectures.RamifiedScalarSystemTranspose
