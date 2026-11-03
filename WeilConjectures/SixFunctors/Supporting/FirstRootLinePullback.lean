/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
import all WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.Pur.PurIntegralTensorTransport
public import WeilConjectures.AlgebraicGeometry.Pur.PurIntegralTwistLineInverseImage

/-! # Root-normalized first-line inverse image

Source: coefficient-twist conventions, first-line inverse image and scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
set_option synthInstance.maxSize 2048
attribute [local irreducible] AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.purTwistZlOne
  AlgebraicGeometry.Scheme.proEtaleRootsOfUnityTower
  WeilConjectures.PurCompactSupport.completed
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

end WeilConjectures

namespace WeilConjectures

/-- The first completed root line is cartesian, with its scalar/root normalization.
Source: `def-coefficient-twists-detailed`, scheme naturality, and
`lem-pur-integral-twist-line-inverse-image`, Integral twist paragraph.
(blueprint: lem-sf-first-root-line-pullback).
Proof: the specified completed coefficient comparison has the required finite
projections. The cartesian root-limit comparison agrees with rootLineMap, by all
root projections. Apply the normalized integral tensor transport theorem to these
coefficient and root maps.
Transpose the additive line map under the inverse-image adjunction. Its completed
semilinearity makes it a map into the module direct image. Transpose under the
module adjunction to get the displayed linear map. The underlying module inverse
image agrees with the additive inverse image when the coefficient comparison is
an isomorphism: scalar extension along that isomorphism is restriction along its
inverse. Thus the linear map is invertible. The tensor formula at constant scalar
one, followed by completed semilinearity, gives the formula for every scalar a.
All comparisons are defined by universal properties, including on the empty site. -/
theorem sfFirstRootLinePullback_exists
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ t : (FrobeniusCoefficientTwists.modulePull l E g).obj
        (purTwistIntegralModule Y l E) ≅ purTwistIntegralModule X l E,
      ∀ (V : Y.ProEt)
        (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
          (Opposite.op V)) (x : Fin 1 → (purTwistZlOne Y l).obj.obj (Opposite.op V)),
        t.hom.val.app (Opposite.op ((proEtaleBaseChange g).obj V))
          (FrobeniusCoefficientTwists.moduleSection l E g
            (FrobeniusCoefficientTwists.positiveLine l E Y 1) V
            (FrobeniusCoefficientTwists.generator l E Y (Opposite.op V) a 1 x)) =
        FrobeniusCoefficientTwists.generator l E X
          (Opposite.op ((proEtaleBaseChange g).obj V))
          ((sfCompletedCoefficientMap l E g).hom.app (Opposite.op V) a) 1
          (fun i ↦ FrobeniusCoefficientTwists.rootSection l g V (x i)) := by
  let R := (PurCompactSupport.completed l E).ring Y
  let S := (PurCompactSupport.completed l E).ring X
  let c := (PurCompactSupport.completed l E).pull g
  let M := purTwistIntegralModule Y l E
  let N := purTwistIntegralModule X l E
  have hc : IsPurIntegralCoefficientComparison g l E c.hom :=
    PurCompactSupport.completedPull_projection l E g
  have hr : IsPurRootLimitComparison g l (FrobeniusCoefficientTwists.rootLineMap l g) := by
    intro n
    change (limit.post (proEtaleRootsOfUnityTower Y l Fact.out)
      (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) ≫
        lim.map (FrobeniusCoefficientTwists.rootTowerMap l g)) ≫
          limit.π (proEtaleRootsOfUnityTower X l Fact.out) (Opposite.op n) = _
    calc
      _ = limit.post _ _ ≫
          (limit.π ((proEtaleRootsOfUnityTower Y l Fact.out) ⋙
            proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) (Opposite.op n) ≫
              (FrobeniusCoefficientTwists.rootTowerMap l g).app (Opposite.op n)) := by
        rw [Category.assoc]
        exact congrArg (_ ≫ ·) (limMap_π _ _)
      _ = _ := by
        rw [limit.post_π_assoc]
        rfl
  obtain ⟨r, hri, hrp⟩ := root_comparison_exists g l
  have her : r = FrobeniusCoefficientTwists.rootLineMap l g := by
    apply limit.hom_ext
    intro n
    exact (hrp n.unop).trans (hr n.unop).symm
  have : IsIso (FrobeniusCoefficientTwists.rootLineMap l g) := her ▸ hri
  obtain ⟨ρ, hρ, htensor, hscalar⟩ := pur_integral_tensor_transport g l E c.hom
    (FrobeniusCoefficientTwists.rootLineMap l g) hc hr
  let a := proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}
  let φ := (a.homEquiv _ _) ρ
  let ψ : M ⟶ (proEtaleRingModuleDirectImage g R S c).obj N :=
    { val :=
      { app := fun W ↦
          ConcreteCategory.ofHom
            (C := ModuleCat.{u + 1}
              ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj W))
            (X := M.val.obj W)
            (Y := ((proEtaleRingModuleDirectImage g R S c).obj N).val.obj W)
            { toFun := fun x ↦ (φ.hom.app W).hom x
              map_add' := fun x y ↦ map_add (φ.hom.app W).hom x y
              map_smul' := fun b x ↦ hscalar W b x }
        naturality := by
          intro U W f
          ext x
          exact congrArg (fun k ↦ k.hom x) (φ.hom.naturality f) } }
  let adj := proEtaleRingModuleAdjunction g R S c
  let f : (FrobeniusCoefficientTwists.modulePull l E g).obj M ⟶ N :=
    (adj.homEquiv M N).symm ψ
  have hf (W : Y.ProEtᵒᵖ) (x : M.val.obj W) :
      f.val.app ((proEtaleBaseChange g).op.obj W)
        (FrobeniusCoefficientTwists.moduleSection l E g M W.unop x) =
          φ.hom.app W x := by
    have h := (adj.homEquiv M N).apply_symm_apply ψ
    rw [Adjunction.homEquiv_unit] at h
    exact congrArg (fun k ↦ k.val.app W x) h
  let U := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
  let V := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let k := (a.homEquiv (V.obj M) (U.obj
    ((FrobeniusCoefficientTwists.modulePull l E g).obj M))).symm
      (V.map (adj.unit.app M))
  have hk : IsIso k := AlgebraicGeometry.ProEtale.pullback_unit_mate_isIso g R S c M
  have he : k ≫ U.map f = ρ := by
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right]
    have hkadj : (a.homEquiv (V.obj M) (U.obj
        ((FrobeniusCoefficientTwists.modulePull l E g).obj M))) k =
        V.map (adj.unit.app M) := Equiv.apply_symm_apply _ _
    rw [hkadj]
    ext W x
    exact hf W x
  have : IsIso (k ≫ U.map f) := he.symm ▸ hρ
  have : IsIso (U.map f) := IsIso.of_isIso_comp_left k _
  have : IsIso f := isIso_of_reflects_iso f U
  refine ⟨asIso f, ?_⟩
  intro W b x
  change f.val.app _ (FrobeniusCoefficientTwists.moduleSection l E g M W
    (@SMul.smul _ _ (purTwistIntegralAction Y l E (Opposite.op W)).toSMul b
      (purTwistIntegralTensor Y l E (Opposite.op W) 1 (x 0)))) = _
  refine (hf (Opposite.op W) _).trans ?_
  change φ.hom.app (Opposite.op W)
    (@SMul.smul _ _ (purTwistIntegralAction Y l E (Opposite.op W)).toSMul b
      (purTwistIntegralTensor Y l E (Opposite.op W) 1 (x 0))) = _
  refine (hscalar (Opposite.op W) b
    (purTwistIntegralTensor Y l E (Opposite.op W) 1 (x 0))).trans ?_
  erw [htensor]
  have hcoeff : ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _)
      c.hom = sfCompletedCoefficientMap l E g := Equiv.apply_symm_apply _ _
  erw [hcoeff]
  simp only [map_one]
  rfl

end WeilConjectures
