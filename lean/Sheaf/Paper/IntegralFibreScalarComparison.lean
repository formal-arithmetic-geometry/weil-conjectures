/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module
public import Sheaf.Paper.FibreFunctorBasepointTransportData
public import Sheaf.Paper.LisseIntegralScalarFiberIsomorphism
import Sheaf.Paper.FibreFunctorLinearTransport
public import Sheaf.Paper.IntegralFibrePathConstruction

/-! # The prescribed integral fibre scalar comparison

Source: Deligne, Weil II (1.1.1) b), d), pp.146-147.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type (u + 1)) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical integral scalar comparison as a natural isomorphism.
Source: Weil II (1.1.1) b), d), pp.146-147.
(blueprint: new-e5-integral-fibre-scalar-comparison). -/
@[irreducible]
def integralFibreScalarIso :
    lisseIntegralFiberFunctor l E Y y ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1}
      (lisseIntegerInclusion l E L ι) ≅
    lisseIntegralScalarExtension l E Y L ι ⋙ lisseIntegralFiberFunctor l L Y y := by
  unfold lisseIntegralScalarExtension
  refine NatIso.ofComponents (fun F ↦ ?_) (fun f ↦ ?_)
  · change (ModuleCat.ringExtendScalars.{u + 1, u + 1}
        (lisseIntegerInclusion l E L ι)).obj (lisseIntegralFiber l E Y y F) ≅
      lisseIntegralFiber l L Y y
        ((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F)
    letI := lisseIntegralScalarFiberComparison_isIso Y y l E L ι F
    exact asIso (lisseIntegralScalarFiberComparison Y y l E L ι F)
  · exact lisseIntegralScalarFiberComparison_naturality Y y l E L ι f

/-- The integral scalar comparison on the canonical scalar-extension unit.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-integral-fibre-scalar-comparison). -/
@[irreducible]
def integralFibreScalarUnit (F : LisseIntegralSheaf l E Y)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F) :
    (lisseIntegralFiberFunctor l L Y y).obj
      ((lisseIntegralScalarExtension l E Y L ι).obj F) :=
  (integralFibreScalarIso l Y y E L ι).hom.app F
    ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1}
      (lisseIntegerInclusion l E L ι)).unit.app _ x)

/-- The scalar unit is the comparison of the coefficient-one tensor.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-integral-fibre-scalar-comparison).
Proof: a coefficient-one tensor is the adjunction unit. -/
theorem integralFibreScalarUnit_eq (F : LisseIntegralSheaf l E Y)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F) :
    integralFibreScalarUnit l Y y E L ι F x =
      (integralFibreScalarIso l Y y E L ι).hom.app F
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1}
          (lisseIntegerInclusion l E L ι) _ 1 x) := by
  unfold integralFibreScalarUnit
  simp only [ModuleCat.ringExtensionTmul, one_smul]

/-- Every scalar coefficient has the prescribed finite-level germ formula.
Source: Weil II (1.1.1) b), d), pp.146-147.
(blueprint: new-e5-integral-fibre-scalar-comparison).
Proof: the existing comparison has this formula for coefficient one. Its linearity,
linearity of the limit projections and stalk maps, and the definition of the scalar
generator give the formula after multiplying by b. -/
theorem integralFibreScalarIso_germ
    (F : LisseIntegralSheaf l E Y) (m : ℕ) (U : Y.Etale)
    (ξ : (pointSmallEtale y).fiber.obj U)
    (b : Padic.coefficientExtensionIntegers l L)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F)
    (s : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U))
    (hs : limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber)
        (op (lisseScalarSourceIndex l E L ι m)) x =
      (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨ξ⟩
        (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj s) :
    ((pointSmallEtale y).ulift.{u + 1}.sheafFiber).map
      (pathIntegralScalarLevelIso l Y E L ι F m).hom
      (limit.π (((lisseIntegralScalarExtension l E Y L ι).obj F).obj ⋙
        (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op m)
        ((integralFibreScalarIso l Y y E L ι).hom.app F
          (ModuleCat.ringExtensionTmul.{u + 1, u + 1}
            (lisseIntegerInclusion l E L ι) _ b x))) =
      (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨ξ⟩
        (lisseIntegralScalarLevel l E Y L ι F m).obj
        (lisseIntegralScalarGenerator l E Y L ι F m U
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (m + 1)) b) s) := by
  unfold integralFibreScalarIso pathIntegralScalarLevelIso lisseIntegralScalarExtension
  dsimp only [id_eq, NatIso.ofComponents_hom_app, asIso_hom]
  have h := lisseIntegralScalarFiberComparison_spec Y y l E L ι F m x U ⟨ξ⟩ s hs
  have hx : ModuleCat.ringExtensionTmul.{u + 1, u + 1} (lisseIntegerInclusion l E L ι) _ b x =
      b • ModuleCat.ringExtensionTmul.{u + 1, u + 1} (lisseIntegerInclusion l E L ι) _ 1 x := by
    simp only [ModuleCat.ringExtensionTmul, one_smul]
  rw [hx, map_smul, map_smul, map_smul]
  erw [h]
  have hgen : b • lisseIntegralScalarGenerator l E Y L ι F m U 1 s =
      lisseIntegralScalarGenerator l E Y L ι F m U
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (m + 1)) b) s := by
    let r := lisseScalarCoefficientMap l E L ι m
    let Fₙ := F.obj.obj (op (lisseScalarSourceIndex l E L ι m))
    let q := (toSheafification Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l L (m + 1)))).app
        (Fₙ.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} r)
    let v : (ModuleCat.ringExtendScalars.{u + 1, u + 1} r).obj
        (Fₙ.obj.obj (op U)) :=
      (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).unit.app _ s
    have hg := (q.app (op U)).hom.map_smul
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (m + 1)) b)
        v
    simp only [lisseIntegralScalarGenerator, lisseIntegralScalarLevel,
      sheafCompose_obj_obj, Functor.comp_obj, ModuleCat.ringExtensionTmul, one_smul]
    exact hg.symm
  exact ((map_smul
    (((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨ξ⟩
      (lisseIntegralScalarLevel l E Y L ι F m).obj).hom) b _).symm).trans
      (congrArg _ hgen)

private def integralScalarSetUnit (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    galoisUnderlyingSetSheaf (Padic.coefficientExtensionIntegers l E)
        (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))) ⟶
      galoisUnderlyingSetSheaf (Padic.coefficientExtensionIntegers l L)
        (((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F).obj.obj (op m)) where
  hom :=
    let Fₙ := F.obj.obj (op (lisseScalarSourceIndex l E L ι m))
    let r := lisseScalarCoefficientMap l E L ι m
    Functor.whiskerRight (Functor.whiskerLeft Fₙ.obj
      (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).unit)
      (CategoryTheory.forget (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))) ≫
    Functor.whiskerRight
      (toSheafify Y.smallEtaleTopology
        (Fₙ.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} r))
      (CategoryTheory.forget (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l L (m + 1)))) ≫
    Functor.whiskerRight
      ((lisseIntegralScalarExtensionData l E Y L ι).levelIso F m).inv.hom
      (CategoryTheory.forget (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)))

set_option backward.isDefEq.respectTransparency false in
private theorem integralScalarSetUnit_stalk (F : LisseIntegralSheaf l E Y) (m : ℕ)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F) :
    pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l L)
      (((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F).obj.obj (op m))
      (limit.π (((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F).obj ⋙
        (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op m)
        (lisseIntegralScalarFiberComparison Y y l E L ι F
          ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1}
            (lisseIntegerInclusion l E L ι)).unit.app _ x))) =
      (pointSmallEtale y).sheafFiber.map (integralScalarSetUnit l Y E L ι F m)
        (pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E)
          (F.obj.obj (op (lisseScalarSourceIndex l E L ι m)))
          (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber)
            (op (lisseScalarSourceIndex l E L ι m)) x)) := by
  let p := (pointSmallEtale y).ulift.{u + 1}
  let D := lisseIntegralScalarExtensionData l E Y L ι
  let Fₙ := F.obj.obj (op (lisseScalarSourceIndex l E L ι m))
  let H := (D.functor.obj F).obj.obj (op m)
  let C := lisseIntegralScalarLevel l E Y L ι F m
  let α := lisseIntegerInclusion l E L ι
  obtain ⟨U, ⟨ξ⟩, s, hs⟩ := p.toPresheafFiber_jointly_surjective (P := Fₙ.obj)
    (limit.π (F.obj ⋙ p.sheafFiber) (op (lisseScalarSourceIndex l E L ι m)) x)
  let g := lisseIntegralScalarGenerator l E Y L ι F m U 1 s
  have hc := lisseIntegralScalarFiberComparison_spec Y y l E L ι F m x U ⟨ξ⟩ s hs.symm
  simp only [ModuleCat.ringExtensionTmul, one_smul] at hc
  have hv : limit.π ((D.functor.obj F).obj ⋙ p.sheafFiber) (op m)
      (lisseIntegralScalarFiberComparison Y y l E L ι F
        ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} α).unit.app _ x)) =
      p.sheafFiber.map (D.levelIso F m).inv (p.toPresheafFiber U ⟨ξ⟩ C.obj g) := by
    apply (ConcreteCategory.bijective_of_isIso
      (p.sheafFiber.map (D.levelIso F m).hom)).injective
    exact hc.trans (ConcreteCategory.congr_hom
      (p.sheafFiber.mapIso (D.levelIso F m)).inv_hom_id _).symm
  have hn := ConcreteCategory.congr_hom
    (p.toPresheafFiber_naturality (D.levelIso F m).inv.hom U ⟨ξ⟩) g
  have hn' : p.sheafFiber.map (D.levelIso F m).inv (p.toPresheafFiber U ⟨ξ⟩ C.obj g) =
      p.toPresheafFiber U ⟨ξ⟩ H.obj ((D.levelIso F m).inv.hom.app (op U) g) := hn
  calc
    _ = pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l L) H
        (p.toPresheafFiber U ⟨ξ⟩ H.obj ((D.levelIso F m).inv.hom.app (op U) g)) :=
      congrArg _ (hv.trans hn')
    _ = (pointSmallEtale y).toPresheafFiber U ξ
        (galoisUnderlyingSetSheaf (Padic.coefficientExtensionIntegers l L) H).obj
        ((D.levelIso F m).inv.hom.app (op U) g) :=
      pathUnderlyingStalk_germ y _ H U ξ _
    _ = (pointSmallEtale y).sheafFiber.map (integralScalarSetUnit l Y E L ι F m)
        ((pointSmallEtale y).toPresheafFiber U ξ
          (galoisUnderlyingSetSheaf (Padic.coefficientExtensionIntegers l E) Fₙ).obj s) := by
      have h := ConcreteCategory.congr_hom
        ((pointSmallEtale y).toPresheafFiber_naturality
          (integralScalarSetUnit l Y E L ι F m).hom U ξ) s
      simp only [integralScalarSetUnit, lisseIntegralScalarGenerator,
        ModuleCat.ringExtensionTmul, one_smul, ConcreteCategory.comp_apply,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        GrothendieckTopology.Point.sheafFiber, Functor.comp_map,
        sheafToPresheaf, ObjectProperty.ι_map, toSheafify, toSheafification, D, H, g, Fₙ,
        lisseIntegralScalarLevel,
        sheafCompose_obj_obj, Functor.comp_obj, TypeCat.ofHom_apply] at h ⊢
      with_unfolding_all exact h.symm
    _ = _ := congrArg ((pointSmallEtale y).sheafFiber.map
      (integralScalarSetUnit l Y E L ι F m))
        ((pathUnderlyingStalk_germ y _ Fₙ U ξ s).symm.trans (congrArg _ hs))

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] GrothendieckTopology.Point.sheafFiber
  GrothendieckTopology.Point.presheafFiber pathUnderlyingStalk

set_option backward.isDefEq.respectTransparency false in
/-- Integral scalar extension commutes with the normalized integral path.
Source: Weil II (1.1.1) b), d), pp.146-147.
(blueprint: new-e5-integral-fibre-scalar-comparison).
Proof: by the scalar-extension adjunction it suffices to test coefficient one.
Test the resulting equality after every inverse-limit projection and the underlying-set
stalk comparison. The comparison germ formula identifies the two sides with the
underlying-set scalar unit before and after the finite path. Naturality of that path
with respect to this unit proves their equality. -/
theorem integralFibreScalarIso_path (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (i : IntegralFibrePathTransport l Y Q)
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L)
    (F : LisseIntegralSheaf l E.val Y) :
    (ModuleCat.ringExtendScalars.{u + 1, u + 1}
      (lisseIntegerInclusion l E.val L.val (IntermediateField.inclusion h))).map
        (((i.linear E).map y z t).hom.app F) ≫
        (integralFibreScalarIso l Y z E.val L.val (IntermediateField.inclusion h)).hom.app F =
      (integralFibreScalarIso l Y y E.val L.val (IntermediateField.inclusion h)).hom.app F ≫
        ((i.linear L).map y z t).hom.app
          ((lisseIntegralScalarExtension l E.val Y L.val
            (IntermediateField.inclusion h)).obj F) := by
  let ι := IntermediateField.inclusion h
  let α := lisseIntegerInclusion l E.val L.val ι
  let adj := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} α
  let H := (lisseIntegralScalarExtensionData l E.val Y L.val ι).functor.obj F
  apply (adj.homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hu := ConcreteCategory.congr_hom
    (adj.unit.naturality (((i.linear E).map y z t).hom.app F)) x
  simp only [ModuleCat.comp_apply] at hu
  change adj.unit.app _ (((i.linear E).map y z t).hom.app F x) =
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} α).map
      (((i.linear E).map y z t).hom.app F) (adj.unit.app _ x) at hu
  unfold integralFibreScalarIso lisseIntegralScalarExtension
  dsimp only [NatIso.ofComponents_hom_app, asIso_hom, id_eq]
  change lisseIntegralScalarFiberComparison Y z l E.val L.val ι F
      ((ModuleCat.ringExtendScalars.{u + 1, u + 1} α).map
        (((i.linear E).map y z t).hom.app F) (adj.unit.app _ x)) =
    ((i.linear L).map y z t).hom.app H
      (lisseIntegralScalarFiberComparison Y y l E.val L.val ι F (adj.unit.app _ x))
  refine (congrArg (lisseIntegralScalarFiberComparison Y z l E.val L.val ι F)
    hu.symm).trans ?_
  apply Concrete.limit_ext (H.obj ⋙ (pointSmallEtale z).ulift.{u + 1}.sheafFiber)
  intro m
  have eeF := @i.evaluation Ωy inferInstance inferInstance y
    Ωz inferInstance inferInstance z t E F
    (lisseScalarSourceIndex l E.val L.val ι m.unop)
  rcases eeF with ⟨hF, eF⟩
  have eeH := @i.evaluation Ωy inferInstance inferInstance y
    Ωz inferInstance inferInstance z t L H m.unop
  rcases eeH with ⟨hH, eH⟩
  apply (pathUnderlyingStalk z (Padic.coefficientExtensionIntegers l L.val)
    (H.obj.obj m)).injective
  let f := integralScalarSetUnit l Y E.val L.val ι F m.unop
  let qx := pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E.val)
    (F.obj.obj (op (lisseScalarSourceIndex l E.val L.val ι m.unop)))
    (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber)
      (op (lisseScalarSourceIndex l E.val L.val ι m.unop)) x)
  let f₀ : galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l E.val)
      (F.obj.obj (op (lisseScalarSourceIndex l E.val L.val ι m.unop))) hF ⟶
    galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l L.val)
      (H.obj.obj m) hH := ObjectProperty.homMk f
  let A := galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l E.val)
    (F.obj.obj (op (lisseScalarSourceIndex l E.val L.val ι m.unop))) hF
  let B := galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l L.val)
    (H.obj.obj m) hH
  have hn := ConcreteCategory.congr_hom (t.hom.naturality f₀) qx
  change t.hom.app B ((pointSmallEtale y).sheafFiber.map f qx) =
    (pointSmallEtale z).sheafFiber.map f (t.hom.app A qx) at hn
  calc
    _ = (pointSmallEtale z).sheafFiber.map f
        (pathUnderlyingStalk z (Padic.coefficientExtensionIntegers l E.val)
          (F.obj.obj (op (lisseScalarSourceIndex l E.val L.val ι m.unop)))
          (limit.π (F.obj ⋙ (pointSmallEtale z).ulift.{u + 1}.sheafFiber)
            (op (lisseScalarSourceIndex l E.val L.val ι m.unop))
            (((i.linear E).map y z t).hom.app F x))) :=
      integralScalarSetUnit_stalk l Y z E.val L.val ι F m.unop _
    _ = (pointSmallEtale z).sheafFiber.map f (t.hom.app A qx) :=
      congrArg ((pointSmallEtale z).sheafFiber.map f) (eF x)
    _ = t.hom.app B ((pointSmallEtale y).sheafFiber.map f qx) := hn.symm
    _ = t.hom.app B (pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l L.val)
        (H.obj.obj m) (limit.π (H.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) m
          (lisseIntegralScalarFiberComparison Y y l E.val L.val ι F
            (adj.unit.app _ x)))) :=
      congrArg (t.hom.app B) (integralScalarSetUnit_stalk l Y y E.val L.val ι F m.unop x).symm
    _ = _ := (eH (lisseIntegralScalarFiberComparison Y y l E.val L.val ι F
      (adj.unit.app _ x))).symm


end AlgebraicGeometry.Scheme
