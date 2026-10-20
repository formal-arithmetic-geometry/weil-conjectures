/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyCoefficientTransport
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison

/-! Frobenius naturality for the fixed coherent pullback. -/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local irreducible] coherentAdditiveEndomorphism
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

private theorem comparison_conjugate
    {A B C : Type*} (e : A ≃ B) (L : B ≃ C) (f : B → B) (g : C → C)
    (h : ∀ x, L (f x) = g (L x)) (x : A) :
    e ((e.trans L).symm (g ((e.trans L) x))) = f (e x) := by
  apply L.injective
  exact ((e.trans L).apply_symm_apply _).trans (h _).symm

private theorem action_small (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ)
    (φ : (SheafOfModules.toSheaf X.ringCatSheaf).obj F ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj F)
    (v : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :
    coherentSmallResolutionEquiv X F q (coherentAdditiveEndomorphism X F q φ v) =
      (coherentExtPresentationFor X F q).smallMap φ (coherentSmallResolutionEquiv X F q v) := by
  unfold coherentAdditiveEndomorphism
  exact comparison_conjugate (coherentSmallResolutionEquiv X F q).toEquiv
    (coherentExtPresentationFor X F q).change.toEquiv
    ((coherentExtPresentationFor X F q).smallMap φ)
    ((coherentExtPresentationFor X F q).largeMap φ)
    ((coherentExtPresentationFor X F q).naturality φ) v

private theorem cancel_square
    {A B C D : Type*} (E : A → C) (E' : B → D) (hi : Function.Injective E')
    (f : A → B) (a : A → A) (b : B → B) (c : C → C) (d : D → D) (T : C → D)
    (ha : ∀ x, E (a x) = c (E x)) (hb : ∀ y, E' (b y) = d (E' y))
    (hf : ∀ x, E' (f x) = T (E x)) (hs : ∀ x, d (T x) = T (c x)) (x : A) :
    b (f x) = f (a x) := by
  apply hi
  exact (hb _).trans ((congrArg d (hf x)).trans
    ((hs _).trans ((congrArg T (ha x).symm).trans (hf _).symm)))

private noncomputable def extPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Y.Modules) (F : X.Modules) (φ : N ⟶ (pushforward f).obj F) (q : ℕ) :
    coherentSmallAbelianGroup Y N q → coherentSmallAbelianGroup X F q := fun x ↦
  Sheaf.H.map (coeff f φ) q
    (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N) q x)

private theorem resolution_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Y.Modules) (F : X.Modules) (φ : N ⟶ (pushforward f).obj F) (q : ℕ)
    (v : (RingedSpace.moduleCohomology Y.toRingedSpace q).obj N) :
    coherentSmallResolutionEquiv X F q (moduleCohomologyFMap f φ q v) =
      extPullback f N F φ q (coherentSmallResolutionEquiv Y N q v) := by
  unfold extPullback coherentSmallResolutionEquiv
  exact moduleCohomology_transport_coefficient f N F φ q
    (fun M ↦ moduleCohomologyExtResolutionEquiv Y M q)
    (moduleCohomologyExtResolutionEquiv X F q)
    (moduleCohomologyExtResolutionEquiv_naturality Y q _ _ φ)
    (moduleCohomologyExtResolutionEquiv_edge f F q) v

private theorem extPullback_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Y.Modules) (F : X.Modules) (φ : N ⟶ (pushforward f).obj F) (q : ℕ)
    (a : (SheafOfModules.toSheaf Y.ringCatSheaf).obj N ⟶
      (SheafOfModules.toSheaf Y.ringCatSheaf).obj N)
    (b : (SheafOfModules.toSheaf X.ringCatSheaf).obj F ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj F)
    (h : (invImage f).map a ≫ coeff f φ = coeff f φ ≫ b)
    (x : coherentSmallAbelianGroup Y N q) :
    extPullback f N F φ q ((coherentExtPresentationFor Y N q).smallMap a x) =
      (coherentExtPresentationFor X F q).smallMap b (extPullback f N F φ q x) := by
  unfold extPullback
  exact sheafComparison_naturality (invImage f) (constIso f).symm
    (coeff f φ) (coeff f φ) a b h q x

private theorem structural_power_square
    {X Y : Scheme.{u}} (j : Y ⟶ X) (p : ℕ)
    (FrZ : (SheafOfModules.toSheaf X.ringCatSheaf).obj (unit X) ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj (unit X))
    (FrZK : (SheafOfModules.toSheaf Y.ringCatSheaf).obj (unit Y) ⟶
      (SheafOfModules.toSheaf Y.ringCatSheaf).obj (unit Y))
    (hFrZ : ∀ (U : X.Opensᵒᵖ) (s : Γ(X, U.unop)), FrZ.hom.app U s = s ^ p)
    (hFrZK : ∀ (U : Y.Opensᵒᵖ) (s : Γ(Y, U.unop)), FrZK.hom.app U s = s ^ p) :
    (invImage j).map FrZ ≫
        coeff j (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) =
      coeff j (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫ FrZK := by
  set_option backward.isDefEq.respectTransparency false in
    refine (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      j.base).homEquiv_naturality_right_square
        (Y := (SheafOfModules.toSheaf Y.ringCatSheaf).obj (unit Y))
        (Y' := (SheafOfModules.toSheaf Y.ringCatSheaf).obj (unit Y)) FrZ
        ((SheafOfModules.toSheaf X.ringCatSheaf).map
          (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom))
        ((SheafOfModules.toSheaf X.ringCatSheaf).map
          (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)) FrZK ?_
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro s
  change (j.app U.unop).hom (FrZ.hom.app U s) =
    FrZK.hom.app (op (j ⁻¹ᵁ U.unop)) ((j.app U.unop).hom s)
  exact (congrArg (j.app U.unop).hom (hFrZ U s)).trans
    ((map_pow (G := Γ(X, U.unop)) (H := Γ(Y, j ⁻¹ᵁ U.unop))
        (j.app U.unop).hom s p).trans
      (hFrZK (op (j ⁻¹ᵁ U.unop)) ((j.app U.unop).hom s)).symm)

/-- Structural coherent pullback commutes with the supplied additive power maps.
Source: Stacks Project, Tags 01FB, 03FD and 06XR.
(blueprint: new-coherent-frobenius-pullback).

Proof: Write E and E' for the fixed module/Ext resolution comparisons. Coefficient
transport, coefficient naturality of E and the fixed identity-edge comparison give
E' fmap = H(coeff) H.mapFunctor E for the structural module coefficient map.
The adjoint of coeff is the underlying structural map of regular functions.
Since j#(s^p) = j#(s)^p, adjunction turns this equality into
invImage.map FrZ followed by coeff = coeff followed by FrZK. The exact-functor
Ext naturality square, with the constant-integer-sheaf comparison, therefore
commutes with both powers. Ext universe transport commutes with coefficient
postcomposition, by the common derived-Hom description of Ext. Consequently the
same square holds for the large presentation used in coherentAdditiveEndomorphism.
Conjugate the square by E and E' and cancel E', which is injective. This proves
the displayed equality for every module cohomology class. Neither properness nor
flatness is required. The argument includes degree zero and empty schemes. -/
theorem coherentFrobenius_pullback
    {X Y : Scheme.{u}} (j : Y ⟶ X) (p q : ℕ)
      (FrZ : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (unit X) ⟶
        (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (unit X))
      (FrZK : (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).obj (unit Y) ⟶
        (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).obj (unit Y))
      (hFrZ : ∀ (U : X.Opensᵒᵖ) (s : Γ(X, U.unop)), FrZ.hom.app U s = s ^ p)
      (hFrZK : ∀ (U : Y.Opensᵒᵖ) (s : Γ(Y, U.unop)), FrZK.hom.app U s = s ^ p)
      (v : (RingedSpace.moduleCohomology X.toRingedSpace q).obj (unit X)) :
      coherentAdditiveEndomorphism Y (unit Y) q FrZK
        (moduleCohomologyFMap j
          (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) q v) =
        moduleCohomologyFMap j
          (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) q
            (coherentAdditiveEndomorphism X (unit X) q FrZ v) := by
  let φ := SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom
  exact cancel_square (coherentSmallResolutionEquiv X (unit X) q)
    (coherentSmallResolutionEquiv Y (unit Y) q)
    (coherentSmallResolutionEquiv Y (unit Y) q).injective
    (moduleCohomologyFMap j φ q)
    (coherentAdditiveEndomorphism X (unit X) q FrZ)
    (coherentAdditiveEndomorphism Y (unit Y) q FrZK)
    ((coherentExtPresentationFor X (unit X) q).smallMap FrZ)
    ((coherentExtPresentationFor Y (unit Y) q).smallMap FrZK)
    (extPullback j (unit X) (unit Y) φ q)
    (action_small X (unit X) q FrZ) (action_small Y (unit Y) q FrZK)
    (resolution_pullback j (unit X) (unit Y) φ q)
    (fun x ↦ (extPullback_naturality j (unit X) (unit Y) φ q FrZ FrZK
      (structural_power_square j p FrZ FrZK hFrZ hFrZK) x).symm) v

end AlgebraicGeometry.Scheme.Modules
