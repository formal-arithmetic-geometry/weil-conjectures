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
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison

/-! Frobenius naturality for the fixed coherent pullback. -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local irreducible] moduleCohomologyFMap moduleAbelianCohomologyLarge
  coherentExtUniverseEquiv coherentAdditiveEndomorphism Abelian.Ext
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local semireducible] moduleCohomologyExtResolutionEquiv

private lemma conjugate_square
    {A A' B B' : Type*}
    (e : A ≃ B) (e' : A' ≃ B') (a : A → A') (b : B → B')
    (f : B → B) (f' : B' → B')
    (ha : ∀ x, e' (a x) = b (e x)) (hf : ∀ y, f' (b y) = b (f y)) (x : A) :
    e'.symm (f' (e' (a x))) = a (e.symm (f (e x))) := by
  apply e'.injective
  rw [Equiv.apply_symm_apply, ha, ha, Equiv.apply_symm_apply]
  exact hf (e x)

-- Keep the coefficient modules abstract while transporting through the resolution API.
private lemma coherentAdditiveEndomorphism_naturality
    {X Y : Scheme.{u}} (j : Y ⟶ X) (N : X.Modules) (F : Y.Modules)
    (φ : N ⟶ (pushforward j).obj F) (q : ℕ)
    (a : (SheafOfModules.toSheaf X.ringCatSheaf).obj N ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj N)
    (b : (SheafOfModules.toSheaf Y.ringCatSheaf).obj F ⟶
      (SheafOfModules.toSheaf Y.ringCatSheaf).obj F)
    (hc : (invImage j).map a ≫ coeff j φ = coeff j φ ≫ b)
    (v : (RingedSpace.moduleCohomology X.toRingedSpace q).obj N) :
    coherentAdditiveEndomorphism Y F q b (moduleCohomologyFMap j φ q v) =
      moduleCohomologyFMap j φ q (coherentAdditiveEndomorphism X N q a v) := by
  let e := ExtEdgeResolution.moduleComparisonEquiv (moduleCohomologyExtResolutionNatIso X q) N
  let e' := ExtEdgeResolution.moduleComparisonEquiv (moduleCohomologyExtResolutionNatIso Y q) F
  have hf (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj N) :
      e' (moduleCohomologyFMap j φ q x) =
      Sheaf.H.map (coeff j φ) q
        (Sheaf.H.mapFunctor (invImage j) (constIso j).symm
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) q (e x)) := by
    exact moduleCohomology_transport_coefficient j N F φ q
      (fun M ↦ moduleCohomologyExtResolutionEquiv X M q)
      (moduleCohomologyExtResolutionEquiv Y F q)
      (moduleCohomologyExtResolutionEquiv_naturality X q N ((pushforward j).obj F) φ)
      (moduleCohomologyExtResolutionEquiv_edge j F q) x
  have h := conjugate_square e.toEquiv e'.toEquiv
    (fun x ↦ moduleCohomologyFMap j φ q x)
    (fun x ↦ Sheaf.H.map (coeff j φ) q
      (Sheaf.H.mapFunctor (invImage j) (constIso j).symm
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) q x))
    (fun x ↦ Sheaf.H.map a q x) (fun x ↦ Sheaf.H.map b q x) hf
    (fun x ↦ (sheafComparison_naturality (invImage j) (constIso j).symm
      (F := (SheafOfModules.toSheaf X.ringCatSheaf).obj N)
      (E := (SheafOfModules.toSheaf X.ringCatSheaf).obj N)
      (F' := (SheafOfModules.toSheaf Y.ringCatSheaf).obj F)
      (E' := (SheafOfModules.toSheaf Y.ringCatSheaf).obj F)
      (coeff j φ) (coeff j φ) a b hc q x).symm) v
  exact (coherentAdditiveEndomorphism_apply Y F q b _).trans
    (h.trans (congrArg (moduleCohomologyFMap j φ q)
      (coherentAdditiveEndomorphism_apply X N q a v).symm))

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
commutes with both powers. Evaluate the additive action by the forward and
inverse components of the same fixed resolution isomorphism. Conjugate the
square by E and E' and cancel E', which is injective. This proves
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
  let φ : unit X ⟶ (pushforward j).obj (unit Y) :=
    SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom
  let c := coeff j φ
  have hc : (invImage j).map FrZ ≫ c = c ≫ FrZK := by
    apply (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      j.base).homEquiv_naturality_right_square
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    change j.app U.unop (FrZ.hom.app U s) =
      FrZK.hom.app (op (j ⁻¹ᵁ U.unop)) (j.app U.unop s)
    have hs := map_pow (G := Γ(X, U.unop)) (H := Γ(Y, j ⁻¹ᵁ U.unop))
      (j.app U.unop).hom (show Γ(X, U.unop) from s) p
    exact (congrArg (j.app U.unop) (hFrZ U s)).trans
      (hs.trans (hFrZK (op (j ⁻¹ᵁ U.unop)) (j.app U.unop s)).symm)
  exact coherentAdditiveEndomorphism_naturality j (unit X) (unit Y) φ q
    FrZ FrZK hc v

end AlgebraicGeometry.Scheme.Modules
