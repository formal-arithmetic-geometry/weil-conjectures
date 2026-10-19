/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.PurityAffineLineOrientation
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Sheaf.Paper.PurityAffineLineSupportRestrictionZeroGerm
import WeilConjectures.SixFunctors.ProEtale.Comparison.Linear
import WeilConjectures.CategoryTheory.Sites.Point.Linear

/-! # Stalk factorization of the normalized supported pullback

Source: blueprint main-20261015, prop-pur-affine-line-orientation-uniqueness,
proof Steps 2–3; Milne, Theorem 9.4 and Example 9.5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

local instance (P : PurityFiniteSetting.{u}) :
    PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} P.Coefficient)) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _

private theorem supportTransport_terminalMap_eq (P : PurityFiniteSetting.{u})
    {T Y : Scheme.{u}} (f : T ⟶ Y)
    (p q : proEtaleSupportHomTransport P (zeroSection Y) (zeroSection T)
      (AffineSpace.map (ULift.{u} (Fin 1)) f)) : p.terminalMap = q.terminalMap := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (pullback.snd (𝟙 (Line Y))
    (AffineSpace.map (ULift.{u} (Fin 1)) f))).1
  exact (CategoryTheory.Over.w ((MorphismProperty.Over.forget _ _ _).map p.terminalMap)).trans
    (CategoryTheory.Over.w ((MorphismProperty.Over.forget _ _ _).map q.terminalMap)).symm

private theorem supportTransport_supportUnit_eq (P : PurityFiniteSetting.{u})
    {T Y : Scheme.{u}} (f : T ⟶ Y)
    (p q : proEtaleSupportHomTransport P (zeroSection Y) (zeroSection T)
      (AffineSpace.map (ULift.{u} (Fin 1)) f)) : p.supportUnit = q.supportUnit := by
  apply NatTrans.ext
  funext F
  apply (cancel_mono (kernel.ι _)).1
  rw [p.supportUnit_spec, q.supportUnit_spec, supportTransport_terminalMap_eq P f p q]

private theorem orientationSupportRestriction_transport_independent
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    {T Y : Scheme.{u}} (f : T ⟶ Y)
    (p q : proEtaleSupportHomTransport P (zeroSection Y) (zeroSection T)
      (AffineSpace.map (ULift.{u} (Fin 1)) f)) :
    P.orientationSupportRestriction h f p = P.orientationSupportRestriction h f q := by
  have hpq := supportTransport_supportUnit_eq P f p q
  unfold orientationSupportRestriction SupportHomPair.Transport.derivedMap
  rw [hpq]

set_option backward.isDefEq.respectTransparency false in
private theorem gysin_stalk_rank_one (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (H : ProEtale.RetractedSupport.EtSheaves P Y)
    (e : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj H ≅
      (DerivedCategory.homologyFunctor
        (ProEtale.RetractedSupport.ProSheaves P Y) 0).obj (P.gysinValue h Y))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y) :
    Nonempty ((Scheme.pointSmallEtale y).sheafFiber.obj H ≅
      ModuleCat.of P.Coefficient P.Coefficient) := by
  obtain ⟨_, _, ⟨H₀, ⟨e₀⟩, V, hv⟩, _⟩ := P.gysin_structure h Y a
  let ν : ProEtale.RetractedSupport.EtSheaves P Y ⥤
      ProEtale.RetractedSupport.ProSheaves P Y :=
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let t : H ≅ H₀ := ν.preimageIso (e ≪≫ e₀.symm)
  obtain ⟨i, v, hv'⟩ := V.exists_eq (y.base (IsLocalRing.closedPoint Ω))
  have : Etale (V.f i) := V.map_prop i
  obtain ⟨ei⟩ := hv i
  obtain ⟨s⟩ := Etale.nonempty_sheafFiber_iso_of_iso H₀ (V.f i) ei y ⟨v, hv'⟩
  exact ⟨(Scheme.pointSmallEtale y).sheafFiber.mapIso t ≪≫ s⟩

private theorem eval_add (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    {F : ProEtale.RetractedSupport.ProSheaves P Y} (f g : P.constant Y ⟶ F) :
    P.gysinEvaluate Y (f + g) = P.gysinEvaluate Y f + P.gysinEvaluate Y g := by
  dsimp only [gysinEvaluate]
  simp only [Adjunction.homEquiv_unit]
  simp
private theorem eval_smul (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    {F : ProEtale.RetractedSupport.ProSheaves P Y} (a : P.Coefficient)
    (f : P.constant Y ⟶ F) :
    P.gysinEvaluate Y (a • f) = a • P.gysinEvaluate Y f := by
  dsimp only [gysinEvaluate]
  simp only [Adjunction.homEquiv_unit]
  have hs {M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)}
      (q : M ⟶ N) : (a • q).hom = a • q.hom := rfl
  simp [Functor.map_smul, hs, NatTrans.app_smul]
private theorem finite_line_factor {A : Type*} [CommRing A] [Finite A]
    {X M N : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (eM : M ≃ₗ[A] A) (eN : N ≃ₗ[A] A) (ev : X →ₗ[A] M) (r : X →ₗ[A] N)
    (hzero : ∀ x, ev x = 0 → r x = 0) (x₀ : X) (hx₀ : eN (r x₀) = 1) :
    ∃ α : M →ₗ[A] N, ∀ x, α (ev x) = r x := by
  let t := LinearMap.toSpanSingleton A M (ev x₀)
  have ht : Function.Injective t := by
    apply (injective_iff_map_eq_zero t).2
    intro a ha
    have h := hzero (a • x₀) (by simpa [t] using ha)
    have hh := congrArg eN h
    simpa [hx₀] using hh
  have hf : Function.Bijective (eM ∘ t) :=
    (Finite.injective_iff_bijective).1 (eM.injective.comp ht)
  have hbij : Function.Bijective t := ⟨ht, fun m ↦ by
    obtain ⟨a, ha⟩ := hf.2 (eM m)
    exact ⟨a, eM.injective ha⟩⟩
  let E := LinearEquiv.ofBijective t hbij
  refine ⟨eN.symm.toLinearMap.comp E.symm.toLinearMap, ?_⟩
  intro x
  let a := E.symm (ev x)
  have h := hzero (x - a • x₀) (by
    rw [map_sub, map_smul]
    change ev x - E (E.symm (ev x)) = 0
    simp)
  have hh := congrArg eN h
  have hx : eN (r x) = a := by simpa [hx₀, sub_eq_zero] using hh
  change eN.symm (E.symm (ev x)) = r x
  apply eN.injective
  simpa [a] using hx.symm

set_option backward.isDefEq.respectTransparency false in
/-- Supported restriction factors through the geometric stalk of the degree-zero
Gysin sheaf. The factorization uses local zero-germ vanishing, finite coefficients,
and the normalized orientation, without assuming exceptional base change invertible.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1,
prop-pur-affine-line-orientation-uniqueness.proof.md, Steps 2–3; Milne, Lectures on
Etale Cohomology, Theorems 9.4 and 9.7 and Example 9.5
(blueprint: lem-pur-affine-line-support-stalk-map).

Proof:
1. The etale Gysin model and a trivializing cover identify H_y with the coefficient
ring A. The orientation theorem gives a residue coordinate on the fibre support.
Use the k-algebra structure induced by y followed by a for its normalization.
2. Define linear maps ev(b)=b_y(1) and r(b)=the specified supported restriction.
Unfolding the two adjunction Hom equivalences proves linearity of gysinEvaluate.
Local zero-germ vanishing gives ker(ev) contained in ker(r).
3. The Hom-to-sections bijection and full comparison lift the normalized orientation
class to b0 with rho(r(b0))=1. Normalized transports induce the same restriction:
their terminal arrows are unique, so supportUnit_spec and the monic kernel inclusion
identify their support units; deriving preserves that equality.
4. The map t:A -> H_y given by c |-> c*ev(b0) is injective. Indeed t(c)=0 implies
r(c*b0)=0 by step 2, and applying rho gives c=0. In line coordinates this is an
injective self-map of the finite ring A, hence bijective. Thus t is a linear
isomorphism. Define alpha=rho inverse after t inverse. Apply ker(ev) contained
in ker(r) to b-t_inverse(ev(b))*b0 and apply rho. The resulting equality is exactly
alpha(ev(b))=r(b). This finite-line argument includes the zero coefficient ring. -/
theorem affineLine_support_stalk_map (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (D : OrientationSupportData P h Y)
    (H : ProEtale.RetractedSupport.EtSheaves P Y)
    (e : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj H ≅
      (DerivedCategory.homologyFunctor
        (ProEtale.RetractedSupport.ProSheaves P Y) 0).obj (P.gysinValue h Y))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (p : proEtaleSupportHomTransport P (zeroSection Y)
      (zeroSection (Spec (CommRingCat.of Ω))) (AffineSpace.map (ULift.{u} (Fin 1)) y)) :
    ∃ α : (Scheme.pointSmallEtale y).sheafFiber.obj H ⟶
        P.gysinSupport h (Spec (CommRingCat.of Ω)),
      ∀ b : P.constantEtale Y ⟶ H,
        α (((Scheme.pointSmallEtale y).sheafFiber.map b)
          (((Scheme.pointSmallEtale y).sheafFiberConstantSheafIso
            (ModuleCat.of P.Coefficient P.Coefficient)).inv 1)) =
          P.orientationSupportRestriction h y p
            (D.support.hom (P.gysinEvaluate Y
              ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).map b ≫
                e.hom))) := by
  classical
  let : Algebra P.field.k Ω := (Spec.preimage (y ≫ a)).hom.toAlgebra
  have hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω)) := by
    exact (Spec.map_preimage (y ≫ a)).symm
  obtain ⟨_, _, _, _, D₀, m₀, _, hfib⟩ := P.affineLine_orientation h Y a
  obtain ⟨_, p₀, ρ, _, hnorm⟩ := hfib Ω y hy
  obtain ⟨eM⟩ := gysin_stalk_rank_one P h Y a H e Ω y
  let Φ := Scheme.pointSmallEtale y
  have : (Φ.sheafFiber (A := ModuleCat.{u + 1} P.Coefficient)).Additive :=
    Φ.sheafFiber_additive
  let ν : ProEtale.RetractedSupport.EtSheaves P Y ⥤
      ProEtale.RetractedSupport.ProSheaves P Y :=
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let ev : (P.constantEtale Y ⟶ H) →ₗ[P.Coefficient]
      (Φ.sheafFiber (A := ModuleCat.{u + 1} P.Coefficient)).obj H := {
    toFun := fun b ↦ (Φ.sheafFiber.map b)
      ((Φ.sheafFiberConstantSheafIso (ModuleCat.of P.Coefficient P.Coefficient)).inv 1)
    map_add' := by intro b c; simp
    map_smul' := by intro r b; simp [Φ.sheafFiber_map_smul] }
  let r : (P.constantEtale Y ⟶ H) →ₗ[P.Coefficient]
      P.gysinSupport h (Spec (CommRingCat.of Ω)) := {
    toFun := fun b ↦ P.orientationSupportRestriction h y p
      (D.support.hom (P.gysinEvaluate Y (ν.map b ≫ e.hom)))
    map_add' := by
      intro b c
      simp only [ν.map_add, Preadditive.add_comp, eval_add]
      simp
    map_smul' := by
      intro r b
      simp only [ν.map_smul, Linear.smul_comp, eval_smul]
      simp }
  have hzero (b : P.constantEtale Y ⟶ H) (hb : ev b = 0) : r b = 0 :=
    P.affineLine_support_restriction_zero_germ h Y a D H e Ω y p b hb
  obtain ⟨_, _, _, hbij, _⟩ := P.gysin_structure h Y a
  obtain ⟨m, hm⟩ := hbij.2
    (D.support.inv (D₀.support.hom (P.gysinHomToSections h Y m₀)))
  let v : P.constant Y ⟶
      (DerivedCategory.homologyFunctor
        (ProEtale.RetractedSupport.ProSheaves P Y) 0).obj (P.gysinValue h Y) :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ProEtale.RetractedSupport.ProSheaves P Y) 0).inv.app (P.constant Y) ≫
      (DerivedCategory.homologyFunctor
        (ProEtale.RetractedSupport.ProSheaves P Y) 0).map m
  obtain ⟨b₀, hb₀⟩ := ν.map_surjective (v ≫ e.inv)
  have hb₀' : ν.map b₀ ≫ e.hom = v := by rw [hb₀]; simp
  have hv : D.support.hom (P.gysinEvaluate Y (ν.map b₀ ≫ e.hom)) =
      D₀.support.hom (P.gysinHomToSections h Y m₀) := by
    rw [hb₀']
    change D.support.hom (P.gysinHomToSections h Y m) = _
    rw [hm, Iso.inv_hom_id_apply]
  have hx : ρ.hom (r b₀) = 1 := by
    dsimp only [r, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hv, orientationSupportRestriction_transport_independent P h y p p₀]
    exact hnorm
  obtain ⟨α, hα⟩ := finite_line_factor eM.toLinearEquiv ρ.toLinearEquiv ev r hzero b₀ hx
  exact ⟨ModuleCat.ofHom α, hα⟩

end WeilConjectures.PurityFiniteSetting
