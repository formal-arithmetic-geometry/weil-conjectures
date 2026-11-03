/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections

/-! # Global sections recover the underlying coefficient ring -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory MonObj Opposite Limits
namespace AlgebraicGeometry.ProEtale.IntegralCoefficientHom
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Constant coefficient functions on profinite test spaces.
Source: coefficient-presentation sub-step of cor-coef-integral-internal-hom.proof.md,
sentence 1 (blueprint: lem-coef-general-integral-global-sections). -/
def constSectionRingHom (S : Profinite.{u}ᵒᵖ) :
    R →+* (Profinite.continuousCoefficientRingPresheaf R).obj S where
  toFun r := ULift.up (ContinuousMap.const _ r)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The global constant section defined by a coefficient.
Source: coefficient-presentation sub-step of cor-coef-integral-internal-hom.proof.md,
sentence 1 (blueprint: lem-coef-general-integral-global-sections). -/
def constRingHom : R →+* Γ (Profinite.continuousCoefficientRingObj R) :=
  Sheaf.ringHomΓSheafCompose (coherentTopology Profinite.{u})
    (Profinite.continuousCoefficientRingSheaf R) (constSectionRingHom R) fun _ _ ↦ rfl

/-- Every global section is uniquely determined by its value at the point.
Source: the continuousMapConstRingHom_surjective proof, with universe-general coefficients;
cor-coef-integral-internal-hom.proof.md, sentence 1.
(blueprint: lem-coef-general-integral-global-sections). -/
theorem constRingHom_bijective : Function.Bijective (constRingHom R) := by
  constructor
  · intro r s h
    have h' := congrArg (fun z : Γ (Profinite.continuousCoefficientRingObj R) ↦
      Functor.LaxMonoidal.ε
          (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
        (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map z.hom) h
    dsimp only [constRingHom] at h'
    have hr := Sheaf.ε_comp_ringHomΓSheafCompose_hom
      (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf R)
      (constSectionRingHom R) (fun _ _ ↦ rfl) r
    have hs := Sheaf.ε_comp_ringHomΓSheafCompose_hom
      (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf R)
      (constSectionRingHom R) (fun _ _ ↦ rfl) s
    have h'' := hr.symm.trans (h'.trans hs)
    have hpoint := congrArg (fun z ↦
      z.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1)) h''
    dsimp [Functor.ringHomΓCompForget₂, Γ.hom, Γ.ofHom, Conv.toHom,
      constSectionRingHom, Profinite.continuousCoefficientRingSheaf,
      Profinite.continuousCoefficientRingPresheaf] at hpoint
    have hvalue := congrArg (fun z ↦ z.down PUnit.unit) hpoint
    dsimp [AddMonoidHom.mulRight, AddEquiv.ulift, Equiv.ulift,
      AddMonoidHom.instFunLike, DFunLike.coe] at hvalue
    simpa using hvalue
  · intro x
    let adj := sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}
    let x' := adj.homEquiv _ _
      (inv (Functor.LaxMonoidal.ε
        (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) ≫ x.hom)
    let b := x'.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1)
    refine ⟨b.down PUnit.unit, ?_⟩
    have hx : x' = (Functor.ringHomΓCompForget₂
        (Profinite.continuousCoefficientRingSheaf R).obj
        (constSectionRingHom R) (fun _ _ ↦ rfl) (b.down PUnit.unit)).hom := by
      ext S n
      obtain ⟨m⟩ := n
      have key : x'.app S (ULift.up 1) =
          (Profinite.continuousCoefficientRingObj R).obj.map
            (Profinite.isTerminalPUnit.from S.unop).op b :=
        NatTrans.naturality_apply x'
          (Profinite.isTerminalPUnit.from S.unop).op (ULift.up 1)
      have hm : (ULift.up m : ULift.{u + 1} ℤ) = m • ULift.up 1 := by
        ext
        simp
      refine (congrArg (x'.app S) hm).trans ?_
      rw [map_zsmul, key]
      exact (zsmul_eq_mul
        (α := (Profinite.continuousCoefficientRingPresheaf R).obj S) _ m).trans rfl
    ext1
    rw [constRingHom, Sheaf.ringHomΓSheafCompose, RingHom.comp_apply,
      RingHom.comp_apply, Γ.map_hom, Γ.mapFunctor_hom, ← hx, Category.assoc,
      Sheaf.sheafifyRingPresheafIso, asIso_hom, ← Adjunction.homEquiv_counit,
      Equiv.symm_apply_apply, IsIso.hom_inv_id_assoc]

/-- A condensed coefficient isomorphism induces an isomorphism of global-section rings.
Source: coefficient transport in cor-coef-integral-internal-hom.proof.md, sentence 1.
(blueprint: lem-coef-general-integral-global-sections). -/
def globalSectionsRingEquiv
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] (e : Mon.mk Λ ≅ Mon.mk Λ') : Γ Λ ≃+* Γ Λ' :=
  { Γ.map e.hom.hom with
    invFun := Γ.map e.inv.hom
    left_inv := fun x ↦ by
      apply Γ.ext
      change (x.hom ≫ e.hom.hom) ≫ e.inv.hom = x.hom
      rw [Category.assoc]
      have h := congrArg Mon.Hom.hom e.hom_inv_id
      simp only [Mon.comp_hom', Mon.id_hom'] at h
      rw [h, Category.comp_id]
    right_inv := fun x ↦ by
      apply Γ.ext
      change (x.hom ≫ e.inv.hom) ≫ e.hom.hom = x.hom
      rw [Category.assoc]
      have h := congrArg Mon.Hom.hom e.inv_hom_id
      simp only [Mon.comp_hom', Mon.id_hom'] at h
      rw [h, Category.comp_id] }

/-- The underlying abstract coefficient rings are recovered from a condensed isomorphism.
Source: coefficient transport in cor-coef-integral-internal-hom.proof.md, sentence 1.
(blueprint: lem-coef-general-integral-global-sections). -/
def coefficientRingEquiv
    {S : Type u} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (e : Mon.mk (Profinite.continuousCoefficientRingObj R) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj S)) : R ≃+* S :=
  (RingEquiv.ofBijective (constRingHom R) (constRingHom_bijective R)).trans
    ((globalSectionsRingEquiv e).trans
      (RingEquiv.ofBijective (constRingHom S) (constRingHom_bijective S)).symm)

/-- The recovered ring equivalence preserves uniformizers algebraically.
Source: coefficient transport in cor-coef-integral-internal-hom.proof.md, sentence 1.
(blueprint: lem-coef-general-integral-global-sections). -/
theorem coefficientRingEquiv_irreducible_iff
    {S : Type u} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (e : Mon.mk (Profinite.continuousCoefficientRingObj R) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj S)) (π : R) :
    Irreducible (coefficientRingEquiv R e π) ↔ Irreducible π :=
  MulEquiv.irreducible_iff (f := (coefficientRingEquiv R e).toMulEquiv)

/-- Transport of every power ideal along the recovered coefficient equivalence.
Source: coefficient transport in cor-coef-integral-internal-hom.proof.md, sentence 1.
(blueprint: lem-coef-general-integral-global-sections). -/
theorem coefficientRingEquiv_map_powerIdeal
    {S : Type u} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (e : Mon.mk (Profinite.continuousCoefficientRingObj R) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj S)) (π : R) (n : ℕ) :
    Ideal.map (coefficientRingEquiv R e).toRingHom (Ideal.span ({π ^ n} : Set R)) =
      Ideal.span ({(coefficientRingEquiv R e π) ^ n} : Set S) := by
  simp only [Ideal.map_span, Set.image_singleton, map_pow,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]

/-- The small-coefficient presentation has the same bijective constant-section map.
Source: continuousMapConstRingHom_surjective and the point evaluation calculation above;
cor-coef-integral-internal-hom.proof.md, sentence 1.
(blueprint: lem-coef-general-integral-global-sections). -/
theorem smallConstRingHom_bijective (T : Type) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] : Function.Bijective (Profinite.continuousMapConstRingHom.{u} T) := by
  refine ⟨?_, Profinite.continuousMapConstRingHom_surjective T⟩
  intro r s h
  have h' := congrArg (fun z : Γ (Profinite.continuousMapRingObj.{u} T) ↦
    Functor.LaxMonoidal.ε
        (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
      (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map z.hom) h
  dsimp only [Profinite.continuousMapConstRingHom] at h'
  have hr := Sheaf.ε_comp_ringHomΓSheafCompose_hom
    (coherentTopology Profinite.{u}) (Profinite.continuousMapRingSheaf T)
    (Profinite.continuousMapConstSectionRingHom T) (fun _ _ ↦ rfl) r
  have hs := Sheaf.ε_comp_ringHomΓSheafCompose_hom
    (coherentTopology Profinite.{u}) (Profinite.continuousMapRingSheaf T)
    (Profinite.continuousMapConstSectionRingHom T) (fun _ _ ↦ rfl) s
  have h'' := hr.symm.trans (h'.trans hs)
  have hpoint := congrArg (fun z ↦
    z.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1)) h''
  dsimp [Functor.ringHomΓCompForget₂, Γ.hom, Γ.ofHom, Conv.toHom,
    Profinite.continuousMapConstSectionRingHom, Profinite.continuousMapRingSheaf,
    Profinite.continuousMapRingPresheaf] at hpoint
  have hvalue := congrArg (fun z ↦ z.down PUnit.unit) hpoint
  dsimp [AddMonoidHom.mulRight, AddEquiv.ulift, Equiv.ulift,
    AddMonoidHom.instFunLike, DFunLike.coe] at hvalue
  simpa using hvalue

/-- Recover the coefficient-ring equivalence for the precise small admissible presentation.
Source: cor-coef-integral-internal-hom.proof.md, coefficient transport in sentence 1.
(blueprint: lem-coef-general-integral-global-sections). -/
def smallCoefficientRingEquiv (T : Type) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T]
    (e : Mon.mk (Profinite.continuousCoefficientRingObj R) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} T)) : R ≃+* T :=
  (RingEquiv.ofBijective (constRingHom R) (constRingHom_bijective R)).trans
    ((globalSectionsRingEquiv e).trans
      (RingEquiv.ofBijective (Profinite.continuousMapConstRingHom.{u} T)
        (smallConstRingHom_bijective T)).symm)

end AlgebraicGeometry.ProEtale.IntegralCoefficientHom
