/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Conj
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.PeriodicQuotientTor
import all WeilConjectures.AlgebraicGeometry.Adic.AdicReductionTriangle
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralLocalReductionLowerBound
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.SuccessiveQuotientFlatTensorSequence
/-! # Nonvanishing Tor between adjacent principal quotients -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

private theorem power_comp
    {C : Type*} [Category* C] [Abelian C] {M N : C}
    (f : End M) (t : End N) (p : M ⟶ N) (h : f ≫ p = p ≫ t) (n : ℕ) :
    (f ^ n) ≫ p = p ≫ (t ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, End.mul_def, Category.assoc]
    rw [ih, ← Category.assoc, h, Category.assoc]

private theorem exact_powers_on_monic_quotient
    {C : Type*} [Category* C] [Abelian C] {M N : C}
    (f : End M) [Mono f] (t : End N) (p : M ⟶ N) [Epi p]
    (a b : ℕ) (hp : (f ^ (a + b)) ≫ p = 0)
    (hep : (ShortComplex.mk (f ^ (a + b)) p hp).Exact)
    (hpt : f ≫ p = p ≫ t) :
    ∃ h : (t ^ a) ≫ (t ^ b) = 0, (ShortComplex.mk (t ^ a) (t ^ b) h).Exact := by
  have hzero : (t ^ a) ≫ (t ^ b) = 0 := by
    apply (cancel_epi p).1
    rw [comp_zero, ← Category.assoc, ← power_comp f t p hpt a,
      Category.assoc, ← power_comp f t p hpt b, ← Category.assoc]
    simpa only [← End.mul_def, ← pow_add, Nat.add_comm b a] using hp
  refine ⟨hzero, (ShortComplex.exact_iff_exact_up_to_refinements _).2 ?_⟩
  intro Q x hx
  obtain ⟨Q', e, he, y, hy⟩ := surjective_up_to_refinements_of_epi p x
  have : Epi e := he
  have hyt : (y ≫ (f ^ b)) ≫ p = 0 := by
    rw [Category.assoc, power_comp f t p hpt b, ← Category.assoc, ← hy,
      Category.assoc, hx, comp_zero]
  obtain ⟨Q'', e', he', z, hz⟩ := hep.exact_up_to_refinements (y ≫ (f ^ b)) hyt
  have : Epi e' := he'
  have hmono (n : ℕ) : Mono (f ^ n) := by
    induction n with
    | zero => change Mono (𝟙 M); infer_instance
    | succ n ih =>
      rw [pow_succ]
      change Mono (f ≫ (f ^ n))
      infer_instance
  have : Mono (f ^ b) := hmono b
  have hcancel : e' ≫ y = z ≫ (f ^ a) := by
    apply (cancel_mono (f ^ b)).1
    have hpow : f ^ (a + b) = (f ^ a) ≫ (f ^ b) := by
      rw [Nat.add_comm a b, pow_add, End.mul_def]
    simpa only [hpow, Category.assoc] using hz
  refine ⟨Q'', e' ≫ e, inferInstance, z ≫ p, ?_⟩
  rw [Category.assoc, hy, ← Category.assoc, hcancel]
  rw [Category.assoc, Category.assoc, power_comp f t p hpt a]

private theorem exact_quotient_descend
    {C : Type*} [Category* C] [Abelian C] {M N P : C}
    (f : End M) (t : End N) (p : M ⟶ N) [Epi p]
    (r : M ⟶ P) (s : N ⟶ P) (hps : p ≫ s = r)
    (hp : f ≫ r = 0) (hex : (ShortComplex.mk f r hp).Exact)
    (hpt : f ≫ p = p ≫ t) :
    ∃ h : t ≫ s = 0, (ShortComplex.mk t s h).Exact := by
  have hz : t ≫ s = 0 := by
    apply (cancel_epi p).1
    rw [← Category.assoc, ← hpt, Category.assoc, hps, hp, comp_zero]
  refine ⟨hz, (ShortComplex.exact_iff_exact_up_to_refinements _).2 ?_⟩
  intro Q x hx
  obtain ⟨Q',e,he,y,hy⟩ := surjective_up_to_refinements_of_epi p x
  have : Epi e := he
  have hyr : y ≫ r = 0 := by
    rw [← hps, ← Category.assoc, ← hy, Category.assoc, hx, comp_zero]
  obtain ⟨Q'',e',he',z,hz'⟩ := hex.exact_up_to_refinements y hyr
  have : Epi e' := he'
  refine ⟨Q'',e' ≫ e,inferInstance,z ≫ p,?_⟩
  rw [Category.assoc, hy, ← Category.assoc, hz', Category.assoc, hpt]
  exact (Category.assoc z p t).symm

universe u
open Opposite
namespace AlgebraicGeometry.Scheme
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private local instance restriction_faithful
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) : (pbcRestrict φ).Faithful where
  map_injective := by
    intro M N f g h
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h

private theorem full_restriction_of_unit_epi
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (p : SheafOfModules.unit ((adicLisseForget T).obj R) ⟶
      (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget T).obj S))) [Epi p]
    (hp : ∀ U : T.ProEtᵒᵖ, p.val.app U (1 : R.obj.obj U) = (1 : S.obj.obj U)) :
    (pbcRestrict φ).Full := by
  let F := SheafOfModules.toSheaf ((adicLisseForget T).obj R)
  have : Epi (F.map p) := inferInstance
  have hsurj : Presheaf.IsLocallySurjective (ProEt.topology T) (F.map p).hom :=
    (Sheaf.isLocallySurjective_iff_epi' _ (F.map p)).2 inferInstance
  have hform (U : T.ProEtᵒᵖ) (x : R.obj.obj U) :
      p.val.app U x = φ.hom.app U x := by
    have h := (p.val.app U).hom.map_smul x (1 : R.obj.obj U)
    change (p.val.app U (x * (1 : R.obj.obj U)) : S.obj.obj U) =
      φ.hom.app U x * (@id (S.obj.obj U) (p.val.app U (1 : R.obj.obj U))) at h
    simpa only [mul_one, hp U, id_eq] using h
  have : Presheaf.IsLocallySurjective (ProEt.topology T)
      ((adicLisseForget T).map φ).hom := by
    constructor
    intro U s
    apply (ProEt.topology T).superset_covering _ (Presheaf.imageSieve_mem _ (F.map p).hom s)
    intro V f hf
    obtain ⟨x, hx⟩ := hf
    exact ⟨x, (hform (op V) x).symm.trans hx⟩
  exact SheafOfModules.restriction_full ((adicLisseForget T).map φ)




private theorem scalar_unit_action
    (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (f : End (SheafOfModules.unit ((adicLisseForget T).obj R))) :
    (ReductionTensor.multiplicationNatural T R f).app
      (SheafOfModules.unit ((adicLisseForget T).obj R)) = f := by
  ext U
  change (ReductionTensor.tensorMultiplication T R f
    (SheafOfModules.unit ((adicLisseForget T).obj R))).val.app U
      (1 : R.obj.obj U) = f.val.app U (1 : R.obj.obj U)
  rw [ReductionTensor.tensorMultiplication_apply]
  change (@id (R.obj.obj U) (f.val.app U (1 : R.obj.obj U))) * (1 : R.obj.obj U) = _
  exact mul_one _


private theorem quotient_periodic_data
    (T : Scheme.{u}) {B R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : B ⟶ R) (ψ : R ⟶ S) (χ : B ⟶ S) (hcomp : φ ≫ ψ = χ)
    (f : End (SheafOfModules.unit ((adicLisseForget T).obj B))) [Mono f]
    (a b : ℕ)
    (p : SheafOfModules.unit ((adicLisseForget T).obj B) ⟶
      (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget T).obj R)))
    (r : SheafOfModules.unit ((adicLisseForget T).obj B) ⟶
      (pbcRestrict χ).obj (SheafOfModules.unit ((adicLisseForget T).obj S)))
    (hp : ∀ U : T.ProEtᵒᵖ, p.val.app U (1 : B.obj.obj U) = (1 : R.obj.obj U))
    (hr : ∀ U : T.ProEtᵒᵖ, r.val.app U (1 : B.obj.obj U) = (1 : S.obj.obj U))
    (hzp : (f ^ (a + b)) ≫ p = 0)
    (hsp : (ShortComplex.mk (f ^ (a + b)) p hzp).ShortExact)
    (hzr : (f ^ a) ≫ r = 0)
    (hsr : (ShortComplex.mk (f ^ a) r hzr).ShortExact) :
    ∃ t : End (SheafOfModules.unit ((adicLisseForget T).obj R)),
      (∀ U : T.ProEtᵒᵖ, t.val.app U (1 : R.obj.obj U) =
        φ.hom.app U (f.val.app U (1 : B.obj.obj U))) ∧
      ∃ (hz₁ : (t ^ b) ≫ (t ^ a) = 0) (hz₂ : (t ^ a) ≫ (t ^ b) = 0),
        (ShortComplex.mk (t ^ b) (t ^ a) hz₁).Exact ∧
        (ShortComplex.mk (t ^ a) (t ^ b) hz₂).Exact ∧
        ∃ hz : (t ^ a) ≫ coefficientUnitMap T ψ = 0,
          (ShortComplex.mk (t ^ a) (coefficientUnitMap T ψ) hz).Exact ∧
          Epi (coefficientUnitMap T ψ) := by
  let F := pbcRestrict φ
  have : Epi p := hsp.epi_g
  have : Epi r := hsr.epi_g
  let := full_restriction_of_unit_epi T φ p hp
  let α := ReductionTensor.multiplicationNatural T B f
  let t : End (SheafOfModules.unit ((adicLisseForget T).obj R)) :=
    F.preimage (α.app (F.obj (SheafOfModules.unit ((adicLisseForget T).obj R))))
  have ht : F.map t = α.app (F.obj (SheafOfModules.unit ((adicLisseForget T).obj R))) :=
    F.map_preimage _
  have hpt : f ≫ p = p ≫ F.map t := by
    have hu : α.app (SheafOfModules.unit ((adicLisseForget T).obj B)) = f :=
      scalar_unit_action T B f
    have hn : p ≫ α.app (F.obj (SheafOfModules.unit ((adicLisseForget T).obj R))) =
        α.app (SheafOfModules.unit ((adicLisseForget T).obj B)) ≫ p := α.naturality p
    exact (congrArg (fun k ↦ k ≫ p) hu).symm.trans
      (hn.symm.trans (congrArg (fun k ↦ p ≫ k) ht.symm))
  let tB : End (F.obj (SheafOfModules.unit ((adicLisseForget T).obj R))) := F.map t
  have hmap (k : ℕ) : F.map (t ^ k) = tB ^ k :=
    map_pow (F.mapEnd (SheafOfModules.unit ((adicLisseForget T).obj R))) t k
  obtain ⟨h₁,he₁⟩ := exact_powers_on_monic_quotient f tB p b a
    (by simpa only [Nat.add_comm b a] using hzp)
    (by simpa only [Nat.add_comm b a] using hsp.exact) hpt
  obtain ⟨h₂,he₂⟩ := exact_powers_on_monic_quotient f tB p a b hzp hsp.exact hpt
  have hz₁ : (t ^ b) ≫ (t ^ a) = 0 := F.map_injective (by
    simpa only [Functor.map_comp, hmap, Functor.map_zero] using h₁)
  have hz₂ : (t ^ a) ≫ (t ^ b) = 0 := F.map_injective (by
    simpa only [Functor.map_comp, hmap, Functor.map_zero] using h₂)
  have he₁' : (ShortComplex.mk (t ^ b) (t ^ a) hz₁).Exact :=
    ((ShortComplex.mk (t ^ b) (t ^ a) hz₁).exact_map_iff_of_faithful F).1 (by
      simpa only [ShortComplex.map, hmap] using he₁)
  have he₂' : (ShortComplex.mk (t ^ a) (t ^ b) hz₂).Exact :=
    ((ShortComplex.mk (t ^ a) (t ^ b) hz₂).exact_map_iff_of_faithful F).1 (by
      simpa only [ShortComplex.map, hmap] using he₂)
  refine ⟨t, ?_, hz₁, hz₂, he₁', he₂', ?_⟩
  · intro U
    have hh := congrArg (fun k ↦ k.val.app U (1 : R.obj.obj U)) ht
    change t.val.app U (1 : R.obj.obj U) =
      (ReductionTensor.tensorMultiplication T B f
        (F.obj (SheafOfModules.unit ((adicLisseForget T).obj R)))).val.app U
          (1 : R.obj.obj U) at hh
    rw [ReductionTensor.tensorMultiplication_apply] at hh
    change t.val.app U (1 : R.obj.obj U) =
      φ.hom.app U (f.val.app U (1 : B.obj.obj U)) * (1 : R.obj.obj U) at hh
    simpa only [mul_one] using hh
  · let s := coefficientUnitMap T ψ
    let e := (pbcRestrictComp φ ψ χ hcomp).app
      (SheafOfModules.unit ((adicLisseForget T).obj S))
    have hps : p ≫ F.map s = r ≫ e.inv := by
      apply (cancel_mono e.hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      ext U
      change e.hom.val.app U (ψ.hom.app U (p.val.app U (1 : B.obj.obj U))) =
        r.val.app U (1 : B.obj.obj U)
      erw [(pbcRestrictComp_exists φ ψ χ hcomp).exists.choose_spec]
      rw [hp, hr, map_one]
    have hzr' : (f ^ a) ≫ (r ≫ e.inv) = 0 := by rw [← Category.assoc,hzr,zero_comp]
    have her' : (ShortComplex.mk (f ^ a) (r ≫ e.inv) hzr').Exact :=
      by
        let s₁ := ShortComplex.mk (f ^ a) r hzr
        let s₂ := ShortComplex.mk (f ^ a) (r ≫ e.inv) hzr'
        let ei : s₁ ≅ s₂ := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e.symm
          (by simp only [s₁,s₂,Iso.refl_hom,Category.comp_id,Category.id_comp])
          (by simp only [s₁,s₂,Iso.refl_hom,Category.id_comp,Iso.symm_hom])
        exact (ShortComplex.exact_iff_of_iso ei).mp hsr.exact
    obtain ⟨hz,hex⟩ := exact_quotient_descend (f ^ a) (tB ^ a) p
      (r ≫ e.inv) (F.map s) hps hzr' her' (power_comp f tB p hpt a)
    have hzs : (t ^ a) ≫ s = 0 := F.map_injective (by
      simpa only [Functor.map_comp,hmap,Functor.map_zero] using hz)
    have hes : (ShortComplex.mk (t ^ a) s hzs).Exact :=
      ((ShortComplex.mk (t ^ a) s hzs).exact_map_iff_of_faithful F).1 (by
        simpa only [ShortComplex.map,hmap] using hex)
    have : Epi (r ≫ e.inv) := inferInstance
    have : Epi (p ≫ F.map s) := by rw [hps]; infer_instance
    have : Epi (F.map s) := epi_of_epi p (F.map s)
    have : Epi s := F.epi_of_epi_map inferInstance
    exact ⟨hzs,hes,inferInstance⟩



private theorem normalized_unit_apply
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S)
    (p : SheafOfModules.unit ((adicLisseForget T).obj R) ⟶
      (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget T).obj S)))
    (hp : ∀ U : T.ProEtᵒᵖ, p.val.app U (1 : R.obj.obj U) = (1 : S.obj.obj U))
    (U : T.ProEtᵒᵖ) (x : R.obj.obj U) : p.val.app U x = φ.hom.app U x := by
  have h := (p.val.app U).hom.map_smul x (1 : R.obj.obj U)
  change (p.val.app U (x * (1 : R.obj.obj U)) : S.obj.obj U) =
    φ.hom.app U x * (@id (S.obj.obj U) (p.val.app U (1 : R.obj.obj U))) at h
  simpa only [mul_one,hp U,id_eq] using h

private theorem unit_end_pow_one
    (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (t : End (SheafOfModules.unit ((adicLisseForget T).obj R)))
    (U : T.ProEtᵒᵖ) (k : ℕ) :
    (t ^ k).val.app U (1 : R.obj.obj U) =
      (@id (R.obj.obj U) (t.val.app U (1 : R.obj.obj U))) ^ k := by
  induction k with
  | zero => simp only [pow_zero,End.one_def]; rfl
  | succ k ih =>
    rw [pow_succ,End.mul_def]
    change (t ^ k).val.app U (t.val.app U (1 : R.obj.obj U)) = _
    have h := ((t ^ k).val.app U).hom.map_smul
      (@id (R.obj.obj U) (t.val.app U (1 : R.obj.obj U))) (1 : R.obj.obj U)
    change (@id (R.obj.obj U) ((t ^ k).val.app U
      ((@id (R.obj.obj U) (t.val.app U (1 : R.obj.obj U))) * (1 : R.obj.obj U)))) =
      (@id (R.obj.obj U) (t.val.app U (1 : R.obj.obj U))) *
        (@id (R.obj.obj U) ((t ^ k).val.app U (1 : R.obj.obj U))) at h
    simpa only [mul_one,one_mul,ih,pow_succ,mul_comm,id_eq] using h


/-- Every nonpositive cohomology of adjacent principal-quotient reduction of the
residue single module is the residue module at the lower level.

Source: blueprint order 1429, counterexample in (1) of the levelwise-truncation
proposition; Stacks Project, Tags 06YU and 0118.
(blueprint: lem-weil-pbc-principal-adjacent-quotient-tor).

Proof: completion preserves each principal quotient sequence. The scalar on the
completed unit descends to an endomorphism t of the next quotient unit, since quotient
restriction is full. Epimorphism refinements and cancellation of the monic completed
scalar show that t and t^(n + 1) form an exact alternating pair. The lower quotient is
the cokernel of the latter map. Its normalized quotient map determines the augmentation.
Both alternating scalars vanish on the residue module: the first completed principal
sequence kills the original scalar on the residue, and quotient-map composition carries
this equality to the next level. Positive powers also vanish. Apply the periodic unit
resolution computation, then transport along the canonical composition of restrictions.
This computes all nonpositive degrees without a flatness assumption on the residue. -/
theorem principalAdjacentQuotient_tor
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] [IsDomain A]
    (d : AdicCoefficientDatum A) (π : A) (hI : d.ideal = Ideal.span {π})
    (hπ : π ≠ 0) (n : ℕ) (i : ℤ) (hi : i ≤ 0) :
    let H := SheafOfModules.unit ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op 0)))
    let M := (pbcRestrict (pbcAdicQuotient T d (n + 1) 0 (Nat.zero_le _))).obj H
    let N := (pbcRestrict (pbcAdicQuotient T d n 0 (Nat.zero_le _))).obj H
    Nonempty ((DerivedCategory.homologyFunctor _ i).obj
      ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) ≅ N) := by
  let B := pbcAdicCompletion T d
  let R := (pbcAdicRings T d).obj (op (n + 1))
  let S := (pbcAdicRings T d).obj (op n)
  let R0 := (pbcAdicRings T d).obj (op 0)
  let H := SheafOfModules.unit ((adicLisseForget T).obj R0)
  let φ := pbcAdicProjection T d (n + 1)
  let ψ := pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)
  let χ := pbcAdicProjection T d n
  let ρ := pbcAdicQuotient T d (n + 1) 0 (Nat.zero_le _)
  let σ := pbcAdicQuotient T d n 0 (Nat.zero_le _)
  let c := CompletedConstantReduction.base T d.ideal ≫
    CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite
  let F := adicLisseConstantModules T A ⋙ completedAdicChange T c
  let e := CompletedConstantReduction.constantChange_unit T c
  let μ : A →* End (ModuleCat.of A A) := {
    toFun a := ModuleCat.ofHom (LinearMap.mulLeft A a)
    map_one' := by apply End.ext; ext; simp
    map_mul' := by intro a b; apply End.ext; ext; simp [End.mul_def] }
  let f : End (SheafOfModules.unit ((adicLisseForget T).obj B)) :=
    e.conj (F.map (μ π))
  have hpow (k : ℕ) : f ^ k = e.inv ≫
      F.map (ModuleCat.ofHom (LinearMap.mulLeft A (π ^ k))) ≫ e.hom := by
    change (e.conj ((F.mapEnd (ModuleCat.of A A)) (μ π))) ^ k =
      e.conj ((F.mapEnd (ModuleCat.of A A)) (μ (π ^ k)))
    rw [map_pow,map_pow,map_pow]
  obtain ⟨p,hzp,hsp,hp⟩ := completed_principal_resolution T d π hI hπ (n + 1)
  obtain ⟨r,hzr,hsr,hr⟩ := completed_principal_resolution T d π hI hπ n
  obtain ⟨p0,hz0,hs0,hp0⟩ := completed_principal_resolution T d π hI hπ 0
  have hf0 : e.inv ≫ F.map (ModuleCat.ofHom (LinearMap.mulLeft A (π ^ (0 + 1)))) ≫
      e.hom = f := by simpa only [Nat.zero_add,pow_one] using (hpow 1).symm
  have : Mono f := by rw [← hf0]; exact hs0.mono_f
  have hz0f : f ≫ p0 = 0 := by rw [← hf0]; exact hz0
  have hzpf : (f ^ (n + 1 + 1)) ≫ p = 0 := by rw [hpow]; exact hzp
  have hspf : (ShortComplex.mk (f ^ (n + 1 + 1)) p hzpf).ShortExact := by
    simpa only [hpow] using hsp
  have hzrf : (f ^ (n + 1)) ≫ r = 0 := by rw [hpow]; exact hzr
  have hsrf : (ShortComplex.mk (f ^ (n + 1)) r hzrf).ShortExact := by
    simpa only [hpow] using hsr
  obtain ⟨t,ht,hfg,hgf,hef,heg,hz,hex,hepi⟩ := quotient_periodic_data T φ ψ χ
    (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) f (n + 1) 1
      p r hp hr hzpf hspf hzrf hsrf
  have := hepi
  have hzero (U : T.ProEtᵒᵖ) :
      (pbcAdicProjection T d 0).hom.app U (f.val.app U (1 : B.obj.obj U)) = 0 := by
    have h := congrArg (fun k ↦ k.val.app U (1 : B.obj.obj U)) hz0f
    change p0.val.app U (f.val.app U (1 : B.obj.obj U)) = 0 at h
    rw [normalized_unit_apply T _ p0 hp0] at h
    exact h
  have htzero (U : T.ProEtᵒᵖ) : ρ.hom.app U (t.val.app U (1 : R.obj.obj U)) = 0 := by
    rw [ht]
    have hc := pbcAdicProjection_comp T d (n + 1) 0 (Nat.zero_le _)
    have hh := congrArg (fun k : B ⟶ R0 ↦
      k.hom.app U (f.val.app U (1 : B.obj.obj U))) hc
    exact hh.trans (hzero U)
  let N := (pbcRestrict σ).obj H
  have hkill (k : ℕ) (hk : 0 < k) (U : T.ProEtᵒᵖ)
      (x : ((pbcRestrict ψ).obj N).val.obj U) :
      (@id (R.obj.obj U) ((t ^ k).val.app U (1 : R.obj.obj U))) • x = 0 := by
    change σ.hom.app U (ψ.hom.app U ((t ^ k).val.app U (1 : R.obj.obj U))) *
      (@id (R0.obj.obj U) x) = 0
    have hc := pbcAdicQuotient_comp T d (n + 1) n 0 (Nat.zero_le _) (Nat.le_succ n)
    have hh := congrArg (fun f : R ⟶ R0 ↦
      f.hom.app U ((t ^ k).val.app U (1 : R.obj.obj U))) hc
    change σ.hom.app U (ψ.hom.app U _) = ρ.hom.app U _ at hh
    rw [hh,unit_end_pow_one,map_pow]
    simp only [id_eq]
    erw [htzero]
    rw [zero_pow (by omega),zero_mul]
  obtain ⟨et⟩ := periodicQuotient_tor T ψ (t ^ 1) (t ^ (n + 1)) hfg hgf hef heg
    (coefficientUnitMap T ψ) (fun U ↦ by
      change ψ.hom.app U (1 : R.obj.obj U) = 1
      exact map_one _) hz hex N
      (hkill 1 (by omega)) (hkill (n + 1) (by omega)) i hi
  let eN := (pbcRestrictComp ψ σ ρ
    (pbcAdicQuotient_comp T d (n + 1) n 0 (Nat.zero_le _) (Nat.le_succ n))).app H
  exact ⟨(DerivedCategory.homologyFunctor _ i).mapIso
    ((pbcDerivedExtend ψ).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso eN.symm)) ≪≫ et⟩
end AlgebraicGeometry.Scheme
