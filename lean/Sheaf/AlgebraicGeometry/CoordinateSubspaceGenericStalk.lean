/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Algebra.MvPolynomial.Equiv

/-! The normal local ring at the generic point of a coordinate subspace. -/
@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
open MvPolynomial

set_option backward.isDefEq.respectTransparency false in
private theorem origin_fraction_localization (R : Type u) [CommRing R] [IsDomain R]
    (σ : Type v) :
    letI := RingHom.ker_isPrime (MvPolynomial.eval (fun _ : σ ↦ (0 : R)))
    letI := RingHom.ker_isPrime (MvPolynomial.eval (fun _ : σ ↦ (0 : FractionRing R)))
    Nonempty (Localization.AtPrime (RingHom.ker (MvPolynomial.eval (fun _ : σ ↦ (0 : R)))) ≃+*
      Localization.AtPrime (RingHom.ker
        (MvPolynomial.eval (fun _ : σ ↦ (0 : FractionRing R))))) := by
  let K := FractionRing R
  let A := MvPolynomial σ R
  let B := MvPolynomial σ K
  let p : Ideal A := RingHom.ker (MvPolynomial.eval (fun _ : σ ↦ (0 : R)))
  let q : Ideal B := RingHom.ker (MvPolynomial.eval (fun _ : σ ↦ (0 : K)))
  have : p.IsPrime := RingHom.ker_isPrime _
  have : q.IsPrime := RingHom.ker_isPrime _
  let : Algebra A B := MvPolynomial.algebraMvPolynomial
  have : IsScalarTower A B (Localization.AtPrime q) := inferInstance
  have hmap : q.comap (algebraMap A B) = p := by
    ext f
    change MvPolynomial.eval (fun _ : σ ↦ (0 : K))
      (MvPolynomial.map (algebraMap R K) f) = 0 ↔
      MvPolynomial.eval (fun _ : σ ↦ (0 : R)) f = 0
    have he : MvPolynomial.eval (fun _ : σ ↦ (0 : K))
        (MvPolynomial.map (algebraMap R K) f) =
        algebraMap R K (MvPolynomial.eval (fun _ : σ ↦ (0 : R)) f) := by
      simpa only [Function.comp_def, map_zero] using
        (MvPolynomial.map_eval (algebraMap R K) (fun _ : σ ↦ (0 : R)) f).symm
    rw [he]
    exact map_eq_zero_iff _ (IsFractionRing.injective R K)
  have : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    have hl := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      ((nonZeroDivisors R).map (MvPolynomial.C : R →+* A)) (Localization.AtPrime q) q
    change IsLocalization.AtPrime (Localization.AtPrime q)
      (q.comap (MvPolynomial.map (algebraMap R K))) at hl
    change q.comap (MvPolynomial.map (algebraMap R K)) = p at hmap
    simpa only [hmap] using hl
  exact ⟨(IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (Localization.AtPrime q)).toRingEquiv⟩

private theorem origin_ker (R : Type u) [CommRing R] (σ : Type v) :
    Ideal.span (Set.range (X : σ → MvPolynomial σ R)) =
      RingHom.ker (MvPolynomial.eval (fun _ : σ ↦ (0 : R))) := by
  let p := Ideal.span (Set.range (X : σ → MvPolynomial σ R))
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp
  · intro q hq
    have h : q - C ((MvPolynomial.eval (fun _ : σ ↦ (0 : R))) q) ∈ p := by
      clear hq
      induction q using MvPolynomial.induction_on with
      | C a => simp
      | add a b ha hb =>
        simpa [map_add, sub_add_sub_comm] using p.add_mem ha hb
      | mul_X a i ha =>
        simpa using p.mul_mem_left a (Ideal.subset_span (Set.mem_range_self i))
    have hz := RingHom.mem_ker.mp hq
    rw [hz, map_zero, sub_zero] at h
    exact h

set_option backward.isDefEq.respectTransparency false in
private theorem coordinate_model_origin_stalk (k : Type u) [Field k] (a b : ℕ) :
    let φ := MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial (Fin a) k)
      (fun j : Fin (a + b) ↦ Fin.addCases (fun i ↦ MvPolynomial.X i) (fun _ ↦ 0) j)
    let p := PrimeSpectrum.comap φ (⊥ : PrimeSpectrum (MvPolynomial (Fin a) k))
    ∃ q : PrimeSpectrum (MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) k))),
      q.asIdeal = Ideal.span (Set.range (MvPolynomial.X : Fin b →
        MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) k)))) ∧
      Nonempty (Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal) := by
  let φ := MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial (Fin a) k)
    (fun j : Fin (a + b) ↦ Fin.addCases (fun i ↦ MvPolynomial.X i) (fun _ ↦ 0) j)
  let p := PrimeSpectrum.comap φ (⊥ : PrimeSpectrum (MvPolynomial (Fin a) k))
  let R := MvPolynomial (Fin a) k
  let J : Ideal (MvPolynomial (Fin b) R) :=
    RingHom.ker (MvPolynomial.eval (fun _ : Fin b ↦ (0 : R)))
  have : J.IsPrime := RingHom.ker_isPrime _
  let E : MvPolynomial (Fin (a + b)) k ≃+* MvPolynomial (Fin b) R :=
    (MvPolynomial.renameEquiv k
      (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin a) (Fin b)))).toRingEquiv.trans
        (MvPolynomial.sumRingEquiv k (Fin b) (Fin a))
  have hφ : (MvPolynomial.eval (fun _ : Fin b ↦ (0 : R))).comp E.toRingHom = φ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have he : E (C r) = C (C r) := by
        dsimp [E]
        rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C]
        exact MvPolynomial.sumRingEquiv_C _ _ _ _
      change MvPolynomial.eval (fun _ : Fin b ↦ (0 : R)) (E (C r)) = φ (C r)
      rw [he, MvPolynomial.eval_C]
      exact (MvPolynomial.eval₂Hom_C _ _ _).symm
    · intro i
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · have he : E (X (Fin.castAdd b j)) = C (X j) := by
          dsimp [E]
          rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
          rw [Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]
          change MvPolynomial.sumRingEquiv k (Fin b) (Fin a) (X (Sum.inr j)) = _
          exact MvPolynomial.sumRingEquiv_X_inr _ _ _ _
        change MvPolynomial.eval (fun _ : Fin b ↦ (0 : R)) (E (X (Fin.castAdd b j))) =
          φ (X (Fin.castAdd b j))
        rw [he, MvPolynomial.eval_C]
        exact (show φ (X (Fin.castAdd b j)) = X j by
          rw [MvPolynomial.eval₂Hom_X', Fin.addCases_left]).symm
      · have he : E (X (Fin.natAdd a j)) = X j := by
          dsimp [E]
          rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
          rw [Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd]
          change MvPolynomial.sumRingEquiv k (Fin b) (Fin a) (X (Sum.inl j)) = _
          exact MvPolynomial.sumRingEquiv_X_inl _ _ _ _
        change MvPolynomial.eval (fun _ : Fin b ↦ (0 : R)) (E (X (Fin.natAdd a j))) =
          φ (X (Fin.natAdd a j))
        rw [he, MvPolynomial.eval_X]
        exact (show φ (X (Fin.natAdd a j)) = 0 by
          rw [MvPolynomial.eval₂Hom_X', Fin.addCases_right]).symm
  have hJ : p.asIdeal = J.comap E.toRingHom := by
    change RingHom.ker φ = Ideal.comap E.toRingHom J
    rw [← hφ]
    rfl
  let Q : Ideal (MvPolynomial (Fin b) (FractionRing R)) :=
    RingHom.ker (MvPolynomial.eval (fun _ : Fin b ↦ (0 : FractionRing R)))
  have : Q.IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨Q, inferInstance⟩, ?_, ?_⟩
  · exact (origin_ker (FractionRing R) (Fin b)).symm
  · obtain ⟨e₂⟩ := origin_fraction_localization R (Fin b)
    exact ⟨(Localization.localRingEquiv p.asIdeal J E hJ).trans e₂⟩

set_option backward.isDefEq.respectTransparency false in
private theorem coordinate_model_origin_stalk_ulift (k : Type u) [Field k] (a b : ℕ) :
    let φ := MvPolynomial.eval₂Hom
      (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin a)) k)
      (fun j : ULift.{u} (Fin (a + b)) ↦
        Fin.addCases (fun i ↦ MvPolynomial.X (ULift.up i)) (fun _ ↦ 0) j.down)
    let p := PrimeSpectrum.comap φ
      (⊥ : PrimeSpectrum (MvPolynomial (ULift.{u} (Fin a)) k))
    ∃ q : PrimeSpectrum (MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) k))),
      q.asIdeal = Ideal.span (Set.range (MvPolynomial.X : Fin b →
        MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) k)))) ∧
      Nonempty (Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal) := by
  let φu := MvPolynomial.eval₂Hom
    (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin a)) k)
    (fun j : ULift.{u} (Fin (a + b)) ↦
      Fin.addCases (fun i ↦ MvPolynomial.X (ULift.up i)) (fun _ ↦ 0) j.down)
  let φ := MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial (Fin a) k)
    (fun j : Fin (a + b) ↦ Fin.addCases (fun i ↦ MvPolynomial.X i) (fun _ ↦ 0) j)
  let p := PrimeSpectrum.comap φ (⊥ : PrimeSpectrum (MvPolynomial (Fin a) k))
  let pu := PrimeSpectrum.comap φu
    (⊥ : PrimeSpectrum (MvPolynomial (ULift.{u} (Fin a)) k))
  let E := (MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin (a + b)) ≃ _))
  let G := (MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin a) ≃ _))
  have hc : G.toRingHom.comp φu = φ.comp E.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [φu, φ, E, G]
    · rintro ⟨l⟩
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) l <;> simp [φu, φ, E, G]
  have hp : pu.asIdeal = p.asIdeal.comap E.toRingHom := by
    ext f
    change φu f = 0 ↔ φ (E f) = 0
    have he := RingHom.congr_fun hc f
    change G (φu f) = φ (E f) at he
    rw [← he]
    exact (map_eq_zero_iff G G.injective).symm
  obtain ⟨q, hq, ⟨eqv⟩⟩ := coordinate_model_origin_stalk k a b
  exact ⟨q, hq, ⟨(Localization.localRingEquiv pu.asIdeal p.asIdeal E.toRingEquiv hp).trans eqv⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem affine_fiber_model {S : Scheme.{u}} (n : Type u) (s : S)
    (k : CommRingCat.{u}) (ek : S.residueField s ≅ k) :
    ∃ E : AffineSpace n (Spec k) ≅ (AffineSpace n S ↘ S).fiber s,
      E.hom ≫ (AffineSpace n S ↘ S).fiberι s =
        AffineSpace.map n (Spec.map ek.hom ≫ S.fromSpecResidueField s) := by
  let f := Spec.map ek.hom ≫ S.fromSpecResidueField s
  let π := AffineSpace n S ↘ S
  let F : pullback π f ⟶ π.fiber s := pullback.map π f π (S.fromSpecResidueField s)
    (𝟙 _) (Spec.map ek.hom) (𝟙 _) (by simp) (by simp [f])
  have : IsIso F := by dsimp [F]; infer_instance
  let E := (AffineSpace.isPullback_map (n := n) f).isoPullback ≪≫ asIso F
  refine ⟨E, ?_⟩
  change (AffineSpace.isPullback_map (n := n) f).isoPullback.hom ≫ F ≫
    pullback.fst π (S.fromSpecResidueField s) = AffineSpace.map n f
  rw [show F ≫ pullback.fst π (S.fromSpecResidueField s) = pullback.fst π f by
    dsimp [F]
    simp only [pullback.map, pullback.lift_fst, Category.comp_id]]
  exact (AffineSpace.isPullback_map (n := n) f).isoPullback_hom_fst

private theorem fiber_generic_transport {V S : Scheme.{u}} (f : V ⟶ S) (v : V) (s : S)
    (h : f v = s) (hg : IsGenericPoint (f.asFiber v) Set.univ) :
    IsGenericPoint ((f.fiberHomeo s).symm ⟨v, h⟩) Set.univ := by
  subst s
  exact hg

set_option backward.isDefEq.respectTransparency false in
private theorem coordinate_fiber_stalk_model {S : Scheme.{u}} (a b : ℕ)
    (z : AffineSpace (ULift.{u} (Fin a)) S)
    (hgen : IsGenericPoint ((AffineSpace (ULift.{u} (Fin a)) S ↘ S).asFiber z) Set.univ)
    (k : CommRingCat.{u}) (ek : S.residueField
      ((AffineSpace (ULift.{u} (Fin a)) S ↘ S) z) ≅ k) :
    let j := AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) S ↘ S)
      (fun l : ULift.{u} (Fin (a + b)) ↦
        Fin.addCases (fun i ↦ AffineSpace.coord S (ULift.up i)) (fun _ ↦ 0) l.down)
    let jk := AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) (Spec k) ↘ Spec k)
      (fun l : ULift.{u} (Fin (a + b)) ↦
        Fin.addCases (fun i ↦ AffineSpace.coord (Spec k) (ULift.up i)) (fun _ ↦ 0) l.down)
    ∃ zk : AffineSpace (ULift.{u} (Fin a)) (Spec k),
      IsGenericPoint zk Set.univ ∧
      Nonempty
        ((((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S).fiber
            ((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S) (j z))).presheaf.stalk
          ((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S).asFiber (j z))) ≃+*
            ((AffineSpace (ULift.{u} (Fin (a + b))) (Spec k)).presheaf.stalk (jk zk))) := by
  let j := AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) S ↘ S)
    (fun l : ULift.{u} (Fin (a + b)) ↦
      Fin.addCases (fun i ↦ AffineSpace.coord S (ULift.up i)) (fun _ ↦ 0) l.down)
  let jk := AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) (Spec k) ↘ Spec k)
    (fun l : ULift.{u} (Fin (a + b)) ↦
      Fin.addCases (fun i ↦ AffineSpace.coord (Spec k) (ULift.up i)) (fun _ ↦ 0) l.down)
  let πa := AffineSpace (ULift.{u} (Fin a)) S ↘ S
  let πb := AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S
  let s := πb (j z)
  have hb : s = πa z := by
    change πb (j z) = πa z
    rw [← Scheme.Hom.comp_apply]
    have hj : j ≫ πb = πa := AffineSpace.homOfVector_over _ _
    rw [hj]
  let ek' : S.residueField s ≅ k := S.residueFieldCongr hb ≪≫ ek
  let f := Spec.map ek'.hom ≫ S.fromSpecResidueField s
  obtain ⟨Ea, hEa⟩ := affine_fiber_model (ULift.{u} (Fin a)) s k ek'
  obtain ⟨Eb, hEb⟩ := affine_fiber_model (ULift.{u} (Fin (a + b))) s k ek'
  let wa : πa.fiber s := (πa.fiberHomeo s).symm ⟨z, hb.symm⟩
  let zk := Ea.inv wa
  have hwa : IsGenericPoint wa Set.univ := fiber_generic_transport πa z s hb.symm hgen
  have hzk : IsGenericPoint zk Set.univ := by
    have hg := hwa.image Ea.inv.continuous
    rw [Set.image_univ] at hg
    have hr : Set.range (fun x ↦ Ea.inv x) = Set.univ := Ea.inv.surjective.range_eq
    rw [hr, closure_univ] at hg
    exact hg
  have hEa' : AffineSpace.map (ULift.{u} (Fin a)) f zk = z := by
    rw [← hEa]
    change (πa.fiberι s) (Ea.hom (Ea.inv wa)) = z
    have he : Ea.hom (Ea.inv wa) = wa := by
      rw [← Scheme.Hom.comp_apply, Ea.inv_hom_id]
      rfl
    rw [he]
    exact πa.fiberι_fiberHomeo_symm s ⟨z, hb.symm⟩
  have hnat : jk ≫ AffineSpace.map (ULift.{u} (Fin (a + b))) f =
      AffineSpace.map (ULift.{u} (Fin a)) f ≫ j := by
    apply AffineSpace.hom_ext
    · simp [j, jk, AffineSpace.map_over]
    · rintro ⟨l⟩
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) l
      · simp [j, jk]
      · simp [j, jk]
  have hpt : Eb.hom (jk zk) = πb.asFiber (j z) := by
    apply (πb.fiberι s).isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hEb, Scheme.Hom.fiberι_asFiber]
    change (AffineSpace.map (ULift.{u} (Fin (a + b))) f) (jk zk) = j z
    rw [← Scheme.Hom.comp_apply, hnat, Scheme.Hom.comp_apply, hEa']
  refine ⟨zk, hzk, ?_⟩
  exact ⟨(((πb.fiber s).presheaf.stalkCongr (.of_eq hpt)).symm ≪≫
    asIso (Eb.hom.stalkMap (jk zk))).commRingCatIsoToRingEquiv⟩

set_option backward.isDefEq.respectTransparency false in
private theorem coordinate_stalk_spec (k : Type u) [Field k] (a b : ℕ)
    (z : AffineSpace (ULift.{u} (Fin a)) (Spec (.of k)))
    (hgen : IsGenericPoint z Set.univ) :
    let j := AffineSpace.homOfVector
      (AffineSpace (ULift.{u} (Fin a)) (Spec (.of k)) ↘ Spec (.of k))
      (fun l : ULift.{u} (Fin (a + b)) ↦
        Fin.addCases (fun i ↦ AffineSpace.coord (Spec (.of k)) (ULift.up i))
          (fun _ ↦ 0) l.down)
    let φ := MvPolynomial.eval₂Hom
      (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin a)) k)
      (fun l : ULift.{u} (Fin (a + b)) ↦
        Fin.addCases (fun i ↦ MvPolynomial.X (ULift.up i)) (fun _ ↦ 0) l.down)
    let p := PrimeSpectrum.comap φ (⊥ : PrimeSpectrum (MvPolynomial (ULift.{u} (Fin a)) k))
    Nonempty (((AffineSpace (ULift.{u} (Fin (a + b))) (Spec (.of k))).presheaf.stalk (j z)) ≃+*
      Localization.AtPrime p.asIdeal) := by
  let j := AffineSpace.homOfVector
    (AffineSpace (ULift.{u} (Fin a)) (Spec (.of k)) ↘ Spec (.of k))
    (fun l : ULift.{u} (Fin (a + b)) ↦
      Fin.addCases (fun i ↦ AffineSpace.coord (Spec (.of k)) (ULift.up i))
        (fun _ ↦ 0) l.down)
  let φ := MvPolynomial.eval₂Hom
    (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin a)) k)
    (fun l : ULift.{u} (Fin (a + b)) ↦
      Fin.addCases (fun i ↦ MvPolynomial.X (ULift.up i)) (fun _ ↦ 0) l.down)
  let e₁ := AffineSpace.SpecIso (ULift.{u} (Fin a)) (CommRingCat.of k)
  let e₂ := AffineSpace.SpecIso (ULift.{u} (Fin (a + b))) (CommRingCat.of k)
  have hzp : e₁.hom z = (⊥ : PrimeSpectrum (MvPolynomial (ULift.{u} (Fin a)) k)) := by
    have hg : IsGenericPoint (e₁.hom z) Set.univ := by
      simpa only [Set.image_univ, e₁.hom.surjective.range_eq, closure_univ]
        using hgen.image e₁.hom.continuous
    apply hg.eq
    have hg₀ := genericPoint_spec (Spec (CommRingCat.of
      (MvPolynomial (ULift.{u} (Fin a)) k)))
    rw [genericPoint_eq_bot_of_affine] at hg₀
    exact hg₀
  have hc : e₁.inv ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ e₂.inv := by
    apply AffineSpace.hom_ext
    · simp only [Category.assoc, j, AffineSpace.homOfVector_over,
        AffineSpace.SpecIso_inv_over, e₁, e₂]
      rw [← Spec.map_comp]
      congr 1
      ext r
      simp [φ]
    · rintro ⟨l⟩
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      change e₁.inv.appTop (j.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up l))) =
        (Spec.map (CommRingCat.ofHom φ)).appTop
          (e₂.inv.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up l)))
      rw [show e₂.inv.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up l)) =
        (Scheme.ΓSpecIso (.of (MvPolynomial (ULift.{u} (Fin (a + b))) k))).inv
          (MvPolynomial.X (ULift.up l)) from
            AffineSpace.SpecIso_inv_appTop_coord (.of k) (ULift.up l)]
      have hn := congrArg (fun m ↦ m (MvPolynomial.X (ULift.up l)))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hn
      rw [← hn]
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) l
      · rw [show j.appTop (AffineSpace.coord (Spec (.of k))
            (ULift.up (Fin.castAdd b i))) =
            AffineSpace.coord (Spec (.of k)) (ULift.up i) by
          simp [j]]
        rw [show e₁.inv.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up i)) =
          (Scheme.ΓSpecIso (.of (MvPolynomial (ULift.{u} (Fin a)) k))).inv
            (MvPolynomial.X (ULift.up i)) from
              AffineSpace.SpecIso_inv_appTop_coord (.of k) (ULift.up i)]
        simp [φ]
      · rw [show j.appTop (AffineSpace.coord (Spec (.of k))
            (ULift.up (Fin.natAdd a i))) = 0 by simp [j], map_zero]
        simp [φ]
  have hc' : j ≫ e₂.hom = e₁.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← cancel_epi e₁.inv]
    simp only [← Category.assoc, hc]
    simp
  have hp : e₂.hom (j z) =
      PrimeSpectrum.comap φ (⊥ : PrimeSpectrum (MvPolynomial (ULift.{u} (Fin a)) k)) := by
    rw [← Scheme.Hom.comp_apply, hc', Scheme.Hom.comp_apply, hzp]
    rfl
  have he : Nonempty
      (((AffineSpace (ULift.{u} (Fin (a + b))) (Spec (.of k))).presheaf.stalk (j z)) ≃+*
        Localization.AtPrime (e₂.hom (j z)).asIdeal) := by
    exact ⟨(asIso (e₂.hom.stalkMap (j z))).commRingCatIsoToRingEquiv.symm.trans
      (Spec.stalkIso _ (e₂.hom (j z))).commRingCatIsoToRingEquiv⟩
  change Nonempty (_ ≃+* Localization.AtPrime
    (PrimeSpectrum.comap φ (⊥ : PrimeSpectrum (MvPolynomial (ULift.{u} (Fin a)) k))).asIdeal)
  exact (congrArg (fun q : PrimeSpectrum (MvPolynomial (ULift.{u} (Fin (a + b))) k) ↦
    Nonempty (((AffineSpace (ULift.{u} (Fin (a + b))) (Spec (.of k))).presheaf.stalk
      (j z)) ≃+* Localization.AtPrime q.asIdeal)) hp) ▸ he

/-- The ambient fibre stalk at the generic point of a coordinate subspace is the
polynomial origin local ring over its tangential function field.
Source: Stacks Project, Tag 01HV; coordinate-chart witness argument, Steps 3--4
(blueprint: lem-pur-coordinate-subspace-generic-stalk).

Proof: Base change to the residue field at the image of z. Use the affine-space
spectrum isomorphism to identify its coordinate ring with k[u,v]. Genericity
identifies the tangential prime with zero, hence the ambient prime is (v).
Rewrite k[u,v] as k[u][v] and invert the nonzero elements of k[u]. Polynomial
localization commutes with localization of coefficients, and transitivity of
localization identifies localization at (v) before and after this operation.
The resulting coefficient field is Frac(k[u]). The affine-open residue-field
isomorphism identifies k with s.ResidueField; relabel the ULift coordinates
by Fin a and Fin b. The affine stalk-localization isomorphism completes the proof.
-/
theorem coordinate_subspace_generic_fiber_stalk
    {S : Scheme.{u}} (a b : ℕ) (U : S.Opens) (hU : IsAffineOpen U)
    (s : PrimeSpectrum Γ(S, U)) (z : AffineSpace (ULift.{u} (Fin a)) S)
    (hz : (AffineSpace (ULift.{u} (Fin a)) S ↘ S) z = hU.fromSpec s)
    (hgen : IsGenericPoint
      ((AffineSpace (ULift.{u} (Fin a)) S ↘ S).asFiber z) Set.univ) :
    let j := AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) S ↘ S)
      (fun l : ULift.{u} (Fin (a + b)) ↦
        Fin.addCases (fun k ↦ AffineSpace.coord S (ULift.up k)) (fun _ ↦ 0) l.down)
    ∃ q : PrimeSpectrum
        (MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) s.asIdeal.ResidueField))),
      q.asIdeal = Ideal.span (Set.range (MvPolynomial.X : Fin b →
        MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) s.asIdeal.ResidueField)))) ∧
      Nonempty
        ((((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S).fiber
            ((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S) (j z))).presheaf.stalk
          ((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S).asFiber (j z))) ≃+*
            Localization.AtPrime q.asIdeal) := by
  let ek : S.residueField ((AffineSpace (ULift.{u} (Fin a)) S ↘ S) z) ≅
      CommRingCat.of s.asIdeal.ResidueField :=
    S.residueFieldCongr hz ≪≫ asIso (hU.fromSpec.residueFieldMap s) ≪≫
      Scheme.Spec.residueFieldIso Γ(S, U) s
  obtain ⟨zk, hzk, ⟨ef⟩⟩ := coordinate_fiber_stalk_model a b z hgen
    (CommRingCat.of s.asIdeal.ResidueField) ek
  obtain ⟨es⟩ := coordinate_stalk_spec s.asIdeal.ResidueField a b zk hzk
  obtain ⟨q, hq, ⟨el⟩⟩ := coordinate_model_origin_stalk_ulift s.asIdeal.ResidueField a b
  exact ⟨q, hq, ⟨ef.trans (es.trans el)⟩⟩

end AlgebraicGeometry
