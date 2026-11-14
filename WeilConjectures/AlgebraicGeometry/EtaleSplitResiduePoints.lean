/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.EtaleNeighbourhoodPrescribedResidueField
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import WeilConjectures.FieldTheory.SeparableSplitPurelyInseparableResidueFields
import WeilConjectures.Mathlib.RingTheory.RingHom.PurelyInseparable

/-!
# Splitting the residue fields of finitely many points by an étale neighborhood

## References

* Stacks Project, Tag 02LM
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem split_tensor_equiv_triplet
    {X U S : Scheme.{u}} {f : X ⟶ S} {g : U ⟶ S}
    (T : Scheme.Pullback.Triplet f g) (L : Type u) [Field L]
    [Algebra (S.residueField T.s) L] (e : L ≃+* U.residueField T.y)
    (he : ∀ a : S.residueField T.s,
      e (algebraMap (S.residueField T.s) L a) =
        (g.residueFieldMap T.y).hom ((S.residueFieldCongr T.hy).inv.hom a)) :
    letI := ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom.toAlgebra
    ∃ ρ : (TensorProduct (S.residueField T.s) L (X.residueField T.x)) ≃+* T.tensor,
      ∀ l : L, ρ (algebraMap L _ l) = T.tensorInr.hom (e l) := by
  let k := S.residueField T.s
  let A := X.residueField T.x
  let B := U.residueField T.y
  let a := ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom.toAlgebra
  let b := ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.toAlgebra
  let : Algebra k A := a
  let : Algebra k B := b
  let e' : L ≃ₐ[k] B := { e with commutes' := he }
  let c := ((Algebra.TensorProduct.congr e' (AlgEquiv.refl : A ≃ₐ[k] A)).trans
    (Algebra.TensorProduct.comm k B A)).toRingEquiv
  let d := (CommRingCat.isPushout_tensorProduct k A B).isoPushout.commRingCatIsoToRingEquiv
  refine ⟨c.trans d, ?_⟩
  intro l
  change d (TensorProduct.tmul k (1 : A) (e l)) = T.tensorInr.hom (e l)
  exact congrArg (fun q ↦ q (e l))
    (CommRingCat.isPushout_tensorProduct k A B).inr_isoPushout_hom

private theorem tensorCongr_inr {X U S : Scheme.{u}} {f : X ⟶ S} {g : U ⟶ S}
    {T₁ T₂ : Scheme.Pullback.Triplet f g} (h : T₁ = T₂)
    (b : U.residueField T₁.y) :
    (Scheme.Pullback.Triplet.tensorCongr h).hom.hom (T₁.tensorInr.hom b) =
      T₂.tensorInr.hom ((U.residueFieldCongr (congrArg (fun T ↦ T.y) h)).hom.hom b) := by
  cases h
  rfl

private theorem fixed_pair_finite {X U S : Scheme.{u}} {f : X ⟶ S} {g : U ⟶ S}
    (T : Scheme.Pullback.Triplet f g) [Finite (PrimeSpectrum T.tensor)] :
    Finite {w : ↥(pullback f g) //
      pullback.fst f g w = T.x ∧ pullback.snd f g w = T.y} := by
  classical
  let b : PrimeSpectrum T.tensor → {w : ↥(pullback f g) //
      pullback.fst f g w = T.x ∧ pullback.snd f g w = T.y} := fun p ↦
    ⟨Scheme.Pullback.carrierEquiv.symm ⟨T, p⟩,
      Scheme.Pullback.carrierEquiv_symm_fst T p,
      Scheme.Pullback.carrierEquiv_symm_snd T p⟩
  apply Finite.of_surjective b
  intro w
  have ht : Scheme.Pullback.Triplet.ofPoint w.val = T :=
    Scheme.Pullback.Triplet.ext w.property.1 w.property.2
  let p : PrimeSpectrum T.tensor :=
    Spec.map (Scheme.Pullback.Triplet.tensorCongr ht).inv
      (Scheme.Pullback.SpecOfPoint w.val)
  refine ⟨p, Subtype.ext ?_⟩
  change T.SpecTensorTo p = w.val
  dsimp [p]
  rw [← Scheme.Hom.comp_apply, Scheme.Pullback.tensorCongr_SpecTensorTo]
  exact Scheme.Pullback.SpecTensorTo_SpecOfPoint w.val

/-- Finiteness of a purely inseparable pullback along a split tensor of residue fields
(Stacks, Tags 02LM, 01JT). -/
private theorem finite_purelyInseparable_pullback_of_split_tensor
    {X U S : Scheme.{u}} (f : X ⟶ S) (g : U ⟶ S)
    (s : S) (x : X) (u : U) (hx : f x = s) (hu : g u = s)
    (L : Type u) [Field L] [Algebra (S.residueField s) L]
    (e : L ≃+* U.residueField u)
    (he : ∀ a : S.residueField s,
      e (algebraMap (S.residueField s) L a) =
        (g.residueFieldMap u).hom ((S.residueFieldCongr hu).inv.hom a))
    (hcard : letI := ((S.residueFieldCongr hx).inv ≫ f.residueFieldMap x).hom.toAlgebra
      Finite (PrimeSpectrum (TensorProduct (S.residueField s) L (X.residueField x))))
    (hsplit : letI := ((S.residueFieldCongr hx).inv ≫ f.residueFieldMap x).hom.toAlgebra
      ∀ (p : Ideal (TensorProduct (S.residueField s) L (X.residueField x))), p.IsPrime →
        IsField ((TensorProduct (S.residueField s) L (X.residueField x)) ⧸ p) ∧
          Module.Finite L ((TensorProduct (S.residueField s) L (X.residueField x)) ⧸ p) ∧
          IsPurelyInseparable L ((TensorProduct (S.residueField s) L (X.residueField x)) ⧸ p)) :
    Finite {w : ↥(pullback f g) // pullback.fst f g w = x ∧ pullback.snd f g w = u} ∧
      ∀ (w : ↥(pullback f g)), pullback.fst f g w = x →
        ∀ (hw : pullback.snd f g w = u),
          letI := ((U.residueFieldCongr hw.symm).hom ≫
            (pullback.snd f g).residueFieldMap w).hom.toAlgebra
          Module.Finite (U.residueField u) ((pullback f g).residueField w) ∧
            IsPurelyInseparable (U.residueField u) ((pullback f g).residueField w) := by
  classical
  let T : Scheme.Pullback.Triplet f g := ⟨x, u, s, hx, hu⟩
  let a := ((S.residueFieldCongr hx).inv ≫ f.residueFieldMap x).hom.toAlgebra
  let : Algebra (S.residueField s) (X.residueField x) := a
  obtain ⟨ρ, hρ⟩ := split_tensor_equiv_triplet T L e he
  let : Finite (PrimeSpectrum (TensorProduct (S.residueField s) L (X.residueField x))) := hcard
  let : Finite (PrimeSpectrum T.tensor) :=
    Finite.of_equiv _ (PrimeSpectrum.comapEquiv ρ).toEquiv
  refine ⟨fixed_pair_finite T, ?_⟩
  intro w hwx hwu
  have ht : Scheme.Pullback.Triplet.ofPoint w = T :=
    Scheme.Pullback.Triplet.ext hwx hwu
  let ρ' := ρ.trans (Scheme.Pullback.Triplet.tensorCongr ht.symm).commRingCatIsoToRingEquiv
  let ψ := (Scheme.Pullback.ofPointTensor w).hom
  let F := ψ.comp ρ'.toRingHom
  let p := RingHom.ker F
  let q := RingHom.ker ψ
  have hq : q = p.map ρ'.toRingHom := by
    change RingHom.ker ψ = (RingHom.ker (ψ.comp ρ'.toRingHom)).map ρ'.toRingHom
    rw [← RingHom.comap_ker ψ ρ'.toRingHom]
    exact (Ideal.map_comap_of_surjective ρ'.toRingHom ρ'.surjective _).symm
  let δ := Ideal.quotientEquiv p q ρ' hq
  obtain ⟨hfield, hfin, hpure⟩ := hsplit p (RingHom.ker_isPrime F)
  have hfieldq : IsField ((Scheme.Pullback.Triplet.ofPoint w).tensor ⧸ q) :=
    δ.symm.toMulEquiv.isField hfield
  obtain ⟨η, hη, _, _⟩ :=
    (Scheme.Pullback.exists_residueField_equiv_ofPointTensor f g w).2 hfieldq
  let θ := δ.trans η
  have hθ : ∀ z, θ (Ideal.Quotient.mk p z) = F z := by
    intro z
    change η (δ (Ideal.Quotient.mk p z)) = ψ (ρ' z)
    rw [Ideal.quotientEquiv_mk]
    exact DFunLike.congr_fun hη (ρ' z)
  have hρ' : ∀ l : L, ρ' (algebraMap L _ l) =
      ((U.residueFieldCongr hwu.symm).hom ≫
        (Scheme.Pullback.Triplet.ofPoint w).tensorInr).hom (e l) := by
    intro l
    change (Scheme.Pullback.Triplet.tensorCongr ht.symm).hom.hom
      (ρ (algebraMap L _ l)) = _
    rw [hρ, tensorCongr_inr]
    rfl
  let r := ((U.residueFieldCongr hwu.symm).hom ≫
    (pullback.snd f g).residueFieldMap w).hom
  let : Algebra (U.residueField u) ((pullback f g).residueField w) := r.toAlgebra
  have hc : r.comp e.toRingHom = θ.toRingHom.comp (algebraMap L _) := by
    ext l
    change r (e l) = θ (Ideal.Quotient.mk p (algebraMap L _ l))
    rw [hθ]
    change r (e l) = ψ (ρ' (algebraMap L _ l))
    rw [hρ']
    change _ = ψ ((Scheme.Pullback.Triplet.ofPoint w).tensorInr.hom
      ((U.residueFieldCongr hwu.symm).hom.hom (e l)))
    have hr := congrArg (fun h ↦ h.hom
      ((U.residueFieldCongr hwu.symm).hom.hom (e l)))
      (pushout.inr_desc _ _
        (Scheme.Pullback.residueFieldCongr_inv_residueFieldMap_ofPoint w))
    exact hr.symm
  let : Module.Finite L ((TensorProduct (S.residueField s) L (X.residueField x)) ⧸ p) := hfin
  refine ⟨Module.Finite.of_equiv_equiv e θ hc, ?_⟩
  let : Field ((TensorProduct (S.residueField s) L (X.residueField x)) ⧸ p) := hfield.toField
  exact RingHom.IsPurelyInseparable.of_comp_eq_comp' e.bijective θ.bijective hc.symm
    (RingHom.isPurelyInseparable_algebraMap_iff.mpr hpure)

/-- There is an étale neighbourhood of `s` splitting the residue points `x i` of `f`
(Stacks, Tag 02LM). -/
theorem exists_etale_split_residue_points
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (n : ℕ) (x : Fin n → X)
    (hx : ∀ i, f (x i) = s)
    (hfinite : ∀ i, letI := (f.residueFieldMap (x i)).hom.toAlgebra
      Module.Finite (S.residueField (f (x i))) (X.residueField (x i))) :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S) (u : U), Etale φ ∧ φ u = s ∧
      ∃ (m : Fin n → ℕ) (y : (i : Fin n) → Fin (m i) → ↥(pullback f φ)),
        (∀ i, Function.Injective (y i)) ∧
        (∀ i j, pullback.fst f φ (y i j) = x i) ∧
        (∀ i j, ∃ (hy : pullback.snd f φ (y i j) = u),
          letI := ((U.residueFieldCongr hy.symm).hom ≫
            (pullback.snd f φ).residueFieldMap (y i j)).hom.toAlgebra
          Module.Finite (U.residueField u) ((pullback f φ).residueField (y i j)) ∧
            IsPurelyInseparable (U.residueField u)
              ((pullback f φ).residueField (y i j))) ∧
        (∀ (i : Fin n) (w : ↥(pullback f φ)),
          pullback.snd f φ w = u → pullback.fst f φ w = x i →
            ∃ j : Fin (m i), w = y i j) := by
  classical
  let K : Fin n → Type u := fun i ↦ X.residueField (x i)
  let a : (i : Fin n) → Algebra (S.residueField s) (K i) := fun i ↦
    ((S.residueFieldCongr (hx i)).inv ≫ f.residueFieldMap (x i)).hom.toAlgebra
  let : (i : Fin n) → Algebra (S.residueField s) (K i) := a
  have hK : (i : Fin n) → Module.Finite (S.residueField s) (K i) := by
    intro i
    have hi := hfinite i
    cases hx i
    simpa [K, a] using hi
  let : (i : Fin n) → Module.Finite (S.residueField s) (K i) := hK
  obtain ⟨L, hL, aL, hfin, hsep, _, _, hsplit⟩ :=
    Algebra.exists_separable_split_purelyInseparable_prime_quotients
      (S.residueField s) n K
  let := hL
  let := aL
  let := hfin
  let := hsep
  obtain ⟨U, φ, hφ, u, hu, e, he⟩ :=
    S.exists_etale_neighbourhood_prescribed_residueField s L
  have hp := fun i ↦ finite_purelyInseparable_pullback_of_split_tensor
    f φ s (x i) u (hx i) hu L e he (hsplit i).1 (hsplit i).2
  let P : Fin n → Type u := fun i ↦
    {w : ↥(pullback f φ) // pullback.fst f φ w = x i ∧ pullback.snd f φ w = u}
  have hP : (i : Fin n) → Finite (P i) := fun i ↦ (hp i).1
  let : (i : Fin n) → Finite (P i) := hP
  let m : Fin n → ℕ := fun i ↦ Nat.card (P i)
  let b : (i : Fin n) → Fin (m i) ≃ P i := fun i ↦ (Finite.equivFin (P i)).symm
  let y : (i : Fin n) → Fin (m i) → ↥(pullback f φ) := fun i j ↦ (b i j).val
  refine ⟨U, φ, u, hφ, hu, m, y, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Subtype.val_injective.comp (b i).injective
  · intro i j
    exact (b i j).property.1
  · intro i j
    exact ⟨(b i j).property.2,
      (hp i).2 (y i j) (b i j).property.1 (b i j).property.2⟩
  · intro i w hw hxw
    let z : P i := ⟨w, hxw, hw⟩
    refine ⟨(b i).symm z, ?_⟩
    exact (congrArg Subtype.val ((b i).apply_symm_apply z)).symm

end AlgebraicGeometry
