/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GenericPoint
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.KummerCover
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
public import Mathlib.FieldTheory.Galois.Profinite
import WeilConjectures.AlgebraicGeometry.EllipticDivisionDifference
import WeilConjectures.AlgebraicGeometry.EllipticDivisionOrbitTransitive
import WeilConjectures.AlgebraicGeometry.EllipticDivisionOrbitContinuous
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale

/-! # Monodromy of the elliptic multiplication tower -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
namespace AlgebraicGeometry


private theorem field_spec_epi {k L : Type u} [Field k] [Field L]
    (g : Spec (.of L) ⟶ Spec (.of k)) : Epi g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  let : Algebra k L := φ.hom.toAlgebra
  have h : Flat (Spec.map φ) ∧ Surjective (Spec.map φ) :=
    (flat_and_surjective_SpecMap_iff φ).mpr (by
      change (algebraMap k L).FaithfullyFlat
      exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have := h.1
  have := h.2
  exact Flat.epi_of_flat_of_surjective _


/-- The multiplication tower has a continuous surjective translation character
into the Tate module, with compatible division points realizing its coordinates.

At level m the connected finite etale cover [r^m] has a field as its generic
fibre. The Galois group acts transitively on its geometric points. Translation
by E[r^m](k) acts simply transitively: two division points differ by torsion,
and finite etale torsion over the algebraically closed ground field is constant.
The transition on these torsors is [r], equivariant for the torsion transition.
Starting at the generic point, lift recursively through [r] over the
separably closed generic field to obtain a compatible system x_m. Define
rho_m(sigma) by sigma(x_m)=x_m+rho_m(sigma).
Constants are Galois fixed, so rho_m is a homomorphism. The finite Galois action
is continuous and transitive, so rho_m is continuous and surjective. The
transition identities make (rho_m) an element of the existing Tate module and
a homomorphism rho. Coordinatewise continuity is exactly continuity for the
induced product topology displayed below. For any compatible torsion tuple,
the sets of sigma with the prescribed value at level m are nonempty closed
subsets of the compact absolute Galois group; they are nested. Compactness
gives a common point, proving surjectivity of rho. The choice of x and rho is
made inside this existence theorem, not used to define a new data object.

Source: the multiplication-cover paragraph of
`literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/
sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md`.
(blueprint: lem-sf-elliptic-tate-galois-data) -/
theorem ellipticTateGaloisData
    (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]
    (_hDim : IsAbelianVariety.dim E = 1)
    (r : ℕ) [Fact r.Prime] (hrp : r ≠ p) :
      letI : TopologicalSpace (IsAbelianVariety.tateModule r E) :=
        TopologicalSpace.induced
          (fun t : IsAbelianVariety.tateModule r E ↦
            (t : ℕ → Additive (Scheme.specAlgebraicClosure k ⟶ E)))
          (@Pi.topologicalSpace ℕ
            (fun _ ↦ Additive (Scheme.specAlgebraicClosure k ⟶ E)) (fun _ ↦ ⊥))
      ∃ (ρ : (SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
          SeparableClosure E.left.functionField) →*
            Multiplicative (IsAbelianVariety.tateModule r E)),
        Continuous ρ ∧ Function.Surjective ρ ∧
          (∃ x : ℕ → ((Over.map E.hom).obj
              ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left)) ⟶ E),
            (∀ m, x m ≫ (𝟙 E ^ (r ^ m)) =
              Over.homMk (Scheme.ProEt.genericPointSep E.left).hom rfl) ∧
            (∀ m, x (m + 1) ≫ (𝟙 E ^ r) = x m) ∧
            ∀ σ m,
              ((Over.map E.hom).map ((Scheme.ProEt.forget E.left).map
                (Scheme.ProEt.genericPointSepAut E.left σ))) ≫ x m =
                x m * (toUnit ((Over.map E.hom).obj
                    ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left))) ≫
                  inv (toUnit (Scheme.specAlgebraicClosure k)) ≫
                  (((ρ σ).toAdd : ℕ → Additive (Scheme.specAlgebraicClosure k ⟶ E))
                    m).toMul)) := by
  classical
  let T := (Over.map E.hom).obj
    ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left))
  let P := Scheme.specAlgebraicClosure k ⟶ E
  let Q := T ⟶ E
  let G := SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
    SeparableClosure E.left.functionField
  let F := Scheme.ProEt.forget E.left ⋙ Over.map E.hom
  let a (σ : G) : T ⟶ T := F.map (Scheme.ProEt.genericPointSepAut E.left σ)
  let gen : Q := Over.homMk (Scheme.ProEt.genericPointSep E.left).hom rfl
  let c := toUnit T ≫ inv (toUnit (Scheme.specAlgebraicClosure k))
  have : Epi (toUnit T) := by
    have : Epi (toUnit T).left := by
      change Epi T.hom
      exact field_spec_epi T.hom
    exact Over.epi_of_epi_left _
  let C : P →* Q :=
    { toFun z := c ≫ z
      map_one' := MonObj.comp_one c
      map_mul' z w := MonObj.comp_mul c z w }
  have hC : Function.Injective C := fun z w h ↦ (cancel_epi c).mp h
  have hc (σ : G) (z : P) : a σ ≫ C z = C z := by
    change a σ ≫ (toUnit T ≫ inv (toUnit (Scheme.specAlgebraicClosure k)) ≫ z) = _
    rw [comp_toUnit_assoc]
    rfl
  have ha1 : a 1 = 𝟙 T := by
    change F.map (Scheme.ProEt.genericPointSepAut E.left 1) = 𝟙 T
    rw [Scheme.ProEt.genericPointSepAut_one, F.map_id]
    rfl
  have hamul (σ τ : G) : a (σ * τ) = a σ ≫ a τ := by
    change F.map (Scheme.ProEt.genericPointSepAut E.left (σ * τ)) = _
    rw [Scheme.ProEt.genericPointSepAut_mul, F.map_comp]
  have hgen (σ : G) : a σ ≫ gen = gen := by
    apply Over.OverMorphism.ext
    exact MorphismProperty.Over.w (Scheme.ProEt.genericPointSepAut E.left σ)
  have hcovers (m : ℕ) : IsFinite (𝟙 E ^ (r ^ m)).left ∧
      Etale (𝟙 E ^ (r ^ m)).left ∧ Surjective (𝟙 E ^ (r ^ m)).left := by
    have hm : 0 < r ^ m := pow_pos (Fact.out : Nat.Prime r).pos _
    have hnp : ¬ p ∣ r ^ m := by
      intro h
      rcases CharP.char_is_prime_or_zero k p with hp' | hp'
      · have hpr : p ∣ r := hp'.dvd_of_dvd_pow h
        exact hrp ((Nat.prime_dvd_prime_iff_eq hp'
          (Fact.out : Nat.Prime r)).mp hpr).symm
      · subst p
        rcases h with ⟨z, hz⟩
        simp at hz
        omega
    exact ⟨isFinite_npow_id E (r ^ m) hm, etale_npow_id p E (r ^ m) hm hnp,
      surjective_npow_id E (r ^ m) hm⟩
  have hlift (z : Q) : ∃ w : Q, w ≫ (𝟙 E ^ r) = z := by
    have : IsFinite (𝟙 E ^ r).left := by simpa using (hcovers 1).1
    have : Etale (𝟙 E ^ r).left := by simpa using (hcovers 1).2.1
    have : Surjective (𝟙 E ^ r).left := by simpa using (hcovers 1).2.2
    obtain ⟨w, hw⟩ := Scheme.Hom.exists_lift_of_isSepClosed (𝟙 E ^ r).left z.left
      ⟨default, (inferInstance : Surjective (𝟙 E ^ r).left).surj _⟩
    refine ⟨Over.homMk w ?_, ?_⟩
    · change w ≫ E.hom = T.hom
      calc
        w ≫ E.hom = w ≫ (𝟙 E ^ r).left ≫ E.hom := by rw [Over.w]
        _ = z.left ≫ E.hom := by rw [← Category.assoc, hw]
        _ = T.hom := Over.w z
    · exact Over.OverMorphism.ext hw
  let lift (z : Q) : Q := Classical.choose (hlift z)
  have hl (z : Q) : lift z ≫ (𝟙 E ^ r) = z := Classical.choose_spec (hlift z)
  let x : ℕ → Q := Nat.rec gen (fun _ z ↦ lift z)
  have hxsucc (m : ℕ) : x (m + 1) ≫ (𝟙 E ^ r) = x m := hl _
  have hx (m : ℕ) : x m ≫ (𝟙 E ^ (r ^ m)) = gen := by
    induction m with
    | zero => simp only [pow_zero, pow_one, Category.comp_id]; rfl
    | succ m hm =>
      rw [pow_succ', ← MonObj.id_pow_comp_id_pow, ← Category.assoc, hxsucc, hm]
  have hax (σ : G) (m : ℕ) : (a σ ≫ x m) ≫ (𝟙 E ^ (r ^ m)) = gen := by
    rw [Category.assoc, hx, hgen]
  let δ (σ : G) (m : ℕ) : P := Function.invFun C ((x m)⁻¹ * (a σ ≫ x m))
  have hδ (σ : G) (m : ℕ) : C (δ σ m) = (x m)⁻¹ * (a σ ≫ x m) := by
    have := (hcovers m).1
    obtain ⟨z, hz, _⟩ := ellipticDivisionDifference k E (r ^ m) (x m) (a σ ≫ x m)
      ((hx m).trans (hax σ m).symm)
    have hzC : C z = (x m)⁻¹ * (a σ ≫ x m) := by
      rw [hz.2]
      change C z = (x m)⁻¹ * (x m * C z)
      group
    change C (Function.invFun C ((x m)⁻¹ * (a σ ≫ x m))) = _
    exact Function.invFun_eq ⟨z, hzC⟩
  have heq (σ : G) (m : ℕ) : a σ ≫ x m = x m * C (δ σ m) := by rw [hδ]; group
  have hδpow (σ : G) (m : ℕ) : δ σ m ^ (r ^ m) = 1 := by
    apply hC
    rw [map_pow, map_one, hδ, mul_pow, inv_pow]
    have h₁ := hx m
    have h₂ := hax σ m
    simp only [comp_pow, Category.comp_id] at h₁ h₂
    rw [h₁, h₂, inv_mul_cancel]
  have hδsucc (σ : G) (m : ℕ) : δ σ (m + 1) ^ r = δ σ m := by
    apply hC
    rw [map_pow, hδ σ m, hδ σ (m + 1)]
    have h : ((x (m + 1))⁻¹ * (a σ ≫ x (m + 1))) ≫ (𝟙 E ^ r) =
        (x m)⁻¹ * (a σ ≫ x m) := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxsucc, Category.assoc, hxsucc]
    simpa only [comp_pow, Category.comp_id] using h
  have hδ1 (m : ℕ) : δ 1 m = 1 := by
    apply hC
    rw [hδ, ha1, Category.id_comp, map_one, inv_mul_cancel]
  have hδmul (σ τ : G) (m : ℕ) : δ (σ * τ) m = δ σ m * δ τ m := by
    apply hC
    rw [map_mul, hδ, hδ, hδ, hamul, Category.assoc, heq τ,
      MonObj.comp_mul, hc, heq σ]
    group
  let ρ : G →* Multiplicative (IsAbelianVariety.tateModule r E) :=
    { toFun σ := Multiplicative.ofAdd ⟨fun m ↦ Additive.ofMul (δ σ m),
        ⟨fun m ↦ by
          change Additive.ofMul (δ σ m ^ (r ^ m)) = 0
          rw [hδpow]; rfl,
        fun m ↦ by
          change Additive.ofMul (δ σ (m + 1) ^ r) = Additive.ofMul (δ σ m)
          rw [hδsucc]⟩⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        funext m
        change Additive.ofMul (δ 1 m) = 0
        rw [hδ1]; rfl
      map_mul' σ τ := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        funext m
        exact congrArg Additive.ofMul (hδmul σ τ m) }
  let : TopologicalSpace P := ⊥
  let : TopologicalSpace Q := ⊥
  have : DiscreteTopology P := ⟨rfl⟩
  have : DiscreteTopology Q := ⟨rfl⟩
  have hδcont (m : ℕ) : Continuous (fun σ : G ↦ δ σ m) := by
    have := (hcovers m).1
    have := (hcovers m).2.1
    have horbit := ellipticDivisionOrbitContinuous k E (r ^ m) (x m) (hx m)
    exact (continuous_of_discreteTopology : Continuous (Function.invFun C)).comp
      (continuous_const.mul horbit)
  have hρ : Continuous ρ := by
    apply continuous_ofAdd.comp
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro m
    exact continuous_ofMul.comp (hδcont m)
  have hρsurj : Function.Surjective ρ := by
    intro t
    let b (m : ℕ) : P := (((t.toAdd : IsAbelianVariety.tateModule r E) :
      ℕ → Additive P) m).toMul
    let S (m : ℕ) : Set G := {σ | δ σ m = b m}
    have hbpow (m : ℕ) : b m ^ (r ^ m) = 1 := by
      have h := AddCommGroup.tateModule.pow_zsmul_coe t.toAdd m
      change Additive.ofMul (b m ^ (r ^ m)) = 0 at h
      exact Additive.ofMul.injective h
    have hbsucc (m : ℕ) : b (m + 1) ^ r = b m := by
      have h := AddCommGroup.tateModule.zsmul_coe_succ t.toAdd m
      change Additive.ofMul (b (m + 1) ^ r) = Additive.ofMul (b m) at h
      exact Additive.ofMul.injective h
    have hSne (m : ℕ) : (S m).Nonempty := by
      have := (hcovers m).1
      have := (hcovers m).2.1
      have := (hcovers m).2.2
      let y : Q := x m * C (b m)
      have hy : y ≫ (𝟙 E ^ (r ^ m)) = gen := by
        change (x m * C (b m)) ≫ (𝟙 E ^ (r ^ m)) = _
        rw [MonObj.mul_comp, hx]
        have hCb : C (b m) ≫ (𝟙 E ^ (r ^ m)) = 1 := by
          rw [comp_pow, Category.comp_id, ← map_pow, hbpow, map_one]
        rw [hCb, _root_.mul_one]
      obtain ⟨σ, hσ⟩ := ellipticDivisionOrbitTransitive k E (r ^ m) (x m) y (hx m) hy
      change a σ ≫ x m = y at hσ
      refine ⟨σ, ?_⟩
      apply hC
      rw [hδ, hσ]
      change (x m)⁻¹ * (x m * C (b m)) = C (b m)
      group
    have hSclosed (m : ℕ) : IsClosed (S m) :=
      isClosed_eq (hδcont m) continuous_const
    obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
      (fun m σ hσ ↦ by
        change δ σ (m + 1) = b (m + 1) at hσ
        change δ σ m = b m
        rw [← hδsucc, hσ, hbsucc]) hSne (hSclosed 0).isCompact hSclosed
    refine ⟨σ, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext m
    exact congrArg Additive.ofMul (Set.mem_iInter.mp hσ m)
  refine ⟨ρ, hρ, hρsurj, x, hx, hxsucc, ?_⟩
  intro σ m
  exact heq σ m


end AlgebraicGeometry
