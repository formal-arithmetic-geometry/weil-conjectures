/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module
public import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Separation.Profinite
/-!
# The prime-to-ell kernel of a tame coordinate

Source: blueprint main-20261015, `lem-exc-dvr-galois.proof.md`, second paragraph;
DAG proof step 2 of `lem-exc-dvr-galois`.
(blueprint: lem-exc-tame-ell-coordinate)
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open Function

namespace ProfiniteGroup

private theorem coprime_card_of_pow_surjective
    (l : ℕ) [Fact l.Prime] (Q : Type u) [Group Q] [Finite Q]
    (hpow : Surjective (fun x : Q ↦ x ^ l)) : Nat.Coprime l (Nat.card Q) := by
  rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hdvd
  have hinj := (Finite.injective_iff_surjective).mpr hpow
  have hxeq : x = 1 := hinj (by simp [← hx])
  rw [hxeq, orderOf_one] at hx
  exact (Fact.out : l.Prime).ne_one hx.symm

private theorem coprime_card_finite_quotient_of_divisible
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (B : Type v) [Group B] (θ : H →* B) (hθ : Surjective θ)
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hlp : l ≠ p)
    (hdiv : Surjective (fun x : B ↦ x ^ l))
    (hwild : ∀ (T : Type w) [Group T] [TopologicalSpace T] [DiscreteTopology T]
      [Finite T] (f : θ.ker →* T), Continuous f → Surjective f →
        ∃ n : ℕ, Nat.card T = p ^ n)
    (Q : Type w) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (f : H →* Q) (hfcont : Continuous f) (hf : Surjective f) :
    Nat.Coprime l (Nat.card Q) := by
  let D := θ.ker.map f
  have : D.Normal := (inferInstance : θ.ker.Normal).map f hf
  let η : θ.ker →* D := (f.comp θ.ker.subtype).codRestrict D
    (fun x ↦ ⟨x.val, x.property, rfl⟩)
  have hη : Surjective η := by
    intro x
    obtain ⟨y, hy, hxy⟩ := x.property
    exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
  obtain ⟨n, hn⟩ := hwild D η
    ((hfcont.comp continuous_subtype_val).subtype_mk _) hη
  let π := (QuotientGroup.mk' D).comp f
  have hker : θ.ker ≤ π.ker := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨x, hx, rfl⟩
  let ψ := θ.liftOfSurjective hθ ⟨π, hker⟩
  have hψθ (x : H) : ψ (θ x) = π x :=
    θ.liftOfRightInverse_comp_apply _ _ _ x
  have hψ : Surjective ψ := by
    intro q
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective D q
    obtain ⟨x, hx⟩ := hf y
    exact ⟨θ x, by rw [hψθ]; change (QuotientGroup.mk' D) (f x) = q; rw [hx, hy]⟩
  have hquot : Nat.Coprime l (Nat.card (Q ⧸ D)) := by
    apply coprime_card_of_pow_surjective
    intro q
    obtain ⟨b, hb⟩ := hψ q
    obtain ⟨a, ha⟩ := hdiv b
    change a ^ l = b at ha
    exact ⟨ψ a, by change ψ a ^ l = q; rw [← map_pow, ha, hb]⟩
  rw [← D.card_mul_index, hn]
  exact ((Nat.coprime_primes (Fact.out : l.Prime)
    (Fact.out : p.Prime)).mpr hlp).pow_right n |>.mul_right hquot

def tameCoordinate (p l : ℕ) [Fact l.Prime] (hlp : l ≠ p) :
    Multiplicative (∀ r : {r : Nat.Primes // (r : ℕ) ≠ p},
      @PadicInt r.1 (Fact.mk r.1.2)) →* Multiplicative ℤ_[l] where
  toFun x := Multiplicative.ofAdd (x.toAdd ⟨⟨l, Fact.out⟩, hlp⟩)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem tameCoordinate_continuous (p l : ℕ) [Fact l.Prime] (hlp : l ≠ p) :
    Continuous (tameCoordinate p l hlp) := by
  exact (continuous_apply (A := fun r : {r : Nat.Primes // (r : ℕ) ≠ p} ↦
    @PadicInt r.1 (Fact.mk r.1.2)) ⟨⟨l, Fact.out⟩, hlp⟩)

theorem tameCoordinate_surjective (p l : ℕ) [Fact l.Prime] (hlp : l ≠ p) :
    Surjective (tameCoordinate p l hlp) := by
  intro x
  refine ⟨Multiplicative.ofAdd (fun r ↦ if h : (r : ℕ) = l then ?_ else 0), ?_⟩
  · exact h ▸ x.toAdd
  · simp [tameCoordinate]

private theorem tameCoordinate_kernel_divisible (p l : ℕ) [Fact l.Prime]
    (hlp : l ≠ p) :
    Surjective (fun x : (tameCoordinate p l hlp).ker ↦ x ^ l) := by
  classical
  intro x
  have hxl : x.val.toAdd ⟨⟨l, Fact.out⟩, hlp⟩ = 0 := by
    exact congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp x.property)
  have hunit (r : {r : Nat.Primes // (r : ℕ) ≠ p}) (h : (r : ℕ) ≠ l) :
      IsUnit (l : @PadicInt r.1 (Fact.mk r.1.2)) := by
    let : Fact (r.1 : ℕ).Prime := ⟨r.1.2⟩
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes r.1.2 (Fact.out : l.Prime)).mpr h
  let y : Multiplicative (∀ r : {r : Nat.Primes // (r : ℕ) ≠ p},
      @PadicInt r.1 (Fact.mk r.1.2)) := Multiplicative.ofAdd
    (fun r ↦ if h : (r : ℕ) = l then 0 else ↑(hunit r h).unit⁻¹ * x.val.toAdd r)
  have hy : y ∈ (tameCoordinate p l hlp).ker := by
    change Multiplicative.ofAdd (y.toAdd ⟨⟨l, Fact.out⟩, hlp⟩) = 1
    simp [y]
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  apply Multiplicative.toAdd.injective
  funext r
  change l • y.toAdd r = x.val.toAdd r
  by_cases hr : (r : ℕ) = l
  · have hre : r = ⟨⟨l, Fact.out⟩, hlp⟩ := by
      apply Subtype.ext; apply Subtype.ext; exact hr
    subst r
    simp [y, hxl]
  · simp only [y, toAdd_ofAdd, dif_neg hr, nsmul_eq_mul]
    have hi : (l : @PadicInt r.1 (Fact.mk r.1.2)) * ↑(hunit r hr).unit⁻¹ = 1 := by
      have hu : (↑(hunit r hr).unit : @PadicInt r.1 (Fact.mk r.1.2)) *
          ↑(hunit r hr).unit⁻¹ = 1 := by simp
      simpa only [(hunit r hr).unit_spec] using hu
    rw [← mul_assoc, hi, one_mul]

/-- Every finite continuous quotient of the inverse image of the other tame coordinates
has order prime to `l`.

Proof: multiplication by `l` is invertible on every `r`-adic factor for `r ≠ l`.
For a finite quotient Q of the coordinate kernel, let D be the image of the wild kernel.
The group D has p-power order. The quotient Q/D is a quotient of the other tame factors,
so its l-th power map is surjective. On a finite group it is then injective; Cauchy's
theorem excludes an element of order l. Thus both D and Q/D have order prime to l,
and the cardinality formula gives the assertion for Q.

Source: blueprint main-20261015, `lem-exc-dvr-galois.proof.md`, second paragraph;
DAG proof step 2 of `lem-exc-dvr-galois`.
(blueprint: lem-exc-tame-ell-coordinate) -/
theorem tameCoordinate_finite_quotients
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hlp : l ≠ p)
    (θ : G →* Multiplicative (∀ r : {r : Nat.Primes // (r : ℕ) ≠ p},
      @PadicInt r.1 (Fact.mk r.1.2))) (hθ : Surjective θ)
    (hwild : ∀ (Q : Type w) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
      [Finite Q] (f : θ.ker →* Q), Continuous f → Surjective f →
        ∃ n : ℕ, Nat.card Q = p ^ n) :
    let π := (tameCoordinate p l hlp).comp θ
    ∀ (Q : Type w) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
      (f : π.ker →* Q), Continuous f → Surjective f → Nat.Coprime l (Nat.card Q) := by
  dsimp only
  let c := tameCoordinate p l hlp
  let π := c.comp θ
  let δ : π.ker →* c.ker := (θ.comp π.ker.subtype).codRestrict c.ker
    (fun x ↦ x.property)
  have hδ : Surjective δ := by
    intro x
    obtain ⟨g, hg⟩ := hθ x.val
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    change c (θ g) = 1
    rw [hg]
    exact x.property
  let j : δ.ker →* θ.ker :=
    { toFun := fun x ↦ ⟨x.val.val, by
        have hx := congrArg Subtype.val (MonoidHom.mem_ker.mp x.property)
        exact hx⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let e : δ.ker ≃* θ.ker :=
    { j with
      invFun := fun x ↦ ⟨⟨x.val, by
        change c (θ x.val) = 1
        rw [MonoidHom.mem_ker.mp x.property, map_one]⟩, by
          apply Subtype.ext
          exact x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hecont : Continuous e.symm := by
    apply continuous_induced_rng.mpr
    apply continuous_induced_rng.mpr
    change Continuous (fun x : θ.ker ↦ x.val)
    exact continuous_subtype_val
  intro Q _ _ _ _ f hfcont hf
  apply coprime_card_finite_quotient_of_divisible π.ker c.ker δ hδ p l hlp
    (tameCoordinate_kernel_divisible p l hlp) ?_ Q f hfcont hf
  intro T _ _ _ _ a hac ha
  exact hwild T (a.comp e.symm.toMonoidHom) (hac.comp hecont)
    (ha.comp e.symm.surjective)

end ProfiniteGroup
