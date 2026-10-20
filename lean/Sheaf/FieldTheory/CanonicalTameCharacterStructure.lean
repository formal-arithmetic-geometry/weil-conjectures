/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.FieldTheory.TameRootsProduct
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology

public import Mathlib.GroupTheory.Index

import Sheaf.FieldTheory.TameRadicalKernel
import Mathlib.CategoryTheory.CofilteredSystem
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! Kernel and topology of the canonical tame character. -/

@[expose] public section
set_option autoImplicit false
universe u v w z q
namespace IsDiscreteValuationRing

private theorem tame_order_isUnit
    (R : Type u) [CommRing R] [IsLocalRing R]
    (p : ℕ) (hp : p = if ringChar (IsLocalRing.ResidueField R) = 0 then 1
      else ringChar (IsLocalRing.ResidueField R)) (d : TameRoots.Order p) :
    IsUnit (d.1 : R) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [map_natCast]
  change ¬(d.1 : IsLocalRing.ResidueField R) = 0
  rw [ringChar.spec]
  by_cases h : ringChar (IsLocalRing.ResidueField R) = 0
  · simpa [h] using d.2.1.ne'
  · have hp' : p = ringChar (IsLocalRing.ResidueField R) := by simpa [h] using hp
    intro hd
    have : p = 1 := Nat.eq_one_of_dvd_coprimes d.2.2 (hp' ▸ hd) dvd_rfl
    exact CharP.ringChar_ne_one (R := IsLocalRing.ResidueField R) (hp' ▸ this)

private theorem mem_tame_limit {F : Type z} [Field F] {p : ℕ}
    (x : TameRoots.Order p → Fˣ) : x ∈ TameRoots.limitSubgroup F p ↔
      (∀ d, x d ^ d.1 = 1) ∧
      ∀ d e : TameRoots.Order p, d.1 ∣ e.1 → x e ^ (e.1 / d.1) = x d := by
  simp only [TameRoots.limitSubgroup, Subgroup.mem_inf, Subgroup.mem_pi,
    Set.mem_univ, forall_const, Subgroup.mem_iInf, MonoidHom.eqLocus]
  rfl

private theorem compatible_primitive_family (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) (hn : ∀ d : TameRoots.Order p, (d.1 : k) ≠ 0) :
    ∃ ζ : TameRoots.Order p → kˣ, TameRoots.IsCompatiblePrimitiveFamily p ζ := by
  classical
  let : LE (TameRoots.Order p) := ⟨fun m n ↦ m.1 ∣ n.1⟩
  let : LT (TameRoots.Order p) := ⟨fun m n ↦ m.1 ∣ n.1 ∧ ¬n.1 ∣ m.1⟩
  let : Preorder (TameRoots.Order p) := {
    le m n := m.1 ∣ n.1
    le_refl m := dvd_refl m.1
    le_trans _ _ _ := dvd_trans }
  let : IsDirectedOrder (TameRoots.Order p) := ⟨fun m n ↦
    ⟨⟨m.1 * n.1, Nat.mul_pos m.2.1 n.2.1, m.2.2.mul_left n.2.2⟩,
      dvd_mul_right _ _, dvd_mul_left _ _⟩⟩
  let P := fun m : TameRoots.Order p ↦ {z : kˣ // IsPrimitiveRoot z m.1}
  have hfinite : ∀ m, Finite (P m) := by
    intro m
    let : NeZero m.1 := ⟨Nat.ne_of_gt m.2.1⟩
    exact Finite.of_injective
      (fun z : P m ↦ (⟨z.1, z.2.pow_eq_one⟩ : rootsOfUnity m.1 k))
      (fun _ _ h ↦ Subtype.ext (congrArg (fun w : rootsOfUnity m.1 k ↦ (w : kˣ)) h))
  have hnonempty : ∀ m, Nonempty (P m) := by
    intro m
    have : NeZero (m.1 : k) := ⟨hn m⟩
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k m.1
    exact ⟨⟨Units.mk0 z (hz.ne_zero m.2.1.ne'), IsPrimitiveRoot.coe_units_iff.mp hz⟩⟩
  let F : CategoryTheory.Functor (TameRoots.Order p)ᵒᵖ (Type u) :=
    { obj := fun m ↦ P m.unop
      map := fun {m n} f ↦ TypeCat.ofHom fun z ↦
        ⟨z.1 ^ (m.unop.1 / n.unop.1),
          z.2.pow m.unop.2.1 ((Nat.div_mul_cancel (CategoryTheory.leOfHom f.unop)).symm)⟩
      map_id := by
        intro m
        ext z
        simp [Nat.div_self m.unop.2.1]
      map_comp := by
        intro a b c f g
        ext z
        dsimp
        rw [← pow_mul]
        congr 1
        apply Nat.eq_of_mul_eq_mul_right c.unop.2.1
        rw [Nat.mul_assoc, Nat.div_mul_cancel (CategoryTheory.leOfHom g.unop),
          Nat.div_mul_cancel (CategoryTheory.leOfHom f.unop),
          Nat.div_mul_cancel
            (dvd_trans (CategoryTheory.leOfHom g.unop) (CategoryTheory.leOfHom f.unop))] }
  let : ∀ m, Finite (F.obj m) := fun m ↦ hfinite m.unop
  let : ∀ m, Nonempty (F.obj m) := fun m ↦ hnonempty m.unop
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun m ↦ (s (.op m)).1, (fun m ↦ (s (.op m)).2), ?_, ?_⟩
  · intro m hm
    have h := (s (.op m)).2.pow_eq_one
    simpa [hm] using h
  · intro m n h
    exact congrArg Subtype.val (hs (CategoryTheory.homOfLE h).op)


open scoped Topology in
private theorem tame_limit_nhds_basis {F : Type z} [Field F] (p : ℕ)
    (x : TameRoots.limitSubgroup F p) :
    @Filter.HasBasis _ (TameRoots.Order p)
      (@nhds _ (TameRoots.limitTopology F p) x)
      (fun _ ↦ True) (fun d ↦ {y | y.1 d = x.1 d}) := by
  classical
  let : TopologicalSpace Fˣ := ⊥
  let : DiscreteTopology Fˣ := ⟨rfl⟩
  rw [TameRoots.limitTopology, nhds_iInf]
  simp_rw [nhds_induced, nhds_discrete, Filter.comap_pure]
  let : Nonempty (TameRoots.Order p) := ⟨⟨1, by simp⟩⟩
  apply Filter.hasBasis_iInf_principal
  intro d e
  let f : TameRoots.Order p :=
    ⟨d.1 * e.1, Nat.mul_pos d.2.1 e.2.1, d.2.2.mul_left e.2.2⟩
  refine ⟨f, ?_, ?_⟩
  · intro y hy
    exact (((mem_tame_limit y.1).mp y.2).2 d f (dvd_mul_right _ _)).symm.trans
      ((congrArg (fun z : Fˣ ↦ z ^ (f.1 / d.1)) hy).trans
        (((mem_tame_limit x.1).mp x.2).2 d f (dvd_mul_right _ _)))
  · intro y hy
    exact (((mem_tame_limit y.1).mp y.2).2 e f (dvd_mul_left _ _)).symm.trans
      ((congrArg (fun z : Fˣ ↦ z ^ (f.1 / e.1)) hy).trans
        (((mem_tame_limit x.1).mp x.2).2 e f (dvd_mul_left _ _)))

private theorem tame_primitive_dense {F : Type z} [Field F] (p : ℕ)
    (σ : TameRoots.limitSubgroup F p)
    (hσ : TameRoots.IsCompatiblePrimitiveFamily p σ.1) :
    @DenseRange _ (TameRoots.limitTopology F p) ℤ (fun n : ℤ ↦ σ ^ n) := by
  let : TopologicalSpace (TameRoots.limitSubgroup F p) := TameRoots.limitTopology F p
  intro x
  apply (mem_closure_iff_nhds_basis (tame_limit_nhds_basis p x)).mpr
  intro d _
  let : NeZero d.1 := ⟨d.2.1.ne'⟩
  obtain ⟨n, _, hn⟩ := (hσ.1 d).eq_pow_of_mem_rootsOfUnity
    (((mem_tame_limit x.1).mp x.2).1 d)
  refine ⟨σ ^ (n : ℤ), ⟨n, rfl⟩, ?_⟩
  change σ.1 d ^ (n : ℤ) = x.1 d
  simpa using hn

private def tame_coordinate {F : Type z} [Field F] {p : ℕ}
    (d : TameRoots.Order p) : TameRoots.limitSubgroup F p →* rootsOfUnity d.1 F where
  toFun x := ⟨x.1 d, ((mem_tame_limit x.1).mp x.2).1 d⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem tame_power_closure {F : Type z} [Field F] (p : ℕ)
    (σ : TameRoots.limitSubgroup F p)
    (hσ : TameRoots.IsCompatiblePrimitiveFamily p σ.1) (d : TameRoots.Order p) :
    ∃ U : Subgroup (TameRoots.limitSubgroup F p),
      (U : Set (TameRoots.limitSubgroup F p)) =
        @closure _ (TameRoots.limitTopology F p)
          (Set.range (fun n : ℤ ↦ (σ ^ d.1) ^ n)) ∧ U.index = d.1 := by
  classical
  let : TopologicalSpace Fˣ := ⊥
  let : DiscreteTopology Fˣ := ⟨rfl⟩
  let : TopologicalSpace (TameRoots.limitSubgroup F p) := TameRoots.limitTopology F p
  let : NeZero d.1 := ⟨d.2.1.ne'⟩
  let U := (tame_coordinate (F := F) d).ker
  have hu : IsClosed (U : Set (TameRoots.limitSubgroup F p)) := by
    have hc : Continuous (fun x : TameRoots.limitSubgroup F p ↦ x.1 d) :=
      continuous_iInf_dom continuous_induced_dom
    have heq : (U : Set (TameRoots.limitSubgroup F p)) = {x | x.1 d = 1} := by
      ext x
      exact Subtype.ext_iff
    rw [heq]
    exact isClosed_singleton.preimage hc
  refine ⟨U, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      apply (mem_closure_iff_nhds_basis (tame_limit_nhds_basis p x)).mpr
      intro e _
      let f : TameRoots.Order p :=
        ⟨d.1 * e.1, Nat.mul_pos d.2.1 e.2.1, d.2.2.mul_left e.2.2⟩
      let : NeZero f.1 := ⟨f.2.1.ne'⟩
      obtain ⟨a, _, ha⟩ := (hσ.1 f).eq_pow_of_mem_rootsOfUnity
        (((mem_tame_limit x.1).mp x.2).1 f)
      have hda : d.1 ∣ a := by
        apply ((hσ.1 d).pow_eq_one_iff_dvd a).mp
        calc
          σ.1 d ^ a = (σ.1 f ^ a) ^ (f.1 / d.1) := by
            rw [pow_right_comm, hσ.2.2 d f (dvd_mul_right _ _)]
          _ = x.1 d := by
            rw [ha, ((mem_tame_limit x.1).mp x.2).2 d f (dvd_mul_right _ _)]
          _ = 1 := congrArg Subtype.val hx
      refine ⟨(σ ^ d.1) ^ (a / d.1),
        ⟨((a / d.1 : ℕ) : ℤ), zpow_natCast _ _⟩, ?_⟩
      change (σ.1 e ^ d.1) ^ (a / d.1) = x.1 e
      rw [← pow_mul, Nat.mul_div_cancel' hda]
      calc
        σ.1 e ^ a = (σ.1 f ^ a) ^ (f.1 / e.1) := by
          rw [pow_right_comm, hσ.2.2 e f (dvd_mul_left _ _)]
        _ = x.1 e := by
          rw [ha, ((mem_tame_limit x.1).mp x.2).2 e f (dvd_mul_left _ _)]
    · apply closure_minimal _ hu
      rintro _ ⟨n, rfl⟩
      apply Subtype.ext
      change (σ.1 d ^ d.1) ^ n = 1
      rw [(hσ.1 d).pow_eq_one, one_zpow]
  · have hsurj : Function.Surjective (tame_coordinate (F := F) d) := by
      intro x
      obtain ⟨a, _, ha⟩ := (hσ.1 d).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).mp x.2)
      exact ⟨σ ^ a, Subtype.ext ha⟩
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
      Nat.card_congr
        (Subgroup.topEquiv : (⊤ : Subgroup (rootsOfUnity d.1 F)) ≃* rootsOfUnity d.1 F).toEquiv]
    exact (hσ.1 d).card_rootsOfUnity'

/-- Consequences of the canonical character construction: the pro-p kernel, the
characteristic-zero kernel, and the primitive-family topological conclusions.

Proof: Choose one uniformizer and a compatible radical family. Each radical is nonzero.
The character formula and injectivity of Ksep → Ω identify t.ker with the intersection
of the stabilizers of these radicals. The radical-kernel theorem supplies its finite
quotient and characteristic-zero assertions. For the target, the finite primitive-root
sets are nonempty since every tame order is invertible in Ω; finite inverse-system
compactness supplies a compatible primitive family. Coordinate fibers form a neighborhood
basis, because a product order dominates any two orders. At each coordinate, every root
is a power of the primitive root, giving density of integer powers. The closure of the
d-th powers is the kernel of the d-coordinate: one inclusion uses closedness, and the
other solves a finite congruence at the product of d and any requested coordinate. The
surjective coordinate homomorphism has cyclic image of order d, giving index d.
(blueprint: lem-per-trait-tame-character-structure). -/
theorem canonical_tame_character_structure
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ksep : Type w) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (Ω : Type z) [Field Ω] [IsAlgClosed Ω] [Algebra Ksep Ω]
    (p : ℕ) (hp : p = if ringChar (IsLocalRing.ResidueField R) = 0 then 1
      else ringChar (IsLocalRing.ResidueField R))
    (t : Gal(Ksep/K) →* TameRoots.limitSubgroup Ω p)
    (_ht : @Continuous _ _ inferInstance (TameRoots.limitTopology Ω p) t)
    (_hs : Function.Surjective t)
    (ha : ∀ π : R, Irreducible π →
      ∃ α : TameRoots.Order p → Ksep,
        (∀ d : TameRoots.Order p,
          α d ^ d.1 = algebraMap K Ksep (algebraMap R K π)) ∧
        ∀ d e : TameRoots.Order p, d.1 ∣ e.1 → α e ^ (e.1 / d.1) = α d)
    (hf : ∀ (π : R), Irreducible π → ∀ α : TameRoots.Order p → Ksep,
      (∀ d : TameRoots.Order p,
        α d ^ d.1 = algebraMap K Ksep (algebraMap R K π)) →
      (∀ d e : TameRoots.Order p, d.1 ∣ e.1 → α e ^ (e.1 / d.1) = α d) →
      ∀ (h : Gal(Ksep/K)) (d : TameRoots.Order p),
        (((t h).1 d : Ωˣ) : Ω) = algebraMap Ksep Ω (h (α d) / α d)) :
    (∀ (Q : Type q) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
      [Finite Q] (f : t.ker →* Q), Continuous f → Function.Surjective f →
        ∃ n : ℕ, Nat.card Q = p ^ n) ∧
    (p = 1 → t.ker = ⊥) ∧
    (∃ σ : TameRoots.limitSubgroup Ω p,
      TameRoots.IsCompatiblePrimitiveFamily p σ.1) ∧
    ∀ σ : TameRoots.limitSubgroup Ω p,
      TameRoots.IsCompatiblePrimitiveFamily p σ.1 →
      @DenseRange (TameRoots.limitSubgroup Ω p) (TameRoots.limitTopology Ω p) ℤ
        (fun n : ℤ ↦ σ ^ n) ∧
      ∀ d : TameRoots.Order p,
        ∃ U : Subgroup (TameRoots.limitSubgroup Ω p),
          (U : Set (TameRoots.limitSubgroup Ω p)) =
            @closure _ (TameRoots.limitTopology Ω p)
              (Set.range (fun n : ℤ ↦ (σ ^ d.1) ^ n)) ∧
          U.index = d.1 := by
  classical
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨α, hα, hαc⟩ := ha π hπ
  have hne (d : TameRoots.Order p) : α d ≠ 0 := by
    have hπne : algebraMap K Ksep (algebraMap R K π) ≠ 0 := by
      intro h
      apply hπ.ne_zero
      apply IsFractionRing.injective R K
      apply (algebraMap K Ksep).injective
      simpa only [map_zero] using h
    intro hz
    apply hπne
    rw [← hα d, hz, zero_pow d.2.1.ne']
  have hker : t.ker = tameRadicalKernel (K := K) α := by
    ext h
    rw [MonoidHom.mem_ker]
    simp only [tameRadicalKernel, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
    constructor
    · intro hh d
      have heq := hf π hπ α hα hαc h d
      have hh' : (((t h).1 d : Ωˣ) : Ω) = 1 := by rw [hh]; rfl
      rw [hh'] at heq
      have heq' : h (α d) / α d = 1 :=
        (algebraMap Ksep Ω).injective (heq.symm.trans (map_one _).symm)
      exact (div_eq_one_iff_eq (hne d)).mp heq'
    · intro hh
      apply Subtype.ext
      funext d
      apply Units.ext
      change (((t h).1 d : Ωˣ) : Ω) = 1
      rw [hf π hπ α hα hαc h d]
      rw [show h (α d) = α d from hh d, div_self (hne d), map_one]
  obtain ⟨hq, hc⟩ := tame_radical_kernel_pro_p R K Ksep p hp π hπ α hα hαc
  have hn (d : TameRoots.Order p) : (d.1 : Ω) ≠ 0 := by
    have hu := (tame_order_isUnit R p hp d).map
      ((algebraMap Ksep Ω).comp ((algebraMap K Ksep).comp (algebraMap R K)))
    simpa only [RingHom.coe_comp, Function.comp_apply, map_natCast] using hu.ne_zero
  obtain ⟨ζ, hζ⟩ := compatible_primitive_family Ω p hn
  have hzmem : ζ ∈ TameRoots.limitSubgroup Ω p :=
    (mem_tame_limit ζ).mpr ⟨fun d ↦ (hζ.1 d).pow_eq_one, hζ.2.2⟩
  refine ⟨?_, ?_, ⟨⟨ζ, hzmem⟩, hζ⟩, ?_⟩
  · rw [hker]
    exact hq
  · rw [hker]
    exact hc
  · intro σ hσ
    exact ⟨tame_primitive_dense p σ hσ, tame_power_closure p σ hσ⟩

end IsDiscreteValuationRing
