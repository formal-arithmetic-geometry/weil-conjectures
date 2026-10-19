/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.CategoryTheory.CofilteredSystem
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms

/-!
# Compatible tame roots and the product of adic integers

Source: Stacks Project, fields.tex Tag 09HW, algebra.tex Tags 00DT and 00M9;
blueprint main-20261015, proof of `lem-exc-dvr-galois`, second paragraph
(blueprint: lem-exc-tame-roots-product).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace TameRoots

/-- The positive orders prime to `p`, ordered by divisibility in the compatibility equations.
Source: Stacks Project, Tag 09HW; blueprint proof of `lem-exc-dvr-galois`, tame quotient
(blueprint: lem-exc-tame-roots-product). -/
abbrev Order (p : ℕ) := {m : ℕ // 0 < m ∧ m.Coprime p}

/-- The prime-to-`p` root limit, as the subgroup of unit-valued families satisfying the root
equations and all power-transition equations. The defining subgroups are Mathlib's actual
`rootsOfUnity`, not a replacement notion of a root group.
Source: Stacks Project, Tag 09HW, and blueprint proof of `lem-exc-dvr-galois`, tame quotient
(blueprint: lem-exc-tame-roots-product). -/
def limitSubgroup (k : Type u) [Field k] (p : ℕ) : Subgroup (Order p → kˣ) :=
  Subgroup.pi Set.univ (fun m : Order p ↦ rootsOfUnity m.1 k) ⊓
    ⨅ (m : Order p) (n : Order p) (_ : m.1 ∣ n.1),
      ((powMonoidHom (n.1 / m.1)).comp (Pi.evalMonoidHom (fun _ : Order p ↦ kˣ) n)).eqLocus
        (Pi.evalMonoidHom (fun _ : Order p ↦ kˣ) m)

/-- The inverse-limit topology: the coarsest topology making each coordinate continuous
into the discrete unit group. Restricting each coordinate to `rootsOfUnity` gives precisely
the usual subspace topology in the product of discrete root groups.
Source: Stacks Project, Tag 00M9, and blueprint proof of `lem-exc-dvr-galois`, tame quotient
(blueprint: lem-exc-tame-roots-product). -/
@[instance_reducible]
def limitTopology (k : Type u) [Field k] (p : ℕ) : TopologicalSpace (limitSubgroup k p) :=
  ⨅ m : Order p, TopologicalSpace.induced (fun x : limitSubgroup k p ↦ x.1 m) ⊥

/-- A primitive root at every positive prime-to-`p` order, normalized at order one and
compatible with every divisibility power map.
Source: Stacks Project, Tag 09HW, and blueprint proof of `lem-exc-dvr-galois`, tame quotient
(blueprint: lem-exc-tame-roots-product). -/
def IsCompatiblePrimitiveFamily {k : Type u} [Field k] (p : ℕ) (ζ : Order p → kˣ) : Prop :=
  (∀ m : Order p, IsPrimitiveRoot (ζ m) m.1) ∧
    (∀ m : Order p, m.1 = 1 → ζ m = 1) ∧
    ∀ m n : Order p, m.1 ∣ n.1 → ζ n ^ (n.1 / m.1) = ζ m

/-- The product of the additive valuation rings at all primes different from `p`.
`Multiplicative` only changes notation for the group law and retains the product topology.
Source: blueprint proof of `lem-exc-dvr-galois`, displayed tame quotient; Stacks Tag 00M9
(blueprint: lem-exc-tame-roots-product). -/
abbrev AdicProduct (p : ℕ) :=
  Multiplicative (∀ r : {r : Nat.Primes // (r : ℕ) ≠ p},
    @PadicInt r.1 (Fact.mk r.1.2))


/-- Compatible primitive roots exist by finite inverse-system compactness. At order `m`,
the primitive roots form a finite nonempty set. Divisibility gives power transition maps,
whose identities and composition follow from cancellation of positive integer quotients.
The orders are directed by multiplication, so Mathlib supplies a compatible section.
At order one its root equation forces the value one.
Source: Stacks Project, fields.tex Tag 09HW; Mathlib.CategoryTheory.CofilteredSystem.
(blueprint: lem-exc-tame-roots-product). -/
private theorem compatible_roots_product_exists (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ ζ : Order p → kˣ, IsCompatiblePrimitiveFamily p ζ := by
  classical
  let : LE (Order p) := ⟨fun m n ↦ m.1 ∣ n.1⟩
  let : LT (Order p) := ⟨fun m n ↦ m.1 ∣ n.1 ∧ ¬n.1 ∣ m.1⟩
  let : Preorder (Order p) := {
    le m n := m.1 ∣ n.1
    le_refl m := dvd_refl m.1
    le_trans _ _ _ := dvd_trans }
  let : IsDirectedOrder (Order p) := ⟨fun m n ↦
    ⟨⟨m.1 * n.1, Nat.mul_pos m.2.1 n.2.1, m.2.2.mul_left n.2.2⟩,
      dvd_mul_right _ _, dvd_mul_left _ _⟩⟩
  let P := fun m : Order p ↦ {z : kˣ // IsPrimitiveRoot z m.1}
  have hfinite : ∀ m, Finite (P m) := by
    intro m
    let : NeZero m.1 := ⟨Nat.ne_of_gt m.2.1⟩
    exact Finite.of_injective
      (fun z : P m ↦ (⟨z.1, z.2.pow_eq_one⟩ : rootsOfUnity m.1 k))
      (fun _ _ h ↦ Subtype.ext (congrArg (fun w : rootsOfUnity m.1 k ↦ (w : kˣ)) h))
  have hnonempty : ∀ m, Nonempty (P m) := by
    intro m
    have : NeZero (m.1 : k) := NeZero.of_not_dvd k
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp m.2.2.symm)
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k m.1
    exact ⟨⟨Units.mk0 z (hz.ne_zero m.2.1.ne'), IsPrimitiveRoot.coe_units_iff.mp hz⟩⟩
  let F : CategoryTheory.Functor (Order p)ᵒᵖ (Type u) :=
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


private abbrev Away (p : ℕ) := {r : Nat.Primes // (r : ℕ) ≠ p}

private abbrev Adics (p : ℕ) :=
  ∀ r : Away p, @PadicInt r.1 (Fact.mk r.1.2)

private def residues (p : ℕ) : Subring (∀ m : Order p, ZMod m.1) where
  carrier := {x | ∀ (m n : Order p) (h : m.1 ∣ n.1),
    ZMod.castHom h (ZMod m.1) (x n) = x m}
  zero_mem' := by simp
  one_mem' := by
    intro m n h
    exact map_one (ZMod.castHom h (ZMod m.1))
  add_mem' := by
    intro x y hx hy m n h
    change ZMod.castHom h (ZMod m.1) (x n + y n) = x m + y m
    rw [map_add, hx m n h, hy m n h]
  neg_mem' := by
    intro x hx m n h
    change ZMod.castHom h (ZMod m.1) (-x n) = -x m
    rw [map_neg, hx m n h]
  mul_mem' := by
    intro x y hx hy m n h
    change ZMod.castHom h (ZMod m.1) (x n * y n) = x m * y m
    rw [map_mul, hx m n h, hy m n h]

private lemma cast_cast {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) (x : ZMod c) :
    ZMod.castHom hab (ZMod a) (ZMod.castHom hbc (ZMod b) x) =
      ZMod.castHom (dvd_trans hab hbc) (ZMod a) x := by
  exact RingHom.congr_fun (ZMod.castHom_comp hab hbc) x

private def factorIndex {p : ℕ} [Fact p.Prime] (m : Order p)
    (q : m.1.primeFactors) : Away p :=
  ⟨⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩, by
    intro h
    have hnd := (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp m.2.2.symm
    apply hnd
    simpa only [← h] using Nat.dvd_of_mem_primeFactors q.2⟩

private noncomputable def crtMap {p : ℕ} [Fact p.Prime] (m : Order p) :
    Adics p →+* ZMod m.1 :=
  (ZMod.equivPi m.1 m.2.1.ne').symm.toRingHom.comp
    (RingHom.pi fun q : m.1.primeFactors ↦
      (@PadicInt.toZModPow q.1 (Fact.mk (Nat.prime_of_mem_primeFactors q.2))
        (m.1.factorization q.1)).comp (Pi.evalRingHom _ (factorIndex m q)))

private lemma crt_factor {p : ℕ} [Fact p.Prime] (m : Order p) (x : Adics p)
    (q : m.1.primeFactors) :
    ZMod.castHom (Nat.ordProj_dvd m.1 q.1) (ZMod (q.1 ^ m.1.factorization q.1))
      (crtMap m x) =
        @PadicInt.toZModPow q.1 (Fact.mk (Nat.prime_of_mem_primeFactors q.2))
          (m.1.factorization q.1) (x (factorIndex m q)) := by
  have he : (Pi.evalRingHom _ q).comp (ZMod.equivPi m.1 m.2.1.ne').toRingHom =
      ZMod.castHom (Nat.ordProj_dvd m.1 q.1) (ZMod (q.1 ^ m.1.factorization q.1)) :=
    Subsingleton.elim _ _
  rw [← he]
  exact congrFun ((ZMod.equivPi m.1 m.2.1.ne').apply_symm_apply _) q

private lemma crt_spec {p : ℕ} [Fact p.Prime] (m : Order p) (x : Adics p)
    (r : Away p) (a : ℕ) (h : (r : ℕ) ^ a ∣ m.1) :
    ZMod.castHom h (ZMod ((r : ℕ) ^ a)) (crtMap m x) =
      @PadicInt.toZModPow r.1 (Fact.mk r.1.2) a (x r) := by
  let : Fact (r.1.1.Prime) := ⟨r.1.2⟩
  by_cases ha : a = 0
  · subst a
    change (ZMod.castHom h (ZMod 1)) (crtMap m x) = _
    exact Subsingleton.elim _ _
  have hr : (r : ℕ) ∣ m.1 := dvd_trans (dvd_pow_self _ ha) h
  let q : m.1.primeFactors := ⟨r, Nat.mem_primeFactors.mpr ⟨r.1.2, hr, m.2.1.ne'⟩⟩
  have hab : a ≤ m.1.factorization (r : ℕ) :=
    (r.1.2.pow_dvd_iff_le_factorization m.2.1.ne').mp h
  have hind : factorIndex m q = r := by rfl
  calc
    _ = ZMod.castHom (pow_dvd_pow (r : ℕ) hab) _
        (ZMod.castHom (Nat.ordProj_dvd m.1 q.1) _ (crtMap m x)) :=
      (cast_cast _ _ _).symm
    _ = _ := by
      rw [crt_factor m x q]
      change ZMod.castHom (pow_dvd_pow (r : ℕ) hab) _
        (@PadicInt.toZModPow r.1 (Fact.mk r.1.2) _ (x r)) = _
      exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow a _ hab) (x r)

private lemma crt_compat {p : ℕ} [Fact p.Prime] (m n : Order p) (h : m.1 ∣ n.1)
    (x : Adics p) : ZMod.castHom h (ZMod m.1) (crtMap n x) = crtMap m x := by
  apply (ZMod.equivPi m.1 m.2.1.ne').injective
  funext q
  have he (z : ZMod m.1) : ZMod.equivPi m.1 m.2.1.ne' z q =
      ZMod.castHom (Nat.ordProj_dvd m.1 q.1) _ z :=
    RingHom.congr_fun
      (Subsingleton.elim ((Pi.evalRingHom _ q).comp
        (ZMod.equivPi m.1 m.2.1.ne').toRingHom)
        (ZMod.castHom (Nat.ordProj_dvd m.1 q.1) _)) z
  rw [he, he, cast_cast, crt_factor]
  exact crt_spec n x (factorIndex m q) (m.1.factorization q.1)
    (dvd_trans (Nat.ordProj_dvd m.1 q.1) h)

private noncomputable def reconstruct (p : ℕ) [Fact p.Prime] : Adics p →+* residues p where
  toFun x := ⟨fun m ↦ crtMap m x, fun m n h ↦ crt_compat m n h x⟩
  map_one' := Subtype.ext (funext fun m ↦ map_one (crtMap m))
  map_zero' := Subtype.ext (funext fun m ↦ map_zero (crtMap m))
  map_add' x y := Subtype.ext (funext fun m ↦ map_add (crtMap m) x y)
  map_mul' x y := Subtype.ext (funext fun m ↦ map_mul (crtMap m) x y)

private def powerOrder {p : ℕ} [Fact p.Prime] (r : Away p) (a : ℕ) : Order p :=
  ⟨(r : ℕ) ^ a, pow_pos r.1.2.pos _,
    (r.1.2.coprime_iff_not_dvd.mpr fun h ↦ r.2
      ((Nat.prime_dvd_prime_iff_eq r.1.2 (Fact.out : p.Prime)).mp h)).pow_left _⟩

private def primeResidue {p : ℕ} [Fact p.Prime] (r : Away p) (a : ℕ) :
    residues p →+* ZMod ((r : ℕ) ^ a) :=
  (Pi.evalRingHom _ (powerOrder r a)).comp (residues p).subtype

private lemma primeResidue_compat {p : ℕ} [Fact p.Prime] (r : Away p)
    (a b : ℕ) (h : a ≤ b) :
    (ZMod.castHom (pow_dvd_pow (r : ℕ) h) _).comp (primeResidue r b) =
      primeResidue r a := by
  ext x
  exact x.2 (powerOrder r a) (powerOrder r b) (pow_dvd_pow _ h)

private noncomputable def restrict (p : ℕ) [Fact p.Prime] : residues p →+* Adics p :=
  RingHom.pi fun r ↦
    @PadicInt.lift _ _ r.1 (primeResidue r) (Fact.mk r.1.2) (primeResidue_compat r)

private lemma restrict_spec {p : ℕ} [Fact p.Prime] (x : residues p) (r : Away p)
    (a : ℕ) :
    @PadicInt.toZModPow r.1 (Fact.mk r.1.2) a (restrict p x r) =
      x.1 (powerOrder r a) := by
  let : Fact (r.1.1.Prime) := ⟨r.1.2⟩
  exact RingHom.congr_fun (PadicInt.lift_spec (primeResidue_compat r) a) x

private lemma reconstruct_restrict {p : ℕ} [Fact p.Prime] (x : residues p) :
    reconstruct p (restrict p x) = x := by
  apply Subtype.ext
  funext m
  apply (ZMod.equivPi m.1 m.2.1.ne').injective
  funext q
  have he (z : ZMod m.1) : ZMod.equivPi m.1 m.2.1.ne' z q =
      ZMod.castHom (Nat.ordProj_dvd m.1 q.1) _ z :=
    RingHom.congr_fun
      (Subsingleton.elim ((Pi.evalRingHom _ q).comp
        (ZMod.equivPi m.1 m.2.1.ne').toRingHom)
        (ZMod.castHom (Nat.ordProj_dvd m.1 q.1) _)) z
  change ZMod.equivPi m.1 m.2.1.ne' (crtMap m (restrict p x)) q = _
  rw [he, crt_factor, he]
  change @PadicInt.toZModPow (factorIndex m q).1
    (Fact.mk (factorIndex m q).1.2) (m.1.factorization q.1)
    (restrict p x (factorIndex m q)) = _
  rw [restrict_spec]
  exact (x.2 (powerOrder (factorIndex m q) (m.1.factorization q.1)) m
    (Nat.ordProj_dvd m.1 q.1)).symm

private lemma restrict_reconstruct {p : ℕ} [Fact p.Prime] (x : Adics p) :
    restrict p (reconstruct p x) = x := by
  funext r
  let : Fact (r.1.1.Prime) := ⟨r.1.2⟩
  apply PadicInt.ext_of_toZModPow.mp
  intro a
  rw [restrict_spec]
  have h := crt_spec (powerOrder r a) x r a dvd_rfl
  change crtMap (powerOrder r a) x = _
  change ZMod.castHom (dvd_refl ((r : ℕ) ^ a)) _ _ = _ at h
  simpa only [ZMod.castHom_self, RingHom.id_apply] using h

private lemma reconstruct_bijective (p : ℕ) [Fact p.Prime] :
    Function.Bijective (reconstruct p) :=
  ⟨Function.HasLeftInverse.injective ⟨restrict p, restrict_reconstruct⟩,
    Function.HasRightInverse.surjective ⟨restrict p, reconstruct_restrict⟩⟩

private lemma mem_limit {k : Type u} [Field k] {p : ℕ} (x : Order p → kˣ) :
    x ∈ limitSubgroup k p ↔
      (∀ m, x m ^ m.1 = 1) ∧ ∀ m n, m.1 ∣ n.1 → x n ^ (n.1 / m.1) = x m := by
  constructor
  · intro hx
    refine ⟨fun m ↦ ?_, fun m n h ↦ ?_⟩
    · exact (Subgroup.mem_pi Set.univ).mp hx.1 m (Set.mem_univ m)
    · exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp
        (Subgroup.mem_iInf.mp hx.2 m) n) h
  · rintro ⟨hx, hc⟩
    refine ⟨(Subgroup.mem_pi Set.univ).mpr (fun m _ ↦ hx m), ?_⟩
    exact Subgroup.mem_iInf.mpr (fun m ↦ Subgroup.mem_iInf.mpr
      (fun n ↦ Subgroup.mem_iInf.mpr (fun h ↦ hc m n h)))

private noncomputable def theta {k : Type u} [Field k] {p : ℕ}
    {ζ : Order p → kˣ} (hζ : IsCompatiblePrimitiveFamily p ζ) (m : Order p) :
    ZMod m.1 ≃+ Additive (rootsOfUnity m.1 k) := by
  let : NeZero m.1 := ⟨m.2.1.ne'⟩
  exact (hζ.1 m).zmodAddEquivRootsOfUnity

private lemma theta_val {k : Type u} [Field k] {p : ℕ}
    {ζ : Order p → kˣ} (hζ : IsCompatiblePrimitiveFamily p ζ) (m : Order p)
    (b : ZMod m.1) :
    (Additive.toMul (theta hζ m b)).val = ζ m ^ b.val := by
  let : NeZero m.1 := ⟨m.2.1.ne'⟩
  change (Additive.toMul ((hζ.1 m).zmodAddEquivRootsOfUnity b)).val = _
  have he := (hζ.1 m).zmodAddEquivRootsOfUnity_natCast b.val
  simpa only [ZMod.natCast_zmod_val] using he

private lemma theta_compat {k : Type u} [Field k] {p : ℕ}
    {ζ : Order p → kˣ} (hζ : IsCompatiblePrimitiveFamily p ζ)
    (m n : Order p) (h : m.1 ∣ n.1) (b : ZMod n.1) :
    (Additive.toMul (theta hζ n b)).val ^ (n.1 / m.1) =
      (Additive.toMul (theta hζ m (ZMod.castHom h (ZMod m.1) b))).val := by
  let : NeZero n.1 := ⟨n.2.1.ne'⟩
  let : NeZero m.1 := ⟨m.2.1.ne'⟩
  rw [theta_val, theta_val]
  calc
    (ζ n ^ b.val) ^ (n.1 / m.1) = (ζ n ^ (n.1 / m.1)) ^ b.val :=
      pow_right_comm _ _ _
    _ = ζ m ^ b.val := by rw [hζ.2.2 m n h]
    _ = _ := by
      have he : ZMod.castHom h (ZMod m.1) b = (b.val : ZMod m.1) := by
        rw [← ZMod.natCast_zmod_val b, map_natCast, ZMod.natCast_zmod_val]
      rw [he, ZMod.val_natCast]
      exact (pow_eq_pow_of_modEq (Nat.mod_mod _ _) (hζ.1 m).pow_eq_one).symm

private noncomputable def rootsMap {k : Type u} [Field k] {p : ℕ}
    {ζ : Order p → kˣ} (hζ : IsCompatiblePrimitiveFamily p ζ) :
    Multiplicative (residues p) →* limitSubgroup k p where
  toFun x := ⟨fun m ↦ (Additive.toMul (theta hζ m ((Multiplicative.toAdd x).1 m))).val,
    (mem_limit _).mpr ⟨fun m ↦ (Additive.toMul (theta hζ m
      ((Multiplicative.toAdd x).1 m))).2,
      fun m n h ↦ by
        rw [theta_compat hζ m n h, (Multiplicative.toAdd x).2 m n h]⟩⟩
  map_one' := by
    apply Subtype.ext
    funext m
    change (Additive.toMul (theta hζ m 0)).val = 1
    rw [map_zero]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    funext m
    change (Additive.toMul (theta hζ m
      ((Multiplicative.toAdd x).1 m + (Multiplicative.toAdd y).1 m))).val = _
    rw [map_add]
    rfl

private lemma rootsMap_bijective {k : Type u} [Field k] {p : ℕ}
    {ζ : Order p → kˣ} (hζ : IsCompatiblePrimitiveFamily p ζ) :
    Function.Bijective (rootsMap hζ) := by
  classical
  constructor
  · intro x y h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext m
    apply (theta hζ m).injective
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun z : limitSubgroup k p ↦ z.1 m) h
  · intro x
    have hx := (mem_limit x.1).mp x.2
    let b : ∀ m : Order p, ZMod m.1 := fun m ↦
      (theta hζ m).symm (Additive.ofMul ⟨x.1 m, hx.1 m⟩)
    have hb (m : Order p) : (Additive.toMul (theta hζ m (b m))).val = x.1 m := by
      dsimp [b]
      rw [AddEquiv.apply_symm_apply]
      rfl
    have hcompat : b ∈ residues p := by
      intro m n h
      apply (theta hζ m).injective
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [← theta_compat hζ m n h, hb, hb, hx.2 m n h]
    refine ⟨Multiplicative.ofAdd ⟨b, hcompat⟩, ?_⟩
    exact Subtype.ext (funext hb)

private lemma crt_continuous {p : ℕ} [Fact p.Prime] (m : Order p) :
    Continuous (crtMap m) := by
  classical
  let : NeZero m.1 := ⟨m.2.1.ne'⟩
  have hc : Continuous (fun x : Adics p ↦ fun q : m.1.primeFactors ↦
      @PadicInt.toZModPow q.1 (Fact.mk (Nat.prime_of_mem_primeFactors q.2))
        (m.1.factorization q.1) (x (factorIndex m q))) := by
    apply continuous_pi
    intro q
    let : Fact q.1.Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
    exact (PadicInt.continuous_toZModPow _).comp (continuous_apply (factorIndex m q))
  have hd : Continuous (fun z : ∀ q : m.1.primeFactors,
      ZMod (q.1 ^ m.1.factorization q.1) ↦
      (ZMod.equivPi m.1 m.2.1.ne').symm z) := continuous_of_discreteTopology
  exact hd.comp hc

/-- For a fixed compatible primitive family, finite cyclic trivializations identify the
root limit with compatible residues. CRT reconstructs every tame-order residue from the
finitely many prime-power residues at primes dividing that order. `PadicInt.lift` and
`lift_spec` reconstruct the adic coordinates; separation by residues proves the inverse
laws. Every CRT coordinate is continuous, since it depends on finitely many continuous
residue maps to discrete finite rings. The adic product is compact and the root limit
is Hausdorff, so the continuous bijection has continuous inverse. The CRT prime-power
specification gives the required normalization, including exponent zero.
Source: Stacks Project, algebra.tex Tags 00DT and 00M9; fields.tex Tag 09HW.
(blueprint: lem-exc-tame-roots-product). -/
private theorem compatible_roots_product_identification (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (ζ : Order p → kˣ) (hζ : IsCompatiblePrimitiveFamily p ζ) :
    ∃ e : @ContinuousMulEquiv (limitSubgroup k p) (limitTopology k p)
        (AdicProduct p) inferInstance inferInstance inferInstance,
      ∀ (x : limitSubgroup k p) (r : {r : Nat.Primes // (r : ℕ) ≠ p})
        (a : ℕ) (m : Order p), m.1 = (r : ℕ) ^ a → x.1 m = ζ m ^
          ((@PadicInt.toZModPow r.1 (Fact.mk r.1.2) a)
            (Multiplicative.toAdd (e x) r)).val := by
  classical
  let : TopologicalSpace kˣ := ⊥
  let : DiscreteTopology kˣ := ⟨rfl⟩
  let : TopologicalSpace (limitSubgroup k p) := limitTopology k p
  have hcoord (m : Order p) : Continuous (fun x : limitSubgroup k p ↦ x.1 m) :=
    continuous_iInf_dom continuous_induced_dom
  let : T2Space (limitSubgroup k p) :=
    T2Space.of_injective_continuous Subtype.val_injective (continuous_pi hcoord)
  let f : AdicProduct p →* limitSubgroup k p :=
    (rootsMap hζ).comp (reconstruct p).toAddMonoidHom.toMultiplicative
  have hf : Function.Bijective f :=
    (rootsMap_bijective hζ).comp (reconstruct_bijective p)
  let e : AdicProduct p ≃* limitSubgroup k p := MulEquiv.ofBijective f hf
  have hc : Continuous e := by
    apply continuous_iInf_rng.mpr
    intro m
    apply continuous_induced_rng.mpr
    change Continuous (fun x : AdicProduct p ↦
      (Additive.toMul (theta hζ m (crtMap m (Multiplicative.toAdd x)))).val)
    let : NeZero m.1 := ⟨m.2.1.ne'⟩
    have hd : Continuous (fun b : ZMod m.1 ↦
        (Additive.toMul (theta hζ m b)).val) := continuous_of_discreteTopology
    exact hd.comp (crt_continuous m)
  let E : AdicProduct p ≃ₜ* limitSubgroup k p :=
    { e with
      continuous_toFun := hc
      continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }
  refine ⟨E.symm, ?_⟩
  intro x r a m hm
  have he : f (E.symm x) = x := E.apply_symm_apply x
  have hv := congrArg (fun z : limitSubgroup k p ↦ z.1 m) he
  change (Additive.toMul (theta hζ m
    (crtMap m (Multiplicative.toAdd (E.symm x))))).val = x.1 m at hv
  rw [theta_val] at hv
  rw [← hv]
  congr 1
  have hs := crt_spec m (Multiplicative.toAdd (E.symm x)) r a (hm ▸ dvd_rfl)
  have hmo : m = powerOrder r a := Subtype.ext hm
  subst m
  change (ZMod.castHom (dvd_refl ((r : ℕ) ^ a)) (ZMod ((r : ℕ) ^ a)))
    (crtMap (powerOrder r a) (Multiplicative.toAdd (E.symm x))) = _ at hs
  have hs' : crtMap (powerOrder r a) (Multiplicative.toAdd (E.symm x)) =
      @PadicInt.toZModPow r.1 (Fact.mk r.1.2) a
        (Multiplicative.toAdd (E.symm x) r) := by
    simpa only [ZMod.castHom_self, RingHom.id_apply] using hs
  exact congrArg (fun b : ZMod ((r : ℕ) ^ a) ↦ b.val) hs'

/--
Compatible tame roots exist, and every compatible family induces the required
topological-group identification with the product of adic integers.
Source: Stacks Project, fields.tex Tag 09HW, algebra.tex Tags 00DT and 00M9;
blueprint main-20261015, proof of `lem-exc-dvr-galois`, second paragraph
(blueprint: lem-exc-tame-roots-product).
-/
theorem compatible_roots_product (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    (∃ ζ : Order p → kˣ, IsCompatiblePrimitiveFamily p ζ) ∧
    ∀ ζ : Order p → kˣ, IsCompatiblePrimitiveFamily p ζ →
      ∃ e : @ContinuousMulEquiv (limitSubgroup k p) (limitTopology k p)
          (AdicProduct p) inferInstance inferInstance inferInstance,
        ∀ (x : limitSubgroup k p) (r : {r : Nat.Primes // (r : ℕ) ≠ p})
          (a : ℕ) (m : Order p), m.1 = (r : ℕ) ^ a → x.1 m = ζ m ^
            ((@PadicInt.toZModPow r.1 (Fact.mk r.1.2) a)
              (Multiplicative.toAdd (e x) r)).val := by
  constructor
  · exact compatible_roots_product_exists k p
  · intro ζ hζ
    exact compatible_roots_product_identification k p ζ hζ

end TameRoots

