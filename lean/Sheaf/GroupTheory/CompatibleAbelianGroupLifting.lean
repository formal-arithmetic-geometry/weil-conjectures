module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Finiteness.Basic

/-! # Compatible lifting of finitely generated abelian group maps

Source: the agent-formulated obstruction lemma for Kato (1988), Theorem 3.5,
used in ILO, Exposé XVI, Proposition 3.6.3, printed p. 252
(blueprint: lem-per-compatible-abelian-group-lifting).
The general group statement is not asserted verbatim by ILO.
-/

@[expose] public section

universe uA uB uE uE₀ uJ

namespace AddCommGroup

/-- Compatible lifting across a short exact sequence of abelian groups when the finite
kernel and torsion-cokernel orders act invertibly on its kernel.

Source: agent-formulated obstruction lemma for Kato (1988), Theorem 3.5, cited in
ILO, Exposé XVI, Proposition 3.6.3, printed p. 252
(blueprint: lem-per-compatible-abelian-group-lifting).

Proof: multiplication by the kernel order annihilates `u.ker`. Its injectivity on `J`
therefore makes `a` vanish on `u.ker`, giving `α : u.range →+ E` with `πα = b₀`.
Put `C = B / u.range`, `T = torsion C`, `N = Nat.card T`, and let `P` be the preimage
of `T` in `B`. For `p ∈ P`, `Np` lies in `u.range`. Choose any lift `e` of `b₀ p`.
The error `Ne - α(Np)` is `i z`; choose `t` with `Nt = z` and replace `e` by `e - i t`.
This gives a lift satisfying `Ne = α(Np)`. It is unique because multiplication by `N`
is injective on `J`. Uniqueness makes these lifts an additive map `γ : P →+ E`,
whose restriction to `u.range` is `α`. The finitely generated torsion-free group
`Q = C / T` is free over `ℤ`, hence projective. Split `q₂ : B →+ Q` by a map `s`,
and lift `b₀s` through `π` to `v`. Then `r(x) = x - s(q₂ x)` belongs to `P`.
The homomorphism `b(x) = γ(r(x)) + v(q₂ x)` has both required composites.
This proves the shared sfb/per declaration directly, without applying it to itself.
-/
theorem exists_compatible_lift_of_bijective_nsmul
    {A : Type uA} {B : Type uB} {E : Type uE} {E₀ : Type uE₀} {J : Type uJ}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup E] [AddCommGroup E₀]
    [AddCommGroup J] [Module.Finite ℤ A] [Module.Finite ℤ B]
    (u : A →+ B) [Finite u.ker] [Finite (AddCommGroup.torsion (B ⧸ u.range))]
    (i : J →+ E) (π : E →+ E₀)
    (hi : Function.Injective i) (hπ : Function.Surjective π) (hexact : π.ker = i.range)
    (hK : Function.Bijective (fun j : J ↦ Nat.card u.ker • j))
    (hC : Function.Bijective
      (fun j : J ↦ Nat.card (AddCommGroup.torsion (B ⧸ u.range)) • j))
    (a : A →+ E) (b₀ : B →+ E₀) (hcompat : π.comp a = b₀.comp u) :
    ∃ b : B →+ E, b.comp u = a ∧ π.comp b = b₀ := by
  classical
  have hπi (j : J) : π (i j) = 0 := by
    apply AddMonoidHom.mem_ker.mp
    rw [hexact]
    exact ⟨j, rfl⟩
  -- Descend the prescribed map to its image.
  have hker : u.ker ≤ a.ker := by
    intro x hx
    have hax : π (a x) = 0 := by
      have h := DFunLike.congr_fun hcompat x
      simpa only [AddMonoidHom.comp_apply, AddMonoidHom.mem_ker.mp hx, map_zero] using h
    obtain ⟨j, hj⟩ := (show a x ∈ i.range by rw [← hexact]; exact hax)
    have hxk : Nat.card u.ker • x = 0 := by
      exact congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨x, hx⟩ : u.ker)))
    have hjk : Nat.card u.ker • j = 0 := by
      apply hi
      rw [map_nsmul, hj, ← map_nsmul, hxk, map_zero, map_zero]
    have hj0 : j = 0 := hK.1 (by simpa only [smul_zero] using hjk)
    exact AddMonoidHom.mem_ker.mpr (by rw [← hj, hj0, map_zero])
  let α : u.range →+ E :=
    u.rangeRestrict.liftOfSurjective u.rangeRestrict_surjective
      ⟨a, by simpa only [AddMonoidHom.ker_rangeRestrict] using hker⟩
  have hαu (x : A) : α (u.rangeRestrict x) = a x := by
    simp [α]
  have hπα (x : u.range) : π (α x) = b₀ x := by
    obtain ⟨x, rfl⟩ := u.rangeRestrict_surjective x
    rw [hαu]
    exact DFunLike.congr_fun hcompat x
  -- The quotient by all torsion is finite free over the integers.
  let C := B ⧸ u.range
  let T := AddCommGroup.torsion C
  let Q := C ⧸ T
  let q : B →+ C := QuotientAddGroup.mk' u.range
  let qT : C →+ Q := QuotientAddGroup.mk' T
  let q₂ : B →+ Q := qT.comp q
  have hq₂ : Function.Surjective q₂ :=
    (QuotientAddGroup.mk'_surjective T).comp (QuotientAddGroup.mk'_surjective u.range)
  let : Module.Finite ℤ Q := Module.Finite.of_surjective q₂.toIntLinearMap hq₂
  have : IsAddTorsionFree Q := by
    dsimp [Q, T]
    infer_instance
  have : Module.IsTorsionFree ℤ Q := inferInstance
  have : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q₂.toIntLinearMap
    (LinearMap.id : Q →ₗ[ℤ] Q) hq₂
  have hqs (x : Q) : q₂ (s x) = x := DFunLike.congr_fun hs x
  obtain ⟨v, hv⟩ := Module.projective_lifting_property π.toIntLinearMap
    (b₀.toIntLinearMap.comp s) hπ
  have hπv (x : Q) : π (v x) = b₀ (s x) := DFunLike.congr_fun hv x
  -- Extend uniquely to the preimage of the torsion subgroup.
  let P : AddSubgroup B := T.comap q
  let N := Nat.card T
  have hNP (p : P) : N • (p : B) ∈ u.range := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change q (N • (p : B)) = 0
    rw [map_nsmul]
    exact congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨q p, p.property⟩ : T)))
  let nD : P →+ u.range :=
    { toFun := fun p ↦ ⟨N • (p : B), hNP p⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hcorr (p : P) : ∃! e : E, π e = b₀ p ∧ N • e = α (nD p) := by
    obtain ⟨e, he⟩ := hπ (b₀ p)
    have hz : N • e - α (nD p) ∈ i.range := by
      rw [← hexact]
      change π (N • e - α (nD p)) = 0
      rw [map_sub, map_nsmul, he, hπα]
      change N • b₀ (p : B) - b₀ (N • (p : B)) = 0
      rw [map_nsmul, sub_self]
    obtain ⟨z, hz⟩ := hz
    obtain ⟨t, ht⟩ := hC.2 z
    change N • t = z at ht
    refine ⟨e - i t, ⟨by rw [map_sub, he, hπi, sub_zero], ?_⟩, ?_⟩
    · rw [nsmul_sub, ← map_nsmul, ht, hz]
      abel
    · intro e' he'
      have hdiff : e' - (e - i t) ∈ i.range := by
        rw [← hexact]
        change π (e' - (e - i t)) = 0
        rw [map_sub, he'.1, map_sub, he, hπi, sub_zero, sub_self]
      obtain ⟨j, hj⟩ := hdiff
      have hjN : N • j = 0 := by
        apply hi
        rw [map_nsmul, hj, nsmul_sub, he'.2, nsmul_sub, ← map_nsmul, ht, hz]
        simp only [map_zero]
        abel
      have hj0 : j = 0 := hC.1 (by simpa only [smul_zero] using hjN)
      apply sub_eq_zero.mp
      rw [← hj, hj0, map_zero]
  choose g hg huniq using hcorr
  let γ : P →+ E :=
    { toFun := g
      map_zero' := by
        apply (huniq 0 0 ?_).symm
        simp
      map_add' := by
        intro x y
        apply (huniq (x + y) (g x + g y) ?_).symm
        constructor
        · rw [map_add, (hg x).1, (hg y).1]
          exact (map_add b₀ (x : B) (y : B)).symm
        · rw [nsmul_add, (hg x).2, (hg y).2, ← map_add, ← map_add] }
  have hγπ (p : P) : π (γ p) = b₀ p := (hg p).1
  have hγD (d : u.range) : γ ⟨d, by
      change q (d : B) ∈ T
      have hqd : q (d : B) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr d.property
      rw [hqd]; exact T.zero_mem⟩ = α d := by
    apply (huniq _ (α d) ?_).symm
    constructor
    · exact hπα d
    · rw [← map_nsmul]
      rfl
  -- Combine the corrected lift on P with a lift on the free complement.
  let r : B →+ P :=
    { toFun := fun x ↦ ⟨x - s (q₂ x), by
        change q (x - s (q₂ x)) ∈ T
        apply (QuotientAddGroup.eq_zero_iff _).mp
        change q₂ (x - s (q₂ x)) = 0
        rw [map_sub, hqs, sub_self]⟩
      map_zero' := by ext; simp
      map_add' := by
        intro x y
        ext
        simp only [map_add, AddSubgroup.coe_add]
        abel }
  refine ⟨(γ.comp r) + v.toAddMonoidHom.comp q₂, ?_, ?_⟩
  · ext x
    have hqu : q₂ (u x) = 0 := by
      change qT (q (u x)) = 0
      have hu : q (u x) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr ⟨x, rfl⟩
      rw [hu, map_zero]
    change γ (r (u x)) + v (q₂ (u x)) = a x
    rw [hqu, map_zero, add_zero]
    have hr : r (u x) = ⟨u x, by
        change q (u x) ∈ T
        have hu : q (u x) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr ⟨x, rfl⟩
        rw [hu]
        exact T.zero_mem⟩ := by
      apply Subtype.ext
      change u x - s (q₂ (u x)) = u x
      rw [hqu, map_zero, sub_zero]
    rw [hr]
    exact (hγD (u.rangeRestrict x)).trans (hαu x)
  · ext x
    change π (γ (r x) + v (q₂ x)) = b₀ x
    rw [map_add, hγπ, hπv]
    change b₀ (x - s (q₂ x)) + b₀ (s (q₂ x)) = b₀ x
    rw [map_sub, sub_add_cancel]

end AddCommGroup
