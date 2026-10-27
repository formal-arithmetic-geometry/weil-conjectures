/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Group completion of an integral monoid sharpening

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.1--3.1.2 and 3.1.11,
printed pp. 98, 100; agent algebraic refinement
(blueprint: lem-trf-integral-sharpening-group-exactness).

We use multiplicative notation, as in the recorded fine-monoid definitions.
`Associates P` is the sharpening, and `Algebra.GrothendieckGroup` is group completion.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.FineFan

open Algebra.GrothendieckGroup

private theorem lift_of {M G : Type u} [CommMonoid M] [CommGroup G]
    (f : M →* G) (m : M) : lift f (of m) = f m := by
  exact DFunLike.congr_fun (lift.symm_apply_apply f) m

private theorem exists_fraction {M : Type u} [CommMonoid M] (x : Algebra.GrothendieckGroup M) :
    ∃ a b : M, of a / of b = x := by
  induction x using Localization.ind with
  | H y =>
    refine ⟨y.1, y.2, ?_⟩
    change Localization.mk y.1 1 / Localization.mk (y.2 : M) 1 = _
    rw [mk_div_mk]
    simp

/-- Sharpening an integral monoid embeds it in its group completion modulo units;
the induced group-completion map is surjective with precisely that unit subgroup
as kernel. Any specified finite monoid generating list descends to monoid generators
of the sharpening and group generators of its completion. The carrier equation fixes
`U` as the actual image of the units, and the representative equation fixes the embedding.

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.1--3.1.2 and 3.1.11,
printed pp. 98, 100; agent algebraic refinement
(blueprint: lem-trf-integral-sharpening-group-exactness).

Proof:
1. Units contain the identity and are closed under multiplication and inverse, so
   their image in the completion is a subgroup U. The relation defining Associates
   is exactly multiplication by a unit (def-trf-fine-fan-blowup).
2. Send the class of p to its coset in G/U. The unit relation proves well-definedness,
   and equality of cosets says that the two representatives differ by a unit.
   Thus the resulting monoid homomorphism is injective.
3. The universal property of group completion (def-trf-fs-log-blowup) extends this
   embedding to H = (Associates P)^gp. Applying the extension proves injectivity
   of the canonical map Associates P to H, hence integrality of the sharpening.
4. Lift the composite P to Associates P to H to obtain the canonical map G to H.
   Every completion element is a quotient of two canonical images. Lift their
   representatives along P to Associates P to prove surjectivity. Composing with
   H to G/U sends every quotient p/p' to its coset, so the kernel is contained in U.
   Conversely every unit has trivial class in Associates P, so U lies in the kernel.
5. Express p as a product of the specified generators with natural exponents.
   Applying the quotient gives generators of Associates P; expressing an element
   of H as a quotient gives integer exponents and therefore group generators.
   With an empty generating list all these products are the identity. -/
theorem integral_sharpening_group_exactness
    (P : Type u) [CommMonoid P]
    (hP : Function.Injective (Algebra.GrothendieckGroup.of (M := P))) :
    ∃ U : Subgroup (Algebra.GrothendieckGroup P),
      (U : Set (Algebra.GrothendieckGroup P)) =
        Algebra.GrothendieckGroup.of '' {p : P | IsUnit p} ∧
      (∃ i : Associates P →* (Algebra.GrothendieckGroup P ⧸ U),
        (∀ p : P, i (Associates.mk p) =
          QuotientGroup.mk' U (Algebra.GrothendieckGroup.of p)) ∧
        Function.Injective i) ∧
      Function.Injective (Algebra.GrothendieckGroup.of (M := Associates P)) ∧
      Function.Surjective (Algebra.GrothendieckGroup.lift
        (Algebra.GrothendieckGroup.of.comp (Associates.mkMonoidHom : P →* Associates P))) ∧
      (Algebra.GrothendieckGroup.lift
        (Algebra.GrothendieckGroup.of.comp
          (Associates.mkMonoidHom : P →* Associates P))).ker = U ∧
      (∀ (d : ℕ) (a : Fin d → P), Submonoid.closure (Set.range a) = ⊤ →
        Submonoid.closure (Set.range (fun k ↦ Associates.mk (a k))) = ⊤ ∧
        Subgroup.closure (Set.range (fun k ↦
          Algebra.GrothendieckGroup.of (Associates.mk (a k)))) = ⊤) := by
  let f : Pˣ →* Algebra.GrothendieckGroup P := of.comp (Units.coeHom P)
  let U : Subgroup (Algebra.GrothendieckGroup P) := f.range
  have hU : (U : Set (Algebra.GrothendieckGroup P)) = of '' {p : P | IsUnit p} := by
    ext g
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, v.isUnit, rfl⟩
    · rintro ⟨p, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
  let q := QuotientGroup.mk' U
  have hunit (v : Pˣ) : q (of (v : P)) = 1 := by
    apply (QuotientGroup.eq_one_iff _).2
    exact ⟨v, rfl⟩
  let i : Associates P →* (Algebra.GrothendieckGroup P ⧸ U) :=
    { toFun := fun b ↦ Quotient.liftOn b (fun p ↦ q (of p)) (by
        rintro p p' ⟨v, hv⟩
        rw [← hv, map_mul, map_mul, hunit, mul_one])
      map_one' := by change q (of 1) = 1; simp
      map_mul' := fun b c ↦ Quotient.inductionOn₂ b c (fun p p' ↦ by
        change q (of (p * p')) = q (of p) * q (of p')
        rw [map_mul, map_mul]) }
  have hi (p : P) : i (Associates.mk p) = q (of p) := rfl
  have hinj : Function.Injective i := by
    intro b c
    obtain ⟨p, rfl⟩ := Associates.mk_surjective b
    obtain ⟨p', rfl⟩ := Associates.mk_surjective c
    intro h
    obtain ⟨g, ⟨v, rfl⟩, hv⟩ := (QuotientGroup.mk'_eq_mk' U).mp h
    apply Associates.mk_eq_mk_iff_associated.mpr
    refine ⟨v, hP ?_⟩
    change of p * of (v : P) = of p' at hv
    simpa only [map_mul] using hv
  have hA : Function.Injective (of (M := Associates P)) := by
    intro b c h
    apply hinj
    simpa only [lift_of] using congrArg (lift i) h
  let π : Algebra.GrothendieckGroup P →* Algebra.GrothendieckGroup (Associates P) :=
    lift (of.comp (Associates.mkMonoidHom : P →* Associates P))
  have hπ (p : P) : π (of p) = of (Associates.mk p) :=
    lift_of _ p
  have hsurj : Function.Surjective π := by
    intro x
    obtain ⟨b, c, rfl⟩ := exists_fraction x
    obtain ⟨p, rfl⟩ := Associates.mk_surjective b
    obtain ⟨p', rfl⟩ := Associates.mk_surjective c
    refine ⟨of p / of p', ?_⟩
    rw [map_div, hπ, hπ]
  have hker : π.ker = U := by
    ext g
    constructor
    · intro hg
      have hg' : π g = 1 := hg
      obtain ⟨p, p', rfl⟩ := exists_fraction g
      have hρ : lift i (π (of p / of p')) = q (of p / of p') := by
        rw [map_div, hπ, hπ, map_div, lift_of, lift_of, hi, hi, map_div]
      apply (QuotientGroup.eq_one_iff _).mp
      change q (of p / of p') = 1
      rw [← hρ, hg', map_one]
    · rintro ⟨v, rfl⟩
      change π (of (v : P)) = 1
      rw [hπ, Associates.mk_eq_one.mpr v.isUnit, map_one]
  refine ⟨U, hU, ⟨i, hi, hinj⟩, hA, hsurj, hker, ?_⟩
  intro d a ha
  have hgen : Submonoid.closure (Set.range (fun k ↦ Associates.mk (a k))) = ⊤ := by
    apply top_le_iff.mp
    intro b htop
    clear htop
    obtain ⟨p, rfl⟩ := Associates.mk_surjective b
    have hp : p ∈ Submonoid.closure (Set.range a) := by rw [ha]; trivial
    induction hp using Submonoid.closure_induction with
    | mem p hp =>
      obtain ⟨k, rfl⟩ := hp
      exact Submonoid.subset_closure ⟨k, rfl⟩
    | one => exact Submonoid.one_mem _
    | mul p p' _ _ hp hp' =>
      exact Submonoid.mul_mem _ hp hp'
  refine ⟨hgen, top_le_iff.mp ?_⟩
  intro x _
  let S := Subgroup.closure (Set.range (fun k ↦ of (Associates.mk (a k))))
  have hb (b : Associates P) : of b ∈ S := by
    have hb' : b ∈ Submonoid.closure (Set.range (fun k ↦ Associates.mk (a k))) := by
      rw [hgen]
      trivial
    induction hb' using Submonoid.closure_induction with
    | mem b hb =>
      obtain ⟨k, rfl⟩ := hb
      exact Subgroup.subset_closure ⟨k, rfl⟩
    | one => simpa only [map_one] using S.one_mem
    | mul b c _ _ hb hc => simpa only [map_mul] using S.mul_mem hb hc
  obtain ⟨b, c, rfl⟩ := exists_fraction x
  exact S.div_mem (hb b) (hb c)

end AlgebraicGeometry.FineFan
