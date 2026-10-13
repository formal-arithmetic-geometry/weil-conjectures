/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Lifting a quotient cover before punctured comparison

Source: Stacks Project, Tags 09ZL and 0ALJ, as used in Tag 0BLS.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A finite etale quotient extension gives a completed cover agreeing on the quotient.

Source: Stacks Project, Tag 0BLS, complete-case lifting paragraph, using Tags 09ZL
and 0ALJ. (blueprint: lem-sbc-completed-quotient-cover-lift)

Proof: Put C = the maximal-ideal completion of A and g = the image of f in C.
The map A/(f) to C/(g) is induced by A to C. Base change the supplied finite etale
cover F₀ to Spec(C/(g)). Since C is a complete Noetherian local ring and g belongs
to its maximal ideal, C is also (g)-adically complete: a (g)-adic Cauchy sequence
is maximal-ideal-adically Cauchy, and each ideal (g)^n is closed by Noetherianity,
so its limit has the prescribed residue modulo every (g)^n. The Krull intersection
theorem gives separatedness. Thus (C,(g)) is henselian (0ALJ). The finite etale lifting
equivalence (09ZL) gives a finite etale cover E of Spec C whose quotient is the
base-changed F₀. Restrict its quotient identification to the inverse image of U.
Base change the supplied identification e₀ along Spec(C/(g)) to Spec(A/(f)).
Associativity of fibre products identifies both restricted covers with the two
pullbacks displayed below. Compose these identifications. Each is over the same
open of Spec(C/(g)), so the composite satisfies the displayed projection equality.
This uses no depth assumption and works for any open U. When f = 0 the quotient
map is an isomorphism; an empty F₀ lifts to the empty cover. -/
theorem exists_completed_cover_with_quotient_iso
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (U : (Spec (.of A)).Opens)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) [IsFinite q] [Etale q]
    (hquot :
      let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      let V := i ⁻¹ᵁ U
      ∃ (F₀ : Scheme.{u}) (r₀ : F₀ ⟶ Spec (.of (A ⧸ Ideal.span {f}))),
        IsFinite r₀ ∧ Etale r₀ ∧
          ∃ e₀ : pullback q (i ∣_ U) ≅ (r₀ ⁻¹ᵁ V).toScheme,
            e₀.hom ≫ r₀ ∣_ V = pullback.snd q (i ∣_ U)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let c := Spec.map (CommRingCat.ofHom (algebraMap A C))
    let W := c ⁻¹ᵁ U
    let j := Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {algebraMap A C f})))
    ∃ (E : Scheme.{u}) (s : E ⟶ Spec (.of C)), IsFinite s ∧ Etale s ∧
      ∃ e₀ : pullback (pullback.snd q (c ∣_ U)) (j ∣_ W) ≅
          pullback (s ∣_ W) (j ∣_ W),
        e₀.hom ≫ pullback.snd (s ∣_ W) (j ∣_ W) =
          pullback.snd (pullback.snd q (c ∣_ U)) (j ∣_ W) := by sorry

end AlgebraicGeometry.Scheme
