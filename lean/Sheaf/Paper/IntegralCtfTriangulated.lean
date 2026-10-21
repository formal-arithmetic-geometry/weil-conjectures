/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.IntegralConstructibleTriangulated
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
import Sheaf.Paper.FiniteCtfTriangulated
import Sheaf.Paper.IntegralDerivedReduction

/-!
# Integral constructible complexes with uniformly finite Tor amplitude

Source: Stacks Project, Cohomology on Sites, Tag 08G2, part (2), applied to each
reduction; Weil blueprint, integral-stage paragraph of `def-weil-finite-tor-amplitude`
(blueprint: lem-weil-integral-ctf-triangulated).
-/

@[expose] public section

set_option autoImplicit false

universe d u

open CategoryTheory AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The property `P` in the integral triangulation lemma: bounded constructibility and
one ordered Tor interval valid simultaneously for every positive reduction exponent.
The index `n : ℕ` denotes exponent `n + 1`, as in `integralDerivedReduction`.
Source: Weil blueprint, integral-stage paragraph of `def-weil-finite-tor-amplitude`;
Stacks Project, Tag 08FZ (blueprint: lem-weil-integral-ctf-triangulated). -/
noncomputable def integralCtfProperty
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty (completedIntegralDerivedCategory l E Y D hl) :=
  boundedConstructibleDerivedCompleteIntegral D l hl E Y ⊓
    fun K ↦ ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
        ((integralDerivedReduction l E Y D hl n).obj K) a b

private theorem torAmplitude_iso
    (Y : AlgebraicGeometry.Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory Y A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude Y A K a b) : HasProEtaleTorAmplitude Y A L a b := by
  refine ⟨h.1, ?_⟩
  rintro N P ⟨q⟩ f hf hP M i hi
  exact h.2 N P ⟨q ≪≫ e.symm⟩ f hf hP M i hi

private theorem torAmplitude_mono
    (Y : AlgebraicGeometry.Scheme.{u}) (A : Type u) [CommRing A]
    {K : proEtaleDerivedCategory Y A} {a b c e : ℤ}
    (h : HasProEtaleTorAmplitude Y A K a b) (hc : c ≤ a) (he : b ≤ e) :
    HasProEtaleTorAmplitude Y A K c e := by
  refine ⟨hc.trans (h.1.trans he), ?_⟩
  intro N P hN f hf hP M i hi
  apply h.2 N P hN f hf hP M i
  exact hi.elim (fun hi ↦ Or.inl (hi.trans_le hc))
    (fun hi ↦ Or.inr (he.trans_lt hi))

set_option linter.unusedVariables false in
/-- The integral finite-Tor property is isomorphism invariant and cuts out a full
triangulated subcategory: zero belongs, every integer shift preserves it in both
directions, and it is closed under middle vertices of distinguished triangles.
Source: Stacks Project, Tag 08G2 (2); Weil blueprint, integral-stage paragraph of
`def-weil-finite-tor-amplitude` (blueprint: lem-weil-integral-ctf-triangulated).

Proof:
1. Each reduction is an exact triangulated functor by `integralDerivedReduction_exact`.
It preserves zero and isomorphisms and commutes with integer shifts.
2. Tor amplitude is invariant under isomorphisms by composing the isomorphisms of
cochain representatives. For zero, finite-stage triangulation first gives some finite
Tor interval [a,b]. For any test degree i, shift the zero object by b-i+1 and transport
back along the isomorphism of zero objects. Its upper Tor bound becomes i-1, forcing
vanishing at i. Consequently [0,0] works for every reduction, independently of its level.
3. The quantitative finite-stage shift clause sends [a,b] to [a-m,b-m]. Transport
through the reduction's shift comparison. These endpoints are independent of the level.
4. Enlarge two Tor intervals to [min(a,c),max(b,e)] directly in the defining vanishing
condition. An index outside the enlarged interval is outside both original intervals.
5. Reduce a distinguished triangle and apply the finite-stage extension clause to the
common interval from step 4. The same interval works for every level.
6. These properties make the uniform Tor predicate triangulated and isomorphism-closed.
Intersect it with the integral bounded-constructibility predicate, using
`boundedConstructibleDerivedCompleteIntegral_isTriangulated` and Mathlib's intersection
instances. This gives precisely `integralCtfProperty`, without changing its definition.
-/
theorem integral_ctf_isTriangulated
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : AlgebraicGeometry.Scheme.{u})
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ObjectProperty.IsClosedUnderIsomorphisms.{u + 2, u + 2} (integralCtfProperty D l hl E Y) ∧
    @ObjectProperty.IsTriangulated.{u + 2, u + 2}
      (completedIntegralDerivedCategory l E Y D hl)
      inferInstance inferInstance inferInstance inferInstance
      (fun (n : ℤ) ↦ inferInstance) inferInstance
      (integralCtfProperty D l hl E Y) :=
  open CategoryTheory.Limits in by
  let : Zero (completedIntegralDerivedCategory l E Y D hl) := HasZeroObject.zero' _
  let P := boundedConstructibleDerivedCompleteIntegral D l hl E Y
  let Q : ObjectProperty (completedIntegralDerivedCategory l E Y D hl) :=
    fun K ↦ ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
        ((integralDerivedReduction l E Y D hl n).obj K) a b
  obtain ⟨hPi, hPt⟩ := boundedConstructibleDerivedCompleteIntegral_isTriangulated
    D l hl E Y
  have : P.IsClosedUnderIsomorphisms := hPi
  have : P.IsTriangulated := hPt
  have : Q.IsClosedUnderIsomorphisms := ⟨by
    intro K L e hK
    obtain ⟨a, b, hab, hK⟩ := hK
    exact ⟨a, b, hab, fun n ↦ torAmplitude_iso Y _
      ((integralDerivedReduction l E Y D hl n).mapIso e) a b (hK n)⟩⟩
  have : Q.ContainsZero := ⟨0, isZero_zero _, 0, 0, le_rfl, by
    intro n
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let F := integralDerivedReduction l E Y D hl n
    obtain ⟨cF, hF⟩ := integralDerivedReduction_exact l E Y D hl n
    have hz := F.map_isZero (isZero_zero _)
    let Z := F.obj 0
    let S : ObjectProperty (proEtaleDerivedCategory Y A) :=
      intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) Y ⊓
        fun K ↦ HasFiniteProEtaleTorAmplitude Y A K
    obtain ⟨hSi, hSt, hs, _⟩ := finite_ctf_isTriangulated l E (n + 1) (by omega) Y
    have : S.IsClosedUnderIsomorphisms := hSi
    have : S.IsTriangulated := hSt
    obtain ⟨a, b, h⟩ := (S.prop_of_isZero hz).2
    refine ⟨le_rfl, ?_⟩
    intro N R hN f hf hR M i _hi
    -- Every shift of a zero object is zero. Move the upper bound below the test degree.
    have ht := hs Z a b (b - i + 1) h
    have hzshift := (shiftFunctor _ (b - i + 1)).map_isZero hz
    have ht' := torAmplitude_iso Y A (hzshift.iso hz) _ _ ht
    exact ht'.2 N R hN f hf hR M i (Or.inr (by omega))⟩
  have : Q.IsStableUnderShift ℤ := ⟨fun m ↦ ⟨by
    intro K hK
    obtain ⟨a, b, hab, hK⟩ := hK
    refine ⟨a - m, b - m, by omega, ?_⟩
    intro n
    let F := integralDerivedReduction l E Y D hl n
    obtain ⟨cF, hF⟩ := integralDerivedReduction_exact l E Y D hl n
    have ht := (finite_ctf_isTriangulated l E (n + 1) (by omega) Y).2.2.1
      (F.obj K) a b m (hK n)
    exact torAmplitude_iso Y _ ((F.commShiftIso m).app K).symm _ _ ht⟩⟩
  have : Q.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (by
    intro T hT h₁ h₃
    obtain ⟨a, b, hab, h₁⟩ := h₁
    obtain ⟨c, e, hce, h₃⟩ := h₃
    refine ⟨min a c, max b e, (min_le_left _ _).trans (hab.trans (le_max_left _ _)), ?_⟩
    intro n
    let F := integralDerivedReduction l E Y D hl n
    obtain ⟨cF, hF⟩ := integralDerivedReduction_exact l E Y D hl n
    exact (finite_ctf_isTriangulated l E (n + 1) (by omega) Y).2.2.2
      (F.mapTriangle.obj T) _ _ (F.map_distinguished T hT)
      (torAmplitude_mono Y _ (h₁ n) (min_le_left _ _) (le_max_left _ _))
      (torAmplitude_mono Y _ (h₃ n) (min_le_right _ _) (le_max_right _ _)))
  have : Q.IsTriangulated := { }
  exact ⟨inferInstanceAs (P ⊓ Q).IsClosedUnderIsomorphisms,
    inferInstanceAs (P ⊓ Q).IsTriangulated⟩

end WeilConjectures
