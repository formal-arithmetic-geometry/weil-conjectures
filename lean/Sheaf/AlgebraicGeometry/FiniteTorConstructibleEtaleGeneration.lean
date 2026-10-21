/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes

import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact
import Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Finite-Tor constructible objects generate the ordinary étale derived category

Source: blueprint main-20261015, `sec-six-functors-basics`,
`sk-prop-ctf-finite-comparison/sk-prop-ctf-finite-comparison-whole.md` and its proof;
Stacks Project, Derived Categories, Tag 09SN (blueprint: det-ctf-finite-comparison-whole).

The localizing hull is the defining intersection of full replete triangulated
subcategories closed under ambient coproducts indexed in the fixed universe `u + 1`.
The ambient category is the ordinary unbounded derived category of module sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Bounded constructible complexes of finite Tor amplitude generate the entire ordinary
unbounded étale derived category over a finite admissible ring. The intersection is over
full replete triangulated subcategories containing these complexes and closed under all
small ambient coproducts, including the empty coproduct.

Source: blueprint main-20261015, `sk-prop-ctf-finite-comparison-whole.md`, and its proof,
Compactness, Detection and Generation; Stacks Project, Tag 09SN
(blueprint: det-ctf-finite-comparison-whole).

Proof:
1. Apply `lem-pur-etale-finite-ring-compact-generators` with `T = X` and `C = A`.
   The field `D.k` is algebraically closed, and the prime ℓ is invertible because it
   differs from `D.p`. Finite type and the finite ℓ-primary coefficient hypothesis
   give a small family `E_s` of bounded constructible finite-Tor objects detecting
   isomorphisms, ambient coproducts, and locally small Hom spaces. Apply
   `det-ctf-finite-compact-etale` to make every `E_s` compact.
2. If all maps from all shifts of `E_s` to `K` vanish, detection applied to `0 → K`
   makes `K` zero. For nonzero `K`, a nonzero map from a shifted generator becomes
   a nonzero map from `E_s` into a shift of `K`. Extend it by zero on the other
   summands of the coproduct of the `E_s`. Its restriction to summand `s` remains
   nonzero, so this coproduct is a weak generator, as in `def-pc-generators`.
3. Apply `lem-pc-compact-generators-build-objects` to an arbitrary unbounded `K`.
   It gives a sequence `X_n` with `X_0` and the successive triangle objects `Z_n`
   coproducts of shifts of `E_s`, distinguished triangles
   `Z_n → X_n → X_(n+1) → Z_n[1]`, and a telescope triangle
   `P → P → K → P[1]`, where `P` is the coproduct of the `X_n` and its first arrow
   is identity minus shift.
4. Every full replete triangulated coproduct-closed subcategory containing the
   finite-Tor constructible objects contains all `E_s`, their shifts, `X_0`, and
   all `Z_n`. Rotate the successive triangles and use the middle-object condition
   of `def-weil-triangulated-subcategory` inductively to put all `X_n` in it.
   Coproduct and shift closure put `P` and `P[1]` in it. The rotated telescope
   triangle `P → K → P[1] → P[1]` then puts `K` in it. Since `K` was arbitrary,
   their intersection is the full object property. -/
theorem finiteTorConstructible_etale_localizing_eq_top
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) (hℓprime : Nat.Prime ℓ) (hℓne : ℓ ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ℓ : A) ^ r = 0) :
    sInf {P : ObjectProperty (DerivedCategoryModule A X) |
      (∀ K : DerivedCategoryModule A X,
        DerivedCategory.isBoundedConstructible A X K →
        (∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b K) → P K) ∧
      P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧
      ∀ I : Type (u + 1), Nonempty (P.IsClosedUnderColimitsOfShape (Discrete I))} =
        (⊤ : ObjectProperty (DerivedCategoryModule A X)) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hcard : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hcard
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hunit : IsUnit (ℓ : D.k) := by
    apply isUnit_iff_ne_zero.mpr
    exact CharP.cast_ne_zero_of_ne_of_prime D.k hℓprime hℓne.symm
  -- The finite-ring theorem supplies the detecting family and ambient coproducts.
  obtain ⟨hcoprod, hsmall, _, S, E, hE, hdetect⟩ :=
    finiteRing_compactGenerators ℓ hℓprime hunit (X ↘ Spec (CommRingCat.of D.k)) hA
  let := hcoprod
  let := hsmall
  let : Zero (DerivedCategoryModule A X) := HasZeroObject.zero' _
  obtain ⟨_, hcompact⟩ := finiteTorConstructible_etale_compact D ℓ hℓprime hℓne X A hA
  -- Vanishing maps out of the coproduct force the zero map to K to be an isomorphism.
  have hgenerate : IsTriangulatedGeneratingFamily E := by
    intro K hK
    by_contra! hn
    have hzero (s : S) (n : ℤ) (f : E s ⟶ K⟦n⟧) : f = 0 := by
      have h := congrArg (fun g ↦ Sigma.ι E s ≫ g)
        (hn n (Sigma.desc (Pi.single s f)))
      simpa using h
    have hshift (s : S) (n : ℤ) (f : (E s)⟦n⟧ ⟶ K) : f = 0 := by
      let e := (shiftEquiv (DerivedCategoryModule A X) n).toAdjunction.homEquiv (E s) K
      apply e.injective
      rw [hzero s (-n) (e f)]
      simp [e, Adjunction.homEquiv_apply]
    have : IsIso (0 : (0 : DerivedCategoryModule A X) ⟶ K) := by
      apply hdetect
      intro s n
      constructor
      · intro f g _
        exact (isZero_zero _).eq_of_tgt f g
      · intro f
        refine ⟨0, ?_⟩
        simp only [zero_comp, hshift s n f]
    exact hK ((isZero_zero _).of_iso (asIso (0 : (0 : DerivedCategoryModule A X) ⟶ K)).symm)
  -- Each candidate contains every stage of the compact-generator telescope.
  apply top_unique
  apply le_sInf
  intro P hP K _
  obtain ⟨hcontains, hiso, htri, hsums⟩ := hP
  let := hiso
  let := htri
  have hsum {I : Type (u + 1)} (F : I → DerivedCategoryModule A X)
      (hF : ∀ i, P (F i)) : P (∐ F) := by
    let := (hsums I).some
    exact P.prop_colimit (Discrete.functor F) (fun i ↦ hF i.as)
  have hshift (s : S) (n : ℤ) : P ((E s)⟦n⟧) :=
    P.le_shift n _ (hcontains _ (hE s).1 (hE s).2)
  obtain ⟨Y, t, hstart, hsteps, q, r, htel⟩ :=
    compactGenerators_buildObjects.{u + 1, u + 1} E
      (fun s ↦ hcompact _ (hE s).1 (hE s).2) hgenerate K
  have hshape (Z : DerivedCategoryModule A X)
      (hZ : ∃ (J : Type (u + 1)) (i : J → S) (m : J → ℤ),
        Nonempty (Z ≅ ∐ fun j : J ↦ (E (i j))⟦m j⟧)) : P Z := by
    obtain ⟨J, i, m, ⟨e⟩⟩ := hZ
    exact P.prop_of_iso e.symm (hsum _ (fun j ↦ hshift (i j) (m j)))
  obtain ⟨Z, a, b, hZ, hdist⟩ := hsteps
  have hY (n : ℕ) : P (Y n) := by
    induction n with
    | zero => exact hshape _ hstart
    | succ n ih =>
      exact P.ext_of_isTriangulatedClosed₃ _ (hdist n) (hshape _ (hZ n)) ih
  have hPsum := hsum (fun n : ULift.{u + 1} ℕ ↦ Y n.down) (fun n ↦ hY n.down)
  exact P.ext_of_isTriangulatedClosed₃ _ htel hPsum hPsum

end AlgebraicGeometry.Etale
