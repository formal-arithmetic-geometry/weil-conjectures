/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# A localization as a filtered colimit of principal localizations

Source: Stacks Project, Algebra, Lemma 10.9.9, Tag 00CR, specialized to the ring itself
(blueprint: lem-weil-pbc-localization-colimit-principal-localizations).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- Stacks Project, Algebra, Tag 00CR, in the ring case.
(blueprint: lem-weil-pbc-localization-colimit-principal-localizations).
The divisibility preorder on `S` is directed, and hence filtered. The maps between the
principal localizations are specified on every fraction, for every choice of the factor `h`.
The functor and its chosen colimit `colimit F` are identified with these rings and maps by
the displayed isomorphisms; these merely transport the diagram, rather than change its objects.

Proof (the node's seven steps):
1. Reflexivity uses the factor 1, and transitivity multiplies factors. The product `f * g`
   belongs to `S` and is an upper bound; `1 ∈ S`, and parallel arrows are equal.
2. If `g = f * h`, the image of `f` in `P_g` has inverse `h/g`. The universal property
   (lem-weil-pbc-localization-away-universal-property) gives the unique transition ring map,
   with fraction formula `a/f^n ↦ a*h^n/g^n`. Uniqueness of the inverse gives independence of h.
3. Identity and composition follow from uniqueness of maps agreeing on the original ring.
4. Elements of `S` become units in the localization (def-weil-pbc-module-localization).
   The same universal property gives the maps kappa, their fraction formula, their compatibility,
   and their composites with the original localization maps.
5. Every fraction `a/s` comes from `P_s`. Equal fractions at stages `s,s'` admit a witness
   `t ∈ S` annihilating their cross difference. At the common stage `s*s'*t` their images agree,
   by the equality criterion in def-weil-ring-localization-away.
6. Given any cocone, send a fraction to its image from any representing stage. Step 5 makes
   this well defined. Moving two representatives to a common stage proves additivity and
   multiplicativity; using the stage 1 proves preservation of the unit.
7. Every element comes from a stage, so the induced ring map is unique. This is the colimit
   universal property (def-weil-pbc-category-colimit). -/
theorem localization_colimit_principalLocalizations
    (P : Type u) [CommRing P] (S : Submonoid P) :
    ∃ p : Preorder S,
      letI : Preorder S := p
      (∀ f g : S, f ≤ g ↔ ∃ h : P, (g : P) = (f : P) * h) ∧
      (∀ f g : S, f ≤ f * g ∧ g ≤ f * g) ∧
      IsDirected S (· ≤ ·) ∧ IsFiltered S ∧
      ∃ (rho : ∀ f g : S, f ≤ g →
          Localization.Away (f : P) →+* Localization.Away (g : P))
        (kappa : ∀ f : S, Localization.Away (f : P) →+* LocalizedModule S P),
        (∀ (f g : S) (l : f ≤ g) (h a : P) (n : ℕ),
          (g : P) = (f : P) * h →
          rho f g l (IsLocalization.mk' (M := Submonoid.powers (f : P))
            (Localization.Away (f : P)) a
            ⟨(f : P) ^ n, ⟨n, rfl⟩⟩) =
          IsLocalization.mk' (M := Submonoid.powers (g : P))
            (Localization.Away (g : P)) (a * h ^ n)
            ⟨(g : P) ^ n, ⟨n, rfl⟩⟩) ∧
        (∀ (f : S) (l : f ≤ f), rho f f l = RingHom.id _) ∧
        (∀ (f g k : S) (l : f ≤ g) (m : g ≤ k),
          (rho g k m).comp (rho f g l) = rho f k (le_trans l m)) ∧
        (∀ (f : S) (a : P) (n : ℕ),
          kappa f (IsLocalization.mk' (M := Submonoid.powers (f : P))
            (Localization.Away (f : P)) a
            ⟨(f : P) ^ n, ⟨n, rfl⟩⟩) = LocalizedModule.mk a (f ^ n)) ∧
        (∀ (f g : S) (l : f ≤ g), (kappa g).comp (rho f g l) = kappa f) ∧
        (∀ f : S, (kappa f).comp (algebraMap P (Localization.Away (f : P))) =
          algebraMap P (LocalizedModule S P)) ∧
        ∃ (F : S ⥤ CommRingCat.{u})
          (e : ∀ f : S, F.obj f ≅ CommRingCat.of (Localization.Away (f : P)))
          (eL : colimit F ≅ CommRingCat.of (LocalizedModule S P)),
          (∀ (f g : S) (l : f ≤ g),
            (e f).inv ≫ F.map (homOfLE l) ≫ (e g).hom = ofHom (rho f g l)) ∧
          (∀ f : S, (e f).inv ≫ colimit.ι F f ≫ eL.hom = ofHom (kappa f)) := by
  sorry

end CommRingCat
