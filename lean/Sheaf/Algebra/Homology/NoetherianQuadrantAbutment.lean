/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.CanonicalFiltration
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Noetherian.Basic

/-! # Finite generation through a shifted-quadrant spectral sequence

Source: Stacks Project, perfect.tex, Tag 0D0C, lemma-coherent-internal-hom,
proof, the finite-generation inference from the two convergent Ext spectral sequences.
(blueprint: lem-trf-noetherian-quadrant-abutment).

All pages, stable terms, graded-piece isomorphisms and filtrations live in ModuleCat A.
Stabilization respects the given homology-to-next-page isomorphisms of E.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SpectralSequence

/-- A shifted-quadrant spectral sequence over a Noetherian ring with finite second
page has finite pages and stable terms, and every finitely filtered abutment is finite.
Source: Stacks Project, perfect.tex, Tag 0D0C, lemma-coherent-internal-hom, proof;
Homology, definition-spectral-sequence and definition-filtered (Tag 0121).
(blueprint: lem-trf-noetherian-quadrant-abutment).

Proof:
1. Induct from page 2 using def-sp-spectral-sequence. Outside the quadrant the
   middle term is zero, so its homology and hence the next page are zero.
2. Induct on pages for finite generation. Lem-trf-noetherian-submodule-finitely-presented
   makes the kernel of each differential finite over the Noetherian ring. Images of
   its finite generating set generate the quotient by the incoming image. Transport
   these generators through E.iso to the next page (def-weil-finitely-generated-module).
3. If s > max (p-a) (q-b+1), the incoming source has first degree p-s < a and the
   outgoing target has second degree q-s+1 < b. Both differentials therefore vanish.
   Set s0 = max 2 (max (p-a+1) (q-b+2)) and take EInf p q to be the term on page s0.
   Zero differentials identify cycles and homology with the page term. Compose these
   identifications with E.iso, and their inverses, to identify every later page with
   EInf p q. The displayed cycles/homology equation records this compatibility.
   Step 2 gives finite generation of this stable term.
4. For a finite abutment filtration (def-sp-filtration), choose l,h with F^l=T and
   F^h=0. Descend from h to l. Lift finite generators of F^p/F^(p+1), identified with
   EInf p (n-p), and adjoin generators of F^(p+1). Subtracting a linear combination
   of the lifts leaves an element of F^(p+1), proving these generators span F^p.
   The empty generating set starts the induction at zero, giving finiteness of T.
5. If n<a+b, every EInf p (n-p) is zero by Step 1 and stabilization. Each successive
   quotient is zero, so consecutive filtration steps agree. The finite interval from
   the zero step to the whole step then shows T=0. -/
theorem noetherian_quadrant_abutment
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a b : ℤ)
    (E : E₂CohomologicalSpectralSequence (ModuleCat.{v} A))
    (hfinite : ∀ p q : ℤ, Module.Finite A ((E.page 2).X (p, q)))
    (hsupport : ∀ p q : ℤ, p < a ∨ q < b → IsZero ((E.page 2).X (p, q))) :
    (∀ (s : ℤ) (hs : 2 ≤ s) (p q : ℤ),
      (p < a ∨ q < b → IsZero ((E.page s hs).X (p, q))) ∧
        Module.Finite A ((E.page s hs).X (p, q))) ∧
    (∀ (s : ℤ) (hs : 2 ≤ s) (p q : ℤ), max (p - a) (q - b + 1) < s →
      (E.page s hs).d (p - s, q + s - 1) (p, q) = 0 ∧
        (E.page s hs).d (p, q) (p + s, q - s + 1) = 0) ∧
    ∃ EInf : ℤ → ℤ → ModuleCat.{v} A,
      (∀ p q : ℤ, Module.Finite A (EInf p q)) ∧
      (∀ p q : ℤ,
        ∃ e : ∀ (s : ℤ) (hs : 2 ≤ s) (_ht : max (p - a) (q - b + 1) < s),
          (E.page s hs).X (p, q) ≅ EInf p q,
        ∀ (s : ℤ) (hs : 2 ≤ s) (ht : max (p - a) (q - b + 1) < s)
          (hs' : 2 ≤ s + 1) (ht' : max (p - a) (q - b + 1) < s + 1),
          (E.page s hs).iCycles (p, q) ≫ (e s hs ht).hom =
            (E.page s hs).homologyπ (p, q) ≫
              (E.iso s (s + 1) (p, q) rfl hs).hom ≫ (e (s + 1) hs' ht').hom) ∧
      (∀ (T : ℤ → ModuleCat.{v} A) (F : ∀ n : ℤ, DecreasingFiltration (T n)),
        (∀ n : ℤ, (F n).IsFinite ∧ (F n).IsExhaustive ∧ (F n).IsSeparated) →
        (∀ p n : ℤ, Nonempty ((F n).gr p ≅ EInf p (n - p))) →
        (∀ n : ℤ, Module.Finite A (T n)) ∧
          ∀ n : ℤ, n < a + b → IsZero (T n)) := by
  sorry

end CategoryTheory.SpectralSequence
