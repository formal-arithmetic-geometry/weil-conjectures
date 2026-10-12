/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Sheaf.CategoryTheory.PushoutShortExactSequence

/-!
# Injective resolutions of short exact sequences of bounded-below complexes

Source: Stacks Project, `derived.tex`, Lemma Tag 013T (lemma-injective-resolution-ses)
(blueprint: lem-weil-pbc-injective-resolution-ses-complexes).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- In an abelian category with enough injectives, a degreewise short exact sequence of
bounded-below cochain complexes admits compatible injective resolutions.

Source: Stacks Project, `derived.tex`, Lemma Tag 013T, line 6571, main assertion and
part (2); injective resolutions of complexes are as in Section Tag 013G.

Proof (the eleven steps of the DAG node, expanding Stacks proof Steps 1--2):
1. Resolve A by a complex I₁ of injectives vanishing below zero, with quasi-isomorphism
   φ₁, using lem-weil-pbc-complex-injective-resolution-mono at lower bound zero.
2. By lem-weil-pbc-cochain-complexes-degreewise-exact, form the pushout along φ₁ in
   the abelian category of complexes (lem-weil-pbc-pushout-short-exact-sequence).
   Obtain I₁ → E → D, with maps ι, p and v : B → E. The row is degreewise short exact,
   v f = ι φ₁, p v = g, and E vanishes below zero since I₁ and D do.
3. The long exact cohomology sequences (lem-weil-pbc-complex-ses-homology-long-exact)
   and their naturality (lem-weil-pbc-complex-ses-long-exact-naturality) give a morphism
   of long exact sequences with outer vertical maps φ₁ and the identity of D.
   The five lemma (lem-weil-pbc-five-lemma) shows that v is a quasi-isomorphism.
4. Split I₁ⁿ → Eⁿ → Dⁿ using lem-weil-pbc-ses-injective-kernel-splits. Choose π and s
   with πι = id, ps = id, ιπ + sp = id and πs = 0.
5. By lem-weil-pbc-degreewise-split-connecting-morphism, δⁿ = πⁿ⁺¹ d_Eⁿ sⁿ defines
   δ : D → I₁[1], and in the splitting the differential of E has diagonal entries
   d_I₁, d_D and upper-right entry δ.
6. Resolve D by a degreewise monomorphic quasi-isomorphism f₃ : D → I₃, with I₃
   injective and zero below zero (lem-weil-pbc-complex-injective-resolution-mono).
7. Resolve I₁ by itself. The bounded-below injective complex I₁[1] admits a lift
   δ' : I₃ → I₁[1] with δ' f₃ = δ by lem-weil-pbc-lift-along-injective-quasi-iso.
8. Define I₂ⁿ = I₁ⁿ ⊞ I₃ⁿ with differential matrix (d_I₁, δ'; 0, d_I₃). Its square
   is zero because δ' is a cochain map to the shift. Its terms are injective by
   lem-weil-pbc-product-injectives and vanish below zero. The inclusion j and
   projection q are cochain maps and form short exact rows (def-sp-abelian).
9. Set ψⁿ = jⁿ πⁿ + εⁿ f₃ⁿ pⁿ, where ε is the second inclusion. The matrix formula
   and δ' f₃ = δ make ψ : E → I₂ a cochain map with ψι = j and qψ = f₃p.
10. Apply lem-weil-pbc-complex-ses-homology-long-exact and
    lem-weil-pbc-complex-ses-long-exact-naturality to (id, ψ, f₃). The outer maps
    on cohomology are isomorphisms, so lem-weil-pbc-five-lemma makes ψ a quasi-isomorphism.
11. Put φ₂ = ψv and φ₃ = f₃. Composition preserves the cohomology isomorphisms;
    φ₂f = jφ₁ and qφ₂ = φ₃g follow from the pushout and ψ identities. The three
    complexes and the degreewise short exact row have the required properties.
(blueprint: lem-weil-pbc-injective-resolution-ses-complexes). -/
theorem exists_injective_resolution_ses_complexes
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (A B D : CochainComplex C ℤ)
    (f : A ⟶ B) (g : B ⟶ D)
    (hA : ∀ n : ℤ, n < 0 → IsZero (A.X n))
    (hB : ∀ n : ℤ, n < 0 → IsZero (B.X n))
    (hD : ∀ n : ℤ, n < 0 → IsZero (D.X n))
    (hSES : ∃ hfg : f ≫ g = 0, ∀ n : ℤ,
      ((ShortComplex.mk f g hfg).map
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).ShortExact) :
    ∃ (I₁ I₂ I₃ : CochainComplex C ℤ)
      (j : I₁ ⟶ I₂) (q : I₂ ⟶ I₃)
      (φ₁ : A ⟶ I₁) (φ₂ : B ⟶ I₂) (φ₃ : D ⟶ I₃),
      (∀ n : ℤ, n < 0 → IsZero (I₁.X n)) ∧
      (∀ n : ℤ, n < 0 → IsZero (I₂.X n)) ∧
      (∀ n : ℤ, n < 0 → IsZero (I₃.X n)) ∧
      (∀ n : ℤ, Injective (I₁.X n)) ∧
      (∀ n : ℤ, Injective (I₂.X n)) ∧
      (∀ n : ℤ, Injective (I₃.X n)) ∧
      (∃ hjq : j ≫ q = 0, ∀ n : ℤ,
        ((ShortComplex.mk j q hjq).map
          (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).ShortExact) ∧
      QuasiIso φ₁ ∧ QuasiIso φ₂ ∧ QuasiIso φ₃ ∧
      f ≫ φ₂ = φ₁ ≫ j ∧ g ≫ φ₃ = φ₂ ≫ q := by
  sorry

end CategoryTheory
