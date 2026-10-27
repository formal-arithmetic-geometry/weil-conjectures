/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.CategoryTheory.TruncationDescends

import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Naturality of canonical good-truncation stage comparisons

Source: Stacks Project, Derived Categories, Tag 0794, `proposition-left-derived-exists`,
the diagram after "The problem is that" and compatibility as the stage varies;
Homology, Tag 0118, canonical upper truncations.
(blueprint: lem-trf-good-truncation-stage-naturality).

The index `k : ℕ` denotes the positive stage `n = k + 1`. The canonical stage inclusions
are specified by their composites with the monomorphisms into the ambient complexes.
The isomorphisms `cE`, `cG` expose the inverses of the localized truncation inclusions,
so the formulas for `tE`, `tG` and `a` require no extra invertibility hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Canonical good-truncation comparisons for two supplied cohomological stage models
are isomorphisms compatible with stage transitions and with their augmentations into
arbitrary ambient complexes. No termwise bound or resolving class is assumed.

Source: Stacks Project, Derived Categories, Tag 0794, `proposition-left-derived-exists`,
the comparison diagram and compatibility as n varies; Homology, Tag 0118.
(blueprint: lem-trf-good-truncation-stage-naturality).

Proof:
1. Use functorial truncation and the natural successive inclusions from
   lem-weil-pbc-truncation-descends. On complexes, naturality gives
   T_n(f) followed by c_n = c_n followed by f, and k_n followed by c_(n+1) = c_n.
   The equality T_n(f) followed by k_n = k_n followed by T_(n+1)(f) holds below
   n by the original components, at n by restriction to cycles, and above n
   because the source is zero. Apply Q to these equalities.
2. By lem-weil-pbc-truncation-cohomology, c_n for E_n and G_n is a
   quasi-isomorphism: it is an isomorphism on cohomology through n, and both
   sides have zero cohomology above n. Naturality of c_n, the augmentation
   isomorphisms through n, and vanishing above n show that T_n(e_n) and T_n(g_n)
   are quasi-isomorphisms. The localization of def-weil-abstract-derived-category
   inverts them. This produces cE, cG, tE and tG with the exact formulas below.
3. Write C_n = Q(c_n) and B_n = Q(T_n(e_n)). Precompose the desired E transition
   equation by C_n. Replace c_n by k_n followed by c_(n+1), use naturality of
   c_(n+1), then u_n followed by e_(n+1) = e_n, and finally naturality of k_n.
   Both sides become Q(k_n of X) after B_n in the usual right-to-left notation.
   Cancel the invertible C_n. Repeat with G, g, v.
4. Naturality of c_n and the defining formula give tE_n followed by Q(c_n of X)
   equal to Q(e_n), and likewise for G and Y. The ambient truncation inclusions
   are never inverted.
5. Truncation preserves the quasi-isomorphism alpha by
   lem-weil-pbc-truncation-descends, so Q(T_n(alpha)) is invertible. Its naturality
   with k_n and c_n gives the transition square and the augmentation square.
6. Define a_n as tE_n followed by Q(T_n(alpha)) followed by the inverse of tG_n.
   This is an isomorphism. Substitute step 3 for E, step 5, and step 3 for G
   to obtain the a transition equation, cancelling only tG isomorphisms.
   For the augmentation equation, use step 4 for G, then the alpha square
   from step 5, and finally step 4 for E. This works in the ambient category.
7. E_n and G_n have the assumed upper cohomology bound n; both truncations
   have that bound by lem-weil-pbc-truncation-cohomology. Cohomology factors
   through Q by def-weil-abstract-derived-category, so the displayed derived
   objects have bounded above cohomology. Apply this also at the next stage.
   Nothing bounds the terms of E or G or the cohomology of X or Y.
-/
theorem good_truncation_stage_naturality
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (E G : ℕ → CochainComplex A ℤ)
    (uE : ∀ k : ℕ, E k ⟶ E (k + 1)) (vG : ∀ k : ℕ, G k ⟶ G (k + 1))
    (X Y : CochainComplex A ℤ) (e : ∀ k : ℕ, E k ⟶ X) (g : ∀ k : ℕ, G k ⟶ Y)
    (he : ∀ k : ℕ, uE k ≫ e (k + 1) = e k)
    (hg : ∀ k : ℕ, vG k ≫ g (k + 1) = g k)
    (hEvanish : ∀ (k : ℕ) (j : ℤ), (k : ℤ) + 1 < j → IsZero ((E k).homology j))
    (hGvanish : ∀ (k : ℕ) (j : ℤ), (k : ℤ) + 1 < j → IsZero ((G k).homology j))
    (heiso : ∀ (k : ℕ) (j : ℤ), j ≤ (k : ℤ) + 1 →
      IsIso (HomologicalComplex.homologyMap (e k) j))
    (hgiso : ∀ (k : ℕ) (j : ℤ), j ≤ (k : ℤ) + 1 →
      IsIso (HomologicalComplex.homologyMap (g k) j))
    (α : X ⟶ Y) (hα : QuasiIso α) :
    ∃ (iX : ∀ k : ℕ, X.truncLE ((k : ℤ) + 1) ⟶ X.truncLE ((k : ℤ) + 2))
      (iY : ∀ k : ℕ, Y.truncLE ((k : ℤ) + 1) ⟶ Y.truncLE ((k : ℤ) + 2)),
      (∀ k : ℕ, iX k ≫ X.ιTruncLE ((k : ℤ) + 2) = X.ιTruncLE ((k : ℤ) + 1)) ∧
      (∀ k : ℕ, iY k ≫ Y.ιTruncLE ((k : ℤ) + 2) = Y.ιTruncLE ((k : ℤ) + 1)) ∧
      ∃ (cE : ∀ k : ℕ, Q.obj ((E k).truncLE ((k : ℤ) + 1)) ≅ Q.obj (E k))
        (cG : ∀ k : ℕ, Q.obj ((G k).truncLE ((k : ℤ) + 1)) ≅ Q.obj (G k))
        (tE : ∀ k : ℕ, Q.obj (E k) ≅ Q.obj (X.truncLE ((k : ℤ) + 1)))
        (tG : ∀ k : ℕ, Q.obj (G k) ≅ Q.obj (Y.truncLE ((k : ℤ) + 1)))
        (a : ∀ k : ℕ, Q.obj (E k) ≅ Q.obj (G k)),
        (∀ k : ℕ, (cE k).hom = Q.map ((E k).ιTruncLE ((k : ℤ) + 1))) ∧
        (∀ k : ℕ, (cG k).hom = Q.map ((G k).ιTruncLE ((k : ℤ) + 1))) ∧
        (∀ k : ℕ, (tE k).hom =
          (cE k).inv ≫ Q.map (CochainComplex.truncLEMap (e k) ((k : ℤ) + 1))) ∧
        (∀ k : ℕ, (tG k).hom =
          (cG k).inv ≫ Q.map (CochainComplex.truncLEMap (g k) ((k : ℤ) + 1))) ∧
        (∀ k : ℕ, Q.map (uE k) ≫ (tE (k + 1)).hom = (tE k).hom ≫ Q.map (iX k)) ∧
        (∀ k : ℕ, Q.map (vG k) ≫ (tG (k + 1)).hom = (tG k).hom ≫ Q.map (iY k)) ∧
        (∀ k : ℕ, IsIso (Q.map (CochainComplex.truncLEMap α ((k : ℤ) + 1)))) ∧
        (∀ k : ℕ, (a k).hom = (tE k).hom ≫
          Q.map (CochainComplex.truncLEMap α ((k : ℤ) + 1)) ≫ (tG k).inv) ∧
        (∀ k : ℕ, Q.map (uE k) ≫ (a (k + 1)).hom = (a k).hom ≫ Q.map (vG k)) ∧
        (∀ k : ℕ, (a k).hom ≫ Q.map (g k) = Q.map (e k) ≫ Q.map α) ∧
        (∀ k : ℕ, ∃ b : ℤ, ∀ j : ℤ, b < j →
          IsZero ((homologyFunctor A j).obj (Q.obj (E k))) ∧
          IsZero ((homologyFunctor A j).obj (Q.obj (G k))) ∧
          IsZero ((homologyFunctor A j).obj (Q.obj (X.truncLE ((k : ℤ) + 1)))) ∧
          IsZero ((homologyFunctor A j).obj (Q.obj (Y.truncLE ((k : ℤ) + 1))))) := by
  sorry

end DerivedCategory
