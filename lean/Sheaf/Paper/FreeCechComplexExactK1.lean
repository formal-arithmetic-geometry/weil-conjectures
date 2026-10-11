/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!
# Exactness of the free presheaf Čech complex

Source: Stacks Project, `sites-cohomology.tex`, Lemmas 03F5 and 03AT
(blueprint: lem-weil-pbc-ringed-site-free-cech-complex-exact).
-/

@[expose] public section

universe u w r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The free presheaf Čech complex of a covering is exact in positive degrees.
The limiting cones `P` are the iterated fibre products. The maps `δ` delete one
factor, as specified by `hδ`. The isomorphisms `e` identify the terms of `K` with
coproducts of free representable module presheaves; `hd` specifies their differential.
Universe lifting in `uliftYoneda` merely raises the sets of representing morphisms.

Source: Stacks Project, `sites-cohomology.tex`, Lemmas 03F5 and 03AT
(blueprint: lem-weil-pbc-ringed-site-free-cech-complex-exact).
Proof:
1. Evaluate at any object W. Exactness of presheaves of modules is objectwise
   (def-weil-presheaf-modules-sheafification). The degree-p basis consists of a tuple
   of cover indices and a map from W to its fibre product. By `hd`, the differential
   is the alternating sum of deletion projections.
2. Decompose these maps by their composite phi : W -> U. By the universal property
   `hP`, maps into each fibre product over phi are tuples of lifts of phi to its
   factors (def-weil-pbc-sites-and-cohomology). The maps `δ` delete tuple entries.
3. Free modules on disjoint unions are direct sums. Thus K(W) is the direct sum,
   over phi, of the free O(W)-module tuple complexes on the lift sets S_phi.
   Homology commutes with these direct sums.
4. An empty S_phi contributes the zero complex. For a nonempty S_phi, insertion of
   one chosen lift is a contracting homotopy in positive degrees, by
   lem-weil-pbc-power-set-complex-contractible. Every summand therefore has zero
   positive-degree homology; objectwise exactness gives the conclusion. -/
theorem free_presheaf_cech_complex_exact
    (C : Type u) [SmallCategory C]
    (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Sheaf J.toGrothendieck RingCat.{max u w r})
    (I : Type w) (U : C) (Uι : I → C)
    (f : ∀ i : I, Uι i ⟶ U)
    (hS : Presieve.ofArrows Uι f ∈ J U)
    (P : ∀ (n : ℕ) (s : Fin (n + 1) → I),
      WidePullbackCone (fun j => f (s j)))
    (hP : ∀ (n : ℕ) (s : Fin (n + 1) → I), IsLimit (P n s))
    (δ : ∀ (n : ℕ) (s : Fin (n + 2) → I) (a : Fin (n + 2)),
      (P (n + 1) s).pt ⟶ (P n (s ∘ a.succAbove)).pt)
    (hδ : ∀ (n : ℕ) (s : Fin (n + 2) → I) (a : Fin (n + 2)) (j : Fin (n + 1)),
      δ n s a ≫ (P n (s ∘ a.succAbove)).π j = (P (n + 1) s).π (a.succAbove j))
    (K : ChainComplex (PresheafOfModules R.obj) ℕ)
    (e : ∀ n : ℕ,
      (∐ fun s : Fin (n + 1) → I =>
        (PresheafOfModules.free R.obj).obj (uliftYoneda.{max w r}.obj (P n s).pt)) ≅ K.X n)
    (hd : ∀ (n : ℕ) (s : Fin (n + 2) → I),
      Sigma.ι (fun t : Fin (n + 2) → I =>
        (PresheafOfModules.free R.obj).obj (uliftYoneda.{max w r}.obj (P (n + 1) t).pt)) s ≫
          (e (n + 1)).hom ≫ K.d (n + 1) n =
        ∑ a : Fin (n + 2), (-1 : ℤ) ^ (a : ℕ) •
          ((PresheafOfModules.free R.obj).map (uliftYoneda.{max w r}.map (δ n s a)) ≫
            Sigma.ι (fun t : Fin (n + 1) → I =>
              (PresheafOfModules.free R.obj).obj (uliftYoneda.{max w r}.obj (P n t).pt))
              (s ∘ a.succAbove) ≫ (e n).hom)) :
    ∀ (n : ℕ), 0 < n → K.ExactAt n := by
  sorry

end CategoryTheory
