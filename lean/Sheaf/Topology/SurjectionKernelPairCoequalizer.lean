/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.Topology.Sheaves.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Surjections as coequalizers of kernel-pair covers

Source: literature/stacks-project/modules.tex, Lemma Tag 0CAI, proof at lines 3038--3046
(blueprint: lem-weil-pbc-sheaf-surjection-kernel-pair-coequalizer)
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace TopCat

/-- A surjection of sheaves of sets is the coequalizer of any epimorphic cover of
its kernel pair. Source: literature/stacks-project/modules.tex, Lemma Tag 0CAI,
proof at lines 3038--3046 (blueprint: lem-weil-pbc-sheaf-surjection-kernel-pair-coequalizer).

Proof:
1. The opens of `X`, with open covers and intersections as fibre products, form the
   site of def-weil-pbc-sites-and-cohomology. By
   lem-weil-pbc-site-sheaf-sets-limits-sectionwise, the pullback `K` is computed on
   sections as pairs `(a,b)` with `p(a) = p(b)`, with the two projections. Its
   pullback universal property gives `r ≫ p = s ≫ p`.
2. By lem-weil-pbc-site-sheaf-sets-epi-kernel-pair-coequalizer (Stacks Sites,
   Tag 086K), the epimorphism `p` is the coequalizer of these projections: every
   map `q : P ⟶ G` satisfying `r ≫ q = s ≫ q` factors uniquely through `p`.
3. Composing the pullback equality with `e` makes `(F,p)` a cofork for the
   composite pair. If `q` equalizes that pair, associativity and cancellation
   of the epimorphism `e` give `r ≫ q = s ≫ q`. Step 2 gives the unique map
   `F ⟶ G` factoring `q`. A cocone on a parallel pair is determined by its
   component on `P`, so this is exactly the colimit universal property of
   def-weil-pbc-category-colimit. -/
theorem surjection_kernel_pair_coequalizer
    (X : TopCat.{u}) (P F : X.Sheaf (Type (max u v))) (p : P ⟶ F) [Epi p]
    (R : X.Sheaf (Type (max u v))) (e : R ⟶ pullback p p) [Epi e] :
    Nonempty
      (IsColimit
        (Cofork.ofπ (f := e ≫ pullback.fst p p)
          (g := e ≫ pullback.snd p p) p
          (by
            rw [Category.assoc, Category.assoc]
            exact congrArg (fun q ↦ e ≫ q) (pullback.condition :
              pullback.fst p p ≫ p = pullback.snd p p ≫ p)))) := by
  sorry

end TopCat
