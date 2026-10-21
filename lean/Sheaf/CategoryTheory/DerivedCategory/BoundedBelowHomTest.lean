/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Bounded-below objects detect derived isomorphisms

Source: Weil conjectures blueprint, main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, final composition/open-locality paragraph
(blueprint: lem-sf-bounded-below-hom-test).

The derived category is ordinary and unbounded. Boundedness below of a test object
is expressed directly by eventual vanishing of its cohomology objects.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Postcomposition tested on every shift of every bounded-below object detects
isomorphisms in the ordinary unbounded derived category of module sheaves.

Source: Weil conjectures blueprint, main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, final composition/open-locality paragraph
(blueprint: lem-sf-bounded-below-hom-test).

Proof:
1. Represent an arbitrary derived object X by a complex K. Its stupid lower
   truncations E_r = sigma_{ge -r} K are bounded below, form an increasing sequence,
   and have degreewise colimit K: in each degree the diagram is eventually constant.
   Use def-weil-abstract-derived-category, def-kun-truncations and
   def-weil-pbc-category-colimit.
2. By lem-kun-complex-colimit-hocolim, P = Q(direct sum E_r) is the derived coproduct
   of Q(E_r), and the telescope supplies a distinguished triangle
   P --u--> P --j--> X --d--> P[1], with u = 1 - s.
3. Consecutive composites vanish by TR3 applied to an identity triangle and by
   rotation (def-weil-triangulated-category). In particular j u = d j = v d = 0,
   where v = -u[1] is the last arrow of the rotated triangle.
4. The coproduct universal property identifies Hom(P,W) with the product of
   Hom(Q(E_r),W). The hypotheses at shifts 0 and 1 therefore give bijections for
   Hom(P,-) and Hom(P[1],-). Use def-weil-pbc-category-colimit and the shift
   equivalence of def-weil-triangulated-category; no compactness is needed.
5. For g : X -> G, lift g j to b : P -> B. Injectivity gives b u = 0.
   Clause (i) of lem-weil-pbc-hom-out-of-triangle-exact supplies c : X -> B
   with c j = b. Clause (ii) factors g - alpha c through d. Lift its factor
   from P[1] to B to obtain a lift of g. This proves surjectivity on Hom(X,-).
6. If alpha f = 0, injectivity on Hom(P,-) gives f j = 0. Clause (ii) writes
   f = k d. Applied to the rotated triangle, the same clause writes alpha k = r v.
   Lift r to t : P[1] -> B. Injectivity gives k = t v, hence f = t v d = 0.
   Taking differences proves injectivity on Hom(X,-).
7. Surjectivity at X = G gives beta with alpha beta = 1. Injectivity at X = B
   gives beta alpha = 1, so alpha is an isomorphism. Neither B nor G is bounded. -/
theorem isIso_of_boundedBelow_hom_bijective
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    {B G : DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))}
    (α : B ⟶ G)
    (hα : ∀ H : DerivedCategory
        (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)),
      (∃ a : ℤ, ∀ q : ℤ, q < a → IsZero ((homologyFunctor _ q).obj H)) →
      ∀ n : ℤ, Function.Bijective (fun f : H⟦n⟧ ⟶ B ↦ f ≫ α)) :
    IsIso α := by
  sorry

end DerivedCategory
