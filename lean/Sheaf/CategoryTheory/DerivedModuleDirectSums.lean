/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Direct sums of module complexes in the derived category

Source: Stacks Project, Injectives, Lemma 07D9 (clauses (1)-(2)) (blueprint:
lem-pc-derived-module-direct-sums).
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- (blueprint: lem-pc-derived-module-direct-sums) Let `R` be a ring and let
`D(R)` be the derived category of `R`-modules. For a family of cochain complexes
`K` indexed by `I`, the image under `DerivedCategory.Q` of the termwise
coproduct complex, together with the images of its coprojections, is a
coproduct of the `Q.obj (K i)` in `D(R)`. Following Stacks Project,
Injectives, Lemma 07D9: first form the complex degreewise by direct sums,
with differentials and inclusions induced from the summands. Next use the
Grothendieck abelian property of modules and exactness of filtered colimits
to show direct sums are exact; hence cohomology and quasi-isomorphisms
commute with these sums. Finally resolve an arbitrary target by a
K-injective complex, identify derived morphisms into it with homotopy
morphisms, and apply the degreewise coproduct property for chain maps and
homotopies to obtain the universal property in the derived category. -/
theorem derivedModuleDirectSums (R : Type u) [Ring R]
    [HasDerivedCategory (ModuleCat.{max u v} R)] (I : Type v)
    (K : I → CochainComplex (ModuleCat.{max u v} R) ℤ) :
    Nonempty (IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ K))
      (fun i => DerivedCategory.Q.map (Sigma.ι K i)))) := by
  sorry

end CategoryTheory
