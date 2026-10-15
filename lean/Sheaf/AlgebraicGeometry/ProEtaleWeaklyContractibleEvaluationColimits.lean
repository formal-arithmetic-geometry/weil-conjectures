/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.LeftExact
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Sheaf.Paper.SiteSheafificationSectionsLocal

/-!
# Evaluation at affine weakly contractible pro-etale objects

Source: Stacks Project, Tags 0946 (1), 03DA and 0935 (2)
(blueprint: lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Functor

namespace AlgebraicGeometry.Scheme.ProEt

/-- Evaluation of module sheaves at an affine weakly contractible object is exact
and preserves all small colimits. The filtered-colimit comparison is invertible
and natural in diagrams. Commutativity is forgotten only to use Mathlib's ringed-site
module category. Smallness is relative to the universe of section modules.

Source: Stacks Project, Tags 0946 (1), 03DA, 0935 (2), and 002F
(blueprint: lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits).

Proof:
1. By lem-weil-pbc-module-sheaves-colimits-forgetful, module cokernels are sheafified
   sectionwise cokernels. By lem-pc-sites-sheafification-underlying-sets and
   lem-weil-pbc-site-sheafification-sections-local, module epimorphisms have local
   section lifts, and hence their underlying set-sheaf maps are epimorphisms.
2. Weak contractibility makes these maps surjective on W-sections. Kernels are
   sectionwise by lem-weil-pbc-module-sheaves-limits-sectionwise. Factoring a map
   through its image proves preservation of cokernels and exactness.
3. Represent a section of a sheafified direct sum locally by finite-support tuples.
   Affineness and def-weil-pbc-proetale-site provide a finite affine refinement of
   the covering. The union of the supports of these representatives is finite.
4. Local equality after sheafification and separatedness make each coordinate agree
   on overlaps. Glue coordinates to obtain surjectivity of the direct-sum comparison.
   The same local-equality argument proves injectivity, also for the empty sum.
5. Present any small diagram colimit as the cokernel of the difference of the two
   maps from the sum over arrows to the sum over objects. Preservation of sums and
   cokernels identifies this with the colimit presentation of the evaluated diagram.
   This includes the empty diagram, by def-weil-pbc-category-colimit.
6. Both sides of the comparison square agree on every colimit inclusion, hence are
   equal by the colimit universal property. Specialize to filtered diagrams. -/
theorem affine_weaklyContractible_evaluation_colimits
    (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1})
    (W : X.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op W))) :
    PreservesFiniteLimits (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)) ∧
    PreservesFiniteColimits (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)) ∧
    PreservesColimitsOfSize.{u + 1, u + 1}
      (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)) ∧
    (∀ (K : Type (u + 1)) [SmallCategory K] [IsFiltered K]
      (D : K ⥤ ringedSiteModules.{u + 1} ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)),
      IsIso (colimit.post D (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)))) ∧
    (∀ (K : Type (u + 1)) [SmallCategory K] [IsFiltered K]
      (D D' : K ⥤ ringedSiteModules.{u + 1} ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (α : D ⟶ D'),
      colimit.post D (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)) ≫
          (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)).map
            (colim.map α) =
        colim.map (whiskerRight α (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W))) ≫
          colimit.post D' (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W))) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
