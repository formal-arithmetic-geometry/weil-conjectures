/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Category.Grp.Abelian
import Sheaf.Algebra.Homology.HomComplexGlobalCochains
import Sheaf.Algebra.Homology.HomComplexProjections
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Ordinary global cohomology of a sheaf Hom complex

Source: Stacks Project, Tag 0A8Z and the global computation in Tag 08JA.
(blueprint: lem-pur-hom-complex-global-homotopy)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace CategoryTheory

/-- Ordinary zeroth cohomology of global cochains is naturally the group of homotopy classes.
Source: Stacks Project, Tag 0A8Z and Tag 08JA, first global-cochain computation.
(blueprint: lem-pur-hom-complex-global-homotopy)

Proof: take the projections furnished by `homComplex_projections_exists` once for the
whole bifunctor. Their product universal property identifies maps from the unit to
Hom(L,M)^n with families L^p → M^(p+n), additively. The differential formula identifies
this with the external Hom differential, as in `homComplex_global_cochains`. The map
formula for these same projections proves naturality under both precomposition and
postcomposition. Pass to degree-zero homology. The external Hom-complex homology
comparison identifies its elements with cocycles modulo coboundaries. Degree-zero
cocycles are chain maps, and coboundaries are precisely maps homotopic to zero.
`CohomologyClass.homAddEquiv` at zero, followed by the shift-zero isomorphism,
therefore identifies this group with morphisms in the homotopy category. On chain-map
representatives all three comparisons send pre- and postcomposition to composition;
surjectivity of the cocycle quotient proves naturality on homology. Assemble these
additive isomorphisms with `NatIso.ofComponents`. This calculation uses no K-flatness,
K-injectivity or boundedness, and applies to zero complexes as well. -/
theorem homComplex_global_homotopy
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
    let Γ := preadditiveCoyoneda.obj (op (SheafOfModules.unit R₀))
    let q := HomotopyCategory.quotient (SheafOfModules.{u} R₀) (ComplexShape.up ℤ)
    Nonempty ((Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
        Γ.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0) ≅
      q.op.prod q ⋙ Functor.uncurry.obj preadditiveCoyoneda) := by sorry

end CategoryTheory
