/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Topology.RingedSpaceModuleCohomology
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
import Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import Sheaf.Paper.PQFCohomology
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation
import Sheaf.Topology.RingedSpaceModuleEnoughInjectives

/-! # Natural comparison of module and abelian cohomology

Source: Stacks Project, sites-cohomology.tex, Tag 03FD.
(blueprint: lem-sc-module-abelian-zariski-cohomology).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
namespace AlgebraicGeometry

/-- Module cohomology and abelian sheaf cohomology are naturally isomorphic.

Source: Stacks Project, sites-cohomology.tex, Lemma Tag 03FD.
(blueprint: lem-sc-module-abelian-zariski-cohomology)

Proof: Choose an injective resolution of each module sheaf. Forgetting to abelian sheaves
is exact, and every forgotten injective module is acyclic for global sections. Thus the
same global-sections complex computes both cohomologies. The acyclic-resolution comparison
provides the component isomorphisms. A module morphism lifts to a chain map of resolutions;
the induced map on the common complex computes both cohomology maps. Independence of the
lift up to homotopy proves the naturality squares. Assemble these component isomorphisms
into a natural isomorphism. The componentwise comparison comes from the common resolution
complex. No degree-zero normalization is asserted here. -/
theorem zariskiModuleAbelianCohomologyNatural (X : Scheme.{u}) (q : ℕ) :
    Nonempty ((RingedSpace.moduleCohomology X.toRingedSpace q ⋙
        forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
          AddCommGrpCat.{u}) ≅
      (SheafOfModules.toSheaf (moduleRings X.toRingedSpace) ⋙
        @CategoryTheory.Sheaf.cohomologyPresheafFunctor.{u, u, u}
          (Opens X.carrier) inferInstance (Opens.grothendieckTopology X.carrier)
          inferInstance
          (@hasExt_of_enoughInjectives _ _ _ inferInstance
            (@IsGrothendieckAbelian.enoughInjectives _ _ _
              (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
                (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))) q ⋙
        (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))) := by
  sorry

end AlgebraicGeometry
