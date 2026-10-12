/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.DirectSum.Basic
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import Sheaf.AlgebraicGeometry.GlobalDerivedHom
import Sheaf.CategoryTheory.DerivedModuleDirectSums

/-! # Zeroth derived global sections of a coproduct
Source: Stacks Project, Tag 09M1, proof of Proposition perfect-proposition-compact-is-perfect,
first paragraph (blueprint: lem-pc-derived-global-sections-cohomology-coproduct).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite DirectSum

namespace AlgebraicGeometry

open Classical in
/-- Zeroth derived global sections commutes with coproducts of quasi-coherent complexes.
Source: Stacks Project, Tag 09M1, proof of Proposition perfect-proposition-compact-is-perfect,
first paragraph (blueprint: lem-pc-derived-global-sections-cohomology-coproduct).
Proof: Let a:X → Spec(ULift ℤ) be the structure morphism. Quasi-compactness and
quasi-separatedness of X make a quasi-compact and quasi-separated. Derived direct image
preserves the displayed ambient coproduct of quasi-coherent complexes. The affine derived
equivalence on Spec(ULift ℤ) computes global sections of Ra_* by module complexes.
Derived global sections of Ra_* are those of the original complex, by composition of
pushforward and the injective-resolution computation. The affine equivalence preserves
coproducts, which are represented termwise in module complexes. Exactness of module sums
identifies their H^0 with the sum of their H^0. Forgetting the global-section ring action
preserves and reflects this bijection. All comparisons are natural in the coprojections,
so their composite is the displayed DirectSum.toAddMonoid map. For the empty family both
sides are zero; the same argument applies to zero summands and arbitrary shifts. -/
theorem derivedGlobalSections_cohomology_coproduct (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    let F := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) 0 ⋙
      forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
    ∀ (I : Type u) (E : I → schemeDerivedQCohCategory X)
      (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S),
      IsColimit (Cofan.mk S ι) →
      Function.Bijective (DirectSum.toAddMonoid (fun i ↦ (F.map (ι i)).hom) :
        (⨁ i : I, F.obj (E i).obj) →+ F.obj S) := by sorry

end AlgebraicGeometry
