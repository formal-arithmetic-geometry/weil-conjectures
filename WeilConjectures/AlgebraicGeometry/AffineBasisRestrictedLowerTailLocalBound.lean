/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.AlgebraicGeometry.AffineScheme

import WeilConjectures.AlgebraicGeometry.AffineBasisRestrictedLowerTailLocalBoundAux
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Local cohomological bound for a restricted lower tail
Source: Stacks Project, Tags 0D64, 01E1 and 03FD. -/

@[expose] public section
universe u wC wV
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
namespace AlgebraicGeometry

/-- The restriction of a lower tail has local cohomological bound zero on an affine basis.
Source: Stacks Project, Tag 0D64, Tag 01E1 (restriction
of injectives), and Tag 03FD (module versus abelian cohomology). -/
theorem affineBasisRestrictedLowerTail_local_bound
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wV} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    (F : CochainComplex X.Modules ℤ)
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1)))
    (a : ℤ) :
    let t := DerivedCategory.TStructure.t
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let E := (schemeOpenRestriction X V).mapDerivedCategory.obj
      ((t.truncLT a).obj (DerivedCategory.Q.obj F))
    ∃ (B : Set (Opens V.toScheme)),
      IsTopologicalBasis ((fun U : Opens V.toScheme => (U : Set V.toScheme)) '' B) ∧
      ∀ (U : Opens V.toScheme), U ∈ B → ∀ (p : ℕ), 0 < p → ∀ (q : ℤ), q < 0 →
        IsZero ((RingedSpace.openModuleCohomology V.toScheme.toRingedSpace p U).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) q).obj E)) := by
  dsimp only
  let B : Set (Opens V.toScheme) := V.toScheme.affineOpens
  refine ⟨B, ?_, ?_⟩
  · exact V.toScheme.isBasis_affineOpens
  · intro U hU p hp q hq
    apply affineBasisRestrictedLowerTail_local_vanishing X V hV F hhomology a U hU p hp q hq

end AlgebraicGeometry
