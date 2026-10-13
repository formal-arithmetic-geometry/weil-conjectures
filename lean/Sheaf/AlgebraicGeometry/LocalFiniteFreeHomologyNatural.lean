/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel

/-! # Coefficient naturality for a local finite free resolution

Source: Stacks Project, Tags 08DL and 08DM. -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A bounded finite free resolution on an open computes restricted Ext
naturally in every coefficient sheaf.
Source: Stacks Project, Tag 08DL (restriction of derived internal Hom), and
Tag 08DM (finite locally free computation of derived internal Hom).
(blueprint: lem-sc-local-finite-free-homology-natural).

Proof: Use the functorial K-injective resolution of each coefficient single
complex. The localization comparison for derived internal Hom is natural in
the coefficient, as is its restriction to the open. Restriction is exact and
preserves K-injectives. Transport from the over site to the open subscheme.
Precomposition with the augmentation is a quasi-isomorphism on Hom into these
K-injectives. Since E is bounded with finite free terms, internal Hom from E
preserves acyclicity: finite free internal Hom is exact and only finitely many
source terms contribute to each total degree. The cone of the coefficient
resolution is acyclic, so postcomposition with that resolution is also a
quasi-isomorphism on Hom out of E. These are natural transformations whose
components are quasi-isomorphisms. Take homology, invert their componentwise
isomorphisms, and compose with the exact restriction homology comparison.
This gives a natural isomorphism of coefficient functors. All computations use
complexes and homology in the ambient supplied derived universe; no derived
category on the open in that universe is required. The zero resolution and
empty open are included. -/
theorem local_finite_free_homology_natural
    {Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (U : Y.Opens) (B : Y.Modules)
    (E : CochainComplex U.toScheme.Modules ℤ)
    (hbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hbelow : ∃ M : ℤ, ∀ p : ℤ, p < M → IsZero (E.X p))
    (hfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
        (ULift.{u} (Fin r))))
    (ε : E ⟶ (CochainComplex.singleFunctor U.toScheme.Modules 0).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj B)) [QuasiIso ε] (q : ℤ) :
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    Nonempty (S ⋙ (Functor.curry.obj H).obj (op (S.obj B)) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q ⋙
        Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙
        CochainComplex.singleFunctor U.toScheme.Modules 0 ⋙
        (homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf)).obj (op E) ⋙
        HomologicalComplex.homologyFunctor U.toScheme.Modules (ComplexShape.up ℤ) q) := by sorry

end AlgebraicGeometry
