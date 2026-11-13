/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.RingTheory.KoszulDualComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.RingTheory.KoszulRegularSequenceDualComplex
import WeilConjectures.AlgebraicGeometry.LocalFiniteFreeScalarHomology
import WeilConjectures.AlgebraicGeometry.AffineKoszulFiniteFreeResolution
import WeilConjectures.AlgebraicGeometry.AffineKoszulHomCoordinates

/-! # Affine scalar Ext and dual Koszul cohomology

Source: Stacks Project, Tag 0BQZ, local finite free Hom computation. -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Restriction of scalar Ext to an affine Koszul chart is the associated sheaf
of the cohomology of the integer-indexed dual Koszul complex (Stacks, Tags 0BQZ, 08DM). -/
theorem affine_koszul_scalar_ext_comparison
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (U : Y.affineOpens) (n : ℕ) (f : Fin n → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (q : ℤ) :
    let F : Y.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf)))
    Nonempty (F.over U.1 ≅
      (Scheme.Modules.overEquiv U.1).inverse.obj
        ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj
          ((ExteriorAlgebra.koszulDualCochainComplex (Γ(Y, U.1) : Type u) n f).homology q)))
    := by
  obtain ⟨ε, hε, _⟩ := ExteriorAlgebra.exists_koszul_quotient_augmentation
    (Γ(Y, U.1) : Type u) (i.ker.ideal U) n f hreg hf
  let := hε
  obtain ⟨hbounded, hfree, a, ha⟩ :=
    affine_koszul_finite_free_resolution i U n f ε
  let := ha
  obtain ⟨e⟩ := local_finite_free_scalar_homology U.1
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    _ hbounded hfree a q
  obtain ⟨c⟩ := affine_koszul_hom_coordinates U n f q
  exact ⟨e ≪≫ (Scheme.Modules.overEquiv U.1).inverse.mapIso c⟩

end AlgebraicGeometry
