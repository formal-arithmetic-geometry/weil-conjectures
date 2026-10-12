/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel
import Sheaf.Paper.AffineProjectiveComplexDerivedHom

/-! # Affine RHom of a pseudo-coherent complex is quasi-coherent

Source: Stacks Project, Tag 0A6H, clauses (1) and (3)(a)
(blueprint: lem-sc-affine-pseudo-coherent-rhom-qcoherent).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace CategoryTheory

/-- Termwise tilde into the shared sheaf carrier preserves zero morphisms.
Source: Stacks Project, Tag 0A6H, affine calculation
(blueprint: lem-sc-affine-pseudo-coherent-rhom-qcoherent).

Proof: tilde is additive (Mathlib's tilde.functor Additive instance). Changing the
category instance to the shared SheafOfModules carrier changes neither the underlying
morphisms nor zero; therefore the image of each zero morphism is zero. -/
theorem affineTildeSheaf_preservesZeroMorphisms (R : Type u) [CommRing R] :
    (@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
      (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
        (tilde.functor (CommRingCat.of R))).PreservesZeroMorphisms := by
  sorry

attribute [instance] affineTildeSheaf_preservesZeroMorphisms

/-- Affine computation of derived internal Hom.
Source: Stacks Project, Tag 0A6H, clauses (1) and (3)(a)
(blueprint: lem-sc-affine-pseudo-coherent-rhom-qcoherent).

Proof:
1. Replace the bounded-above finite-projective representative by a homotopy equivalent
   bounded-above finite-free complex using complementary projectives (Stacks Tag 064U).
2. Truncate the second representative below its cohomological lower bound. The ordinary
   module Hom complex computes derived Hom by lem-sc-affine-projective-complex-derived-hom.
3. Termwise tilde carries the homotopy equivalence to a homotopy equivalence. Apply
   lem-sc-derived-hom-finite-free-model. In each degree only finitely many Hom factors
   occur, and finite-free Hom and the matrix differentials commute with tilde.
4. By lem-weil-pbc-localization-module-exact and
   lem-weil-pbc-spec-module-tilde-sections, cohomology commutes with tilde on principal opens.
5. The associated cohomology sheaves are quasi-coherent by
   lem-weil-pbc-spec-module-tilde-sections and vanish sufficiently far below, since a
   nonzero Hom factor requires p ≤ b and p + n ≥ a. -/
theorem affinePseudoCoherentRHomQuasiCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))]
    (P L : DerivedCategory (ModuleCat.{u} R))
    (p l : CochainComplex (ModuleCat.{u} R) ℤ)
    (_hp : ∃ b : ℤ, p.IsStrictlyLE b)
    (_hfinite : ∀ i : ℤ, Module.Finite R (p.X i))
    (_hprojective : ∀ i : ℤ, Module.Projective R (p.X i))
    (_hL : ∃ a : ℤ, L.IsGE a)
    (_eP : Nonempty (DerivedCategory.Q.obj p ≅ P))
    (_eL : Nonempty (DerivedCategory.Q.obj l ≅ L))
    (c : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : ∀ n : ℤ, c.X n ≅ ModuleCat.of R (CochainComplex.HomComplex.Cochain p l n))
    (_hc : ∀ n m : ℤ, c.d n m ≫ (e m).hom =
      (e n).hom ≫ ModuleCat.ofHom (CochainComplex.HomComplex.δ_hom R p l n m)) :
    Nonempty ((derivedInternalHom (Opens.grothendieckTopology
        (Spec (CommRingCat.of R))) (Spec (CommRingCat.of R)).sheaf).obj
      (op (DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj p)),
        DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj l)) ≅
      DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj c)) ∧
    schemeDerivedQCohProperty (Spec (CommRingCat.of R))
      ((derivedInternalHom (Opens.grothendieckTopology (Spec (CommRingCat.of R)))
        (Spec (CommRingCat.of R)).sheaf).obj
      (op (DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj p)),
        DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj l))) ∧
    ∃ a : ℤ,
      ((derivedInternalHom (Opens.grothendieckTopology (Spec (CommRingCat.of R)))
        (Spec (CommRingCat.of R)).sheaf).obj
      (op (DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj p)),
        DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj l))).IsGE a := by
  sorry

end CategoryTheory
