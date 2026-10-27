/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal

/-! # Pseudo-coherent complexes on algebraic spaces

Source: Stacks Project, sites-cohomology.tex, Tag 08FT; spaces-perfect.tex, Tag 0A8A;
perfect.tex, Tags 08E5 and 08E7.
(blueprint: def-sfb-space-pseudocoherent-complex).
The affine etale basis is the already recorded small ringed model. Bounds and finite
ranks vary with the covering object, and ranks also vary with the degree.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [instance] CategoryTheory.module_overFunctor_preservesZero
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.AlgebraicSpace

/-- Etale-local bounded-above finite-free models of a derived object.
Source: Stacks Project, Tag 08FT and the scheme characterization, Tags 08E5 and 08E7
(blueprint: def-sfb-space-pseudocoherent-complex).
A representative is fixed only existentially. On every covering member the model
maps quasi-isomorphically to its exact slice restriction; no global bound is required. -/
def IsPseudoCoherent {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] (K : X.DerivedModules) : Prop :=
  ∃ P : CochainComplex X.SmallModules ℤ,
    Nonempty (K ≅ DerivedCategory.Q.obj P) ∧
    ∀ V : X.SmallEtaleModel, ∃ T : Sieve V, T ∈ X.smallEtaleModelTopology V ∧
      ∀ (U : X.SmallEtaleModel) (f : U ⟶ V), T f →
        ∃ F : CochainComplex
            (SheafOfModules.{u} (X.smallStructureRings.over U)) ℤ,
          (∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (F.X n)) ∧
          (∀ n : ℤ, ∃ r : ℕ, Nonempty (F.X n ≅ SheafOfModules.free
            (R := X.smallStructureRings.over U) (ULift.{u} (Fin r)))) ∧
          ∃ α : F ⟶ ((SheafOfModules.overFunctor.{u} X.smallStructureRings U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P, QuasiIso α

end AlgebraicGeometry.AlgebraicSpace
