/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.FinitePresentation

/-! # Realizing affine algebraic module models
Source: Stacks Project, Tags 01ZR and 05N7. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Realize an algebraic finite-presentation model of sections as an affine sheaf.
Source: Stacks Project, Modules on Schemes Tag 01I6; Limits Tag 01ZR, affine proof.
(blueprint: lem-pc-fp-affine-sections-realization).

Proof: Transport Q to Spec of the global-section ring of X and take its associated
quasi-coherent sheaf; pull it back along the canonical isomorphism X to that
spectrum. A finite presentation of Q gives a finite global presentation of the
associated sheaf, so it is finitely presented. The affine pullback/tensor comparison
identifies the sections of its pullback along g with scalar extension of Q.
Compose this with e. Both sheaves on Y are quasi-coherent, hence the affine module
equivalence lifts that section isomorphism to an isomorphism of sheaves. The
construction uses Q itself and its associated sheaf, not an arbitrary witness of
existence. Empty affine schemes and zero modules follow from the same equivalence. -/
theorem exists_finitePresentation_affine_sections_realization
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : Y ⟶ X)
    (P : Y.Modules) (hPq : P.IsQuasicoherent)
    (Q : ModuleCat.{u} Γ(X, ⊤)) (hQ : Module.FinitePresentation Γ(X, ⊤) Q)
    (e : Nonempty ((ModuleCat.extendScalars g.appTop.hom).obj Q ≅
      ModuleCat.of Γ(Y, ⊤) Γ(P, ⊤))) :
    ∃ N : X.Modules, N.IsFinitePresentation ∧ N.IsQuasicoherent ∧
      Nonempty ((Scheme.Modules.pullback g).obj N ≅ P) := by sorry

end AlgebraicGeometry
