/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-! # BertiniFiniteCoverTransverseComponent

Source: blueprint paragraph 3 of the finite-cover Bertini argument
(blueprint: lem-zl-bertini-finite-cover-transverse-component).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

set_option linter.unusedVariables false in
/-- An immersive system on the complement of finitely many points has a transverse
codimension-two intersection component on a connected finite etale cover.

Source: main-20261015, `lem-zl-bertini-finite-cover-curve.proof.md`, paragraph 3;
Stacks Project, Tag 0G4F, condition (3), and Tag 0B2G.
(blueprint: lem-zl-bertini-finite-cover-transverse-component).

Proof: the finite inverse image of S cannot exhaust the connected smooth scheme T:
its closed points have local dimension d at least two, whereas a finite space of
closed points has dimension zero. Choose a closed t outside it using the Jacobson
property, and put x = π(t). Both residue fields are k. Generation supplies a section
s₁ nonzero at x, which trivializes L nearby. In that frame, the coordinate ratios
of the given basis sections induce the local map to the standard projective chart.
The immersion makes the map on cotangent spaces surjective. Subtracting the values
at x times s₁ produces sections vanishing at x whose classes span its cotangent
space. Etaleness gives a surjection to the cotangent space at t. Both regular local
rings have dimension d. Choose two linear combinations with independent classes
at t. Nakayama extends their coefficients to a regular system of parameters; the
quotient by its first two elements is regular local of dimension d-2, hence a
domain. Their ideal is prime of height two. Contracting this prime to a trivializing
affine neighbourhood gives a minimal prime of the two-section ideal of height two.
The closure of its component in T is a maximal irreducible closed subset of the
intersection, has coheight two, and contains t, where s₁ does not vanish. -/
theorem bertini_finiteCover_transverse_component
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsAffine X] [ConnectedSpace X]
    [Smooth (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ℕ) (hd : 2 ≤ d) (hdim : X.IsPureDimension d)
    (T : Scheme.{u}) [ConnectedSpace T] (π : T ⟶ X) [IsFinite π] [Etale π]
    (S : Finset X) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (U₀ : X.Opens) (hU₀ : (U₀ : Set X) = (S : Set X)ᶜ)
    (L : X.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V]
    (r : ℕ) (b : Module.Basis (Fin r) k V) (ψ : V →+ Γ(L, ⊤))
    (hlinear : ∀ (c : k) (v : V),
      ψ (c • v) = (X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c) • ψ v)
    (hgen : Epi (((Scheme.Modules.tensorPullback U₀.ι).obj L).freeHomEquiv.symm
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (ψ (b i.down)))))))
    [IsImmersion (@ProjectiveSpace.homOfGeneratingSections
      (ULift.{u} (Fin r)) inferInstance U₀.toScheme (Spec (.of k))
      (U₀.ι ≫ (X ↘ Spec (.of k))) ((Scheme.Modules.tensorPullback U₀.ι).obj L)
      (Scheme.Modules.IsInvertible.of_iso
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U₀.ι)).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction U₀.ι)).app L).symm)
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (ψ (b i.down))))) hgen)] :
    letI : ((Scheme.Modules.tensorPullback π).obj L).IsInvertible :=
      Scheme.Modules.IsInvertible.of_iso
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction π)).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction π)).app L).symm
    ∃ (v₁ v₂ v₃ : V) (W : TopologicalSpace.IrreducibleCloseds T),
      Maximal (fun Z : TopologicalSpace.IrreducibleCloseds T ↦
        (Z : Set T) ⊆
          (Scheme.Modules.homOfGlobalSection ((Scheme.Modules.tensorPullback π).obj L)
            (Scheme.Modules.tensorSectionsUnit π L (ψ v₂))).zeroLocus.support ∩
          (Scheme.Modules.homOfGlobalSection ((Scheme.Modules.tensorPullback π).obj L)
            (Scheme.Modules.tensorSectionsUnit π L (ψ v₃))).zeroLocus.support) W ∧
      ¬ (W : Set T) ⊆
        (Scheme.Modules.homOfGlobalSection ((Scheme.Modules.tensorPullback π).obj L)
          (Scheme.Modules.tensorSectionsUnit π L (ψ v₁))).zeroLocus.support ∧
      Order.coheight W = 2 := by
  sorry

end AlgebraicGeometry
