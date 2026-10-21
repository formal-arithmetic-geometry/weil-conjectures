/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S6
-/
module

public import Sheaf.AlgebraicGeometry.PrescribedPointSystemData

/-!
# High-degree prescribed first-order linear systems

Source: Stacks Project, Tags 0FD5 and 0B5T, and the finite first-neighbourhood argument
in blueprint main-20261015, finite-cover-curve proof, paragraph 2.
(blueprint: lem-zl-prescribed-point-eventual-jet-system).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

noncomputable section

/-- The kernel system eventually generates off a finite set, immerses its complement,
and separates simultaneous first-order values. No smoothness or dimension assumption
is required here.

Source: Stacks Project, Tags 0FD5 and 0B5T; blueprint main-20261015,
finite-cover-curve proof, paragraph 2.
(blueprint: lem-zl-prescribed-point-eventual-jet-system).

Proof: Let L be the pullback of O(1). The closed projective embedding makes it very
ample; its n-th tensor power is canonically isomorphic to the pullback of O(n).
Form the reduced closed subscheme Z supported on the images of S. These images are
closed, since X and Y are finite type over the algebraically closed field and the
points of S are closed. Its ideal I and I squared are coherent on the Noetherian
scheme Y. Tag 0FD5 gives eventual generation and immersion for the kernel of
restriction to Z. The residue-fibre vanishing test is exactly that kernel. Choose a
finite basis, using finite-dimensionality of proper coherent global sections.

Tensor 0 -> I squared -> I -> I/I squared -> 0 with L to the n-th power.
Serre vanishing for I squared makes the map of global sections onto the quotient
surjective for all sufficiently large n. The quotient sheaf is supported on Z;
its global sections are the product of its stalks, by extension by zero from an
open excluding the other points. The stalk at x is the cotangent space tensored
with the line-bundle stalk. The quotient map sends a vanishing section to the
stated jet: in a frame its coefficient a maps to [a] tensor the frame generator.
Thus it is the simultaneous jet map, independently of the frame. Enlarge the
bound for both applications and transport the basis, generation and immersion
along the tensor-power isomorphisms and the open immersion X minus S -> Y minus Z.
-/
theorem exists_eventual_prescribedPoint_jetSystem
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (S : Finset X) (hS : S.Nonempty) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (N : ℕ) (Y : Scheme.{u}) [IsReduced Y]
    (c : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) [IsClosedImmersion c]
    (j : X ⟶ Y) [IsOpenImmersion j] (hdense : DenseRange j)
    (hchart : Set.range j = c ⁻¹' (ProjectiveSpace.standardOpen
      (ULift.{u} (Fin (N + 1))) (Spec (.of k)) ⟨0⟩ : Set _))
    (hover : j ≫ c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)) =
      X ↘ Spec (.of k)) :
    ∃ (n₀ : ℕ) (U : X.Opens),
      (∀ x : X, x ∈ U ↔ x ∉ S) ∧
      ∀ n : ℕ, n₀ ≤ n →
        ∃ (I : Type u) (_ : Fintype I) (s : I → Γ(prescribedPointTwist c n, ⊤)),
          (∀ v : Γ(prescribedPointTwist c n, ⊤),
            prescribedPointVanishes ((tensorPullback j).obj (prescribedPointTwist c n)) S
                (tensorSectionsUnit j (prescribedPointTwist c n) v) ↔
              ∃! a : I → k, prescribedPointCombination
                (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                (prescribedPointTwist c n) s a = v) ∧
          (∃ ht : Epi ((((tensorPullback (U.ι ≫ j)).obj
              (prescribedPointTwist c n)).freeHomEquiv).symm
                (prescribedPointRestrictedFamily (prescribedPointTwist c n) j U s)),
            IsImmersion (@ProjectiveSpace.homOfGeneratingSections I inferInstance
              U.toScheme (Spec (.of k)) (U.ι ≫ (X ↘ Spec (.of k)))
              ((tensorPullback (U.ι ≫ j)).obj (prescribedPointTwist c n))
              ((@id (∀ L : Y.Modules, L.IsInvertible → _)
                (invertible_pullback_tensor (U.ι ≫ j)).1) (prescribedPointTwist c n)
                ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist _ _ (n : ℤ))).2).2
              (prescribedPointRestrictedFamily (prescribedPointTwist c n) j U s) ht)) ∧
          Function.Surjective (fun a : I → k ↦ fun x : S ↦
            @prescribedPointJet X ((tensorPullback j).obj (prescribedPointTwist c n))
              ((@id (∀ L : Y.Modules, L.IsInvertible → _)
                (invertible_pullback_tensor j).1) (prescribedPointTwist c n)
                ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist _ _ (n : ℤ))).2).2
              x.val
              (tensorSectionsUnit j (prescribedPointTwist c n)
                (prescribedPointCombination
                  (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                  (prescribedPointTwist c n) s a))) := by
  sorry

end

end AlgebraicGeometry
