/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S6
-/
module

public import Sheaf.AlgebraicGeometry.PrescribedPointSystemData

/-!
# Bertini for a linear system with finite prescribed base locus

Source: Stacks Project, Tag 0FD6, and blueprint main-20261015,
finite-cover-curve proof, paragraph 2, first derivative conditions.
(blueprint: lem-zl-prescribed-point-bertini-open).
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The smoothness and nonzero-jet open for a finite linear system with prescribed
base points. The ambient smooth scheme need not be affine or connected.

Source: Stacks Project, Tag 0FD6; blueprint main-20261015, finite-cover-curve proof,
paragraph 2, derivative conditions at the prescribed points.
(blueprint: lem-zl-prescribed-point-bertini-open).

Proof: Apply Bertini smoothness to the system on the complement U. At each closed
base point, smoothness and pure dimension identify the dimension of the cotangent
fibre with d, which is positive. The invertible stalk is free of rank one, so its
jet module is nonzero. The jet map on the vanishing subspace is k-linear: changing
a stalk frame cancels between the two tensor factors. Each zero-jet locus is
therefore a linear closed subset of affine coefficient space. Choose nonzero
vectors at every base point and lift the tuple by simultaneous jet surjectivity.
The complements of these finitely many zero-jet loci have nonempty intersection.
Intersect this open with the Bertini open; affine space over k is irreducible, so
the intersection is still nonempty. At each base point the cotangent map to the
relative differential fibre is an isomorphism (the residue field is k). Hence
a nonzero jet gives a nonzero differential of the local equation; the smooth
hypersurface criterion supplies a smooth neighbourhood. Together with the open
complement of the base points these neighbourhoods cover the member, which is
smooth. The resulting coefficient open has both asserted properties.
-/
theorem exists_open_prescribedPoint_bertini
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [Smooth (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ℕ) (hd : 2 ≤ d) (hdim : X.IsPureDimension d)
    (S : Finset X) (hS : S.Nonempty) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) (j : X ⟶ Y)
    (hover : j ≫ f = X ↘ Spec (.of k))
    (M : Y.Modules) [M.IsInvertible] [((tensorPullback j).obj M).IsInvertible]
    (U : X.Opens) (hU : ∀ x : X, x ∈ U ↔ x ∉ S)
    {I : Type u} [Fintype I] (s : I → Γ(M, ⊤))
    (hvan : ∀ a : I → k, prescribedPointVanishes ((tensorPullback j).obj M) S
      (tensorSectionsUnit j M (prescribedPointCombination f M s a)))
    (hgen : ∃ ht : Epi ((((tensorPullback (U.ι ≫ j)).obj M).freeHomEquiv).symm
        (prescribedPointRestrictedFamily M j U s)),
      @IsImmersion U.toScheme _
        (@ProjectiveSpace.homOfGeneratingSections I inferInstance U.toScheme
          (Spec (.of k)) (U.ι ≫ (X ↘ Spec (.of k)))
          ((tensorPullback (U.ι ≫ j)).obj M)
          ((invertible_pullback_tensor (U.ι ≫ j)).1 M).2
          (prescribedPointRestrictedFamily M j U s) ht))
    (hjet : Function.Surjective (fun a : I → k ↦ fun x : S ↦
      prescribedPointJet ((tensorPullback j).obj M) x.val
        (tensorSectionsUnit j M (prescribedPointCombination f M s a)))) :
    ∃ O : (Spec (CommRingCat.of (MvPolynomial I k))).Opens,
      (O : Set (Spec (CommRingCat.of (MvPolynomial I k)))).Nonempty ∧
      ∀ a : I → k, Set.range (bertiniCoefficientPoint (k := k) a) ⊆ (O : Set _) →
        Smooth ((prescribedPointMember f j M s a).subschemeι ≫ (X ↘ Spec (.of k))) ∧
        ∀ x ∈ S, prescribedPointJet ((tensorPullback j).obj M) x
          (tensorSectionsUnit j M (prescribedPointCombination f M s a)) ≠ 0 := by
  sorry

end

end AlgebraicGeometry
