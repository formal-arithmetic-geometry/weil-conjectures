/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.SequentialDerivedInverseLimitCompleted
import Sheaf.Paper.CompletedKoszulReductionRoosTriangle
import Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism

/-! # The completion unit in a specified quotient Roos triangle

Source: blueprint order 1249, proof via Koszul reconstruction, and order 1248;
Stacks Tags 091Z and 099M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

/-- The complete object is isomorphic to any specified Roos limit, with its evaluations
normalized by the scalar adjunction unit.

Source: blueprint order 1249, steps 2 and 3; order 1248; Stacks Tags 091Z and 099M
(blueprint: lem-weil-pbc-completed-reconstruction-unit-comparison).
Proof: compute the strict quotient tower on M.complex. The Koszul-to-quotient
reconstruction comparison carries the explicit Koszul unit (u,0) to the tower of
ordinary quotient units. Exact countable products identify its mapping fibre with a
Roos triangle. Compare that triangle with L by rotating and completing the identities
on the two product vertices to a triangle morphism; its third component is invertible,
so unshifting gives an isomorphism compatible with L.p. Completeness makes the Koszul
unit invertible, and composing it with those comparisons gives e. At level n, the
K-flat scalar-extension counit, the degreewise identity restriction comparison and
M.realization identify the quotient unit with the derived adjunction unit. This is
exactly the displayed evaluation equation. The argument uses no boundedness of M,
no regularity of the generators, and no constancy assertion about a reduced tower.
For the zero ideal the constant quotient tower gives the identity unit; for the unit
ideal completeness forces the object to be zero and the same triangle argument applies. -/
theorem completedReconstructionUnitComparison {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = d.ideal)
    (hcomplete : IsCompletedIntrinsicallyDerivedComplete T d r f hf
      M.complex M.realization)
    (L : CompletedSequentialDerivedLimit T d (adicDatumModelTower T d M)) :
    ∃ e : K ≅ L.obj, ∀ n : ℕ,
      e.hom ≫ (L.p ≫ Pi.π (fun a : ℕ ↦ (adicDatumModelTower T d M).obj (op a)) n ≫
        (adicDatumModelRestriction T d M n).hom ≫
        (adicDatumRestriction T (adicDatumProjection T d n)).map
          (adicDatumModelReductionIso T d M n).inv) =
        (adicDatumAdjunction T (adicDatumProjection T d n)).unit.app K := by
  obtain ⟨p, δ, htriangle, hunit⟩ := completedKoszulReductionRoosTriangle T d M r f hf
  obtain ⟨ψ, hψp, hψδ⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism₁ _ _ htriangle L.distinguished
      (𝟙 _) (𝟙 _) (by simp)
  have hp : ψ ≫ L.p = p := by simpa using hψp.symm
  have hδ : δ ≫ ψ⟦(1 : ℤ)⟧' = L.δ := by simpa using hψδ
  have : IsIso ψ := isIso_derivedLimit_of_levelwise _ _ _ _ p L.p δ L.δ
    htriangle L.distinguished (fun _ ↦ 𝟙 _) (by simp) ψ
    (by simpa using hp) (by simpa using hδ)
  have : IsIso (completedIntrinsicCompletionMap T d r f M.complex M.realization) := hcomplete
  refine ⟨asIso (completedIntrinsicCompletionMap T d r f M.complex M.realization) ≪≫
    asIso ψ, fun n ↦ ?_⟩
  simpa only [Iso.trans_hom, asIso_hom, Category.assoc, reassoc_of% hp] using hunit n

end AlgebraicGeometry.Scheme
