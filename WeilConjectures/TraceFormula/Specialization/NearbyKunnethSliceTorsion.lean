/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFormula

/-!

# The generic-slicing step of Gabber's Künneth formula modulo `ϖ`

WIP (statement only; proof in progress).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k' : Type u}
  [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

set_option hygiene false in
/-- The condensed field `𝔽̲_E`. -/
local notation "𝔽" => Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E.1)

/-- WIP: **the generic-slicing step modulo `ϖ`** (blueprint `sk-prop-tf-nearby-external-kunneth`,
identification (2) and projection formula (3), coefficients `𝔽_E`): if the Künneth map of the
geometric slice of the product along a coordinate `b` of `M` is invertible, so is the pullback of
`Π_{A,B}` to the special fibre of the slice of `P`. -/
theorem isIso_map_kunnethMap_of_isIso_sliceFst_residueField (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qM)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj 𝔽 X))}
    (hA : boundedConstructible (condensedRingObj 𝔽 M.generic) (L((M.ε)^*⟦𝔽⟧).obj A))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj 𝔽 Y))}
    (hB : boundedConstructible (condensedRingObj 𝔽 N.generic) (L((N.ε)^*⟦𝔽⟧).obj B))
    (h : IsIso (kunnethMap 𝔽 (sliceFst hM hP hb) (sliceSnd hN hpb hP hgen hb) A B)) :
    IsIso (L((baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
        (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))^*⟦𝔽⟧).map
      (kunnethMap 𝔽 φ₁ φ₂ A B)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
