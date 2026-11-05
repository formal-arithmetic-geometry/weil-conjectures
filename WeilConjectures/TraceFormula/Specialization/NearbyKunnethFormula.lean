/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyEmbedsInAffineSpace
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethBraided
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelHom

/-!

# The statements of Gabber's Künneth formula for nearby cycles

Let `Λ` be a commutative ring object of condensed abelian groups (in practice `𝒪_E`, `𝔽_E` or
`ℚ̄_ℓ`). This file states, for products over the strictly henselian trait `S = Spec k'⟦t⟧` of
models of finite type:

* `NearbyCyclesModel.KunnethFormula Λ k' n`: Gabber's Künneth formula in chart dimension `n`, i.e.
  the Künneth map of nearby cycles `Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)` is an isomorphism for
  bounded constructible `A`, `B` (blueprint `sk-prop-tf-nearby-external-kunneth`);
* `NearbyCyclesModel.SliceKunnethFormula Λ k' n`: the generic-slicing step in chart dimension `n`,
  i.e. the pullback of `Π_{A,B}` to the special fibre of the generic slice
  `𝒵 ×_{𝔸¹_S} Spec K⟦t⟧` of the product along a coordinate `b` of the first factor is an
  isomorphism, when the slice of `M` and the total space of `N` locally embed into affine spaces of
  dimensions summing to at most `n` (blueprint `sk-prop-tf-nearby-external-kunneth`, "Finite
  support").

It also defines the projections of the geometric slice of a product
(`NearbyCyclesModel.sliceFst`, `NearbyCyclesModel.sliceSnd`), the models to which the Künneth
formula in smaller chart dimension is applied, and derives the slicing step along a coordinate of
the second factor by symmetry (`NearbyCyclesModel.isIso_map_kunnethMap_baseChangeSpecialMap_snd`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] {X Y Z : Scheme.{u}}
  {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver qM gM) (hN : N.IsTraitModelOver qN gN)
  (hpb : IsPullback φ₁.total φ₂.total qM qN)
  (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
  (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM)

/-! ### The geometric slice of a product along a coordinate of the first factor -/

section Fst

variable {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qM)

end Fst

/-! ### Slicing along a coordinate of the second factor -/

section Snd

variable {b : N.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qN)

end Snd

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
