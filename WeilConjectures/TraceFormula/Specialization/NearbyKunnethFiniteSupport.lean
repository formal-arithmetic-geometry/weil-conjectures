/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedPoints
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteClosedPoints
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFormula
public import WeilConjectures.TraceFormula.Specialization.TraitProductRestrict
import WeilConjectures.TraceFormula.Specialization.SliceSupport
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLimitDimension

/-!

# Gabber's Künneth formula for nearby cycles: the finite-support step

Let `P` be the product over the strictly henselian trait `S = Spec k'⟦t⟧` of models `M`, `N` of
finite type, and let `C` be the cone of the Künneth map `Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)`
for bounded constructible `A`, `B`. This file proves that `C` is supported on finitely many closed
points of the special fibre `X_s × Y_s`
(`NearbyCyclesModel.exists_finite_isIso_upperStar_map_kunnethMap_of_boundedConstructible`), given
that its source and target are bounded constructible, that the total spaces locally embed into
`𝔸ᵐ_S`, `𝔸^{m'}_S`, and that the generic-slicing step holds in chart dimension `m + m' - 1`:
by the generic-slicing step (`NearbyCyclesModel.SliceKunnethFormula`, blueprint
`sk-prop-tf-nearby-external-kunneth`, "Finite support"), `C` vanishes on the special fibre
`(𝒵 ×_{𝔸¹_S} Spec K⟦t⟧)_s` of the generic slice of every chart coordinate.

## Proof

Around a point of `X_s × Y_s`, choose charts `V ⟶ 𝔸(ι_V; S)`, `W ⟶ 𝔸(ι_W; S)` (immersions over
`S` of opens of the total spaces of `M`, `N`). Their coordinates, pulled
back to `V ×_S W`, are coordinates of the restriction of the product to `V ×_S W`; on the special
fibre they detect closed points (`AlgebraicGeometry.AffineSpace`
`.isClosed_singleton_of_forall_isClosed_singleton_reindex` and
`AlgebraicGeometry.Scheme.Pullback.isClosed_singleton_iff`). By the generic-slicing step, the cone
of the restricted Künneth map vanishes over the generic point of each coordinate line, so `C` is
supported on finitely many closed points
(`ProEtale.CondensedRing.exists_finset_isZero_of_forall_exists_coordinates`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

/-! ### Special coordinates -/

section SpecialCoordinate

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

end SpecialCoordinate

/-! ### Closed points of the special fibre of a product -/

section Product

variable {k' : Type u} [Field k'] {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

end Product

/-! ### The special fibre of a generic slice -/

section Slice

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

end Slice

/-! ### Restrictions of the Künneth map, after a further pullback -/

section Restriction

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' Z Z' XU XU' YU YU' ZU ZU' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {MU : NearbyCyclesModel XU XU'}
  {NU : NearbyCyclesModel YU YU'} {PU : NearbyCyclesModel ZU ZU'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} {e₁ : ZU ⟶ XU}
  {e₁' : ZU' ⟶ XU'} {e₂ : ZU ⟶ YU} {e₂' : ZU' ⟶ YU'} {r₁ : XU ⟶ X} {r₁' : XU' ⟶ X'}
  {r₂ : YU ⟶ Y} {r₂' : YU' ⟶ Y'} {r : ZU ⟶ Z} {r' : ZU' ⟶ Z'}

end Restriction

/-! ### The finite-support step -/

section FiniteSupport

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {X Y Z : Scheme.{u}}
  {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

end FiniteSupport

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
