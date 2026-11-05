/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowAutLift

/-!
# Automorphisms of `(ℤ/ℓⁿ)_X^r` lift to `(ℤ/ℓⁿ⁺¹)_X^r`

The rank `r` version of `WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowAutLift`. An
endomorphism of the direct sum `(ℤ/m)|_Y^r` of `r` copies of `(ℤ/m)|_Y` is a matrix of
endomorphisms of `(ℤ/m)|_Y`, i.e. of multiplications by locally constant functions: it is the
action of a matrix `A ∈ M_r(C(Y, ℤ/m))`
(`AlgebraicGeometry.ProEtale.eq_zmodAbSheafOverMatrix`), and the composition of such actions is
the product of matrices. An automorphism is thus a matrix which is pointwise invertible, and a
pointwise invertible matrix `Y → GL_r(ℤ/ℓⁿ)` lifts pointwise, hence continuously, to
`Y → GL_r(ℤ/ℓⁿ⁺¹)` (`ZMod.exists_isUnit_det_map_castHom_eq`).

Consequently, an `ℓ`-adic tower `(Gₙ)` of abelian sheaves with each `Gₙ` locally isomorphic to
`(ℤ/ℓⁿ)_X^r` has a limit which is locally isomorphic to `lim_n (ℤ/ℓⁿ)_X^r`
(`AlgebraicGeometry.ProEtale.exists_cover_nonempty_iso_limit_zmodPowAbSheafDiagramPow`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace CategoryTheory

namespace Limits

variable {D : Type*} [Category* D] [Preadditive D]

end Limits

end CategoryTheory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] {ι : Type*} {f g : ι → C} [HasBiproduct f]
  [HasBiproduct g] [PreservesBiproduct f F] [PreservesBiproduct g F]
  [HasBiproduct fun i ↦ F.obj (f i)] [HasBiproduct fun i ↦ F.obj (g i)]

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {K D : Type*} [Category* K] [Category* D] [Preadditive D] [HasFiniteBiproducts D]

end CategoryTheory.Functor

namespace ZMod

end ZMod

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X : Scheme.{u}}

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

end AlgebraicGeometry.ProEtale
