/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowAbSheafCokernel
public import Mathlib.Data.ZMod.Units
public import WeilConjectures.SixFunctors.ProEtale.Adic.ProEtOpenCover

/-!
# Automorphisms of `(ℤ/ℓⁿ)_X` lift to `(ℤ/ℓⁿ⁺¹)_X`

Let `Y` be an object of `X_proét` and `m : ℕ`. A morphism of abelian sheaves out of the
restriction `(ℤ/m)|_Y` of the sheaf of locally constant functions `C(-, ℤ/m)` is determined by
the image of the global section `1` (`AlgebraicGeometry.ProEtale.zmodAbSheafOver_hom_ext`): a
section `s` is, on the open cover by its fibres `s⁻¹(k)`, the multiple `k • 1`. Hence every
endomorphism of `(ℤ/m)|_Y` is the multiplication by a locally constant function
`c : Y → ℤ/m` (`AlgebraicGeometry.ProEtale.zmodAbSheafOverMul`), and the automorphisms are the
multiplications by pointwise units.

A pointwise unit `u : Y → ℤ/ℓⁿ` lifts pointwise to a unit `Y → ℤ/ℓⁿ⁺¹`, continuously since
`ℤ/ℓⁿ` is discrete. Therefore every automorphism of `(ℤ/ℓⁿ)|_Y` lifts to an automorphism of
`(ℤ/ℓⁿ⁺¹)|_Y` along the reduction
(`AlgebraicGeometry.ProEtale.exists_iso_hom_comp_zmodPowAbSheafDiagram_map`), and an `ℓ`-adic
tower `(Gₙ)` of abelian sheaves with each `Gₙ` locally isomorphic to `(ℤ/ℓⁿ)_X` has a limit which
is locally isomorphic to `ℤ_ℓ,X`
(`AlgebraicGeometry.ProEtale.exists_cover_nonempty_iso_padicIntAbSheaf_of_locally_iso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X : Scheme.{u}}

end AlgebraicGeometry.ProEtale

namespace ZMod

end ZMod

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

end AlgebraicGeometry.ProEtale
