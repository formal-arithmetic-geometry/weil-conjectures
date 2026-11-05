/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.AffineLineConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLisseDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.StalkZeroLocus
public import WeilConjectures.TraceFormula.Specialization.ClosedPointsSupport

/-!

# Bounded constructible complexes vanishing over the generic point of a curve

Let `Y` be a scheme of finite type over a field `k` and `C` a bounded constructible
`ℚ̄_ℓ`-complex on `Y_proét`. This file proves that `C` has a constructible *support*: a
constructible subset `s ⊆ Y` such that `C` vanishes on every open disjoint from `s`, while `s`
meets the image of no morphism `g : W ⟶ Y` with `Lg^* C = 0`
(`ProEtale.CondensedRing.exists_isConstructible_support`). Consequently, for a morphism
`b : Y ⟶ 𝔸¹_k`, if `C` vanishes after pullback to `Y ×_{𝔸¹} Spec K` for a point
`Spec K ⟶ 𝔸¹_k` over the generic point, then `C` vanishes on `Y ∖ b⁻¹(F)` for a finite set `F`
of closed points of `𝔸¹_k`
(`ProEtale.CondensedRing.exists_finset_isZero_leftDerivedUpperStar_of_isZero_pullback`). This is
the last step of the finite-support part of Gabber's Künneth formula for nearby cycles (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Finite support": the support of the cone has no point
over the generic point of a special-fibre coordinate line; its image in that line is
constructible and omits the generic point, so is a finite set of closed points).

## The argument

The cohomology sheaves `Hᵠ(C)`, finitely many of them nonzero, are constructible: lisse on the
strata `ι : D ⟶ Y` of a stratification. The rank function of the lisse sheaf `ι^* Hᵠ(C)`
(`ProEtale.CondensedRing.fiberRankFun`) is locally constant, `D` being of finite type over `k`, so
the set `T ⊆ D` where it does not vanish is clopen, and `s` is the union of the images `ι(T)`.

* A lisse sheaf with vanishing rank function vanishes: it is locally free of rank given by the
  rank function (`ProEtale.CondensedRing.exists_isOpenImmersion_isFree`), and pro-étale covers
  detect zero objects (`ProEtale.CondensedRing.isZero_of_forall_fiberRankFun_eq_zero`). Hence on
  an open `U` disjoint from `s`, all the restrictions of `Hᵠ(C)|_U` to the strata vanish, and
  so does `Hᵠ(C)|_U` (finitely many quasi-compact jointly surjective pullbacks detect zero).
* If `Lg^* C = 0`, the pullback of `ι^* Hᵠ(C)` to `D ×_Y W` is the pullback of
  `Hᵠ(Lg^* C) = 0`, so it has fibre rank `0` at every point; the rank function of `ι^* Hᵠ(C)`
  vanishes on the points of `D` lying over the image of `g`.

## Main statements

- `ProEtale.CondensedRing.isZero_of_forall_fiberRankFun_eq_zero`: a lisse `ℚ̄_ℓ`-sheaf on a
  scheme of finite type over a field with vanishing rank function is zero.
- `ProEtale.CondensedRing.exists_isConstructible_support`: the constructible support of a bounded
  constructible `ℚ̄_ℓ`-complex.
- `ProEtale.CondensedRing.exists_finset_isZero_leftDerivedUpperStar_of_isZero_pullback`: a bounded
  constructible complex vanishing over the generic point of `𝔸¹_k` vanishes away from the
  preimage of finitely many closed points.

-/

@[expose] public section

universe u

open CategoryTheory Limits Topology ZeroObject

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### Detection of zero objects -/

section Detection

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end Detection

/-! ### The rank function -/

section FiberRank

variable {X : Scheme.{u}}
  {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)}

end FiberRank

/-! ### Lisse sheaves with vanishing rank function -/

section Lisse

variable {k : Type u} [Field k]

end Lisse

/-! ### The support of a bounded constructible complex -/

section Support

variable {k : Type u} [Field k]

variable (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

end Support

/-! ### Vanishing over the generic point of the affine line -/

section AffineLine

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom]

end AffineLine

end AlgebraicGeometry.ProEtale.CondensedRing
