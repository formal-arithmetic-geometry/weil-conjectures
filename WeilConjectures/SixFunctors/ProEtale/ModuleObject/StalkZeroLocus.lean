/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.StalkZeroLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.Topology.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# The vanishing locus of a constructible `ℚ̲̄_ℓ`-module

For a module object `M` over `ℚ̲̄_ℓ,X` on `X_proét`, `ProEtale.CondensedRing.stalkZeroLocus ℓ M`
is the set of points `x` of `X` such that the pullback of `M` along every geometric point
`Spec Ω ⟶ X` over `x` (`Ω` separably closed) vanishes. This is the pro-étale analogue of
`AlgebraicGeometry.Etale.stalkZeroLocus`.

* If `M` is pro-étale locally finitely presented, the pullback of `M` along a geometric point over
  `x` vanishes exactly when the fibre rank `fiberRankFun ℓ M x` is zero
  (`ProEtale.CondensedRing.isZero_upperStar_iff_fiberRankFun_eq_zero`); in particular vanishing
  at one geometric point over `x` gives vanishing at all of them.
* For `M` constructible, vanishing at one geometric point over `x` gives
  `x ∈ stalkZeroLocus ℓ M` (`ProEtale.CondensedRing.mem_stalkZeroLocus_of_isZero_upperStar`).
* For `M` constructible on a scheme of finite type over a field, `stalkZeroLocus ℓ M` is
  a constructible subset (`ProEtale.CondensedRing.isConstructible_stalkZeroLocus`): on each
  stratum the fibre rank is locally constant
  (`ProEtale.CondensedRing.isLocallyConstant_fiberRankFun`).
* For a bounded constructible complex `K` on such a scheme, the common vanishing locus
  `ProEtale.CondensedRing.complexStalkZeroLocus ℓ K` of its cohomology sheaves is constructible
  (`ProEtale.CondensedRing.isConstructible_complexStalkZeroLocus`), only finitely many of them
  being nonzero.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Topology

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]

section FiniteType

variable {k : Type u} [Field k] (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom]

end FiniteType

section Complex

end Complex

end AlgebraicGeometry.ProEtale.CondensedRing
