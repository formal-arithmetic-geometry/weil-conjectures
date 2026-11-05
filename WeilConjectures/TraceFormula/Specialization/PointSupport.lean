/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PointComplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback

/-!

# Complexes supported at a rational point

Let `X` be a separated `k`-scheme of finite type and `x` a rational point of `X`. A bounded
constructible complex `C` on `X` whose restriction to the open complement `X ∖ {x}` vanishes is
the direct image of its stalk at `x`, `C ≅ Rx_* Lx^* C`; its global sections are therefore
`RΓ(X, C) ≅ Lx^* C`, and they detect vanishing
(`ProEtale.CondensedRing.isZero_of_isZero_upperStar_pointComplι_of_isZero_lowerStar`). This is
the case of a single rational point of the blueprint lemma `det-nearby-kunneth-finite-support`
(global sections detect complexes with finite support), used in the finite-support step of
Gabber's Künneth formula for nearby cycles.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

end AlgebraicGeometry.ProEtale.CondensedRing
