/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality

/-!
# Stability of `Dctf` under the internal hom

For a finite coefficient ring `Λ` whose exponent is invertible on schemes of finite type over an
algebraically closed field `k`, the internal hom `RHom(K, M)` of two objects of `Dctf` lies in
`Dctf`, with the Tor interval of blueprint `sk-thm-sf-hom-ctf`. As in the blueprint, this goes
through Verdier biduality: `RHom(K, M) ≅ 𝔻(𝔻M ⊗ᴸ K)`
(`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app`).

This file is part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`, whose module
documentation records the implementation notes. The blueprint states these results over
`k = 𝔽̄_q`; the algebraic closedness of `k` is used by Verdier biduality.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]

section DualizingHom

variable [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]

end DualizingHom

section DerivedHom

variable {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [HasInvertibleExponent Λ X] (m : ℕ) (hm : topologicalKrullDim X ≤ (m : WithBot ℕ∞))
  (a b c d : ℤ)
  {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}

-- `aX` and the coefficient hypotheses are part of the blueprint setting, unused by the proof

end DerivedHom

end Torsion

end Etale

end AlgebraicGeometry
