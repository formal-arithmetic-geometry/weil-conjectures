/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Constructible sheaves with a filtration by prime-field sheaves

Let `X` be a scheme and `Λ` a commutative ring. A constructible sheaf of `Λ`-modules on the
small étale site of `X` *has a prime-field filtration*
(`AlgebraicGeometry.Scheme.HasPrimeFieldFiltration`) if it is obtained by finitely many
extensions of constructible sheaves from constructible sheaves whose underlying abelian sheaf
is that of a constructible sheaf of `𝔽_r`-modules for some prime `r`. This is the dévissage
of the second proof of [Stacks 03SC].
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- A sheaf of `Λ`-modules on the small étale site of `X` *has a prime-field filtration* if it
is built by the following two rules:

1. a constructible sheaf `F` whose underlying abelian sheaf is isomorphic to the underlying
  abelian sheaf of a constructible sheaf `G` of `𝔽_r`-modules, for some prime `r`, has a
  prime-field filtration;
2. if `0 → F₁ → F → F₃ → 0` is a short exact sequence with `F₁` and `F₃` constructible and
  both having a prime-field filtration, then `F` has a prime-field filtration.

A witness is a finite extension tree whose leaves are constructible prime-field sheaves; there
is no cohomological condition. The prime field `𝔽_r` is `ULift (ZMod r)`, lifted to the
universe of the coefficients. (blueprint: `def-v2-prime-field-filtration`) -/
@[stacks 03SC]
inductive HasPrimeFieldFiltration :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) → Prop
  /-- A constructible sheaf whose underlying abelian sheaf is that of a constructible sheaf of
  `𝔽_r`-modules, `r` prime. -/
  | of_primeField (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (hF : IsConstructibleSheaf F) (r : ℕ) (hr : r.Prime)
      (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
      (hG : IsConstructibleSheaf G)
      (e : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F ≅
        (sheafCompose _
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})).obj G) :
      HasPrimeFieldFiltration F
  /-- An extension of two constructible sheaves having prime-field filtrations. -/
  | extension (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (hS : S.ShortExact) (h₁ : IsConstructibleSheaf S.X₁) (h₃ : IsConstructibleSheaf S.X₃)
      (hf₁ : HasPrimeFieldFiltration S.X₁) (hf₃ : HasPrimeFieldFiltration S.X₃) :
      HasPrimeFieldFiltration S.X₂

end AlgebraicGeometry.Scheme
