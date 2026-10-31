/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KunnethGlobalSections
public import WeilConjectures.SixFunctors.Etale.ZModCoefficients


/-!
# Künneth formula for ordinary étale cohomology

Source: literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-smooth-purity/
  sk-prop-sf-kunneth-ordinary/thm-kun-0f1p.md, node thm-kun-0f1p, order 3164
(blueprint: thm-kun-0f1p).

## Main statements

- `isIso_kunnethGlobalSectionsMap_of_isSepClosed`: the Künneth map on derived
  global sections is an isomorphism for finite coefficients `ℤ/nℤ` over a
  separably closed field.
-/

@[expose] public section

set_option linter.style.haveILetI false

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The Künneth map `κ_{E,K} : RΓ(X, E) ⊗ᴸ RΓ(Y, K) ⟶ RΓ(X ×ₖ Y, pr₁^*E ⊗ᴸ pr₂^*K)` of
`def-kun-kunneth-map` is an isomorphism for schemes `X`, `Y` of finite type over a separably
closed field `k` and coefficients `ℤ/nℤ`, `n ≥ 1` invertible in `k`, for all unbounded `E`, `K`.

Proof plan (the node's proof, step by step):
1. The adopted source theorem `isIso_kunnethMap_of_isSepClosed` applies to the pullback
   square for `aX` and `aY` after supplying the finite coefficient ring instance for
   `ZModCoeff n` and the `HasInvertibleExponent` instance obtained from `hn` and `hunit`.
   It gives an isomorphism for the native Künneth morphism in the derived category over
   `Spec k`.
2. Unfolding `kunnethGlobalSectionsMap` exhibits the specified global-sections map as a
   composite of tensor comparison isomorphisms, the native Künneth map from step 1 after
   applying derived global sections, and Leray isomorphisms. Each factor is an isomorphism,
   so the composite is an isomorphism.

Source: literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-smooth-purity/
  sk-prop-sf-kunneth-ordinary/thm-kun-0f1p.md, node thm-kun-0f1p, order 3164
(blueprint: thm-kun-0f1p). -/
theorem isIso_kunnethGlobalSectionsMap_of_isSepClosed
    {k : Type u} [Field k] [IsSepClosed k]
    (n : ℕ) (hn : 1 ≤ n) (hunit : IsUnit (n : k))
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ZModCoeff.{u} n))))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (ZModCoeff.{u} n)))) :
    IsIso (kunnethGlobalSectionsMap (ZModCoeff.{u} n)
      (pullback.fst aX aY) (pullback.snd aX aY) aX aY pullback.condition.symm E K) := by
  letI : Finite (ZModCoeff.{u} n) :=
    Finite.of_equiv (ZMod n)
      (h := @Finite.of_fintype _
        (@ZMod.fintype n ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)⟩))
      Equiv.ulift.symm
  letI : HasInvertibleExponent (ZModCoeff.{u} n) (Spec (.of k)) := by
    refine ⟨n, Nat.pos_of_ne_zero (by omega), ?_, ?_⟩
    · exact ULift.ext _ _ (ZMod.natCast_self n)
    · simpa using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom
  have h := isIso_kunnethMap_of_isSepClosed (ZModCoeff.{u} n) aX aY
    (pullback.fst aX aY) (pullback.snd aX aY)
    (IsPullback.of_hasPullback aX aY) E K
  unfold kunnethGlobalSectionsMap
  infer_instance

end AlgebraicGeometry.Etale
