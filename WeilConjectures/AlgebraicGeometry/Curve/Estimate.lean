/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# The curve estimate

For a smooth proper connected curve `C` of genus `g` over an algebraically closed field `k`
and `n` prime to the characteristic, the cohomology of the constant sheaf `ℤ/n` on `C_ét` is

`H⁰ = ℤ/n`, `H¹ = (ℤ/n)^{2g}`, `H² = ℤ/n`, `H^q = 0` for `q ≥ 3`.

These groups are invariant under an extension of algebraically closed base fields, in the
strong sense that the canonical pullback map on cohomology is an isomorphism.

## Main definitions

- `AlgebraicGeometry.Scheme.constantZMod`: the constant étale sheaf `ℤ/n`.

## Main statements

- `AlgebraicGeometry.nonempty_addEquiv_sheafH_constantZMod`: the curve estimate.
- `AlgebraicGeometry.bijective_cohomologyMap_constantZMod`: invariance of the cohomology of
  `ℤ/n` on a smooth curve under extension of algebraically closed base fields.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The constant étale sheaf `ℤ/n` on a scheme `X`, valued in abelian groups of the universe of
the small étale site. -/
noncomputable abbrev Scheme.constantZMod (X : Scheme.{u}) (n : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsCurve f]

/-- **The curve estimate.** Let `C` be a smooth proper connected curve of genus `g` over an
algebraically closed field `k`, and let `n ≥ 1` be prime to `char k`. Then

`H⁰(C_ét, ℤ/n) ≅ ℤ/n`, `H¹(C_ét, ℤ/n) ≅ (ℤ/n)^{2g}`, `H²(C_ét, ℤ/n) ≅ ℤ/n`,

and `H^q(C_ét, ℤ/n) = 0` for `q ≥ 3`. The isomorphisms depend on the choice of a primitive
`n`-th root of unity, that is, of an isomorphism `μₙ ≅ ℤ/n` of étale sheaves, so they are only
asserted to exist. A connected curve has dimension exactly one, which is the hypothesis `hC`;
without it `Spec k` would be a smooth proper connected curve with `H² = 0`.

`H¹` and `H²` come from the Kummer computations
`AlgebraicGeometry.exists_exact_sheafH_rootsOfUnitySheaf_one` and
`AlgebraicGeometry.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two`, with
`Pic(C)[n] ≅ (ℤ/n)^{2g}` and `Pic(C)/n ≅ ℤ/n` through the degree; the vanishing for `q ≥ 3`
is `AlgebraicGeometry.subsingleton_sheafH_of_three_le`.
(blueprint: `sk-thm-curveestimate`) -/
theorem nonempty_addEquiv_sheafH_constantZMod [Smooth f] [IsProper f] [ConnectedSpace C]
    (hC : topologicalKrullDim C = 1) (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 0 ≃+ ZMod n) ∧
      Nonempty (Sheaf.H (C.constantZMod n) 1 ≃+ (Fin (2 * f.genus) → ZMod n)) ∧
      Nonempty (Sheaf.H (C.constantZMod n) 2 ≃+ ZMod n) ∧
      ∀ q, 3 ≤ q → Subsingleton (Sheaf.H (C.constantZMod n) q) :=
  sorry

/-- **Invariance under extension of algebraically closed fields.** Let `k ⊆ k'` be an
extension of algebraically closed fields, let `C` be a smooth curve over `k` and let `n ≥ 1`
be prime to `char k`. Form the base change

```
   C ×_{Spec k} Spec k' ──pullback.fst──▶ C
            │                             │ f
            │ pullback.snd                ▼
            ▼                          Spec k
        Spec k' ──Spec.map (algebraMap k k')──▶ Spec k
```

Then for every `q ≥ 0` the pullback map along the first projection

`ρ^q : H^q(C_ét, ℤ/n) ⟶ H^q((C_{k'})_ét, ℤ/n)`

is an isomorphism. In particular the curve estimate
`AlgebraicGeometry.nonempty_addEquiv_sheafH_constantZMod` is compatible with algebraically
closed extension of the base field: the isomorphisms over `k` and over `k'` are matched by
`ρ^q`, not merely abstractly isomorphic.

The map is `AlgebraicGeometry.Etale.cohomologyMap`; its target is the cohomology of the
pullback of the constant sheaf, which is the constant sheaf on `C_{k'}` by
`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`.
(blueprint: `sk-prop-ext-invariance`) -/
theorem bijective_cohomologyMap_constantZMod [Smooth f] {k' : Type u} [Field k'] [IsAlgClosed k']
    [Algebra k k'] (n : ℕ) (hn : (n : k) ≠ 0) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) (C.constantZMod n) q) :=
  sorry

end AlgebraicGeometry
