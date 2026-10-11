/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Invariance of cohomology under extension of algebraically closed fields

For an extension `k ⊆ k'` of algebraically closed fields, a quasi-compact quasi-separated
`k`-scheme `X` and `n` prime to the characteristic, the pullback map
`H^q(X_ét, ℤ/n) ⟶ H^q((X_{k'})_ét, ℤ/n)` is bijective.

## Main statements

- `AlgebraicGeometry.bijective_cohomologyMap_constantZMod`: the invariance statement.
- `AlgebraicGeometry.bijective_cohomologyMap_constantZMod_of_smoothOfRelativeDimension`: the
  invariance statement for a smooth separated curve.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Invariance under extension of algebraically closed fields.** Let `k ⊆ k'` be an
extension of algebraically closed fields, let `X` be a quasi-compact quasi-separated scheme
over `k` and let `n ≥ 1` be prime to `char k`. Form the base change

```
  X ×_{Spec k} Spec k' ──pullback.fst──▶ X
          │                             │
    pullback.snd                        f
          ▼                             ▼
       Spec k' ──Spec.map (algebraMap k k')──▶ Spec k
```

Then for every `q ≥ 0` the pullback map along the first projection

`ρ^q : H^q(X_ét, ℤ/n) ⟶ H^q((X_{k'})_ét, ℤ/n)`

is bijective. Its target is the cohomology of the pullback of the constant sheaf `ℤ/n`.
(blueprint: `sk-prop-ext-invariance`) -/
theorem bijective_cohomologyMap_constantZMod {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k'] (n : ℕ) (hn : (n : k) ≠ 0)
    (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) (X.constantZMod n) q) :=
  -- Proof sketch: write `k'` as a filtered union of finitely generated `k`-algebras `A`. Each
  -- `Spec A ⟶ Spec k` is smooth on a dense open, since `k` is perfect, and has a section,
  -- since `k` is algebraically closed; smooth base change
  -- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth` and a limit argument over
  -- the `A` then give the claim. The target of `ρ^q` is the cohomology of the constant sheaf
  -- on `X_{k'}` by `AlgebraicGeometry.Scheme.upperStarConstantSheafIso`.
  sorry

/-- Blueprint `sbc-thm-algebraically-closed-invariance`: Invariance under extension of
algebraically closed fields.

Let `k ⊆ k'` be algebraically closed fields, let `C` be a smooth separated curve over `k` and
let `d ≥ 1` be prime to `char k`. For every `q ≥ 0` the pullback map
`H^q(C_ét, ℤ/d) ⟶ H^q((C_{k'})_ét, ℤ/d)` along the projection `C_{k'} ⟶ C` is bijective.

This is the case of a curve of `AlgebraicGeometry.bijective_cohomologyMap_constantZMod`
(blueprint `sk-prop-ext-invariance`). -/
@[stacks 0A5E]
theorem bijective_cohomologyMap_constantZMod_of_smoothOfRelativeDimension {k : Type u}
    [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f] {k' : Type u} [Field k']
    [IsAlgClosed k'] [Algebra k k'] (d : ℕ) (hd : (d : k) ≠ 0) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) (C.constantZMod d) q) :=
  bijective_cohomologyMap_constantZMod f d hd q

end AlgebraicGeometry
