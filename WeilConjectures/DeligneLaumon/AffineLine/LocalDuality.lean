/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.DeligneLaumon.AffineLine.Defs

/-!
# Local boundary duality on a curve, and ramification at infinity

Let `j : U₀ ↪ C₀` be a dense open immersion of smooth curves and `F` a lisse Weil sheaf on
`U₀`. At a missing closed point `s` the two boundary modules `(j_*F^∨)_s̄` and `(R¹j_*F)_s̄`
are dual to one another, up to a Tate twist: the duality `𝔻_Z A(F) ≃ A(F^∨)(1)[1]` for the
boundary complex `A(F) = i^*Rj_*F` on the finite complement, obtained from Verdier exchange
and smooth curve duality, reads in degree `-1` as a perfect pairing into `ℚ̄_ℓ(-1)`.

The file also records the second half of the same blueprint subsection: a nonzero linear
Artin–Schreier sheaf `ℒ_{ψ(a x)}` is ramified at infinity, because in `t = 1/x` the
Artin–Schreier cover `u^q - u = a/t` of `k((t))` is totally ramified of degree `q` with Galois
group `k₀`, on which a nontrivial `ψ` is nontrivial. This is what excludes linear characters in
the nonexceptionality test of `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension`.

## Main statements

- `AlgebraicGeometry.exists_linearEquiv_dual_stalk_higherDirectImage`: the local boundary
  pairing.
- `AlgebraicGeometry.not_isUnramifiedAtInfinity_artinSchreier`: `ℒ_{ψ(a x)}` is ramified at
  infinity for `a ≠ 0`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/--
For a dense open immersion `j : U₀ ↪ C₀` of smooth curves, a lisse Weil sheaf `F` on `U₀` and a
closed point `s` of `C₀` outside `U₀`, there is a Frobenius-equivariant perfect pairing
`(j_*F^∨)_s̄ ⊗ (R¹j_*F)_s̄ → ℚ̄_ℓ(-1)`:

```
  (j_*F^∨)_s̄ ⊗ (R¹j_*F)_s̄ ──────▶ ℚ̄_ℓ(-1)
       │           │                  │
  Frob │      Frob │                  │ q_s
       ▼           ▼                  ▼
  (j_*F^∨)_s̄ ⊗ (R¹j_*F)_s̄ ──────▶ ℚ̄_ℓ(-1)
```

It is exhibited as a linear isomorphism of `(j_*F^∨)_s̄` onto the `ℚ̄_ℓ`-dual of `(R¹j_*F)_s̄`
which intertwines the two local Frobenius actions up to the factor `q_s` coming from the Tate
twist. (blueprint: `sk-i-dl-a1-local`)
-/
theorem exists_linearEquiv_dual_stalk_higherDirectImage
    {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) (hF : F.IsLisse) (s : C.finitePoints)
    (hsU : s.1 ∉ Set.range j.base) :
    ∃ e : (((WeilSheaf.directImage j).obj F.dual).stalk s).carrier ≃ₗ[PadicAlgCl l]
        Module.Dual (PadicAlgCl l) (((WeilSheaf.higherDirectImage j 1).obj F).stalk s).carrier,
      ∀ a b, e ((((WeilSheaf.directImage j).obj F.dual).stalk s).frobenius a)
          ((((WeilSheaf.higherDirectImage j 1).obj F).stalk s).frobenius b) =
        (((C ↘ Spec (CommRingCat.of k₀)).residueCard s.1 : PadicAlgCl l)) * e a b := by
  sorry

/-- For a nontrivial additive character `ψ` of `k₀` and a nonzero `a`, the linear Artin–Schreier
sheaf `ℒ_{ψ(a x)}` on the affine line is ramified at infinity: in `t = 1/x` the cover
`u^q - u = a/t` of `k((t))` is totally ramified of degree `q` with Galois group `k₀`, on which
a nontrivial `ψ` is nontrivial, so inertia at `∞` acts nontrivially.
(blueprint: `sk-i-dl-a1-local`) -/
theorem not_isUnramifiedAtInfinity_artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    {a : k₀} (ha : a ≠ 0) :
    ¬ (artinSchreier ψ a).IsUnramifiedAtInfinity (𝟙 (affineLine k₀)) := by
  sorry

end AlgebraicGeometry
