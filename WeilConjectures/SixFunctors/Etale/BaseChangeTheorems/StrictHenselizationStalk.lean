/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# The strict henselisation stalk formula

Let `f : X ⟶ S` be quasi-compact and quasi-separated, let `s̄ : Spec Ω ⟶ S` be a geometric
point and let `S_(s̄) = Spec 𝒪ˢʰ_{S,s̄}` be the strict localisation
(`AlgebraicGeometry.Scheme.strictLocalization`). For a torsion étale sheaf `F` on `X` the
stalk at `s̄` of the higher direct image `Rᵠf_* F` is the cohomology of the restriction of `F`
to `X ×_S S_(s̄)`: the stalk is the colimit of `Hᵠ(X ×_S V, F)` over the pointed étale
neighbourhoods `V` of `s̄`, and étale cohomology is continuous along the inverse limit
`X ×_S S_(s̄) = lim X ×_S V`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_higherDirectImage`: the stalk formula,
  recorded as the existence of an additive isomorphism.

## References

- Stacks Project, Theorem 59.53.1, <https://stacks.math.columbia.edu/tag/03Q9>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The strict henselisation stalk formula.** Let `f : X ⟶ S` be quasi-compact and
quasi-separated, `s̄ : Spec Ω ⟶ S` a geometric point and

```
W ---a---> X
|          |
h          f
v          v
S_(s̄) ---> S
```

a cartesian square over the strict localisation `S_(s̄) ⟶ S` at `s̄`. For every torsion sheaf
`F` of `Λ`-modules on `X_ét` and every `q ≥ 0`, the stalk `(Rᵠf_* F)_{s̄}` is isomorphic to
`Hᵠ(W, a^* F)`.

**Form of the statement.** The blueprint asserts that the canonical map, obtained by
restricting representative sections from the neighbourhoods `X ×_S V` to `W`, is an
isomorphism. This statement only records that the two groups are isomorphic, which is what
is used for vanishing arguments.
(blueprint: `prop-weil-pbc-strict-henselization-stalk-formula`) -/
@[stacks 03Q9]
theorem Etale.nonempty_addEquiv_sheafFiber_higherDirectImage {X S W : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {a : W ⟶ X} {h : W ⟶ strictLocalization s}
    (sq : IsPullback a h f (strictLocalizationToBase s))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsTorsionModuleSheaf F] (q : ℕ) :
    Nonempty (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
        (Etale.higherDirectImage Λ f q F) ≃+
      Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((a)^*[ModuleCat.{u + 1} Λ].obj F)) q) :=
  sorry

end AlgebraicGeometry
