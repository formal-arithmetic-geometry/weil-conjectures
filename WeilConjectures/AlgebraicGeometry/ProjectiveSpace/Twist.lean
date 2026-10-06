/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist

/-!
# The twisting sheaves `𝒪(m)` on projective space

The projective space `ℙ(n; S)` is the base change to `S` of the integral model
`Proj.projectiveSpaceOverAffine n (ULift ℤ) = Proj ℤ[Tᵢ]`, and `ProjectiveSpace.toProjInt` is
the projection to it. The twisting sheaf `𝒪(m)` on `ℙ(n; S)` is the pullback along this
projection of the twisting sheaf `Proj.twist` of the integral model.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.twist`: the twisting sheaf `𝒪(m)` on `ℙ(n; S)`.
- `AlgebraicGeometry.ProjectiveSpace.twistRestrict`: the pullback `i^* 𝒪(m)` of `𝒪(m)` along a
  morphism `i : X ⟶ ℙ(n; S)`.

## Main results

- `AlgebraicGeometry.Proj.isInvertible_twist_homogeneousSubmodule`: `𝒪(m)` is invertible on
  `Proj R[Tᵢ]`.
- `AlgebraicGeometry.ProjectiveSpace.unitIsoTwistZero`: `𝒪(0)` is the structure sheaf.
- `AlgebraicGeometry.ProjectiveSpace.isInvertible_twist`: `𝒪(m)` is invertible on `ℙ(n; S)`.
- `AlgebraicGeometry.ProjectiveSpace.nonempty_twist_tensorObj_iso`: `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`,
  and `nonempty_tensorPow_twist_one_iso`: `𝒪(1)^{⊗ t} ≅ 𝒪(t)`.
- `AlgebraicGeometry.ProjectiveSpace.pullbackMapTwistIso`: `𝒪(m)` commutes with base change.

## TODO

- Identify `ℙ(n; Spec A)` with `Proj.projectiveSpaceOverAffine n A`, and under this
  identification `twist n (Spec A) m` with `Proj.twist (homogeneousSubmodule n A) m`. This is
  what is needed to compute the cohomology of `𝒪(m)` over a field.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u)

/-- **`𝒪(m)` is invertible on `Proj R[Tᵢ]`**: the standard opens `D₊(Tᵢ)` cover `Proj R[Tᵢ]`
and `Tᵢ` has degree `1`. No finiteness of `n` is needed. -/
instance Proj.isInvertible_twist_homogeneousSubmodule (R : Type u) [CommRing R] (m : ℤ) :
    (Proj.twist (MvPolynomial.homogeneousSubmodule n R) m).IsInvertible :=
  Proj.isInvertible_twist _ m fun x ↦ by
    have h := Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule n R)
      (MvPolynomial.X : n → MvPolynomial n R) (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X R i⟩)
      (MvPolynomial.adjoin_range_X_eq_top n R)
    have hx : x ∈ ⨆ i, Proj.basicOpen (MvPolynomial.homogeneousSubmodule n R)
        (MvPolynomial.X i) := by
      rw [h]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨_, MvPolynomial.isHomogeneous_X R i, hi⟩

namespace ProjectiveSpace

variable (S : Scheme.{u})

/-- **The twisting sheaf `𝒪(m)` on `ℙ(n; S)`**: the pullback along the projection
`toProjInt : ℙ(n; S) ⟶ Proj ℤ[Tᵢ]` of the twisting sheaf `𝒪(m)` of the integral model, i.e.
along the top arrow of the defining base-change square of `ℙ(n; S)`:

```
             toProjInt
  ℙ(n; S) ─────────────▶ Proj ℤ[Tᵢ]
     │                       │
     │ ↘                     │
     ▼                       ▼
     S ─────────────────▶ Spec ℤ
```

Since `toProjInt` commutes with `map n f` for any `f : S ⟶ T`, `𝒪(m)` commutes with base
change (`pullbackMapTwistIso`). -/
def twist (m : ℤ) : (ℙ(n; S)).Modules :=
  (Scheme.Modules.pullback (toProjInt n S)).obj
    (Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) m)

lemma twist_def (m : ℤ) :
    twist n S m = (Scheme.Modules.pullback (toProjInt n S)).obj
      (Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) m) :=
  rfl

/-- **`𝒪(0)` is the structure sheaf** of `ℙ(n; S)`. -/
def unitIsoTwistZero : SheafOfModules.unit (ℙ(n; S)).ringCatSheaf ≅ twist n S 0 :=
  (Scheme.Modules.pullbackObjUnitIso (toProjInt n S)).symm ≪≫
    (Scheme.Modules.pullback (toProjInt n S)).mapIso Proj.unitIsoTwistZero

/-- **`𝒪(m)` is invertible** on `ℙ(n; S)`, being the pullback of an invertible module. -/
instance isInvertible_twist (m : ℤ) : (twist n S m).IsInvertible :=
  Scheme.Modules.IsInvertible.pullback (toProjInt n S)
    (Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) m)

/-- **`𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`** on `ℙ(n; S)`. The twisting module `𝒪(d)` is glued from the
free modules on the standard opens `D₊(Tᵢ)` with bases `eᵢ⁽ᵈ⁾` and transition rule
`eᵢ⁽ᵈ⁾ = (Tᵢ / Tⱼ)ᵈ eⱼ⁽ᵈ⁾`; the bases `eᵢ⁽ᵃ⁾ ⊗ eᵢ⁽ᵇ⁾` of `𝒪(a) ⊗ 𝒪(b)` obey the transition
rule of `𝒪(a + b)`.

(blueprint: `def-pc-projective-space-twist`) -/
theorem nonempty_twist_tensorObj_iso (a b : ℤ) :
    Nonempty (twist n S a ⊗ twist n S b ≅ twist n S (a + b)) :=
  sorry

/-- **`𝒪(1)^{⊗ t} ≅ 𝒪(t)`** on `ℙ(n; S)`, by induction from `nonempty_twist_tensorObj_iso`. -/
theorem nonempty_tensorPow_twist_one_iso (t : ℕ) :
    Nonempty ((twist n S 1).tensorPow t ≅ twist n S t) := by
  induction t with
  | zero => exact ⟨unitIsoTwistZero n S⟩
  | succ t ih =>
    obtain ⟨e⟩ := nonempty_twist_tensorObj_iso n S 1 t
    exact ⟨(Iso.refl _ ⊗ᵢ ih.some) ≪≫ e ≪≫ eqToIso (by rw [add_comm]; push_cast; rfl)⟩

/-- **`𝒪(m)` commutes with base change**: for `f : S ⟶ T`, the pullback of `𝒪(m)` on
`ℙ(n; T)` along `map n f` is `𝒪(m)` on `ℙ(n; S)`. -/
def pullbackMapTwistIso {S T : Scheme.{u}} (f : S ⟶ T) (m : ℤ) :
    (Scheme.Modules.pullback (map n f)).obj (twist n T m) ≅ twist n S m :=
  (Scheme.Modules.pullbackComp (map n f) (toProjInt n T)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (map_toProjInt n f)).app _

variable {n S} {X : Scheme.{u}}

/-- The pullback `𝒪_X(m) = i^* 𝒪(m)` of the twisting sheaf along a morphism
`i : X ⟶ ℙ(n; S)`, e.g. its restriction to a closed subscheme. -/
abbrev twistRestrict (i : X ⟶ ℙ(n; S)) (m : ℤ) : X.Modules :=
  (Scheme.Modules.pullback i).obj (twist n S m)

end ProjectiveSpace

end AlgebraicGeometry
