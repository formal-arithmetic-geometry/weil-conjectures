/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction

/-!
# Purity for regular closed immersions and finite reduction

Let `i : Z ⟶ X` be a regular closed immersion of pure codimension `c`, with `X` smooth over a
perfect field `k` and `Z` regular, and let `J` be an ideal of the finite coefficient ring `Λ`.
The purity isomorphism `cl_i : Λ_Z ≅ Ri^! (Λ_X(c)[2c])`
(`AlgebraicGeometry.Etale.isIso_fundamentalClassMap`) reduces modulo `J` to a morphism

`cl_i mod J : Λ_Z ⊗ᴸ (Λ/J)_Z ⟶ Ri^! (Λ_X(c)[2c] ⊗ᴸ (Λ/J)_X)`,

the reduction of `cl_i` followed by the canonical comparison
`Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)` and `(Λ/J)_Z ≅ Li^* (Λ/J)_X`. This is the form of the
finite reduction `A_{E,n} ⟶ A_{E,n-1}` of item 4 of blueprint
`prop-pur-regular-immersion-purity-compatibilities` in which the reduction is applied to the
target *before* `Ri^!`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekDerivedTensorMap`: the comparison
  `Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)`, adjoint to the inverse of the projection map followed by
  the counit of `Ri_! ⊣ Ri^!`.
- `AlgebraicGeometry.Etale.fundamentalClassMapModIdeal`: the reduced purity map `cl_i mod J`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekDerivedTensorMap_tateObject`: the
  comparison is an isomorphism for `K = Λ_X(c)[2c]` and `M = (Λ/J)_X`.
- `AlgebraicGeometry.Etale.isIso_fundamentalClassMapModIdeal`: `cl_i mod J` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Comparison

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
  [HasCompactification i]

/-- The canonical comparison `Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)` for `K, M ∈ D(X_ét, Λ)`: the
adjoint, under `Ri_! ⊣ Ri^!`, of the composite

`Ri_! (Ri^! K ⊗ᴸ Li^* M) ≅ Ri_! Ri^! K ⊗ᴸ M ⟶ K ⊗ᴸ M`

of the inverse of the projection map (`AlgebraicGeometry.Etale.projectionMap`, invertible at a
finite coefficient ring by `AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`) and of the
counit of the adjunction. -/
noncomputable def rightDerivedUpperShriekDerivedTensorMap
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((L((i)^*[ModuleCat.{u + 1} Λ])).obj M) ⟶
      (R(i)^![ModuleCat.{u + 1} Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj M) :=
  haveI := isIso_projectionMap_of_finite Λ i
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).homEquiv _ _
    (inv (((projectionMap (ModuleCat.{u + 1} Λ) i).app
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj K)).app M) ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app K)).app M)

end Comparison

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Z : Scheme.{u}} [HasInvertibleExponent Λ X] {k : Type u}
  [Field k] [PerfectField k] (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]

/-- The comparison `Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekDerivedTensorMap`) is an isomorphism for
`K = Λ_X(c)[2c]` and the constant complex `M = (Λ/J)_X`, when `i : Z ⟶ X` is a regular closed
immersion of codimension `c` with `X` smooth over a perfect field and `Z` regular.

Mathematically both sides are `(Λ/J)_Z` in degree `0`: this is purity for `i` with coefficients
in the `Λ`-module `Λ/J`, and the comparison is the identity on `𝓗⁰` at every geometric point. -/
theorem isIso_rightDerivedUpperShriekDerivedTensorMap_tateObject (aX : X ⟶ Spec (.of k))
    [Smooth aX] (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (J : Ideal Λ) :
    IsIso (rightDerivedUpperShriekDerivedTensorMap Λ i ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)
      (constantSingle (ModuleCat.{u + 1} Λ) X (ModuleCat.of Λ (Λ ⧸ J)))) :=
  sorry

/-- The purity map reduced modulo an ideal `J` of `Λ`,

`cl_i mod J : Λ_Z ⊗ᴸ (Λ/J)_Z ⟶ Ri^! (Λ_X(c)[2c] ⊗ᴸ (Λ/J)_X)`:

the reduction `cl_i ⊗ᴸ (Λ/J)_Z` of `cl_i`
(`AlgebraicGeometry.Etale.fundamentalClassMap`), followed by `(Λ/J)_Z ≅ Li^* (Λ/J)_X` and the
comparison `Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekDerivedTensorMap`). -/
noncomputable def fundamentalClassMapModIdeal (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (J : Ideal Λ) :
    (reductionModIdeal Λ Z J).obj (constantComplex Λ Z) ⟶
      (R(i)^![ModuleCat.{u + 1} Λ]).obj
        ((reductionModIdeal Λ X J).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) :=
  (reductionModIdeal Λ Z J).map (fundamentalClassMap Λ c i aX hZ) ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj _).map
      (leftDerivedUpperStarSingleConstantSheafIso _ i (ModuleCat.of Λ (Λ ⧸ J))).inv ≫
    rightDerivedUpperShriekDerivedTensorMap Λ i _ _

/-- Blueprint `prop-pur-regular-immersion-purity-compatibilities`: Compatibilities of purity for
regular immersions

**Finite reduction** (item 4). For an ideal `J` of `Λ` (for `Λ = A_{E,n}` and `J = ϖ^{n-1}`
this is the reduction `A_{E,n} ⟶ A_{E,n-1}`), the purity isomorphism
`cl_i : Λ_Z ≅ Ri^! (Λ_X(c)[2c])` reduces to an isomorphism

`cl_i mod J : Λ_Z ⊗ᴸ (Λ/J)_Z ≅ Ri^! (Λ_X(c)[2c] ⊗ᴸ (Λ/J)_X)`

(`AlgebraicGeometry.Etale.fundamentalClassMapModIdeal`): the reduction of coefficients may be
performed before applying `Ri^!`. The map is the reduction of `cl_i`, invertible by clause (c)
of `sk-thm-regular` (`AlgebraicGeometry.Etale.isIso_fundamentalClassMap`), followed by
`(Λ/J)_Z ≅ Li^* (Λ/J)_X` and the comparison `Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)`, invertible
for `K = Λ_X(c)[2c]` and `M = (Λ/J)_X`
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekDerivedTensorMap_tateObject`). -/
theorem isIso_fundamentalClassMapModIdeal (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (J : Ideal Λ) :
    IsIso (fundamentalClassMapModIdeal Λ c i aX hZ J) := by
  have := isIso_fundamentalClassMap Λ c i aX hZ
  have := isIso_rightDerivedUpperShriekDerivedTensorMap_tateObject Λ c i aX hZ J
  rw [fundamentalClassMapModIdeal]
  infer_instance

end Etale

end AlgebraicGeometry
