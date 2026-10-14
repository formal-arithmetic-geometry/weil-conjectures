/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

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

The reduction map `ρ : K ⟶ K ⊗ᴸ (Λ/J)_X` is natural in `K`, and the adjoint of the reduced
fundamental class is the purity map followed by `Ri^!(ρ)`: the classes reduce compatibly.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekDerivedTensorMap`: the comparison
  `Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)`, adjoint to the inverse of the projection map followed by
  the counit of `Ri_! ⊣ Ri^!`.
- `AlgebraicGeometry.Etale.fundamentalClassMapModIdeal`: the reduced purity map `cl_i mod J`.
- `AlgebraicGeometry.Etale.constantComplexToQuotient`: the map `Λ_X ⟶ (Λ/J)_X` induced by the
  quotient map `Λ ⟶ Λ/J`.
- `AlgebraicGeometry.Etale.reductionModIdealUnit`: the reduction map `K ⟶ K ⊗ᴸ (Λ/J)_X`, natural
  in `K`.

## Main statements

- `AlgebraicGeometry.Etale.supportedClassMap_comp_map_rightDerivedUpperShriek`: the adjoint
  `Λ_Z ⟶ Ri^! L` of a class with supports is natural in the coefficients `L`.
- `AlgebraicGeometry.Etale.supportedClassMap_fundamentalClass_reductionModIdealUnit`: the
  adjoint of the reduced fundamental class is the purity map followed by `Ri^!(ρ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

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

section General

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

/-- For a morphism `q : Λ_X ⟶ M` out of the unit, the natural transformation `K ⟶ K ⊗ᴸ M`:
the inverse of the right unitor `K ⊗ᴸ Λ_X ≅ K` followed by `K ⊗ᴸ q`. -/
noncomputable def derivedTensorRightUnitorInvComp
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (q : 𝟙_ _ ⟶ M) :
    𝟭 _ ⟶ (derivedTensor A X).flip.obj M where
  app K := (derivedTensorRightUnitor A X K).inv ≫ ((derivedTensor A X).obj K).map q
  naturality K L f := by
    change f ≫ (ρ_ L).inv ≫ L ◁ q = ((ρ_ K).inv ≫ K ◁ q) ≫ f ▷ M
    rw [rightUnitor_inv_naturality_assoc, Category.assoc, whisker_exchange]

end General

section Reduction

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) (J : Ideal Λ)

/-- The map `Λ_X ⟶ (Λ/J)_X` of constant complexes induced by the quotient map `Λ ⟶ Λ/J`: the
constant complex `Λ_X` is the unit sheaf, which is the constant sheaf on `Λ`, placed in degree
zero (`AlgebraicGeometry.Etale.singleFunctorObjUnitIso`). -/
noncomputable def constantComplexToQuotient :
    constantComplex Λ X ⟶ constantSingle (ModuleCat.{u + 1} Λ) X (ModuleCat.of Λ (Λ ⧸ J)) :=
  (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).inv ≫
    (_root_.DerivedCategory.singleFunctor _ 0).map
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
        (ModuleCat.ofHom (Ideal.Quotient.mkₐ Λ J).toLinearMap))

/-- The reduction map `ρ_K : K ⟶ K ⊗ᴸ (Λ/J)_X` to the reduction of the coefficients modulo `J`
(`AlgebraicGeometry.Etale.reductionModIdeal`): the inverse of the right unitor
`K ⊗ᴸ Λ_X ≅ K` followed by `K ⊗ᴸ (Λ_X ⟶ (Λ/J)_X)`
(`AlgebraicGeometry.Etale.constantComplexToQuotient`). It is natural in `K`. -/
noncomputable def reductionModIdealUnit : 𝟭 _ ⟶ reductionModIdeal Λ X J :=
  derivedTensorRightUnitorInvComp (ModuleCat.{u + 1} Λ) X (constantComplexToQuotient Λ X J)

lemma reductionModIdealUnit_app
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (reductionModIdealUnit Λ X J).app K =
      (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X K).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map (constantComplexToQuotient Λ X J) :=
  rfl

end Reduction

section SupportedClass

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
  [IsClosedImmersion i]

/-- The adjoint `Λ_Z ⟶ Ri^! L` of a class with supports `γ : Λ_X ⟶ Ri_! Ri^! L`
(`AlgebraicGeometry.Etale.supportedClassMap`) is natural in the coefficients `L`. -/
theorem supportedClassMap_comp_map_rightDerivedUpperShriek
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj L)) (f : L ⟶ L') :
    supportedClassMap Λ i (γ ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map
      ((R(i)^![ModuleCat.{u + 1} Λ]).map f)) =
      supportedClassMap Λ i γ ≫ (R(i)^![ModuleCat.{u + 1} Λ]).map f := by
  rw [supportedClassMap_eq_supportedTranspose, supportedClassMap_eq_supportedTranspose,
    supportedTranspose_comp]

end SupportedClass

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Z : Scheme.{u}} [HasInvertibleExponent Λ X] {k : Type u}
  [Field k] [PerfectField k] (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]

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

**Finite reduction** (item 4), on the level of classes. For an ideal `J` of `Λ` (for
`Λ = A_{E,n}` and `J = ϖ^{n-1}` this is the reduction `A_{E,n} ⟶ A_{E,n-1}`), the reduction
`ρ : K ⟶ K ⊗ᴸ (Λ/J)_X` (`AlgebraicGeometry.Etale.reductionModIdealUnit`) carries the fundamental
class `[Z ⊂ X] : Λ_X ⟶ Ri_! Ri^! (Λ_X(c)[2c])` to a class with supports in the reduced
coefficients `Λ_X(c)[2c] ⊗ᴸ (Λ/J)_X`, and the adjoint of this reduced class is the purity map
`cl_i` followed by `Ri^!(ρ)`: the purity map is natural in the coefficients, so the classes
reduce compatibly. -/
theorem supportedClassMap_fundamentalClass_reductionModIdealUnit (aX : X ⟶ Spec (.of k))
    [Smooth aX] (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (J : Ideal Λ) :
    supportedClassMap Λ i (fundamentalClass Λ c i aX hZ ≫
      (R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![ModuleCat.{u + 1} Λ]).map
        ((reductionModIdealUnit Λ X J).app ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)))) =
      fundamentalClassMap Λ c i aX hZ ≫ (R(i)^![ModuleCat.{u + 1} Λ]).map
        ((reductionModIdealUnit Λ X J).app ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) :=
  supportedClassMap_comp_map_rightDerivedUpperShriek Λ i _ _

end Etale

end AlgebraicGeometry
