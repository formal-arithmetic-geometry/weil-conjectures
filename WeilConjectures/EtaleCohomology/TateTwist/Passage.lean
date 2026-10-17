/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor

/-!
# Passing a Tate twist through a functor

Let `e : Λ_X ≅ Λ_X(m)` be a trivialisation of a twisting object, for instance the one given by
a basis of the twist module (for `m = 1`, a primitive `n`-th root of unity `ζ` on `X`,
`AlgebraicGeometry.Etale.constantComplexIsoTateTwistObjectOne`). It induces an isomorphism
`b_e : K ≅ K ⊗ᴸ Λ_X ≅ K ⊗ᴸ Λ_X(m) = K(m)`, natural in `K`
(`AlgebraicGeometry.Etale.tateTwistIsoOfTrivialization`). For a functor
`Φ : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` and trivialisations `e_X`, `e_Y` on both sides, the composite

`τ_Φ = b_{e_Y} ∘ Φ(b_{e_X})⁻¹ : Φ(K(m)) ≅ Φ(K) ≅ Φ(K)(m)`

passes the twist through `Φ` (`AlgebraicGeometry.Etale.tateTwistPassageIso`).

## Main definitions

- `AlgebraicGeometry.Etale.tateTwistIsoOfTrivialization`: `b_e : K ≅ K(m)`.
- `AlgebraicGeometry.Etale.tateTwistPassageIso`: `τ_Φ : Φ(K(m)) ≅ Φ(K)(m)`.
- `AlgebraicGeometry.Etale.constantComplexIsoTateTwistObjectOne`: the trivialisation
  `Λ_X ≅ Λ_X(1)` given by an `n`-th root of unity whose powers have invertible differences.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ]

section Passage

variable {X Y : Scheme.{u}} {m : ℤ}

/-- The isomorphism `b_e : K ≅ K ⊗ᴸ Λ_X ≅ K ⊗ᴸ Λ_X(m) = K(m)` induced by a trivialisation
`e : Λ_X ≅ Λ_X(m)` of the twisting object, through the right unitor. It is natural in `K`. -/
noncomputable def tateTwistIsoOfTrivialization (e : constantComplex Λ X ≅ tateObject Λ X m) :
    𝟭 _ ≅ tateTwist Λ X m :=
  (derivedTensorRightUnitorNatIso (ModuleCat.{u + 1} Λ) X).symm ≪≫
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso e

lemma tateTwistIsoOfTrivialization_hom_app (e : constantComplex Λ X ≅ tateObject Λ X m)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (tateTwistIsoOfTrivialization Λ e).hom.app K =
      (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X K).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map e.hom :=
  rfl

/-- Blueprint `pur9-def-twist-passage`: Passing a twist through a linear functor

For a functor `Φ : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` and trivialisations `e_X : Λ_X ≅ Λ_X(m)` and
`e_Y : Λ_Y ≅ Λ_Y(m)` (in the blueprint both induced by a basis `e` of the twist module `P(m)`),
the isomorphism

`τ_{Φ, K} = b_{e_Y} ∘ Φ(b_{e_X})⁻¹ : Φ(K(m)) ≅ Φ(K) ≅ Φ(K)(m)`,

natural in `K`, where `b_e : K ≅ K(m)` is `AlgebraicGeometry.Etale.tateTwistIsoOfTrivialization`.
The blueprint asks `Φ` to be `Λ`-linear; this is not needed for the construction. -/
noncomputable def tateTwistPassageIso
    (Φ : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eX : constantComplex Λ X ≅ tateObject Λ X m) (eY : constantComplex Λ Y ≅ tateObject Λ Y m) :
    tateTwist Λ X m ⋙ Φ ≅ Φ ⋙ tateTwist Λ Y m :=
  Functor.isoWhiskerRight (tateTwistIsoOfTrivialization Λ eX).symm Φ ≪≫ Φ.leftUnitor ≪≫
    Φ.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft Φ (tateTwistIsoOfTrivialization Λ eY)

lemma tateTwistPassageIso_hom_app
    (Φ : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eX : constantComplex Λ X ≅ tateObject Λ X m) (eY : constantComplex Λ Y ≅ tateObject Λ Y m)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (tateTwistPassageIso Λ Φ eX eY).hom.app K =
      Φ.map ((tateTwistIsoOfTrivialization Λ eX).inv.app K) ≫
        (tateTwistIsoOfTrivialization Λ eY).hom.app (Φ.obj K) := by
  simp [tateTwistPassageIso]

end Passage

section RootOfUnity

variable {Λ} (X : Scheme.{u}) [HasInvertibleExponent Λ X] [NeZero (ringChar Λ)]

/-- The trivialisation `Λ_X ≅ Λ_X(1) = μₙ ⊗ Λ` given by an `n`-th root of unity `ζ` on `X` whose
powers have invertible differences, `n` being the characteristic of `Λ`: `ζ` generates
`μₙ ≅ ℤ/n` (`AlgebraicGeometry.Etale.tateSheafIsoConstantSheaf`). This is the trivialisation
induced by the basis `ζ ⊗ 1` of the twist module `P(1)`. -/
noncomputable def constantComplexIsoTateTwistObjectOne (ζ : Γ(X, ⊤)ˣ)
    (hζ : ζ ^ ringChar Λ = 1)
    (hζ' : ∀ i < ringChar Λ, ∀ j < ringChar Λ, i ≠ j →
      IsUnit ((ζ : Γ(X, ⊤)) ^ i - (ζ : Γ(X, ⊤)) ^ j)) :
    constantComplex Λ X ≅ tateTwistObject Λ X 1 :=
  (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).symm ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (tateSheafIsoConstantSheaf X ζ hζ hζ').symm ≪≫
    (tateTwistObjectOneIso X Λ).symm

end RootOfUnity

end Etale

end AlgebraicGeometry
