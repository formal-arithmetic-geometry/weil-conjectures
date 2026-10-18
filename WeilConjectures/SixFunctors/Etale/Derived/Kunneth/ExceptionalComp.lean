/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ExceptionalClosed

/-!

# The exceptional Künneth property and its stability under composition

For morphisms `f₁ : X₁ ⟶ Y₁` and `f₂ : X₂ ⟶ Y₂` and a morphism `φ : P ⟶ Q` lying over them,
i.e. `φ ≫ q₁ = p₁ ≫ f₁` and `φ ≫ q₂ = p₂ ≫ f₂` for maps `pᵢ : P ⟶ Xᵢ`, `qᵢ : Q ⟶ Yᵢ`, the
*exceptional Künneth property* (`AlgebraicGeometry.Etale.ExceptionalKunneth`) asserts that for
all `N₁ ∈ Dctf(Y₁, Λ)` and `N₂ ∈ Dctf(Y₂, Λ)`

`Lp₁^* Rf₁^! N₁ ⊗ᴸ Lp₂^* Rf₂^! N₂ ≅ Rφ^! (Lq₁^* N₁ ⊗ᴸ Lq₂^* N₂)`.

When `P = X₁ ×_S X₂`, `Q = Y₁ ×_S Y₂` with their projections and `φ = f₁ × f₂`, this is the
exceptional Künneth formula `α` of `prop-trf-exceptional-kunneth`, whose two sides are external
products. The property is stated for arbitrary `P` and `Q` so that it composes without
identifying iterated fibre products (`AlgebraicGeometry.Etale.ExceptionalKunneth.comp`), and is
symmetric in the two factors (`AlgebraicGeometry.Etale.ExceptionalKunneth.symm`).

## Main statements

- `AlgebraicGeometry.Etale.ExceptionalKunneth.comp`: composition.
- `AlgebraicGeometry.Etale.ExceptionalKunneth.symm`: exchanging the two factors.
- `AlgebraicGeometry.Etale.ExceptionalKunneth.of_isOpenImmersion`: open immersions.
- `AlgebraicGeometry.Etale.exceptionalKunneth_pullbackMapLeft_of_isClosedImmersion`: a closed
  immersion in the first factor and the identity in the second.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The composition isomorphism `Rh^! ≅ Rg^! ⋙ Rf^!` for any `h` equal to `f ≫ g`. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp_of_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) [HasCompactification f] [HasCompactification g]
    [HasCompactification h] [QuasiCompact h] :
    Nonempty (R(h)^![ModuleCat.{u + 1} Λ] ≅
      R(g)^![ModuleCat.{u + 1} Λ] ⋙ R(f)^![ModuleCat.{u + 1} Λ]) := by
  subst w
  exact nonempty_iso_rightDerivedUpperShriek_comp Λ f g

/-- `R𝟙^! ≅ 𝟭`. -/
noncomputable def rightDerivedUpperShriekIdIsoOfFinite (X : Scheme.{u}) :
    R(𝟙 X)^![ModuleCat.{u + 1} Λ] ≅ 𝟭 _ :=
  rightDerivedUpperShriekIsoOfIso (ModuleCat.{u + 1} Λ) (Iso.refl X) ≪≫
    leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X

/-- For an open immersion `j` with quasi-compact source map, `Rj^! ≅ Lj^*`. -/
noncomputable def rightDerivedUpperShriekIsoLeftDerivedUpperStar {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [HasCompactification j] :
    R(j)^![ModuleCat.{u + 1} Λ] ≅ L((j)^*[ModuleCat.{u + 1} Λ]) :=
  rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory _ j).symm

/-- The tensor product of two isomorphisms in `D(X_ét)`, written with `derivedTensor`. -/
noncomputable def derivedTensorMapIso {X : Scheme.{u}}
    {K K' M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e₁ : K ≅ K') (e₂ : M ≅ M') :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj M ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K').obj M' :=
  ((derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso e₁).app M ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K').mapIso e₂

/-- The derived pullback of `Lq₁^* N₁ ⊗ᴸ Lq₂^* N₂` along `φ : P ⟶ Q` with `φ ≫ qᵢ = pᵢ ≫ fᵢ` is
`Lp₁^* Lf₁^* N₁ ⊗ᴸ Lp₂^* Lf₂^* N₂`. -/
noncomputable def leftDerivedUpperStarDerivedTensorPullbackIso {P Q X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (q₁ : Q ⟶ Y₁) (q₂ : Q ⟶ Y₂) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (φ : P ⟶ Q) (w₁ : φ ≫ q₁ = p₁ ≫ f₁) (w₂ : φ ≫ q₂ = p₂ ≫ f₂)
    (N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((φ)^*[ModuleCat.{u + 1} Λ])).obj (((derivedTensor (ModuleCat.{u + 1} Λ) Q).obj
        ((L((q₁)^*[ModuleCat.{u + 1} Λ])).obj N₁)).obj ((L((q₂)^*[ModuleCat.{u + 1} Λ])).obj N₂)) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) P).obj ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((f₁)^*[ModuleCat.{u + 1} Λ])).obj N₁))).obj
          ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj ((L((f₂)^*[ModuleCat.{u + 1} Λ])).obj N₂)) :=
  leftDerivedUpperStarTensorIso _ φ _ _ ≪≫ derivedTensorMapIso Λ
    (((leftDerivedUpperStarComp _ φ q₁ (p₁ ≫ f₁) w₁.symm).app N₁).symm ≪≫
        ((leftDerivedUpperStarComp _ p₁ f₁).app N₁))
    (((leftDerivedUpperStarComp _ φ q₂ (p₂ ≫ f₂) w₂.symm).app N₂).symm ≪≫
        ((leftDerivedUpperStarComp _ p₂ f₂).app N₂))

/-- The **exceptional Künneth property** of `φ : P ⟶ Q` over `f₁ : X₁ ⟶ Y₁` and
`f₂ : X₂ ⟶ Y₂`, with respect to maps `pᵢ : P ⟶ Xᵢ` and `qᵢ : Q ⟶ Yᵢ`: for all
`N₁ ∈ Dctf(Y₁, Λ)` and `N₂ ∈ Dctf(Y₂, Λ)`,

`Lp₁^* Rf₁^! N₁ ⊗ᴸ Lp₂^* Rf₂^! N₂ ≅ Rφ^! (Lq₁^* N₁ ⊗ᴸ Lq₂^* N₂)`.

For the projections of fibre products `P = X₁ ×_S X₂`, `Q = Y₁ ×_S Y₂` and `φ = f₁ × f₂` this is
the exceptional Künneth formula `α` of `prop-trf-exceptional-kunneth`. -/
def ExceptionalKunneth {P Q X₁ X₂ Y₁ Y₂ : Scheme.{u}} (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂)
    (q₁ : Q ⟶ Y₁) (q₂ : Q ⟶ Y₂) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (φ : P ⟶ Q)
    [HasCompactification f₁] [HasCompactification f₂] [HasCompactification φ] : Prop :=
  ∀ ⦃N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))⦄
    ⦃N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))⦄,
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₁ N₁ →
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₂ N₂ →
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) P).obj ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(f₁)^![ModuleCat.{u + 1} Λ]).obj N₁))).obj ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj
          ((R(f₂)^![ModuleCat.{u + 1} Λ]).obj N₂)) ≅
      (R(φ)^![ModuleCat.{u + 1} Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) Q).obj
        ((L((q₁)^*[ModuleCat.{u + 1} Λ])).obj N₁)).obj ((L((q₂)^*[ModuleCat.{u + 1} Λ])).obj N₂)))

namespace ExceptionalKunneth

variable {Λ}

/-- **Composition.** If `φf : P ⟶ Q` has the exceptional Künneth property over `(f₁, f₂)` and
`φg : Q ⟶ R` over `(g₁, g₂)`, and `Rgᵢ^!` preserves `Dctf`, then `φf ≫ φg` has it over
`(f₁ ≫ g₁, f₂ ≫ g₂)`: this is the composition law `R(f ≫ g)^! ≅ Rf^! ∘ Rg^!`. -/
theorem comp {P Q R W₁ W₂ X₁ X₂ Y₁ Y₂ : Scheme.{u}} {p₁ : P ⟶ W₁} {p₂ : P ⟶ W₂}
    {q₁ : Q ⟶ X₁} {q₂ : Q ⟶ X₂} {r₁ : R ⟶ Y₁} {r₂ : R ⟶ Y₂} {f₁ : W₁ ⟶ X₁} {f₂ : W₂ ⟶ X₂}
    {g₁ : X₁ ⟶ Y₁} {g₂ : X₂ ⟶ Y₂} {φf : P ⟶ Q} {φg : Q ⟶ R}
    [HasCompactification f₁] [HasCompactification f₂] [HasCompactification g₁]
    [HasCompactification g₂] [HasCompactification φf] [HasCompactification φg]
    (hf : ExceptionalKunneth Λ p₁ p₂ q₁ q₂ f₁ f₂ φf)
    (hg : ExceptionalKunneth Λ q₁ q₂ r₁ r₂ g₁ g₂ φg)
    (hg₁ : ∀ N, constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₁ N →
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X₁ ((R(g₁)^![ModuleCat.{u + 1} Λ]).obj N))
    (hg₂ : ∀ N, constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₂ N →
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X₂ ((R(g₂)^![ModuleCat.{u + 1} Λ]).obj N))
    (h₁ : W₁ ⟶ Y₁) (h₂ : W₂ ⟶ Y₂) (φh : P ⟶ R) (w₁ : f₁ ≫ g₁ = h₁) (w₂ : f₂ ≫ g₂ = h₂)
    (w : φf ≫ φg = φh) [HasCompactification h₁] [HasCompactification h₂]
    [HasCompactification φh] [QuasiCompact h₁] [QuasiCompact h₂] [QuasiCompact φh] :
    ExceptionalKunneth Λ p₁ p₂ r₁ r₂ h₁ h₂ φh := by
  intro N₁ N₂ hN₁ hN₂
  obtain ⟨a⟩ := hg hN₁ hN₂
  obtain ⟨b⟩ := hf (hg₁ _ hN₁) (hg₂ _ hN₂)
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp_of_eq Λ f₁ g₁ h₁ w₁
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_comp_of_eq Λ f₂ g₂ h₂ w₂
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_comp_of_eq Λ φf φg φh w
  exact ⟨derivedTensorMapIso Λ ((L((p₁)^*[ModuleCat.{u + 1} Λ])).mapIso (e₁.app N₁))
      ((L((p₂)^*[ModuleCat.{u + 1} Λ])).mapIso (e₂.app N₂)) ≪≫ b ≪≫
    (R(φf)^![ModuleCat.{u + 1} Λ]).mapIso a ≪≫ (e.app _).symm⟩

/-- **Symmetry.** The exceptional Künneth property is symmetric in the two factors, by the
symmetry of the derived tensor product. -/
theorem symm {P Q X₁ X₂ Y₁ Y₂ : Scheme.{u}} {p₁ : P ⟶ X₁} {p₂ : P ⟶ X₂}
    {q₁ : Q ⟶ Y₁} {q₂ : Q ⟶ Y₂} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {φ : P ⟶ Q}
    [HasCompactification f₁] [HasCompactification f₂] [HasCompactification φ]
    (h : ExceptionalKunneth Λ p₁ p₂ q₁ q₂ f₁ f₂ φ) :
    ExceptionalKunneth Λ p₂ p₁ q₂ q₁ f₂ f₁ φ := by
  intro N₂ N₁ hN₂ hN₁
  obtain ⟨a⟩ := h hN₁ hN₂
  obtain ⟨βP⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) P
  obtain ⟨βQ⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) Q
  exact ⟨(βP.app _).app _ ≪≫ a ≪≫ (R(φ)^![ModuleCat.{u + 1} Λ]).mapIso ((βQ.app _).app _)⟩

/-- **Open immersions.** If `f₁`, `f₂` and `φ` are quasi-compact open immersions, then
`φ` has the exceptional Künneth property: the three exceptional inverse images are restrictions
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion`), and the derived
pullback is monoidal. -/
theorem of_isOpenImmersion {P Q X₁ X₂ Y₁ Y₂ : Scheme.{u}} (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂)
    (q₁ : Q ⟶ Y₁) (q₂ : Q ⟶ Y₂) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (φ : P ⟶ Q)
    [IsOpenImmersion f₁] [IsOpenImmersion f₂] [IsOpenImmersion φ]
    [QuasiCompact f₁] [QuasiCompact f₂] [QuasiCompact φ]
    [HasCompactification f₁] [HasCompactification f₂] [HasCompactification φ]
    (w₁ : φ ≫ q₁ = p₁ ≫ f₁) (w₂ : φ ≫ q₂ = p₂ ≫ f₂) :
    ExceptionalKunneth Λ p₁ p₂ q₁ q₂ f₁ f₂ φ := by
  intro N₁ N₂ _ _
  exact ⟨derivedTensorMapIso Λ
      ((L((p₁)^*[ModuleCat.{u + 1} Λ])).mapIso
        ((rightDerivedUpperShriekIsoLeftDerivedUpperStar Λ f₁).app N₁))
      ((L((p₂)^*[ModuleCat.{u + 1} Λ])).mapIso
        ((rightDerivedUpperShriekIsoLeftDerivedUpperStar Λ f₂).app N₂)) ≪≫
    (leftDerivedUpperStarDerivedTensorPullbackIso Λ p₁ p₂ q₁ q₂ f₁ f₂ φ w₁ w₂ N₁ N₂).symm ≪≫
    ((rightDerivedUpperShriekIsoLeftDerivedUpperStar Λ φ).app _).symm⟩

end ExceptionalKunneth

/-- Blueprint `prop-trf-exceptional-kunneth`, closed immersions: for `Y₁`, `Y₂` separated of
finite type over a field `k` and a closed immersion `i : Z ⟶ Y₁`, the base change
`i × 𝟙 : Z ×_k Y₂ ⟶ Y₁ ×_k Y₂` has the exceptional Künneth property over `(i, 𝟙)`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_pullbackMapLeft_externalProduct`). -/
theorem exceptionalKunneth_pullbackMapLeft_of_isClosedImmersion {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {Y₁ Y₂ Z : Scheme.{u}}
    (b₁ : Y₁ ⟶ Spec (.of k)) (b₂ : Y₂ ⟶ Spec (.of k))
    [IsSeparated b₁] [LocallyOfFiniteType b₁] [QuasiCompact b₁]
    [IsSeparated b₂] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
    (i : Z ⟶ Y₁) [IsClosedImmersion i] :
    ExceptionalKunneth Λ (pullback.fst (i ≫ b₁) b₂) (pullback.snd (i ≫ b₁) b₂)
      (pullback.fst b₁ b₂) (pullback.snd b₁ b₂) i (𝟙 Y₂) (pullbackMapLeft b₁ b₂ i) := by
  intro N₁ N₂ h₁ h₂
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_pullbackMapLeft_externalProduct Λ b₁ b₂ i
    h₁ h₂
  exact ⟨((derivedTensor (ModuleCat.{u + 1} Λ) _).obj _).mapIso
      ((L((pullback.snd (i ≫ b₁) b₂)^*[ModuleCat.{u + 1} Λ])).mapIso
        ((rightDerivedUpperShriekIdIsoOfFinite Λ Y₂).app N₂)) ≪≫ e.symm⟩

end Etale

end AlgebraicGeometry
