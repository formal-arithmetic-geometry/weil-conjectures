/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-!
# Étale localization of the derived categories of étale sheaves

Two facts about a surjective or arbitrary étale morphism `u : U ⟶ X` and the derived categories
`D(X_ét, Λ)`:

* isomorphisms descend along surjective étale morphisms: a morphism `φ` of `D(X_ét, Λ)` with
  `Lu^* φ` invertible is invertible (blueprint `lem-pur-etale-iso-descent`). Pullback along `u`
  is exact, so it commutes with the cohomology sheaves, and the pullbacks along the members of a
  jointly surjective family of étale maps reflect isomorphisms of sheaves;
* the exceptional inverse image localizes along étale maps,
  `Lu^* Rf^! ≅ R(u ≫ f)^!` (blueprint `lem-amb-etale-adjoint-locality`, a node of the blueprint
  subsection `sk-prop-sf-cbc`, recorded here without proof).

## Main statements

- `AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map_of_surjective`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekIdIso`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-pur-etale-iso-descent`: Isomorphisms descend along étale surjections.

Let `u : U ⟶ X` be a surjective étale morphism and `φ : M ⟶ N` a morphism of `D(X_ét, Λ)`. If
`Lu^* φ` is an isomorphism, then so is `φ`. It suffices that the cohomology sheaves `ℋʳ(φ)` are
isomorphisms; as `u^*` is exact, `u^* ℋʳ(φ) ≅ ℋʳ(Lu^* φ)` is an isomorphism, and since `u` is
surjective every geometric point of `X` lifts to `U`, where the stalks of `u^* ℋʳ(φ)` are those
of `ℋʳ(φ)` (`AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective`).

The blueprint states this for bounded constructible complexes on separated schemes of finite
type over a field; neither hypothesis is needed. -/
theorem isIso_of_isIso_leftDerivedUpperStar_map_of_surjective {U X : Scheme.{u}} (u : U ⟶ X)
    [Etale u] [Surjective u]
    {M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ N) (h : IsIso ((L((u)^*[ModuleCat.{u + 1} Λ])).map φ)) : IsIso φ := by
  have h' : IsIso (D((u)^*[ModuleCat.{u + 1} Λ]).map φ) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ u) φ).1 h
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (fun _ : PUnit.{u + 1} ↦ u) (fun x ↦ ⟨⟨⟩, u.surjective x⟩) _ fun _ ↦ ?_
  exact (NatIso.isIso_map_iff
    (((u)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n) φ).2
    (Functor.map_isIso (_root_.DerivedCategory.homologyFunctor _ n)
      (D((u)^*[ModuleCat.{u + 1} Λ]).map φ))


/-! ### Descent of invertibility for dualizable objects -/

section Rigid

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]

/-- In an exact pairing `(X, Y)` with `X` invertible, the coevaluation `𝟙 ⟶ X ⊗ Y` is an
isomorphism: tensoring with `X` is an equivalence, so the unit of the adjunction
`tensorLeft Y ⊣ tensorLeft X` is invertible. -/
lemma isIso_coevaluation_of_isInvertible [BraidedCategory C] {X Y : C} [ExactPairing X Y]
    (hX : IsInvertible X) : IsIso (η_ X Y) := by
  obtain ⟨Z, ⟨e⟩, ⟨e'⟩⟩ := hX
  have : (tensorLeft X).IsEquivalence :=
    Functor.isEquivalence_of_iso (G := tensorLeft X)
      (F := (tensorRightEquivalenceOfTensorIso e e').functor)
      (NatIso.ofComponents (fun W ↦ (β_ X W).symm) fun f ↦ by
        change f ▷ X ≫ _ = _
        simp)
  have h := NatIso.isIso_app_of_isIso (tensorLeftAdjunction X Y).unit (𝟙_ C)
  have hu : (tensorLeftAdjunction X Y).unit.app (𝟙_ C) =
      (λ_ _).inv ≫ η_ X Y ▷ 𝟙_ C ≫ (α_ X Y (𝟙_ C)).hom := by
    simp [tensorLeftAdjunction, tensorLeftHomEquiv]
  rw [hu] at h
  have : IsIso (η_ X Y ▷ 𝟙_ C) := by
    have := IsIso.of_isIso_comp_left (λ_ (𝟙_ C)).inv (η_ X Y ▷ 𝟙_ C ≫ (α_ X Y (𝟙_ C)).hom)
    exact IsIso.of_isIso_comp_right _ (α_ X Y (𝟙_ C)).hom
  rw [MonoidalCategory.whiskerRight_id] at this
  have := IsIso.of_isIso_comp_left (ρ_ (𝟙_ C)).hom (η_ X Y ≫ (ρ_ (X ⊗ Y)).inv)
  exact IsIso.of_isIso_comp_right (η_ X Y) (ρ_ (X ⊗ Y)).inv

/-- **Invertibility of dualizable objects is reflected by conservative monoidal functors.** If
`F` is monoidal and reflects isomorphisms, `X` is dualizable and `F X` is invertible, then `X` is
invertible: the coevaluation of the image of the duality of `X` is invertible
(`isIso_coevaluation_of_isInvertible`), hence so is `F` of the coevaluation of `X`. -/
lemma isInvertible_of_isInvertible_map [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D)
    [F.Monoidal] (hF : ∀ {M N : C} (φ : M ⟶ N), IsIso (F.map φ) → IsIso φ) {X : C}
    (hX : IsDualizable X) (h : IsInvertible (F.obj X)) : IsInvertible X := by
  obtain ⟨_⟩ := hX
  let _ := ExactPairing.map F X Xᘁ
  have h' : IsIso (ε F ≫ F.map (η_ X Xᘁ) ≫ δ F X Xᘁ) :=
    isIso_coevaluation_of_isInvertible (X := F.obj X) (Y := F.obj Xᘁ) h
  have : IsIso (F.map (η_ X Xᘁ) ≫ δ F X Xᘁ) := IsIso.of_isIso_comp_left (ε F) _
  have : IsIso (F.map (η_ X Xᘁ)) := IsIso.of_isIso_comp_right _ (δ F X Xᘁ)
  have := hF _ this
  exact (isInvertible_iff_of_braided X).2 ⟨Xᘁ, ⟨(asIso (η_ X Xᘁ)).symm⟩⟩

end Rigid

/-- Lean-only partial step towards blueprint `lem-pur-co-smooth-etale-locality`: invertibility
of a dualizable object descends along a surjective étale morphism. If `L ∈ D(X_ét, Λ)` is
dualizable and `Lu^* L` is invertible, then `L` is invertible: `Lu^*` is monoidal and reflects
isomorphisms (`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map_of_surjective`).
Whether `ω_f` is dualizable is not known in general, so this does not give clause 1 of the
descent `AlgebraicGeometry.Etale.IsCohomologicallySmooth.of_comp_of_surjective`. -/
theorem isInvertible_of_isInvertible_leftDerivedUpperStar {U X : Scheme.{u}} (u : U ⟶ X)
    [Etale u] [Surjective u]
    {L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hd : IsDualizable L)
    (h : IsInvertible ((L((u)^*[ModuleCat.{u + 1} Λ])).obj L)) : IsInvertible L := by
  obtain ⟨_⟩ := nonempty_monoidal_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) u
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  exact isInvertible_of_isInvertible_map _
    (fun φ hφ ↦ isIso_of_isIso_leftDerivedUpperStar_map_of_surjective Λ u φ hφ) hd h

variable [Finite Λ]

/-- Blueprint `lem-amb-etale-adjoint-locality`: Étale localization of the ambient adjoint.

For a separated étale morphism `u : U ⟶ X` of finite type, and `f : X ⟶ Y` such that `f` and
`h = u ≫ f` admit compactifications, the exceptional inverse image localizes along `u`:

`Lu^* Rf^! K ≅ R(u ≫ f)^! K`,

naturally in `K`. The blueprint also records that the extension by zero `u_!` along `u` is
exact and left adjoint to `u^*`; the extension by zero along an étale map that is not an open
immersion is not available in the library. The canonical isomorphism is the mate of the
composition `R(u ≫ f)_! ≅ Rf_! ⋙ Ru_!` with `Ru_! ⊣ Lu^*`; only its existence is recorded.

This is a node of the blueprint subsection `sk-prop-sf-cbc`. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale
    {U X Y : Scheme.{u}} (u : U ⟶ X) [Etale u] [IsSeparated u] [QuasiCompact u]
    (f : X ⟶ Y) (h : U ⟶ Y) (w : u ≫ f = h) [HasCompactification f]
    [HasCompactification h] :
    Nonempty (R(f)^![ModuleCat.{u + 1} Λ] ⋙ L((u)^*[ModuleCat.{u + 1} Λ]) ≅
      R(h)^![ModuleCat.{u + 1} Λ]) :=
  sorry

/-- The exceptional inverse image along the identity is the identity, `R(𝟙 X)^! ≅ 𝟭`: the
identity is a quasi-compact open immersion, for which `Rj^! ≅ D(j^*)`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion`), and `(𝟙 X)^* ≅ 𝟭`. -/
noncomputable def rightDerivedUpperShriekIdIso (X : Scheme.{u}) :
    R(𝟙 X)^![ModuleCat.{u + 1} Λ] ≅ 𝟭 _ :=
  rightDerivedUpperShriekIsoOfIsOpenImmersion Λ (𝟙 X) ≪≫
    Functor.mapDerivedCategoryNatIso (Etale.upperStarId _ X) ≪≫
    Functor.mapDerivedCategoryIdIso _

end Etale

end AlgebraicGeometry
