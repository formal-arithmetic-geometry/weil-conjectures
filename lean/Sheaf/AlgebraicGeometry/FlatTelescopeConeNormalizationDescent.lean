/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.AlgebraicGeometry.FlatTelescopeStageMapRefinement
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso

/-! # Extending normalized sum maps across transition cones

Source: the cone and refinement parts of steps 1--2 of
lem-sc-flat-telescope-normalization-morphisms.
(blueprint: lem-sc-flat-telescope-cone-normalization-descent). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- Extend supplied normalized sum morphisms across telescope transition cones.
The sum morphisms, their coprojection formulas, naturality for stage sums, and
translated-unit shift equation are inputs, rather than constructions of this lemma.

Source: steps 1--2 of lem-sc-flat-telescope-normalization-morphisms, inherited
agent expansion; Stacks Tags 06YS and 06YJ for flat models and common refinements.

Proof. For each bounded-flat tower, the naturality of the supplied sum morphisms
intertwines one minus transition. Apply the same sum map to both copies of the
sum, and the supplied shifted sum map to the translated copy in the cone.
Use flat resolutions of the arrow diagram to realize these squares by chain maps
and compatible homotopies before taking the explicit mapping cone; arbitrary
completion of a square to a triangle map is not used. The shifted-sum equation
identifies the differential and connecting component with the prescribed e.
For a tower map, resolve its square together with these arrow diagrams and take
the explicit cone map. The two composites are equal after localization.
A common flat arrow-diagram refinement of two presentations has invertible
localized augmentation; cancellation identifies their transported cone maps.
Thus the maps descend to homotopy objects and are natural for the stage maps,
including the integer shifts and homotopy-isomorphism transports in their definition.
For a bounded-flat telescope representative, resolve its augmentation alongside
a constant bounded-flat tower. The coprojection formulas and bounded naturality
identify the comparison with beta; do this also for its one-fold translate.
Finally translate the same resolved cone square: the two supplied sum maps obey
the displayed shift identity, and the explicit cone formulas preserve it, yielding
exactly the telescope shift equation. No inverse for a comparison is required.
Zero towers and empty schemes use zero maps, and the bounds are stage-dependent.
(blueprint: lem-sc-flat-telescope-cone-normalization-descent). -/
theorem exists_flat_telescope_cone_normalization_descent
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (β : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        boundedFlatShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X))
    (hβnat : (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : boundedFlatShiftRepresentative Y X) (hX' : boundedFlatShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (β X' hX').hom =
            (β X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s))
    (σ₀ : ∀ (E : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (∐ E)
        (DerivedCategory.Qh ⋙ derivedPullback f).obj X ⟶
          ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z)).obj X)
    (σ₁ : ∀ (E : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)),
        let X := ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (∐ E))⟦(1 : ℤ)⟧
        (DerivedCategory.Qh ⋙ derivedPullback f).obj X ⟶
          ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z)).obj X)
    (hσ0ι : ∀ (E : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) (n : ℕ),
        (DerivedCategory.Qh ⋙ derivedPullback f).map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Sigma.ι E n)) ≫
            σ₀ E hb hf =
          (β
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (E n))
            ⟨E n, hb n, hf n, Or.inl rfl⟩).hom ≫
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z)).map
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Sigma.ι E n)))
    (hσ1ι : ∀ (E : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) (n : ℕ),
        (DerivedCategory.Qh ⋙ derivedPullback f).map
          (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Sigma.ι E n))⟦(1 : ℤ)⟧') ≫
            σ₁ E hb hf =
          (β (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (E n))⟦(1 : ℤ)⟧)
            ⟨E n, hb n, hf n, Or.inr rfl⟩).hom ≫
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z)).map (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
              (Sigma.ι E n))⟦(1 : ℤ)⟧'))
    (hσ0nat : ∀ (E E' : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i))
        (hb' : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E' n).X i))
        (hf' : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E' n).X i))
        (a : ∀ n : ℕ, E n ⟶ E' n),
        (DerivedCategory.Qh ⋙ derivedPullback f).map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Limits.Sigma.map a)) ≫
            σ₀ E' hb' hf' =
          σ₀ E hb hf ≫
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z)).map
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Limits.Sigma.map a)))
    (hσ1nat : ∀ (E E' : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i))
        (hb' : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E' n).X i))
        (hf' : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E' n).X i))
        (a : ∀ n : ℕ, E n ⟶ E' n),
        (DerivedCategory.Qh ⋙ derivedPullback f).map
          (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Limits.Sigma.map a))⟦(1 : ℤ)⟧') ≫
            σ₁ E' hb' hf' =
          σ₁ E hb hf ≫
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z)).map (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
              (Limits.Sigma.map a))⟦(1 : ℤ)⟧'))
    (hσshift : ∀ (E : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (∐ E)
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        σ₁ E hb hf ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            σ₀ E hb hf⟦(1 : ℤ)⟧') :
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ⟶
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'), flatTelescopeStageMap Y s →
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX') =
            (α X hX) ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        (∀ (X : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X)
          (hb : boundedFlatShiftRepresentative Y X), α X hX = (β X hb).hom) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩) ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, htel, Or.inl rfl⟩)⟦(1 : ℤ)⟧' := by sorry

end AlgebraicGeometry
