/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.CechCoefficientComparisonData

/-! # Strict Čech coefficient maps and their totalizations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false
universe u wYp
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace CategoryTheory

/-- Strict coefficient maps, unit augmentations, their chain square, homotopy invariance,
and refinement naturality for arbitrary nonnegative complexes.

Source: Stacks derived.tex, Tags 015F and 070I, and homology.tex Tag 0133;
steps 3, 5 (chain square), 6, and 7 of the coefficient comparison.
(blueprint: lem-sfb-cech-coefficient-strict-maps).

Proof: transpose the scalar commutations across the slice adjunctions. The counit
mate equation and the sectionwise identity for pullback show that these commute
with relocalization, hence all cofaces and degeneracies. Apply the alternating
coface functor, then the complex functor in the resolution direction and flip.
The component is exactly cechCoefficientComponent. Totalize using the inverse
finite-coproduct comparison; the coprojection equations characterize the total.
Insert each localization unit in degree (0,q), giving the two augmentations.
The counit mate equation implies the unit mate equation by the triangle identities;
this and naturality at t give their chain square. Extend by zero, commuting the
additive functors with extension, to obtain the equation below.
A homotopy between t₀ and t₁ maps columnwise to a homotopy; on column n multiply
by (-1)^n. Horizontal terms cancel and vertical terms yield the difference of
the maps. Extend and apply Q, which identifies homotopic maps. Finally every
refinement is a morphism of the same nerve diagrams; its naturality square gives
the component equation, and finite diagonal coprojections give the total equation.
-/
theorem cech_coefficient_strict_maps
    {C Y : Type u} [SmallCategory C] [SmallCategory Y]
    {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
    {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}
    {f : RingedToposMorphism R S} {f' : RingedToposMorphism R' S'}
    {φ : R' ⟶ R} {ψ : S' ⟶ S} {hd : f.direct = f'.direct}
    {D : CoherentCechImageModel R} {D' : CoherentCechImageModel R'}
    [HasDerivedCategory.{wYp} (ringedSiteModules.{u} S')]
    (E : CechCoefficientCommutations f f' φ ψ hd D D')
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (I' : CochainComplex (ringedSiteModules.{u} R') ℕ) :
    ∃ (maps : ∀ (V : Sheaf J (Type u))
        (t : (cechCoefficientComplex φ (.up ℕ)).obj I ⟶ I'),
        CechCoefficientMapData E V I I' t)
      (b : ∀ V : Sheaf J (Type u),
        (f.modules.mapHomologicalComplex (.up ℕ)).obj I ⟶
          (D.bicomplex f.modules V I).total (.up ℕ))
      (b' : ∀ V : Sheaf J (Type u),
        (f'.modules.mapHomologicalComplex (.up ℕ)).obj I' ⟶
          (D'.bicomplex f'.modules V I').total (.up ℕ)),
      (∀ V : Sheaf J (Type u), D.IsAugmentation f.modules V I (b V) ∧
        D'.IsAugmentation f'.modules V I' (b' V)) ∧
      (∀ (V : Sheaf J (Type u)) (t : (cechCoefficientComplex φ (.up ℕ)).obj I ⟶ I'),
        (cechCoefficientComplex ψ (.up ℤ)).map
            (cechCoefficientExtendMap f.modules (b V)) ≫
          cechCoefficientExtendMap (SheafOfModules.restrictScalars ψ) (maps V t).total =
        (NatTrans.mapHomologicalComplex E.base.hom (.up ℤ)).app
            (I.extend ComplexShape.embeddingUpNat) ≫
          (f'.modules.mapHomologicalComplex (.up ℤ)).map (cechCoefficientLiftExtend φ t) ≫
            cechCoefficientExtendMap f'.modules (b' V)) ∧
      (∀ (V : Sheaf J (Type u)) (t₀ t₁ :
          (cechCoefficientComplex φ (.up ℕ)).obj I ⟶ I'),
        Nonempty (Homotopy t₀ t₁) →
        DerivedCategory.Q.map (HomologicalComplex.extendMap (maps V t₀).total
            ComplexShape.embeddingUpNat) =
          DerivedCategory.Q.map (HomologicalComplex.extendMap (maps V t₁).total
            ComplexShape.embeddingUpNat) ∧
        ∀ n : ℕ, DerivedCategory.Q.map (HomologicalComplex.extendMap
            ((maps V t₀).bicomplex.f n) ComplexShape.embeddingUpNat) =
          DerivedCategory.Q.map (HomologicalComplex.extendMap
            ((maps V t₁).bicomplex.f n) ComplexShape.embeddingUpNat)) ∧
      (∀ (V W : Sheaf J (Type u)) (r : W ⟶ V)
        (t : (cechCoefficientComplex φ (.up ℕ)).obj I ⟶ I'),
        (cechCoefficientComplex ψ (.up ℕ)).map
            (D.totalRefinement f.modules r I) ≫ (maps W t).total =
          (maps V t).total ≫ D'.totalRefinement f'.modules r I' ∧
        ∀ n q : ℕ,
          (SheafOfModules.restrictScalars ψ).map (f.modules.map
              ((D.image.map (((Arrow.mapCechNerve
                (Arrow.homMk r (𝟙 _) (terminal.hom_ext _ _) :
                  Arrow.mk (terminal.from W) ⟶ Arrow.mk (terminal.from V))).app
                  (op (SimplexCategory.mk n))).op)).app (I.X q))) ≫
            ((maps W t).bicomplex.f n).f q =
          ((maps V t).bicomplex.f n).f q ≫ f'.modules.map
            ((D'.image.map (((Arrow.mapCechNerve
              (Arrow.homMk r (𝟙 _) (terminal.hom_ext _ _) :
                  Arrow.mk (terminal.from W) ⟶ Arrow.mk (terminal.from V))).app
                (op (SimplexCategory.mk n))).op)).app (I'.X q))) := by
  sorry

end CategoryTheory
