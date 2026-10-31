/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCoordinatesExistence
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearScalarTensorComposition
import WeilConjectures.AlgebraicGeometry.Geometry.SemilinearCoefficientPullbackComposition

/-! # A step in normalized strict compactification comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

section MatePasting
universe a v
variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type a}
  [Category.{v} A₀] [Category.{v} A₁] [Category.{v} A₂]
  [Category.{v} B₀] [Category.{v} B₁] [Category.{v} B₂]

private theorem mate_pasting_with_comparisons
    {L₀ : A₀ ⥤ B₀} {R₀ : B₀ ⥤ A₀}
    {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁}
    {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂}
    (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G₁ : A₀ ⥤ A₁} {G₂ : A₁ ⥤ A₂} {G : A₀ ⥤ A₂}
    {H₁ : B₀ ⥤ B₁} {H₂ : B₁ ⥤ B₂} {H : B₀ ⥤ B₂}
    (α₁ : TwoSquare G₁ L₀ L₁ H₁) (α₂ : TwoSquare G₂ L₁ L₂ H₂)
    (α : TwoSquare G L₀ L₂ H)
    (γ : G₁ ⋙ G₂ ⟶ G) (η : H₁ ⋙ H₂ ⟶ H)
    (hα : ∀ P : A₀, L₂.map (γ.app P) ≫ α.natTrans.app P =
      α₂.natTrans.app (G₁.obj P) ≫ H₂.map (α₁.natTrans.app P) ≫ η.app (L₀.obj P))
    (Q : B₀) :
    G₂.map ((mateEquiv adj₀ adj₁ α₁).natTrans.app Q) ≫
        (mateEquiv adj₁ adj₂ α₂).natTrans.app (H₁.obj Q) ≫ R₂.map (η.app Q) =
      γ.app (R₀.obj Q) ≫ (mateEquiv adj₀ adj₂ α).natTrans.app Q := by
  apply (adj₂.homEquiv _ _).symm.injective
  change L₂.map _ ≫ adj₂.counit.app _ = L₂.map _ ≫ adj₂.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  have hε := adj₂.counit.naturality (η.app Q)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hε
  rw [hε]
  erw [reassoc_of% (mateEquiv_counit adj₁ adj₂ α₂ (H₁.obj Q))]
  have hn := α₂.natTrans.naturality ((mateEquiv adj₀ adj₁ α₁).natTrans.app Q)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← H₂.map_comp_assoc]
  erw [mateEquiv_counit adj₀ adj₁ α₁ Q]
  rw [H₂.map_comp]
  have hη := η.naturality (adj₀.counit.app Q)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hη
  erw [Category.assoc, hη]
  erw [← reassoc_of% (hα (R₀.obj Q))]
  erw [mateEquiv_counit adj₀ adj₂ α Q]

end MatePasting

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Existence of coefficient and geometric coordinates with their three-index coherences.
Source: blueprint operations proof (2), expanded steps 1--3; Zheng Construction 4.1,
Lemma 4.10; Stacks 07A4 and 06YS.
(blueprint: lem-sp-strict-system-geometric-realization).

Proof: write ell as a unit times a positive power of the specified uniformizer.
Taking powers gives equality of the actual quotient ideals and finiteness of R_n.
Use the identity on sections to identify strict towers with the ringed sequence site.
For each scheme apply semilinearDerivedSections to its actual quotient system, taking
its systems field as the calculus. Transport inverse and direct image along the
constant-ring section identifications. Construct ordinary composition from composition
of inverse image; localize it termwise. The normalized open extension and open tensor
comparison are supplied by openTensorNormalization on the sequence site.
For the scalar/tensor equation, resolve the two level inputs by flat K-flat complexes.
Both composites send each pure total summand to the identical scalar-associated
pure tensor; scalarComposition_transpose fixes the scalar associator, so localization
and naturality give the equation for arbitrary inputs. This includes equal indices.
For the geometric equation, the coefficient restriction squares compose on sections.
Transpose their composite using the specified scalar adjunctions and apply
mateEquiv_vcomp. Naturality moves the scalar comparison through the right adjoint,
giving precisely the displayed coefficientMate equation. No coefficient mate is
inverted, and no flatness of a quotient map is used. -/
theorem strictSystemGeometricRealization :
    ∃ b : Base l E, ∃ o : Operations l E b,
  (∀ T : Scheme.{u},
    ∃ s : SemilinearSections.SemilinearDerivedSectionsData.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (B l E T) (tau l E T), s.systems = b.calculus T) ∧
    (∀ (T : Scheme.{u}) {r m n : ℕ} (h : n ≤ m) (k : m ≤ r)
    (K L : SemilinearSections.D.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (B l E T r)),
    ((b.calculus T).scalar h).T.map
        (((b.calculus T).scalarTensor k).hom.app (K, L)) ≫
      ((b.calculus T).scalarTensor h).hom.app
        (((b.calculus T).scalar k).T.obj K, ((b.calculus T).scalar k).T.obj L) ≫
      (comparisonLevelTensor l E b T n).map
        (Prod.mkHom (((b.calculus T).scalarComposition h k).hom.app K)
          (((b.calculus T).scalarComposition h k).hom.app L)) =
    ((b.calculus T).scalarComposition h k).hom.app
        ((comparisonLevelTensor l E b T r).obj (K, L)) ≫
      ((b.calculus T).scalarTensor (h.trans k)).hom.app (K, L)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    {r m n : ℕ} (h : n ≤ m) (k : m ≤ r)
    (Q : SemilinearSections.D.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) ((o.geometry f).generic.coefficients r)),
    ((b.calculus Y).scalar h).T.map
        ((comparisonCoefficientMate l E b o f k).app Q) ≫
      (comparisonCoefficientMate l E b o f h).app
        (((o.geometry f).generic.target.scalar k).T.obj Q) ≫
      ((o.geometry f).generic.levelPush n).rightDerivedFunctor.map
        (((o.geometry f).generic.target.scalarComposition h k).hom.app Q) =
    ((b.calculus Y).scalarComposition h k).hom.app
        (((o.geometry f).generic.levelPush r).rightDerivedFunctor.obj Q) ≫
      (comparisonCoefficientMate l E b o f (h.trans k)).app Q) := by
  obtain ⟨b, o, hs⟩ := strictCoordinatesExistence l E
  refine ⟨b, o, hs, ?_, ?_⟩
  · intro T s m n h k K L
    exact SemilinearSections.scalarTensor_composition
      (Scheme.ProEt.topology T) (B l E T) (tau l E T) (b.calculus T) h k K L
  · intro X Y f s m n h k Q
    let G := (o.geometry f).generic
    exact mate_pasting_with_comparisons
      (G.derivedLevelAdjunction s) (G.derivedLevelAdjunction m)
      (G.derivedLevelAdjunction n)
      (TwoSquare.mk _ _ _ _ (G.coefficientPullback k).hom)
      (TwoSquare.mk _ _ _ _ (G.coefficientPullback h).hom)
      (TwoSquare.mk _ _ _ _ (G.coefficientPullback (h.trans k)).hom)
      ((b.calculus Y).scalarComposition h k).hom
      (G.target.scalarComposition h k).hom
      (G.coefficientPullback_composition
        (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
        (Scheme.ProEt.topology X)
        (proEtaleSheafInverseImage f (Type (u + 1)))
        (proEtaleSheafDirectImage f (Type (u + 1)))
        (proEtaleSheafAdjunction f (Type (u + 1))) h k) Q

end AlgebraicGeometry.ProEtale.SpTowerShriek
