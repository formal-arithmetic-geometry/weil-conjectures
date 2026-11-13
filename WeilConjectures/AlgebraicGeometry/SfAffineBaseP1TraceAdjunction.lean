/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
public import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
public import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.SfCompactificationKernelTransport
import WeilConjectures.AlgebraicGeometry.SfP1CoordinateIntegrals
import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence

/-! # Projective-line trace adjunction over an arbitrary affine base

The counit equality is written after precomposition with the canonical projection
isomorphism. Cancelling that isomorphism gives precisely the inverse-projection
formula. For the identity/proper factorization this is the proper counit-defined
projection map. Specializing to the coefficient unit identifies the counit with
its trace under the canonical unit comparisons.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option Elab.async false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The identity/proper compactification of the projective line in standard-chart
coordinates. -/
noncomputable abbrev sfProjectiveLineCompactification (S : Scheme.{u}) :
    Compactification (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S) :=
  Compactification.ofIsProper (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S)

/-- The canonical identification of a complex with its tensor product with the
pullback of the coefficient unit. -/
noncomputable def sfTensorPullbackUnitIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : DerivedCategoryModule A X) :
    B ≅ ((derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
      ((L(upperStar (ModuleCat.{u + 1} A) f)).obj (constantComplex A Y)) :=
  (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X B).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj B).mapIso
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).symm

open MonoidalCategory

attribute [local irreducible] rightDerivedLowerShriek
  SfDiagonalKernel.unit SfDiagonalKernel.counit

/-- Assemble the kernel adjunction before choosing a concrete geometric morphism. -/
private theorem exists_kernelAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsProper f]
    {B : DerivedCategoryModule A X} (d : TraceDiagonalDatum A f B)
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (n : ℤ)
    (e : B ≅ (CoordinateTrace.pull A f).obj (CoordinateTrace.shiftedLine A J n))
    (h : SfDiagonalKernel.Integrals A d (CoordinateTrace.shiftedLine A J n) e) :
    ∃ adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣
        CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B,
      adj.counit = SfDiagonalKernel.counit A d := by
  obtain ⟨hF, hG⟩ := SfDiagonalKernel.triangles A d J hJ n e h
  refine ⟨{ unit := SfDiagonalKernel.unit A d
            counit := SfDiagonalKernel.counit A d
            left_triangle_components := hF
            right_triangle_components := hG }, rfl⟩

/-- Right unitality identifies the coefficient-unit component with its trace. -/
private theorem trace_unit_normalization
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D]
    (F : C ⥤ D) {B W : C} (a : B ≅ W)
    (p : F.obj B ⊗ 𝟙_ D ⟶ F.obj W) (ε : F.obj W ⟶ 𝟙_ D)
    (t : F.obj B ⟶ 𝟙_ D)
    (hu : p ≫ F.map a.inv = (ρ_ (F.obj B)).hom)
    (h : p ≫ ε = (t ▷ 𝟙_ D) ≫ (λ_ (𝟙_ D)).hom) :
    F.map a.hom ≫ ε = t := by
  have ha : F.map a.hom = (ρ_ (F.obj B)).inv ≫ p := by
    apply (cancel_mono (F.map a.inv)).1
    rw [Category.assoc, hu, Iso.inv_hom_id, ← F.map_comp, Iso.hom_inv_id, F.map_id]
  rw [ha, Category.assoc, h, unitors_equal, rightUnitor_naturality,
    Iso.inv_hom_id_assoc]

section

/-- Specialize projection unitality before fixing the concrete module coefficients. -/
private theorem trace_unit_normalization_derived
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [Etale.UpperStarPreservesFlat C]
    {FC : C → C → Type (u + 1)} {CC : C → Type (u + 1)}
    [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} C FC]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget C)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget C)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (ε : (rightDerivedLowerShriekOfCompactification C c).obj
      (((derivedTensor C X).obj B).obj
        ((L(upperStar C f)).obj (derivedTensorUnit C Y))) ⟶ derivedTensorUnit C Y)
    (t : (rightDerivedLowerShriekOfCompactification C c).obj B ⟶ derivedTensorUnit C Y)
    (h : ((projectionMapOfCompactification C c).app B).app (derivedTensorUnit C Y) ≫ ε =
      ((derivedTensor C Y).map t).app (derivedTensorUnit C Y) ≫
        (derivedTensorLeftUnitor C Y (derivedTensorUnit C Y)).hom) :
    (rightDerivedLowerShriekOfCompactification C c).map
      ((derivedTensorRightUnitor C X B).inv ≫
        ((derivedTensor C X).obj B).map (leftDerivedUpperStarUnitIso C f).inv) ≫ ε = t := by
  let a : B ≅ ((derivedTensor C X).obj B).obj
      ((L(upperStar C f)).obj (derivedTensorUnit C Y)) :=
    (derivedTensorRightUnitor C X B).symm ≪≫
      ((derivedTensor C X).obj B).mapIso (leftDerivedUpperStarUnitIso C f).symm
  have hu : ((projectionMapOfCompactification C c).app B).app (derivedTensorUnit C Y) ≫
      (rightDerivedLowerShriekOfCompactification C c).map
        (((derivedTensor C X).obj B).map (leftDerivedUpperStarUnitIso C f).hom ≫
          (derivedTensorRightUnitor C X B).hom) =
      (derivedTensorRightUnitor C Y
        ((rightDerivedLowerShriekOfCompactification C c).obj B)).hom := by
    have hp (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
        ((projectionMapOfCompactification C c).app B).app L =
          (derivedUpperStarLowerStarAdjunction C c.g).compProjectionMap
            (leftDerivedUpperStarTensorComparison C c.g) D((c.i)_!open[C])
            (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso C c.i).inv.app K).app N)
            (fun L ↦ (leftDerivedUpperStarCompactificationIso C c).hom.app L) B L := rfl
    have hm {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)} (x : K ⟶ K') :
        (rightDerivedLowerShriekOfCompactification C c).map x =
          (D((c.i)_!open[C]) ⋙ R((c.g)_*[C])).map x := rfl
    rw [hp, hm]
    change _ ≫ (D((c.i)_!open[C]) ⋙ R((c.g)_*[C])).map
      (B ◁ (leftDerivedUpperStarUnitIso C f).hom ≫ (ρ_ B).hom) = _
    exact compactificationProjectionMap_rightUnitality C c B
  exact trace_unit_normalization (rightDerivedLowerShriekOfCompactification C c) a _ ε t hu h

end

attribute [local irreducible] derivedTensor

/-- The ordinary unbounded projective-line pushforward has the shifted finite Tate
line tensored with inverse image as right adjoint, with the specified actual counit.
Here S is any affine scheme and the projective line has the two coordinates
Option (ULift (Fin 1)); Rq_* and its projection map come from the identity/proper
compactification. At the coefficient unit the counit is the trace t. -/
theorem sfAffineBaseP1TraceAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (_hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsAffine S]
    (_hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s)) :
    ∃ (t : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (sfProjectiveLineCompactification S)).obj
        (((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateLine
            (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S) N A hA))⟦(2 : ℤ)⟧) ⟶
        constantComplex A S)
      (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (sfProjectiveLineCompactification S) ⊣
        (upperStar (ModuleCat.{u + 1} A)
          (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S)).leftDerivedFunctor ⋙
        (derivedTensor (ModuleCat.{u + 1} A)
          (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S)).obj
          (((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateLine
              (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S) N A hA))⟦(2 : ℤ)⟧)),
      (∀ K : DerivedCategoryModule A S,
        ((projectionMapOfCompactification (ModuleCat.{u + 1} A)
            (sfProjectiveLineCompactification S)).app
          (((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateLine
              (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S) N A hA))⟦(2 : ℤ)⟧)).app K ≫
          adj.counit.app K =
        ((derivedTensor (ModuleCat.{u + 1} A) S).map t).app K ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) S K).hom) ∧
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (sfProjectiveLineCompactification S)).map
          (sfTensorPullbackUnitIso A
            (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S)
            (((_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateLine
                (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S) N A hA))⟦(2 : ℤ)⟧)).hom ≫
        adj.counit.app (constantComplex A S) = t := by
  classical
  let P := ProjectiveSpace (Option (ULift.{u} (Fin 1))) S
  let q := P ↘ S
  let B : DerivedCategoryModule A P :=
    ((_root_.DerivedCategory.singleFunctor _ 0).obj
      (Scheme.finiteEtaleTateLine P N A hA))⟦(2 : ℤ)⟧
  obtain ⟨d, e, hJ, hi⟩ := sfP1CoordinateIntegrals A N _hN hA S _hInvertible
  obtain ⟨adj₀, heps⟩ := exists_kernelAdjunction A d
    (Scheme.finiteEtaleTateLine S N A hA) hJ 1 e hi
  obtain ⟨t, adj, hp⟩ := sfCompactificationKernelTransport A
    (sfProjectiveLineCompactification S) d adj₀ heps
  refine ⟨t, adj, hp, ?_⟩
  exact trace_unit_normalization_derived (ModuleCat.{u + 1} A)
    (sfProjectiveLineCompactification S) B
    (adj.counit.app (constantComplex A S)) t (hp (constantComplex A S))

end AlgebraicGeometry.Etale
