/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.SmoothPurity.DncCoefficientTransport.DncCoefficientTransportData
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackUnitCoherence
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarSectionCompositor
import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantCtf

/-! # Scalar compatibility of the diagonal base-change factor

Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (3), Orientation.
(blueprint: lem-sp-finite-smooth-diagonal-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

open ExceptionalCoefficients

-- The coefficient exchange calculation works for an arbitrary Cartesian presentation,
-- including the flipped self-product used by finiteSmoothDiagonalFactor.
private theorem exceptional_scalar_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {h : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [HasCompactification f] [HasCompactification f']
    (sq : IsPullback h f' f g) (K : DerivedCategoryModule A Y)
    (hM : _root_.DerivedCategory.TStructure.t.plus
      ((rightDerivedUpperShriek A f).obj K))
    (hSM : _root_.DerivedCategory.TStructure.t.plus
      ((scalarExtension φ X).obj
        ((rightDerivedUpperShriek A f).obj K))) :
    (scalarExtension φ X').map ((rightDerivedUpperShriekBaseChangeMap A sq).app K) ≫
        mateMap φ f' ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) ≫
        (rightDerivedUpperShriek B f').map
          ((scalarPullbackIso φ g).inv.app K) =
      (scalarPullbackIso φ h).inv.app
          ((rightDerivedUpperShriek A f).obj K) ≫
        (upperStar (ModuleCat.{u + 1} B) h).leftDerivedFunctor.map (mateMap φ f K) ≫
        (rightDerivedUpperShriekBaseChangeMap B sq).app ((scalarExtension φ Y).obj K) := by
  let := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  let := isIso_rightDerivedLowerShriekBaseChangeMap B sq
  let eA := asIso (rightDerivedLowerShriekBaseChangeMap A sq)
  let eB := asIso (rightDerivedLowerShriekBaseChangeMap B sq)
  let a := rightDerivedUpperShriekAdjunction A f
  let b := rightDerivedUpperShriekAdjunction A f'
  let ae := rightDerivedUpperShriekAdjunction B f
  let be := rightDerivedUpperShriekAdjunction B f'
  let αU := chosenCompactSupportIso φ f
  let αV := chosenCompactSupportIso φ f'
  have hfwd := compact_scalar_exchange_left φ sq ⟨_, hM⟩ ⟨⟨_, hSM⟩, rfl⟩
  rw [← chosenCompactSupportIso_hom φ f, ← chosenCompactSupportIso_hom φ f'] at hfwd
  have hcube : Adjunction.coefficientPullbackSquare eA.inv eB.inv αU αV
      (scalarPullbackIso φ h).inv (scalarPullbackIso φ g).inv
        ((rightDerivedUpperShriek A f).obj K) := by
    unfold Adjunction.coefficientPullbackSquare
    change (upperStar (ModuleCat.{u + 1} B) g).leftDerivedFunctor.map
        (αU.hom.app _) ≫ eB.hom.app _ ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
            ((scalarPullbackIso φ h).hom.app _) =
      (scalarPullbackIso φ g).hom.app _ ≫
        (scalarExtension φ Y').map (eA.hom.app _) ≫ αV.hom.app _ at hfwd
    have hi := IsIso.inv_eq_inv.mpr hfwd
    have hh := congrArg (fun z ↦ αV.hom.app
      ((upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj
        ((rightDerivedUpperShriek A f).obj K)) ≫
      z ≫ (upperStar (ModuleCat.{u + 1} B) g).leftDerivedFunctor.map
        (αU.hom.app ((rightDerivedUpperShriek A f).obj K))) hi
    simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
      Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app_assoc, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id] using hh.symm
  have hh := Adjunction.coefficient_exchange_of_counit_at a b ae be eA.inv eB.inv K
    ((rightDerivedUpperShriekBaseChangeMap A sq).app K)
    ((rightDerivedUpperShriekBaseChangeMap B sq).app ((scalarExtension φ Y).obj K))
    (mateEquiv_counit a b eA.inv K)
    (mateEquiv_counit ae be eB.inv ((scalarExtension φ Y).obj K))
    αU αV (scalarPullbackIso φ h).inv (scalarPullbackIso φ g).inv
    (mateMap φ f K)
    (mateMap φ f' ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
    (mateMap_counit φ f K) (mateMap_counit φ f' _) hcube
  exact hh.symm

private theorem mate_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] {K L : DerivedCategoryModule A Y}
    (a : K ⟶ L) :
    (scalarExtension φ X).map ((rightDerivedUpperShriek A f).map a) ≫
        mateMap φ f L =
      mateMap φ f K ≫
        (rightDerivedUpperShriek B f).map
          ((scalarExtension φ Y).map a) := by
  simp only [mateMap_eq]
  exact (mateEquiv (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction B f)
    (TwoSquare.mk _ _ _ _
      (compactSupportIso φ (HasCompactification.compactification f)).inv)).naturality a

private theorem dualizing_scalar_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {h : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [HasCompactification f] [HasCompactification f']
    (sq : IsPullback h f' f g)
    (hM : _root_.DerivedCategory.TStructure.t.plus
      (dualizingComplex A f))
    (hSM : _root_.DerivedCategory.TStructure.t.plus
      ((scalarExtension φ X).obj (dualizingComplex A f))) :
    (scalarExtension φ X').map (dualizingComplexBaseChangeMap A sq) ≫
        dualizingScalarMap φ f' =
      (scalarPullbackIso φ h).inv.app (dualizingComplex A f) ≫
        (upperStar (ModuleCat.{u + 1} B) h).leftDerivedFunctor.map
          (dualizingScalarMap φ f) ≫ dualizingComplexBaseChangeMap B sq := by
  have hu : (scalarExtension φ Y').map
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom ≫
        (unitIso φ Y').hom =
      (scalarPullbackIso φ g).inv.app (𝟙_ _) ≫
        (upperStar (ModuleCat.{u + 1} B) g).leftDerivedFunctor.map (unitIso φ Y).hom ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) g).hom := by
    apply (cancel_epi ((scalarPullbackIso φ g).hom.app (𝟙_ _))).1
    simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using
      etaleScalarPullback_unit φ g
  have hs := exceptional_scalar_square φ sq (𝟙_ _) hM hSM
  have hn := (rightDerivedUpperShriekBaseChangeMap B sq).naturality (unitIso φ Y).hom
  dsimp only [Functor.comp_map] at hn
  simp only [dualizingComplexBaseChangeMap, dualizingScalarMap_eq,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% (mate_naturality φ f'
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom)]
  rw [← Functor.map_comp, hu, Functor.map_comp, Functor.map_comp]
  rw [reassoc_of% hs, ← reassoc_of% hn]
  rfl

-- Cancellation of the inverse section compositor is purely categorical.
private theorem scalar_section_factor
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    (S₀ : C₀ ⥤ D₀) (S₁ : C₁ ⥤ D₁)
    (P : C₀ ⥤ C₁) (I : C₁ ⥤ C₀) (Q : D₀ ⥤ D₁) (J : D₁ ⥤ D₀)
    (rA : P ⋙ I ≅ 𝟭 _) (rB : Q ⋙ J ≅ 𝟭 _)
    (lp : P ⋙ S₁ ⟶ S₀ ⋙ Q) (li : I ⋙ S₀ ⟶ S₁ ⋙ J)
    (C : C₀) (C' : D₀) (D : C₁) (D' : D₁)
    (bA : P.obj C ⟶ D) (bB : Q.obj C' ⟶ D')
    (cC : S₀.obj C ⟶ C') (cD : S₁.obj D ⟶ D')
    (hbase : S₁.map bA ≫ cD = lp.app C ≫ Q.map cC ≫ bB)
    (hcancel : li.app (P.obj C) ≫ J.map (lp.app C) ≫
        rB.hom.app (S₀.obj C) = S₀.map (rA.hom.app C)) :
    S₀.map (rA.inv.app C ≫ I.map bA) ≫ li.app D ≫ J.map cD =
      cC ≫ rB.inv.app C' ≫ J.map bB := by
  have hc : S₀.map (rA.inv.app C) ≫ li.app (P.obj C) ≫ J.map (lp.app C) =
      rB.inv.app (S₀.obj C) := by
    apply (cancel_mono (rB.hom.app (S₀.obj C))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [hcancel, ← S₀.map_comp]
    simp only [Iso.inv_hom_id_app, S₀.map_id, Functor.id_obj]
  have hn := li.naturality bA
  dsimp only [Functor.comp_map] at hn
  simp only [S₀.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← J.map_comp, hbase]
  simp only [J.map_comp]
  rw [reassoc_of% hc]
  have hr := rB.inv.naturality cC
  dsimp only [Functor.comp_map, Functor.id_map] at hr
  rw [← reassoc_of% hr]

/-- The diagonal base-change factor commutes with finite scalar extension.
This assertion contains no deformation, vector integration or smooth orientation.
Source: coefficient compatibility proof (3), the diagonal base-change square.
(blueprint: lem-sp-finite-smooth-diagonal-scalar).

Proof: transpose the exceptional base-change square under the compact-support
adjunction. The proper scalar mate and extension-by-zero scalar comparison commute
with base change, so the two transposes agree by their counit equations. Evaluate
at the coefficient unit and use scalar/pullback unit coherence. Pull the resulting
square along the diagonal. Scalar balancing commutes with the section compositor
for Delta followed by the second projection; cancelling that compositor gives the
stated square. In these formulas sectionMap is balancing followed by pullback of
the unit-normalized exceptional scalar mate. Thus every edge is prescribed before
an orientation is constructed. This also covers empty schemes, d=0, and non-flat
coefficient quotients. -/
theorem finiteSmoothDiagonalScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (f : X ⟶ Y)
    [HasCompactification f] [IsSeparated f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    (ordinaryScalar φ X).map (finiteSmoothDiagonalFactor A f) ≫
        WeilConjectures.DncCoefficientTransport.sectionMap φ
          (pullback.fst f f) (pullback.diagonal f) =
      ExceptionalCoefficients.dualizingScalarMap φ f ≫
        finiteSmoothDiagonalFactor B f := by
  have _ := hB
  have : HasInvertibleExponent A Y := ⟨N, hN, hA, hY⟩
  have : HasInvertibleExponent A X := HasInvertibleExponent.of_hom f
  have hω := boundedConstructibleFiniteTor_dualizingComplex A d f
  have hM := hω.1.1.1
  have hSM := scalar_extension_plus_of_finiteTor φ X _ hω.2
  have hs := dualizing_scalar_square φ (IsPullback.of_hasPullback f f).flip hM hSM
  have hc := scalar_section_compositor φ (pullback.diagonal f) (pullback.snd f f)
    (pullback.diagonal_snd f) (dualizingComplex A f)
  have hf := scalar_section_factor (scalarExtension φ X) (scalarExtension φ (pullback f f))
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f f)).leftDerivedFunctor
    (upperStar (ModuleCat.{u + 1} A) (pullback.diagonal f)).leftDerivedFunctor
    (upperStar (ModuleCat.{u + 1} B) (pullback.snd f f)).leftDerivedFunctor
    (upperStar (ModuleCat.{u + 1} B) (pullback.diagonal f)).leftDerivedFunctor
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f))
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} B)
      (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f))
    (scalarPullbackIso φ (pullback.snd f f)).inv
    (scalarPullbackIso φ (pullback.diagonal f)).inv
    _ _ _ _
    (dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f f).flip)
    (dualizingComplexBaseChangeMap B (IsPullback.of_hasPullback f f).flip)
    (dualizingScalarMap φ f) (dualizingScalarMap φ (pullback.fst f f)) hs hc
  simp only [ordinaryScalar, finiteSmoothDiagonalFactor,
    WeilConjectures.DncCoefficientTransport.sectionMap,
    WeilConjectures.DncCoefficientTransport.dualizingMap,
    dualizingScalarMap_eq, Category.assoc, Functor.id_obj,
    sectionInvariant, dualizingComplex] at hf ⊢
  exact hf

end AlgebraicGeometry.Etale.FiniteSmoothPurity
