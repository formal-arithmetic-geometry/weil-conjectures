/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import all WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMapsEtale
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition

/-! # Shift and composition laws for normalized scalar pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory

private theorem scalarPullbackShift
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {S T : Scheme.{u}} (f : S ⟶ T)
    (K : DerivedCategoryModule A T) (n : ℤ) :
    L(upperStar (ModuleCat.{u + 1} B) f).map
        ((FiniteSmoothPurity.scalarShiftIso φ T n).hom.app K) ≫
      (L(upperStar (ModuleCat.{u + 1} B) f).commShiftIso n).hom.app
        ((scalarExtension φ T).obj K) ≫
      ((scalarPullbackIso φ f).hom.app K)⟦n⟧' =
    (scalarPullbackIso φ f).hom.app (K⟦n⟧) ≫
      (scalarExtension φ S).map
        ((L(upperStar (ModuleCat.{u + 1} A) f).commShiftIso n).hom.app K) ≫
      (FiniteSmoothPurity.scalarShiftIso φ S n).hom.app
        (L(upperStar (ModuleCat.{u + 1} A) f).obj K) := by
  have := WeilConjectures.ExceptionalFiniteScalar.scalarPullbackShift φ f
  simpa only [Functor.commShiftIso_comp_hom_app, FiniteSmoothPurity.scalarShiftIso,
    FiniteSmoothPurity.ordinaryScalar, Category.assoc] using
    NatTrans.shift_app_comm (scalarPullbackIso φ f).hom n K

private theorem compositionTransport
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (S₀ : A₀ ⥤ B₀) (S₁ : A₁ ⥤ B₁) (S₂ : A₂ ⥤ B₂)
    (F₀ F₀' : A₀ ⥤ A₁) (F₁ F₁' : A₁ ⥤ A₂) (F₂ F₂' : A₀ ⥤ A₂)
    (G₀ G₀' : B₀ ⥤ B₁) (G₁ G₁' : B₁ ⥤ B₂) (G₂ G₂' : B₀ ⥤ B₂)
    (a₀ : F₀ ≅ F₀') (a₁ : F₁ ≅ F₁') (a₂ : F₂ ≅ F₂')
    (b₀ : G₀ ≅ G₀') (b₁ : G₁ ≅ G₁') (b₂ : G₂ ≅ G₂')
    (c₀ : S₀ ⋙ G₀ ≅ F₀ ⋙ S₁) (c₁ : S₁ ⋙ G₁ ≅ F₁ ⋙ S₂)
    (c₂ : S₀ ⋙ G₂ ≅ F₂ ⋙ S₂)
    (dA : F₂' ≅ F₀' ⋙ F₁') (dB : G₂' ≅ G₀' ⋙ G₁') (K : A₀)
    (h : dB.hom.app (S₀.obj K) ≫
        G₁'.map (b₀.inv.app (S₀.obj K) ≫ c₀.hom.app K ≫ S₁.map (a₀.hom.app K)) ≫
        b₁.inv.app (S₁.obj (F₀'.obj K)) ≫ c₁.hom.app (F₀'.obj K) ≫
        S₂.map (a₁.hom.app (F₀'.obj K)) =
      b₂.inv.app (S₀.obj K) ≫ c₂.hom.app K ≫ S₂.map (a₂.hom.app K) ≫
        S₂.map (dA.hom.app K)) :
    (b₂ ≪≫ dB ≪≫ Functor.isoWhiskerRight b₀.symm G₁' ≪≫
      Functor.isoWhiskerLeft G₀ b₁.symm).hom.app (S₀.obj K) ≫
        G₁.map (c₀.hom.app K) ≫ c₁.hom.app (F₀.obj K) =
      c₂.hom.app K ≫ S₂.map
        ((a₂ ≪≫ dA ≪≫ Functor.isoWhiskerRight a₀.symm F₁' ≪≫
          Functor.isoWhiskerLeft F₀ a₁.symm).hom.app K) := by
  apply (cancel_epi (b₂.inv.app (S₀.obj K))).1
  apply (cancel_mono (S₂.map (F₁.map (a₀.hom.app K) ≫
    a₁.hom.app (F₀'.obj K)))).1
  have hba := b₁.inv.naturality (c₀.hom.app K)
  have hbc := b₁.inv.naturality (S₁.map (a₀.hom.app K))
  have hca := c₁.hom.naturality (a₀.hom.app K)
  have haa := congrArg S₂.map (a₁.inv.naturality (a₀.hom.app K))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp] at hba hbc hca haa
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% hba, ← reassoc_of% hca, ← reassoc_of% hbc,
    ← reassoc_of% haa]
  simp only [← S₂.map_comp, ← F₁'.map_comp,
    Iso.inv_hom_id_app, Category.comp_id]
  simpa [Category.assoc] using h

set_option maxHeartbeats 2000000 in
-- Elaborating the six derived comparison isomorphisms needs a larger budget.
private theorem scalarComposition
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ Z)
    (K : DerivedCategoryModule A Z) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) u v).hom.app
        ((scalarExtension φ Z).obj K) ≫
      L(upperStar (ModuleCat.{u + 1} B) u).map ((scalarPullbackIso φ v).hom.app K) ≫
      (scalarPullbackIso φ u).hom.app (L(upperStar (ModuleCat.{u + 1} A) v).obj K) =
    (scalarPullbackIso φ (u ≫ v)).hom.app K ≫
      (scalarExtension φ X).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) u v).hom.app K) := by
  have h := compositionTransport
    (scalarExtension φ Z) (scalarExtension φ Y) (scalarExtension φ X)
    L(upperStar (ModuleCat.{u + 1} A) v) (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory
    L(upperStar (ModuleCat.{u + 1} A) u) (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory
    L(upperStar (ModuleCat.{u + 1} A) (u ≫ v))
      (upperStar (ModuleCat.{u + 1} A) (u ≫ v)).mapDerivedCategory
    L(upperStar (ModuleCat.{u + 1} B) v) (upperStar (ModuleCat.{u + 1} B) v).mapDerivedCategory
    L(upperStar (ModuleCat.{u + 1} B) u) (upperStar (ModuleCat.{u + 1} B) u).mapDerivedCategory
    L(upperStar (ModuleCat.{u + 1} B) (u ≫ v))
      (upperStar (ModuleCat.{u + 1} B) (u ≫ v)).mapDerivedCategory
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) u)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (u ≫ v))
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) u)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) (u ≫ v))
    (scalarPullbackIso φ v) (scalarPullbackIso φ u) (scalarPullbackIso φ (u ≫ v))
    (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) u v) ≪≫
      Functor.mapDerivedCategoryCompIso _ _)
    (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} B) u v) ≪≫
      Functor.mapDerivedCategoryCompIso _ _) K
    (by simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
      Category.assoc] using scalarPullback_composition φ v u (u ≫ v) rfl K)
  simpa only [leftDerivedUpperStarComp, leftDerivedUpperStarIsoMapDerivedCategory,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    Iso.trans_assoc, Iso.symm_self_id, Iso.symm_self_id_assoc, Iso.refl_trans] using h


/-- Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, canonical reassociation.
(blueprint: lem-sp-finite-affine-right-scalar-composition-coherence-gamma-package)

Proof: identify the inverse comparison with the scalar-adjunction mate of the
restriction/pullback comparison. The latter is the termwise exact comparison conjugated
by the derived pullback comparisons. These comparisons commute with integer shifts.
The adjunction unit and counit commute with the adjoint-normalized scalar shifts;
pasting their shift squares proves the mate's shift square. Inversion gives the three
forward shift squares below. For composition use the ordinary inverse-image compositors
with the constant coefficient identifications. The restriction squares paste, and the
unit and counit identities show that their scalar-adjunction mates paste in the same
order. Equivalently this is the composition equation of K-flat scalar normalization:
on a flat-term K-flat representative each path sends the same balanced generator to
itself. Cancel the representative isomorphisms and use flat K-flat resolutions and
naturality to descend to every unbounded derived object. This gives the final equation.
No boundedness, coefficient flatness, or choice of Tate roots is used. -/
theorem finiteAffineRightScalarCompositionCoherenceGammaPackage
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ Z) :
    let gammaShift := fun {S T : Scheme.{u}} (f : S ⟶ T) ↦
      ∀ (K : DerivedCategoryModule A T) (n : ℤ),
        L(upperStar (ModuleCat.{u + 1} B) f).map
            ((FiniteSmoothPurity.scalarShiftIso φ T n).hom.app K) ≫
          (L(upperStar (ModuleCat.{u + 1} B) f).commShiftIso n).hom.app
            ((scalarExtension φ T).obj K) ≫
          ((scalarPullbackIso φ f).hom.app K)⟦n⟧' =
        (scalarPullbackIso φ f).hom.app (K⟦n⟧) ≫
          (scalarExtension φ S).map
            ((L(upperStar (ModuleCat.{u + 1} A) f).commShiftIso n).hom.app K) ≫
          (FiniteSmoothPurity.scalarShiftIso φ S n).hom.app
            (L(upperStar (ModuleCat.{u + 1} A) f).obj K)
    gammaShift u ∧ gammaShift v ∧ gammaShift (u ≫ v) ∧
    (∀ K : DerivedCategoryModule A Z,
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) u v).hom.app
          ((scalarExtension φ Z).obj K) ≫
        L(upperStar (ModuleCat.{u + 1} B) u).map ((scalarPullbackIso φ v).hom.app K) ≫
        (scalarPullbackIso φ u).hom.app (L(upperStar (ModuleCat.{u + 1} A) v).obj K) =
      (scalarPullbackIso φ (u ≫ v)).hom.app K ≫
        (scalarExtension φ X).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) u v).hom.app K)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K n
    exact scalarPullbackShift φ u K n
  · intro K n
    exact scalarPullbackShift φ v K n
  · intro K n
    exact scalarPullbackShift φ (u ≫ v) K n
  · intro K
    exact scalarComposition φ u v K

end AlgebraicGeometry.Etale
