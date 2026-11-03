/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionFixedCoordinates
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicConjugateComparisonTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! Compatibility of finite pullback compositors with fixed coefficient realization.
Source: the first paragraph of the proof of prop-sf-pf-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
section Transport
variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category A₀] [Category A₁] [Category A₂]
  [Category B₀] [Category B₁] [Category B₂]

private theorem inverse_coordinate_comp
    (E₀ : A₀ ≌ B₀) (E₁ : A₁ ≌ B₁) (E₂ : A₂ ≌ B₂)
    (F₀ : A₀ ⥤ A₂) (F₁ : A₀ ⥤ A₁) (F₂ : A₁ ⥤ A₂)
    (P₀ : B₀ ⥤ B₂) (P₁ : B₀ ⥤ B₁) (P₂ : B₁ ⥤ B₂)
    (k : P₀ ≅ P₁ ⋙ P₂) (q : F₀ ≅ F₁ ⋙ F₂)
    (o₀ : P₀ ≅ E₀.inverse ⋙ F₀ ⋙ E₂.functor)
    (o₁ : P₁ ≅ E₀.inverse ⋙ F₁ ⋙ E₁.functor)
    (o₂ : P₂ ≅ E₁.inverse ⋙ F₂ ⋙ E₂.functor)
    (l₀ : F₀ ⋙ E₂.functor ≅ E₀.functor ⋙ P₀)
    (l₁ : F₁ ⋙ E₁.functor ≅ E₀.functor ⋙ P₁)
    (l₂ : F₂ ⋙ E₂.functor ≅ E₁.functor ⋙ P₂)
    (h₀ : ∀ M, o₀.hom.app M ≫ l₀.hom.app (E₀.inverse.obj M) =
      P₀.map (E₀.counitInv.app M))
    (h₁ : ∀ M, o₁.hom.app M ≫ l₁.hom.app (E₀.inverse.obj M) =
      P₁.map (E₀.counitInv.app M))
    (h₂ : ∀ M, o₂.hom.app M ≫ l₂.hom.app (E₁.inverse.obj M) =
      P₂.map (E₁.counitInv.app M))
    (h : ∀ N, E₂.functor.map (q.hom.app N) ≫ l₂.hom.app (F₁.obj N) ≫
      P₂.map (l₁.hom.app N) = l₀.hom.app N ≫ k.hom.app (E₀.functor.obj N))
    (M : B₀) :
    E₂.inverse.map (k.hom.app M) ≫
        E₂.inverse.map (o₂.hom.app (P₁.obj M)) ≫ E₂.unitInv.app _ ≫
        F₂.map (E₁.inverse.map (o₁.hom.app M) ≫ E₁.unitInv.app _) =
      E₂.inverse.map (o₀.hom.app M) ≫ E₂.unitInv.app _ ≫
        q.hom.app (E₀.inverse.obj M) := by
  let d₀ := E₂.inverse.map (o₀.hom.app M) ≫ E₂.unitInv.app _
  let d₁ := E₁.inverse.map (o₁.hom.app M) ≫ E₁.unitInv.app _
  let d₂ := E₂.inverse.map (o₂.hom.app (P₁.obj M)) ≫ E₂.unitInv.app _
  have hr : E₁.functor.map d₁ = E₁.counit.app (P₁.obj M) ≫ o₁.hom.app M := by
    dsimp only [d₁]
    rw [E₁.functor.map_comp, ← E₁.counit_app_functor]
    exact E₁.counit.naturality _
  have hr₀ : E₂.functor.map d₀ = E₂.counit.app (P₀.obj M) ≫ o₀.hom.app M := by
    dsimp only [d₀]
    rw [E₂.functor.map_comp, ← E₂.counit_app_functor]
    exact E₂.counit.naturality _
  have hr₂ : E₂.functor.map d₂ = E₂.counit.app (P₂.obj (P₁.obj M)) ≫
      o₂.hom.app (P₁.obj M) := by
    dsimp only [d₂]
    rw [E₂.functor.map_comp, ← E₂.counit_app_functor]
    exact E₂.counit.naturality _
  suffices hh : E₂.inverse.map (k.hom.app M) ≫ d₂ ≫ F₂.map d₁ =
      d₀ ≫ q.hom.app (E₀.inverse.obj M) by
    simpa only [d₀, d₁, d₂, Category.assoc] using hh
  apply E₂.functor.map_injective
  simp only [CategoryTheory.Functor.map_comp, hr₀, hr₂, Category.assoc]
  rw [reassoc_of% (E₂.counit.naturality (k.hom.app M))]
  rw [cancel_epi]
  apply (cancel_mono (l₂.hom.app (F₁.obj (E₀.inverse.obj M)) ≫
    P₂.map (l₁.hom.app (E₀.inverse.obj M)))).mp
  simp only [Category.assoc]
  erw [reassoc_of% (l₂.hom.naturality d₁)]
  rw [reassoc_of% h₂ (P₁.obj M)]
  rw [← P₂.map_comp_assoc, hr]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← P₂.map_comp, h₁]
  rw [h, reassoc_of% h₀]
  exact (k.hom.naturality (E₀.counitInv.app M)).symm

end Transport

namespace AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  sfIntrinsicDerivedEquivalence

private def exactPullCoordinates (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sfIntrinsicDerivedPullback A f ⋙ (sfIntrinsicDerivedEquivalence X A).inverse ≅
      (sfIntrinsicDerivedEquivalence Y A).inverse ⋙ sfFixedDerivedPullback A f :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryCompIso (sfIntrinsicModuleEquivalence Y A).inverse
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f ⋙
        (sfIntrinsicModuleEquivalence X A).functor) ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _))
    (sfIntrinsicDerivedEquivalence X A).inverse ≪≫
      Functor.isoWhiskerLeft
        ((sfIntrinsicDerivedEquivalence Y A).inverse ⋙ sfFixedDerivedPullback A f)
        (sfIntrinsicDerivedEquivalence X A).unitIso.symm

private theorem exactPullCoordinates_comp (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : proEtaleDerivedCategory Z A) :
    (sfIntrinsicDerivedEquivalence X A).inverse.map
        ((sfIntrinsicDerivedPullbackComp A f g).hom.app M) ≫
      (exactPullCoordinates A f).hom.app ((sfIntrinsicDerivedPullback A g).obj M) ≫
      (sfFixedDerivedPullback A f).map ((exactPullCoordinates A g).hom.app M) =
    (exactPullCoordinates A (f ≫ g)).hom.app M ≫
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g)).hom.app
          ((sfIntrinsicDerivedEquivalence Z A).inverse.obj M) := by
  let EX := sfIntrinsicModuleEquivalence X A
  let EY := sfIntrinsicModuleEquivalence Y A
  let EZ := sfIntrinsicModuleEquivalence Z A
  let Lf := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let Lg := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g
  let Lc := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (f ≫ g)
  let of := Functor.mapDerivedCategoryCompIso EY.inverse (Lf ⋙ EX.functor) ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso Lf EX.functor)
  let og := Functor.mapDerivedCategoryCompIso EZ.inverse (Lg ⋙ EY.functor) ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso Lg EY.functor)
  let oc := Functor.mapDerivedCategoryCompIso EZ.inverse (Lc ⋙ EX.functor) ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso Lc EX.functor)
  have h := inverse_coordinate_comp EZ.mapDerivedCategory EY.mapDerivedCategory
    EX.mapDerivedCategory Lc.mapDerivedCategory Lg.mapDerivedCategory Lf.mapDerivedCategory
    (sfIntrinsicDerivedPullback A (f ≫ g)) (sfIntrinsicDerivedPullback A g)
    (sfIntrinsicDerivedPullback A f) (sfIntrinsicDerivedPullbackComp A f g)
    (Functor.mapDerivedCategoryTriangleIso
      (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g)) oc og of
    (Functor.mapDerivedCategorySquareIso (EZ.funInvIdAssoc (Lc ⋙ EX.functor)).symm)
    (Functor.mapDerivedCategorySquareIso (EZ.funInvIdAssoc (Lg ⋙ EY.functor)).symm)
    (Functor.mapDerivedCategorySquareIso (EY.funInvIdAssoc (Lf ⋙ EX.functor)).symm)
    (derived_square_coherence EZ Lc EX.functor)
    (derived_square_coherence EZ Lg EY.functor)
    (derived_square_coherence EY Lf EX.functor)
    (derived_pullback_compositor_square A f g) M
  simpa only [exactPullCoordinates, oc, og, of, EX, EY, EZ, Lc, Lf, Lg,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    sfIntrinsicDerivedEquivalence, Equivalence.unitInv, sfFixedDerivedPullback,
    Functor.comp_obj, Category.assoc] using h
end AlgebraicGeometry.Scheme

namespace WeilConjectures.CompactSupportFiniteProjection

attribute [local implicit_reducible] realization sixFunctorFiniteRealization
  sixFunctorFinitePullback coordinates fixedDerivedPull

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

private def finiteExactCoordinates (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    S.finite.pull f ⋙ coordinates (C := C) (E := E) (n := n) (hn := hn) X ≅
      coordinates (C := C) (E := E) (n := n) (hn := hn) Y ⋙
        ProEtale.sfFixedDerivedPullback (Padic.coefficientExtensionRing C.l E n) f.hom.left :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  Functor.isoWhiskerRight (S.finitePullback f)
      (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse ≪≫
    Functor.isoWhiskerLeft
      (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
      (exactPullCoordinates (Padic.coefficientExtensionRing C.l E n) f.hom.left)

private theorem finiteExactCoordinates_comp (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : sixFunctorFiniteCategory D C E n hn Z) :
    (coordinates (C := C) (E := E) (n := n) (hn := hn) X).map
        ((S.finite.pullComposition f g).hom.app M) ≫
      (finiteExactCoordinates S f).hom.app ((S.finite.pull g).obj M) ≫
      (ProEtale.sfFixedDerivedPullback (Padic.coefficientExtensionRing C.l E n)
        f.hom.left).map ((finiteExactCoordinates S g).hom.app M) =
    (finiteExactCoordinates S (f ≫ g)).hom.app M ≫
      (Functor.mapDerivedCategoryTriangleIso
        (ProEtale.upperStarComp
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          f.hom.left g.hom.left)).hom.app
        ((coordinates (C := C) (E := E) (n := n) (hn := hn) Z).obj M) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := Padic.coefficientExtensionRing C.l E n
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  have hb := (exactPullCoordinates A f.hom.left).hom.naturality
    ((S.finitePullback g).hom.app M)
  dsimp only [Functor.comp_map] at hb
  have h := congrArg RX.inverse.map (S.finitePullCompositionNormalization f g M)
  simp only [finiteExactCoordinates, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  dsimp only [coordinates, realization, sixFunctorFiniteRealization,
    sixFunctorFinitePullback, Functor.comp_map, Functor.comp_obj] at hb h RX ⊢
  rw [← reassoc_of% hb]
  simp only [Functor.map_comp] at h
  erw [reassoc_of% h]
  simpa only [A, RX, realization, sixFunctorFiniteRealization,
    Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.FullSubcategory.comp_hom,
    Over.comp_left, Iso.trans_hom, NatTrans.comp_app, Category.assoc] using congrArg
    (fun t ↦ RX.inverse.map ((S.finitePullback (f ≫ g)).hom.app M) ≫ t)
    (exactPullCoordinates_comp A f.hom.left g.hom.left M.obj)

private theorem finiteExactCoordinates_total (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (M : sixFunctorFiniteCategory D C E n hn Y) :
    (fixedPullRealization S f M).hom = (finiteExactCoordinates S f).hom.app M ≫
      (fixedPullComparison (C := C) (E := E) (n := n) f).inv.app
        ((coordinates (C := C) (E := E) (n := n) (hn := hn) Y).obj M) := by
  simp only [fixedPullRealization, pullRealization, finiteExactCoordinates,
    exactPullCoordinates, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rfl

/-- The prescribed pullback compositor becomes the canonical fixed-coefficient
compositor. There is no tensor product or Tor-amplitude hypothesis in this assertion.

Source: the coefficient-realization calculation in the first paragraph of
the blueprint proof of `prop-sf-pf-coherence` (first paragraph).
(blueprint: lem-sf-finite-pullback-composition-fixed-coordinates).

Proof: apply the inverse coefficient realization at X to
`S.finitePullCompositionNormalization f g M`. Expand `fixedPullRealization` as the
inverse realization applied to `pullRealization`, followed by the inverse realization
unit and the inverse of `fixedPullComparison`. The two exact-functor composition
comparisons in `pullRealization` identify the intrinsic pullback with the conjugate
of fixed-scalar exact pullback. Naturality moves these comparisons past the realized
map for g. The associativity identity for `mapDerivedCategoryCompIso`, together with
its compatibility with `mapDerivedCategoryNatIso` and whiskering, identifies the
image of `sfIntrinsicDerivedPullbackComp` with the fixed-scalar exact compositor;
the middle coefficient unit inserted by `sfIntrinsicTransportComp` cancels the
inverse unit occurring in `fixedPullRealization`. Finally expand
`leftDerivedUpperStarComp` using the exact-to-left-derived comparison. Its two
comparison factors cancel the two `fixedPullComparison` factors on the left,
leaving the displayed right-hand side. All cancellations are of the specified
realization units and exact-to-derived comparisons, so no alternative compositor
or coefficient equivalence is chosen. -/
theorem pullbackComposition_fixed_coordinates
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : sixFunctorFiniteCategory D C E n hn Z) :
    let A := ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
    (coordinates (C := C) (E := E) (n := n) (hn := hn) X).map
        ((S.finite.pullComposition f g).hom.app M) ≫
      (fixedPullRealization S f ((S.finite.pull g).obj M)).hom ≫
      (fixedDerivedPull (C := C) (E := E) (n := n) f).map
        (fixedPullRealization S g M).hom =
    (fixedPullRealization S (f ≫ g) M).hom ≫
      (AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp A f.hom.left g.hom.left).hom.app
        ((coordinates (C := C) (E := E) (n := n) (hn := hn) Z).obj M) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  have hnat := (fixedPullComparison (C := C) (E := E) (n := n) f).inv.naturality
    ((finiteExactCoordinates S g).hom.app M)
  dsimp only
  rw [ProEtale.leftDerivedUpperStarComp_hom_app]
  simp only [finiteExactCoordinates_total, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hnat]
  have hnat₂ := (fixedPullComparison (C := C) (E := E) (n := n) f).inv.naturality
    ((fixedPullComparison (C := C) (E := E) (n := n) g).inv.app
      ((coordinates (C := C) (E := E) (n := n) (hn := hn) Z).obj M))
  simp only [fixedPullComparison] at hnat₂ ⊢
  rw [← hnat₂]
  simp only [fixedDerivedPull, ProEtale.sfFixedDerivedPullback,
    ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% (finiteExactCoordinates_comp S f g M)]

set_option maxHeartbeats 800000 in
-- The comparison rewrites retain several large derived-category endpoint types.
end WeilConjectures.CompactSupportFiniteProjection
