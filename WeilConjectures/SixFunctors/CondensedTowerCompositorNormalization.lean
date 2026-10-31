/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.CondensedPullbackCoherence
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleProperOpenInterchange

/-! # Compact-support compositor on a supplied Cartesian compactification tower

Source: latest blueprint, sk-thm-sf-comp-composition.proof.md, the composition
isomorphism and canonicity paragraphs
(blueprint: lem-sf-condensed-tower-compositor-normalization).

A triangle records exactly the supplied compactifications and the Cartesian middle
square. No density condition is imposed. The equality is stated on every object of
the full bounded constructible finite-Tor subcategory, hence is an equality of the
restricted natural transformations. The coherent data and open units are the
normalized witnesses of the recorded dependency statements, not arbitrary maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CondensedOpenProper

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

private theorem mateComponent
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {G : C ⥤ E} {H : D ⥤ F}
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (M : D) :
    (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ α)).natTrans.app M =
      a₂.unit.app (G.obj (R₁.obj M)) ≫
        R₂.map (α.app (R₁.obj M)) ≫ R₂.map (H.map (a₁.counit.app M)) := by
  simp [mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans]

private theorem transposeComponent
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (F : E ⥤ C) (G : E ⥤ D)
    (α : F ⟶ G ⋙ R) (M : E) :
    ((Functor.leftUnitor (F ⋙ L)).inv ≫ Functor.whiskerRight α L ≫
      (Functor.associator G R L).hom ≫ Functor.whiskerLeft G a.counit ≫
      (Functor.rightUnitor G).hom).app M =
        (a.homEquiv (F.obj M) (G.obj M)).symm (α.app M) := by
  simp [Adjunction.homEquiv_counit]

private theorem restrictionComponent
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (J : C ⥤ D) (R : D ⥤ E) (P : E ⥤ F) (Q : C ⥤ F) (U : D ⥤ C)
    (α : R ⋙ P ⟶ U ⋙ Q) (β : J ⋙ U ⟶ 𝟭 C) (M : C) :
    ((Functor.associator _ _ _).hom ≫ Functor.whiskerLeft J α ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight β Q ≫
      (Functor.leftUnitor _).hom).app M = α.app (J.obj M) ≫ Q.map (β.app M) := by
  simp

private theorem exactAdjunction_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedUpperStarLowerStarAdjunction Λ f).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f) =
      (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction := by
  have hd : derivedUpperStarLowerStarAdjunction Λ f =
      ((upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm := by
    exact Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
      (leftDerivedUpperStarIsoMapDerivedCategory Λ f)
      (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac (upperStar Λ f)).symm
  rw [hd]
  apply Adjunction.ext
  ext M
  simp [Adjunction.ofNatIsoLeft_unit, ← Functor.map_comp, Category.assoc]

private theorem openComp_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (j : X ⟶ Y) (i : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] :
    CompactSupportComposition.openComp Λ j i = jComp Λ j i := by
  apply Iso.ext
  ext K
  simp [CompactSupportComposition.openComp, jComp, pComp, Adjunction.leftAdjointUniq,
    conjugateEquiv_symm_apply_app, Adjunction.ofNatIsoRight_unit,
    Functor.map_comp, Category.assoc]

private theorem openFactor_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (j : X ⟶ Y) (i : Y ⟶ Z) (h : X ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion h] (e : j ≫ i = h) :
    CompactSupportComposition.openFactor Λ j i h e =
      jComp Λ j i ≪≫ jCongr Λ e := by
  subst h
  unfold CompactSupportComposition.openFactor
  rw [openComp_eq]
  simp only [jCongr, eqToIso_refl, Iso.trans_refl]

private theorem conjugateTransport
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ L₁' L₂' : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') (c : L₂' ≅ L₁') :
    conjugateIsoEquiv a₁ a₂ (e₂ ≪≫ c ≪≫ e₁.symm) =
      conjugateIsoEquiv (a₁.ofNatIsoLeft e₁) (a₂.ofNatIsoLeft e₂) c := by
  apply Iso.ext
  ext M
  simp [conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app,
    Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit,
    Functor.map_comp, Category.assoc]

private theorem compTransport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : D ⥤ E} {R₂ : E ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') :
    (a₁.comp a₂).ofNatIsoLeft
        (Functor.isoWhiskerRight e₁ L₂ ≪≫ Functor.isoWhiskerLeft L₁' e₂) =
      (a₁.ofNatIsoLeft e₁).comp (a₂.ofNatIsoLeft e₂) := by
  apply Adjunction.ext
  ext M
  simp only [Adjunction.ofNatIsoLeft_unit, Adjunction.comp_unit_app,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.trans_hom,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [← R₁.map_comp_assoc]
  have hn := a₂.unit.naturality (e₁.hom.app M)
  change e₁.hom.app M ≫ a₂.unit.app (L₁'.obj M) =
    a₂.unit.app (L₁.obj M) ≫ R₂.map (L₂.map (e₁.hom.app M)) at hn
  rw [← hn]
  simp only [Functor.map_comp, Category.assoc]

private theorem directComp_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rightDerivedLowerStarComp Λ f g = rComp Λ f g := by
  let ef := leftDerivedUpperStarIsoMapDerivedCategory Λ f
  let eg := leftDerivedUpperStarIsoMapDerivedCategory Λ g
  let efg := leftDerivedUpperStarIsoMapDerivedCategory Λ (f ≫ g)
  let ec := Functor.isoWhiskerRight eg ((upperStar Λ f).leftDerivedFunctor) ≪≫
    Functor.isoWhiskerLeft (P Λ g) ef
  have hc : leftDerivedUpperStarComp Λ f g =
      efg ≪≫ pComp Λ f g ≪≫ ec.symm := by
    apply Iso.ext
    ext M
    simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso, ef, eg, efg, ec, pComp,
      leftDerivedUpperStarIsoMapDerivedCategory]
  unfold rightDerivedLowerStarComp
  rw [hc, conjugateTransport, compTransport, exactAdjunction_eq,
    exactAdjunction_eq, exactAdjunction_eq]
  rfl

private theorem restrictionComparison_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ Z)
    [IsOpenImmersion i] (c : Compactification.BoundaryCompactification (p ≫ i))
    (M : D Λ c.obj.obj.Z) :
    compositionInterchangeRestriction Λ p i c M =
      (derivedDirectImageOpenRestriction Λ ⟨c.obj.obj.comm.symm⟩).app M := by
  unfold compositionInterchangeRestriction
  rw [exactAdjunction_eq, exactAdjunction_eq]
  conv_rhs => rw [derivedDirectImageOpenRestriction, mateComponent]
  conv_lhs => rw [Adjunction.homEquiv_unit, Functor.map_comp]
  rfl

attribute [local irreducible] derivedOpenImmersionLowerShriekUpperStarAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  Functor.rightDerivedFunctorNatIso

set_option maxHeartbeats 1500000 in
-- Comparing the ambient derived models has a large instance footprint.
private theorem normalized_eq_gamma
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (B : Pasting Λ)
    {X Y Z : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ Z) [IsOpenImmersion i]
    (c : Compactification.BoundaryCompactification (p ≫ i))
    [QuasiCompact i] (sq : IsPullback c.obj.obj.i p c.obj.obj.g i)
    (M : D Λ X)
    (m : (J Λ i).obj ((R Λ p).obj M) ⟶
      (R Λ c.obj.obj.g).obj ((J Λ c.obj.obj.i).obj M))
    (hm : compositionInterchangeIsNormalized Λ p i c M m) :
    m = (gamma Λ B.units sq.toCommSq).app M := by
  have : QuasiCompact c.obj.obj.i := c.obj.property
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i
  let ρ := restriction Λ B.units sq.toCommSq
  have hρ : IsIso ρ := B.restriction_isIso sq.toCommSq (Or.inl sq)
  have hγ : (gamma Λ B.units sq.toCommSq).app M =
      (a.homEquiv _ _).symm ((comparisonInverse ρ).app M) := by
    exact transposeComponent a (R Λ p) (J Λ c.obj.obj.i ⋙ R Λ c.obj.obj.g)
      (comparisonInverse ρ) M
  rw [hγ]
  apply (a.homEquiv _ _).injective
  simp only [Functor.comp_obj, Equiv.apply_symm_apply]
  apply (cancel_mono (ρ.app M)).mp
  have hinv : comparisonInverse ρ = inv ρ := by
    simp only [comparisonInverse, dif_pos hρ]
  rw [hinv]
  conv_rhs => rw [← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app]
  rw [show ρ.app M =
      (derivedDirectImageOpenRestriction Λ sq.toCommSq).app
          ((J Λ c.obj.obj.i).obj M) ≫
        (R Λ p).map ((B.units.unitIso c.obj.obj.i).inv.app M) from
      restrictionComponent _ _ _ _ _ _ _ M]
  change a.homEquiv _ _ m ≫
      ((derivedDirectImageOpenRestriction Λ sq.toCommSq).app
          ((J Λ c.obj.obj.i).obj M) ≫
        (R Λ p).map ((B.units.unitIso c.obj.obj.i).inv.app M)) = _
  rw [← Category.assoc]
  have hm' := hm
  unfold compositionInterchangeIsNormalized at hm'
  rw [restrictionComparison_eq] at hm'
  dsimp only [a, R, J, moduleObjectDerivedPushforward]
  rw [hm']
  rw [← Functor.map_comp]
  have hu := congrArg (fun t ↦ t.app M) (B.units.normalized c.obj.obj.i)
  rw [← hu, Iso.hom_inv_id_app]
  exact CategoryTheory.Functor.map_id _ M

-- Preserve the inherited proof-valued subtype witness, whose `S` is used implicitly.
set_option linter.unusedVariables false in
set_option maxHeartbeats 1500000 in
-- The supplied data law is a conjunction of large derived-category equations.
/-- The canonical compact-support compositor, read in a supplied tower, is the open-adjunction
transpose of inverse open restriction followed by the specified proper and open compositors.
This is a component equation for every object of Dctf, with the ambient derived arrows intact.
The same formula includes identity proper and open factors.

Source: latest blueprint, sk-thm-sf-comp-composition.proof.md, displayed composition
formula and canonicity paragraph
(blueprint: lem-sf-condensed-tower-compositor-normalization).

Proof: apply the composition normalization law of `A` directly to the supplied triangle
and to the generator `K` in the localizing closure. It gives a normalized interchange `m`
and the desired word with `openFactor` and `rightDerivedLowerStarComp`.

Transporting the derived pullback/direct-image adjunction to the exact pullback model
identifies it with the exact-left/right-derived adjunction. Thus the restriction map in
the normalization of `m` is exactly the canonical mate used in `restriction`. Compose
its normalization equation with direct image of the inverse specified open unit. The
unit normalization and inverse identities show that the open adjunct of `m`, followed
by `restriction`, is the identity. On this Cartesian square `restriction` is invertible,
so the adjunct is its inverse. The adjunction Hom bijection gives `m = gamma`.

The uniqueness-of-left-adjoint formula identifies `openComp` with `jComp`, and equality
transport gives `openFactor = jComp ≪≫ jCongr`. Naturality of the adjunction unit shows
that transporting adjunctions commutes with composition. Transporting the conjugate
comparison therefore identifies the native direct-image compositor with `rComp`.
Substituting these three equalities in the supplied normalization law proves the result.
No density or nonemptiness is used; identity factors satisfy the same computation. -/
theorem condensedTowerCompositor_normalization
    (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime] (_hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hΛ : IsAdmissibleCoefficient Λ)
    (A : CompactSupportComposition.CoherentData Λ k) (B : Pasting Λ)
    {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (T : Compactification.Triangle f.hom.left g.hom.left)
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
    (K : ConstantModelConstructibleFiniteTor Λ X.obj.left) :
    (A.comp f g T.cf T.cg T.cfg).hom.app
        ⟨K.obj, fun S _hS hCS ↦ hCS K.obj K.property⟩ =
      (R Λ T.cg.g).map
        ((gamma Λ B.units T.isPullback.flip.toCommSq).app ((J Λ T.cf.i).obj K.obj) ≫
          (R Λ T.p).map
            ((jComp Λ T.cf.i T.q ≪≫ jCongr Λ T.i_q).hom.app K.obj)) ≫
        (rComp Λ T.p T.cg.g).hom.app ((J Λ T.cfg.i).obj K.obj) ≫
        (Functor.rightDerivedFunctorNatIso
          (eqToIso (congrArg (lowerStar Λ) T.p_g))).hom.app
            ((J Λ T.cfg.i).obj K.obj) := by
  let KL : (localizingClosureProEtale Λ X.obj.left).FullSubcategory :=
    ⟨K.obj, fun S _hS hCS ↦ hCS K.obj K.property⟩
  obtain ⟨m, hm, he⟩ := A.laws.2.2.2.1 f g T KL
  have hmγ := normalized_eq_gamma Λ B T.cf.g T.cg.i
    (detSfBoundaryCompactification (CompactSupportComposition.middle T))
    T.isPullback.flip ((J Λ T.cf.i).obj K.obj) m hm
  dsimp only [R, J, moduleObjectDerivedPushforward] at hmγ ⊢
  rw [hmγ] at he
  simpa only [openFactor_eq, directComp_eq] using he

end AlgebraicGeometry.ProEtale.CondensedRing
