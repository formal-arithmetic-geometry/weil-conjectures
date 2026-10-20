/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
import WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget

/-! Base change of affine ind-etale objects along universal homeomorphisms. -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The actual pullback functor on affine ind-etale objects.
Source: Stacks Project, Tags 098E and 09AB. -/
noncomputable abbrev proEtaleAffineBaseChange {X Y : Scheme.{u}} (r : X ⟶ Y)
    [IsAffineHom r] : Y.AffineProEt ⥤ X.AffineProEt :=
  MorphismProperty.Over.pullback proAffineEtale ⊤ r

private theorem affineBaseChange_faithful {X Y : Scheme.{u}}
    (r : X ⟶ Y) [IsUniversalHomeomorphism r] :
    (proEtaleAffineBaseChange r).Faithful where
  map_injective {U V} g h e := by
    apply MorphismProperty.Over.Hom.ext
    obtain ⟨J, _, _, D, t, s, hs, hts⟩ := V.prop
    apply hs.hom_ext
    intro j
    have : Etale (t.app j) := (hts j).1.1
    apply Scheme.Hom.ext_of_surjective_of_formallyUnramified
      (pullback.fst U.hom r) (t.app j)
    · simp only [Category.assoc, (hts j).2]
      exact (MorphismProperty.Over.w g).trans (MorphismProperty.Over.w h).symm
    · have he := congrArg (fun k ↦ k.left ≫ pullback.fst V.hom r) e
      have hg : ((proEtaleAffineBaseChange r).map g).left ≫ pullback.fst V.hom r =
          pullback.fst U.hom r ≫ g.left := by
        exact pullback.lift_fst _ _ _
      have hh : ((proEtaleAffineBaseChange r).map h).left ≫ pullback.fst V.hom r =
          pullback.fst U.hom r ≫ h.left := by
        exact pullback.lift_fst _ _ _
      rw [hg, hh] at he
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ s.app j) he

private theorem affineBaseChange_full {X Y : Scheme.{u}}
    (r : X ⟶ Y) [IsUniversalHomeomorphism r] :
    (proEtaleAffineBaseChange r).Full := by
  classical
  refine ⟨?_⟩
  intro U V a
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := V.prop
  have het (j : J) : Etale (t.app j) := (hts j).1.1
  let b (j : J) : pullback U.hom r ⟶ pullback (t.app j) r :=
    a.left ≫ pullback.map V.hom r (t.app j) r (s.app j) (𝟙 X) (𝟙 Y)
      (by simpa using (hts j).2.symm) (by simp)
  have hb (j : J) : b j ≫ pullback.snd (t.app j) r = pullback.snd U.hom r := by
    dsimp [b]
    simp only [Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id]
    exact MorphismProperty.Over.w a
  have hex (j : J) : ∃! g : U.left ⟶ D.obj j,
      g ≫ t.app j = U.hom ∧
        pullback.fst U.hom r ≫ g = b j ≫ pullback.fst (t.app j) r := by
    have := het j
    exact r.existsUnique_of_isPullback U.hom (t.app j)
      (IsPullback.of_hasPullback U.hom r) (IsPullback.of_hasPullback (t.app j) r) (b j) (hb j)
  choose g hg using fun j ↦ (hex j).exists
  have hnat {i j : J} (f : i ⟶ j) : g i ≫ D.map f = g j := by
    have := het j
    apply Scheme.Hom.ext_of_surjective_of_formallyUnramified
      (pullback.fst U.hom r) (t.app j)
    · rw [Category.assoc, t.naturality f]
      simpa using (hg i).1.trans (hg j).1.symm
    · rw [← Category.assoc, (hg i).2, (hg j).2]
      dsimp [b]
      simp only [Category.assoc, pullback.map, pullback.lift_fst, Category.comp_id]
      have hn : s.app i ≫ D.map f = s.app j := by
        simpa using (s.naturality f).symm
      rw [hn]
  let c : Cone D := ⟨U.left, ⟨g, fun _ _ f ↦ by simpa using (hnat f).symm⟩⟩
  let k := hs.lift c
  have hfac (j : J) : k ≫ s.app j = g j := hs.fac c j
  have hky : k ≫ V.hom = U.hom := by
    obtain ⟨j⟩ := IsCofiltered.nonempty (C := J)
    rw [← (hts j).2, ← Category.assoc, hfac]
    exact (hg j).1
  refine ⟨MorphismProperty.Over.homMk k hky, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · change _ ≫ pullback.fst V.hom r = a.left ≫ pullback.fst V.hom r
    erw [pullback.lift_fst]
    apply hs.hom_ext
    intro j
    change pullback.fst U.hom r ≫ k ≫ s.app j =
      (a.left ≫ pullback.fst V.hom r) ≫ s.app j
    rw [hfac, (hg j).2]
    dsimp [b]
    simp
  · exact (pullback.lift_snd _ _ _).trans (MorphismProperty.Over.w a).symm

private theorem affineBaseChange_essSurj {X Y : Scheme.{u}} [IsAffine Y]
    (r : X ⟶ Y) [IsUniversalHomeomorphism r] :
    (proEtaleAffineBaseChange r).EssSurj := by
  classical
  refine ⟨fun V ↦ ?_⟩
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := V.prop
  have : IsConnected J := IsCofiltered.isConnected J
  let E : J ⥤ X.Etale :=
    { obj j := MorphismProperty.Over.mk _ (t.app j) (hts j).1.1
      map {i j} f := MorphismProperty.Over.homMk (D.map f) (by
        simp [t.naturality f]) }
  let H := E ⋙ r.Etale.asEquivalence.inverse
  let e := Functor.isoWhiskerLeft E r.Etale.asEquivalence.counitIso
  have haff (j : J) : IsAffine (H.obj j).left := by
    have : IsAffine (D.obj j) := (hts j).1.2.1
    let ej := (Etale.forget X ⋙ Over.forget X).mapIso (e.app j)
    change (r.Etale.obj (H.obj j)).left ≅ D.obj j at ej
    have hp : IsAffine (r.Etale.obj (H.obj j)).left := IsAffine.of_isIso ej.hom
    have : IsAffine (pullback (H.obj j).hom r) := hp
    exact isAffine_of_surjective_of_universallyClosed (pullback.fst (H.obj j).hom r)
  have (j : J) : IsAffine (H.obj j).left := haff j
  let A : J ⥤ Over (AffineScheme.of Y) :=
    { obj j := Over.mk (@AffineScheme.ofHom (H.obj j).left Y (haff j)
        inferInstance (H.obj j).hom)
      map {i j} f := Over.homMk (@AffineScheme.ofHom (H.obj i).left (H.obj j).left
        (haff i) (haff j) (H.map f).left) (by
        apply InducedCategory.hom_ext
        exact MorphismProperty.Over.w (H.map f))
      map_id j := by
        apply Over.OverMorphism.ext
        apply InducedCategory.hom_ext
        change (H.map (𝟙 j)).left = 𝟙 _
        rw [H.map_id]
        rfl
      map_comp f g := by
        apply Over.OverMorphism.ext
        apply InducedCategory.hom_ext
        change (H.map (f ≫ g)).left = (H.map f).left ≫ (H.map g).left
        rw [H.map_comp]
        rfl }
  let Q := Over.post (X := AffineScheme.of Y) AffineScheme.forgetToScheme
  have : PreservesLimitsOfShape J Q := by
    have : PreservesLimitsOfShape J (Q ⋙ Over.forget Y) :=
      inferInstanceAs (PreservesLimitsOfShape J
        (Over.forget (AffineScheme.of Y) ⋙ AffineScheme.forgetToScheme))
    exact preservesLimitsOfShape_of_reflects_of_preserves Q (Over.forget Y)
  let cY := Q.mapCone (limit.cone A)
  have hcY : IsLimit cY := isLimitOfPreserves Q (limit.isLimit A)
  let DY := A ⋙ Q
  have hc : IsLimit ((Over.forget Y).mapCone cY) :=
    isLimitOfPreserves (Over.forget Y) hcY
  have hpro : proAffineEtale cY.pt.hom := by
    refine ⟨J, inferInstance, inferInstance, DY ⋙ Over.forget Y,
      { app j := (DY.obj j).hom
        naturality i j f := by simp [Over.w (DY.map f)] },
      ((Over.forget Y).mapCone cY).π, hc, fun j ↦ ⟨?_, ?_⟩⟩
    · change Etale (H.obj j).hom ∧ IsAffine (H.obj j).left ∧ True
      exact ⟨(H.obj j).prop, haff j, trivial⟩
    · exact Over.w (cY.π.app j)
  let W : Y.AffineProEt := MorphismProperty.Over.mk _ cY.pt.hom hpro
  have : PreservesLimitsOfSize.{u, u} (Over.pullback r) :=
    (Over.mapPullbackAdj r).rightAdjoint_preservesLimits
  let cX := (Over.pullback r).mapCone cY
  have hcX : IsLimit cX := isLimitOfPreserves (Over.pullback r) hcY
  let eD : DY ⋙ Over.pullback r ≅ E ⋙ Etale.forget X :=
    NatIso.ofComponents (fun j ↦ by
      change (Over.pullback r).obj (Over.mk (H.obj j).hom) ≅ Over.mk (t.app j)
      exact (MorphismProperty.Over.forget _ _ _).mapIso (e.app j)) (by
        intro i j f
        exact congrArg (fun k ↦ k.toCommaMorphism) (e.hom.naturality f))
  let cV := Over.liftCone D t (Cone.mk _ s) V.hom (fun j ↦ (hts j).2)
  have hcV : IsLimit cV := Over.isLimitLiftCone D t (Cone.mk _ s) V.hom
    (fun j ↦ (hts j).2) hs
  let cV' : Cone (DY ⋙ Over.pullback r) :=
    (Cone.postcompose eD.inv).obj cV
  have hcV' : IsLimit cV' := (IsLimit.postcomposeHomEquiv eD.symm cV).symm hcV
  let eW := hcX.conePointUniqueUpToIso hcV'
  refine ⟨W, ⟨MorphismProperty.Over.isoMk ((Over.forget X).mapIso eW) ?_⟩⟩
  exact Over.w eW.hom

/-- Universal homeomorphisms with affine target induce equivalences on affine
ind-etale objects.
Source: Stacks Project, Tag 09AB, `proetale-lemma-thickening`, affine-algebra argument.
Proof: Present each affine ind-etale object as a small cofiltered limit of affine
etale schemes. Full faithfulness is checked against the etale terms of the target
presentation: the uniqueness and existence of a map into an etale scheme descend
through the universal homeomorphism, and the limit universal property combines the
compatible maps. For essential surjectivity apply the inverse of the etale equivalence
to the entire presenting diagram. Its terms are affine, since affineness descends
through the surjective universally closed base-change projections. Form its limit in
affine schemes over Y. The inclusion into schemes preserves this cofiltered limit, and
pullback in the over category preserves limits as a right adjoint. The counit of the
etale equivalence identifies the pulled-back diagram with the original one, so uniqueness
of limits identifies its limit with the given object. This proves essential surjectivity
for the actual pullback functor. Empty affine schemes and arbitrary integral universal
homeomorphisms are included, without a finite-type assumption.
(blueprint: lem-trf-proetale-affine-base-change-equivalence) -/
theorem proEtaleAffineBaseChange_isEquivalence {X Y : Scheme.{u}} [IsAffine Y]
    (r : X ⟶ Y) [IsUniversalHomeomorphism r] :
    (proEtaleAffineBaseChange r).IsEquivalence := by
  have := affineBaseChange_faithful r
  have := affineBaseChange_full r
  have := affineBaseChange_essSurj r
  exact {}

end AlgebraicGeometry.Scheme
