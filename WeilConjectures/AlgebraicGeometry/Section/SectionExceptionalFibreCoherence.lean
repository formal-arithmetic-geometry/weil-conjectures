/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientLeftComparisonBaseChange
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothDualityBaseChangeCompat
import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
import WeilConjectures.AlgebraicGeometry.Derived.DerivedPullbackCompositionMonoidal

/-! # Counit-normalized exceptional comparisons for section families

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-dnc, opening fibre restrictions,
Local construction and Gluing (blueprint: lem-trf-section-exceptional-fibre-coherence).

The records below package the geometric diagrams, not their cohomological comparisons.
Every comparison is constructed from the existing counit mate or the unique counit-normalized
locality isomorphism. The two fibre labels are `false` (zero) and `true` (one).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- A smooth compactifiable map with a closed section, as in the opening fibre restrictions
of blueprint sk-thm-dnc (blueprint: lem-trf-section-exceptional-fibre-coherence).
This is only a record of the geometric hypotheses; it contains no comparison maps. -/
structure ExceptionalSectionPair (B : Scheme.{u}) (d : ℕ) where
  total : Scheme.{u}
  map : total ⟶ B
  sect : B ⟶ total
  section_map : sect ≫ map = 𝟙 B
  [base_noetherian : IsNoetherian B]
  [total_noetherian : IsNoetherian total]
  [compactifiable : HasCompactification map]
  [separated : IsSeparated map]
  [smooth : SmoothOfRelativeDimension d map]
  [closed : IsClosedImmersion sect]

attribute [instance] ExceptionalSectionPair.total_noetherian ExceptionalSectionPair.compactifiable
  ExceptionalSectionPair.separated ExceptionalSectionPair.smooth ExceptionalSectionPair.closed

/-- A Cartesian change of a section pair, including the compatibility of the sections.
Source: blueprint sk-thm-dnc, fibre restrictions and Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
structure ExceptionalSectionChange {B B' : Scheme.{u}} {d : ℕ}
    (P : ExceptionalSectionPair B d) (P' : ExceptionalSectionPair B' d) (v : B' ⟶ B) where
  upper : P'.total ⟶ P.total
  square : IsPullback upper P'.map P.map v
  section_comm : P'.sect ≫ upper = v ≫ P.sect

/-- Pullback along the two equal composites in a commuting square, using the canonical
inverse-image compositors. Source: blueprint sk-thm-dnc, Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def sectionCoherencePullbackIso
    (A : Type (u + 1)) [CommRing A]
    {B B' X X' : Scheme.{u}} (v : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X')
    (r : X' ⟶ X) (h : v ≫ i = i' ≫ r) (K : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor.obj K) ≅
      (upperStar (ModuleCat.{u + 1} A) i').leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v i).symm.app K ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i' r (v ≫ i) h).app K

private theorem sectionPullback_endpoint
    (A : Type (u + 1)) [CommRing A]
    {B B' X X' : Scheme.{u}} (v : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X')
    (r : X' ⟶ X) (z z' : B' ⟶ X)
    (h₁ : z = v ≫ i) (h₂ : z = i' ≫ r)
    (h₁' : z' = v ≫ i) (h₂' : z' = i' ≫ r) (K : DerivedCategoryModule A X) :
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v i z h₁).symm ≪≫
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i' r z h₂).app K =
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v i z' h₁').symm ≪≫
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i' r z' h₂').app K := by
  subst z
  subst z'
  rfl

/-- Section pullback of the actual counit-defined exceptional comparison at the coefficient
unit. Source: blueprint sk-thm-dnc, opening fibre restrictions
(blueprint: lem-trf-section-exceptional-fibre-coherence). The input map is the existing
`dualizingComplexBaseChangeMap`, not a chosen isomorphism of its source and target. -/
noncomputable def sectionExceptionalComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B B' : Scheme.{u}} {d : ℕ} {P : ExceptionalSectionPair B d}
    {P' : ExceptionalSectionPair B' d} {v : B' ⟶ B}
    (e : ExceptionalSectionChange P P' v) :
    (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj
        (sectionInvariant A P.map P.sect) ⟶ sectionInvariant A P'.map P'.sect :=
  (sectionCoherencePullbackIso A v P.sect P'.sect e.upper
      e.section_comm.symm (dualizingComplex A P.map)).hom ≫
    (upperStar (ModuleCat.{u + 1} A) P'.sect).leftDerivedFunctor.map
      (dualizingComplexBaseChangeMap A e.square)

/-- The zero or one section of the affine line. Source: blueprint sk-thm-dnc, opening
fibre restrictions (blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def exceptionalFamilyPoint (S : Scheme.{u}) (t : Bool) :
    S ⟶ AffineSpace (ULift.{u} (Fin 1)) S :=
  if t then AffineSpace.oneSection (ULift.{u} (Fin 1)) S
  else AffineSpace.zeroSection (ULift.{u} (Fin 1)) S

/-- A section family over the affine line with its two Cartesian fibre pairs.
Source: blueprint sk-thm-dnc, opening fibre restrictions
(blueprint: lem-trf-section-exceptional-fibre-coherence).
No isomorphism of derived objects is a field of this geometric record. -/
structure ExceptionalSectionFamily (S : Scheme.{u}) (d : ℕ) where
  ambient : ExceptionalSectionPair (AffineSpace (ULift.{u} (Fin 1)) S) d
  fibre : Bool → ExceptionalSectionPair S d
  restriction : ∀ t : Bool,
    ExceptionalSectionChange ambient (fibre t) (exceptionalFamilyPoint S t)

/-- The specified fibre map: `theta` at one and `eta` at zero. Source: blueprint sk-thm-dnc,
opening fibre restrictions (blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def ExceptionalSectionFamily.fibreMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S : Scheme.{u}} {d : ℕ} (P : ExceptionalSectionFamily S d) (t : Bool) :=
  sectionExceptionalComparison A (P.restriction t)

/-- The canonical counit-normalized locality isomorphism for a structural map and an etale
map into its source, evaluated at the constant unit. Source: blueprint sk-thm-dnc, Local
construction (blueprint: lem-trf-section-exceptional-fibre-coherence). The choice is from the
unique counit-normalized isomorphism of `lem-amb-etale-adjoint-locality`; hence its data are
determined, rather than chosen from an uncharacterized existence assertion. -/
noncomputable def sectionStructuralLocalityIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X B : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    (h : U ⟶ X) [Etale h] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (f : X ⟶ B) [HasCompactification f] (f' : U ⟶ B) [HasCompactification f']
    (hf : h ≫ f = f') :
    (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj
      (dualizingComplex A f) ≅
        dualizingComplex A f' := by
  subst f'
  exact (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).app _ ≪≫
    (Classical.choose (existsUnique_etaleAmbientAdjointLocalityIso A h f
      (HasCompactification.compactification f)
      (HasCompactification.compactification (h ≫ f))
      (rightDerivedUpperShriek A f)
      (rightDerivedUpperShriek A (h ≫ f))
      (rightDerivedUpperShriekAdjunction A f)
      (rightDerivedUpperShriekAdjunction A (h ≫ f)))).app (𝟙_ _)

/-- Normalization of a family isomorphism at the one fibre, including the inverse-image
unit compositor. Source: blueprint sk-thm-dnc, Local construction and Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
def ExceptionalSectionFamily.IsNormalized
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S : Scheme.{u}} {d : ℕ} (P : ExceptionalSectionFamily S d)
    (κ : sectionInvariant A P.ambient.map P.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A (P.fibre true).map (P.fibre true).sect)) : Prop :=
  (upperStar (ModuleCat.{u + 1} A) (exceptionalFamilyPoint S true)).leftDerivedFunctor.map
      κ.hom ≫
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
      (AffineSpace.oneSection_comp_over _ _)).hom.app _ = P.fibreMap A true

/-- The specialization determined by a normalized family isomorphism, from the one fibre
to the zero fibre. Source: blueprint sk-thm-dnc, final paragraph
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def ExceptionalSectionFamily.specialization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S : Scheme.{u}} {d : ℕ} (P : ExceptionalSectionFamily S d)
    (κ : sectionInvariant A P.ambient.map P.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A (P.fibre true).map (P.fibre true).sect)) :
    sectionInvariant A (P.fibre true).map (P.fibre true).sect ⟶
      sectionInvariant A (P.fibre false).map (P.fibre false).sect :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace.zeroSection_comp_over _ _)).inv.app _ ≫
  (upperStar (ModuleCat.{u + 1} A) (exceptionalFamilyPoint S false)).leftDerivedFunctor.map
    κ.inv ≫ P.fibreMap A false

private theorem normalized_transport
    {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) (H : D ⥤ C) (T : G ⋙ H ≅ 𝟭 C)
    {X X' : D} {Y Y' : C} (b : X ≅ X') (c : Y ≅ Y') (κ : X ≅ G.obj Y)
    (θ : H.obj X ⟶ Y) (θ' : H.obj X' ⟶ Y')
    (hk : H.map κ.hom ≫ T.hom.app Y = θ)
    (hs : H.map b.hom ≫ θ' = θ ≫ c.hom) :
    H.map (b.symm ≪≫ κ ≪≫ G.mapIso c).hom ≫ T.hom.app Y' = θ' := by
  have hn := T.hom.naturality c.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [hn, reassoc_of% hk, ← hs]
  rw [← H.map_comp_assoc, b.inv_hom_id, H.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem locality_inverse_counit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R : D ⥤ C} {F : D ⥤ E} {G : E ⥤ D}
    {T : C ⥤ E} {H : E ⥤ C}
    (a : L ⊣ R) (b : F ⊣ G) (c : T ⊣ H)
    (α : L ⋙ F ≅ T) (ℓ : G ⋙ R ≅ H)
    (hℓ : ∀ K, T.map (ℓ.hom.app K) ≫ c.counit.app K =
      α.inv.app _ ≫ F.map (a.counit.app (G.obj K)) ≫ b.counit.app K) (K : E) :
    F.map (L.map (ℓ.inv.app K)) ≫ F.map (a.counit.app (G.obj K)) ≫
      b.counit.app K = α.hom.app _ ≫ c.counit.app K := by
  apply (cancel_epi (α.inv.app (H.obj K))).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% (α.inv.naturality (ℓ.inv.app K)), ← hℓ]
  simp only [← T.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem locality_mate_naturality
    {C D E C' D' E' : Type*}
    [Category* C] [Category* D] [Category* E]
    [Category* C'] [Category* D'] [Category* E']
    {L : C ⥤ D} {R : D ⥤ C} {F : D ⥤ E} {G : E ⥤ D}
    {T : C ⥤ E} {H : E ⥤ C}
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} {F' : D' ⥤ E'} {G' : E' ⥤ D'}
    {T' : C' ⥤ E'} {H' : E' ⥤ C'}
    (a : L ⊣ R) (b : F ⊣ G) (c : T ⊣ H)
    (a' : L' ⊣ R') (b' : F' ⊣ G') (c' : T' ⊣ H')
    {U : C ⥤ C'} {V : D ⥤ D'} {W : E ⥤ E'}
    (α : L ⋙ F ≅ T) (α' : L' ⋙ F' ≅ T')
    (ℓ : G ⋙ R ≅ H) (ℓ' : G' ⋙ R' ≅ H')
    (hℓ : ∀ K, T.map (ℓ.hom.app K) ≫ c.counit.app K =
      α.inv.app _ ≫ F.map (a.counit.app (G.obj K)) ≫ b.counit.app K)
    (hℓ' : ∀ K, T'.map (ℓ'.hom.app K) ≫ c'.counit.app K =
      α'.inv.app _ ≫ F'.map (a'.counit.app (G'.obj K)) ≫ b'.counit.app K)
    (J : R ⋙ U ⟶ V ⋙ R')
    (ξ : TwoSquare V F F' W) (ζ : TwoSquare U T T' W)
    (hx : ∀ M, ζ.app M ≫ W.map (α.inv.app M) =
      α'.inv.app (U.obj M) ≫
        F'.map (((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ J)).app M) ≫
          ξ.app (L.obj M)) (K : E) :
    J.app (G.obj K) ≫ R'.map ((mateEquiv b b' ξ).app K) ≫
      ℓ'.hom.app (W.obj K) = U.map (ℓ.hom.app K) ≫ (mateEquiv c c' ζ).app K := by
  have hm := Adjunction.mateEquiv_inv_comp a b c a' b' c'
    ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ J)) ξ ζ α.symm α'.symm hx
    ℓ.inv (locality_inverse_counit a b c α ℓ hℓ)
    ℓ'.inv (locality_inverse_counit a' b' c' α' ℓ' hℓ') K
  simp only [Equiv.apply_symm_apply, TwoSquare.mk, TwoSquare.natTrans] at hm
  apply (cancel_epi (U.map (ℓ.inv.app K))).mp
  simp only [← U.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hm]
  simp

private theorem exceptional_base_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (K : DerivedCategoryModule A Y) :
    (rightDerivedUpperShriekBaseChangeMap A (sq₂.paste_horiz sq₁)).app K =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app
        ((rightDerivedUpperShriek A f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        ((rightDerivedUpperShriekBaseChangeMap A sq₁).app K) ≫
      (rightDerivedUpperShriekBaseChangeMap A sq₂).app
        ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj K) ≫
      (rightDerivedUpperShriek A f'').map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).inv.app K) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq₁
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq₂
  have := isIso_rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)
  let E₁ := rightDerivedLowerShriekBaseChangeMap A sq₁
  let E₂ := rightDerivedLowerShriekBaseChangeMap A sq₂
  let E₃ := rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)
  let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v
  let c' := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v'
  let δ₁ := TwoSquare.mk _ _ _ _ (inv E₁)
  let δ₂ := TwoSquare.mk _ _ _ _ (inv E₂)
  have h : TwoSquare.mk _ _ _ _ (inv E₃) =
      ((δ₁.hComp δ₂).whiskerTop c'.hom).whiskerBottom c.inv := by
    apply TwoSquare.ext
    intro M
    dsimp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    let Vw := (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor
    let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f''
    have he : (asIso E₃).app M =
        c.app _ ≪≫ Vw.mapIso ((asIso E₁).app M) ≪≫
          (asIso E₂).app _ ≪≫ F.mapIso (c'.symm.app M) := by
      apply Iso.ext
      apply (cancel_epi (c.inv.app _)).mp
      apply (cancel_mono (F.map (c'.hom.app M))).mp
      simp only [Iso.app_hom, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        asIso_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
        ← F.map_comp, Iso.inv_hom_id_app]
      have hid := CategoryTheory.Functor.map_id F
        (((upperStar (ModuleCat.{u + 1} A) v').leftDerivedFunctor ⋙
          (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor).obj M)
      rw [hid]
      erw [Category.comp_id]
      exact (affineLinearExchange_paste A sq₁ sq₂ M).symm
    have hi := congrArg Iso.inv he
    simpa only [Iso.app_inv, asIso_inv, Iso.trans_inv, Functor.mapIso_inv,
      Iso.symm_inv, Category.assoc, Vw, F] using hi
  have hm := congrArg (fun z ↦ z.natTrans.app K)
    (congrArg (mateEquiv
      (rightDerivedUpperShriekAdjunction A f)
      (rightDerivedUpperShriekAdjunction A f'')) h)
  rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp] at hm
  simpa only [rightDerivedUpperShriekBaseChangeMap, δ₁, δ₂, E₁, E₂, E₃,
    TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.natTrans, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, c, c'] using hm

private theorem dualizing_base_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w) :
    dualizingComplexBaseChangeMap A (sq₂.paste_horiz sq₁) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app
        (dualizingComplex A f) ≫
      (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A sq₁) ≫ dualizingComplexBaseChangeMap A sq₂ := by
  have hu := (canonicalDerivedPullbackCompositionMonoidal A v w (𝟙 Y'')
    (𝟙_ _) (𝟙_ _)).2.1
  have hn := (rightDerivedUpperShriekBaseChangeMap A sq₂).naturality
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) v).hom
  simp only [Functor.comp_map] at hn
  unfold dualizingComplexBaseChangeMap dualizingComplex
  rw [exceptional_base_comp A sq₁ sq₂]
  simp only [Category.assoc, Functor.map_comp]
  erw [reassoc_of% hn]
  rw [← hu]
  simp only [Functor.map_comp]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc]

private theorem section_pullback_comp
    (A : Type (u + 1)) [CommRing A]
    {B B' B'' X X' X'' : Scheme.{u}}
    (v : B' ⟶ B) (w : B'' ⟶ B')
    (s : B ⟶ X) (s' : B' ⟶ X') (s'' : B'' ⟶ X'')
    (r : X' ⟶ X) (r' : X'' ⟶ X')
    (h₁ : v ≫ s = s' ≫ r) (h₂ : w ≫ s' = s'' ≫ r')
    (h₃ : (w ≫ v) ≫ s = s'' ≫ (r' ≫ r)) (K : DerivedCategoryModule A X) :
    (sectionCoherencePullbackIso A (w ≫ v) s s'' (r' ≫ r) h₃ K).hom ≫
        (upperStar (ModuleCat.{u + 1} A) s'').leftDerivedFunctor.map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r' r).hom.app K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).hom.app
        ((upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor.map
        (sectionCoherencePullbackIso A v s s' r h₁ K).hom ≫
      (sectionCoherencePullbackIso A w s' s'' r' h₂
        ((upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K)).hom := by
  let C := ModuleCat.{u + 1} A
  have ha := leftDerivedUpperStarComp_assoc'_app C w v s (w ≫ v) (v ≫ s)
    ((w ≫ v) ≫ s) rfl rfl rfl K
  have hb := leftDerivedUpperStarComp_assoc'_app C w s' r (w ≫ s') (v ≫ s)
    ((w ≫ v) ≫ s) rfl h₁ (by rw [Category.assoc, h₁, Category.assoc]) K
  have hc := leftDerivedUpperStarComp_assoc'_app C s'' r' r (w ≫ s') (r' ≫ r)
    ((w ≫ v) ≫ s) h₂ rfl (by rw [Category.assoc, h₁, Category.assoc]) K
  unfold sectionCoherencePullbackIso
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  apply (cancel_epi ((leftDerivedUpperStarComp C (w ≫ v) s).hom.app K)).mp
  dsimp only [C] at ha hb hc ⊢
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% ha]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [reassoc_of% hb, Iso.hom_inv_id_app_assoc]
  exact hc

private noncomputable def structural_locality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X B : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    (u : U ⟶ X) [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (f : X ⟶ B) [HasCompactification f] [HasCompactification (u ≫ f)] :
    rightDerivedUpperShriek A f ⋙
        (upperStar (ModuleCat.{u + 1} A) u).leftDerivedFunctor ≅
      rightDerivedUpperShriek A (u ≫ f) :=
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) u) ≪≫
  Classical.choose (existsUnique_etaleAmbientAdjointLocalityIso A u f
    (HasCompactification.compactification f)
    (HasCompactification.compactification (u ≫ f))
    (rightDerivedUpperShriek A f)
    (rightDerivedUpperShriek A (u ≫ f))
    (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction A (u ≫ f)))

set_option backward.isDefEq.respectTransparency false in
private theorem structural_locality_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X B : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    (u : U ⟶ X) [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (f : X ⟶ B) [HasCompactification f] [HasCompactification (u ≫ f)]
    (K : DerivedCategoryModule A B) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (u ≫ f)).map
        ((structural_locality A u f).hom.app K) ≫
        (rightDerivedUpperShriekAdjunction A (u ≫ f)).counit.app K =
      (etaleAmbientLeftComparison A N u f
        (HasCompactification.compactification f)
        (HasCompactification.compactification (u ≫ f))).inv.app _ ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) u inferInstance).ofNatIsoRight
            (leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} A) u).symm).counit.app
                ((rightDerivedUpperShriek A f).obj K)) ≫
      (rightDerivedUpperShriekAdjunction A f).counit.app K := by
  have hh := (Classical.choose_spec (existsUnique_etaleAmbientAdjointLocalityIso A u f
    (HasCompactification.compactification f)
    (HasCompactification.compactification (u ≫ f))
    (rightDerivedUpperShriek A f)
    (rightDerivedUpperShriek A (u ≫ f))
    (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction A (u ≫ f)))).1 N K
  simp only [structural_locality, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  change (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (u ≫ f)).map _ ≫ _ = _ at hh
  rw [hh]
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.symm_inv, Functor.map_comp, Category.assoc]
  have hn := (etaleAmbientLeftComparison A N u f
    (HasCompactification.compactification f)
    (HasCompactification.compactification (u ≫ f))).inv.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) u).hom.app
          ((rightDerivedUpperShriek A f).obj K))
  change (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (u ≫ f)).map _ ≫ _ =
    _ ≫ (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map _ at hn
  rw [reassoc_of% hn]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem structural_locality_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X B U' X' B' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    [IsNoetherian U'] [IsNoetherian X'] [IsNoetherian B']
    (u : U ⟶ X) (f : X ⟶ B) (u' : U' ⟶ X') (f' : X' ⟶ B')
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [Etale u'] [IsSeparated u'] [LocallyOfFiniteType u'] [QuasiCompact u']
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f']
    (f₁ : U ⟶ B) (hf₁ : u ≫ f = f₁)
    (f₁' : U' ⟶ B') (hf₁' : u' ≫ f' = f₁')
    [HasCompactification f₁] [HasCompactification f₁']
    [QuasiCompact f'] [QuasiCompact f₁']
    (v : B' ⟶ B) (r : X' ⟶ X) (r₁ : U' ⟶ U)
    (sq : IsPullback r f' f v) (sqU : IsPullback r₁ u' u r)
    (sq₁ : IsPullback r₁ f₁' f₁ v) :
    (sectionCoherencePullbackIso A r₁ u u' r sqU.w
      (dualizingComplex A f)).hom ≫
      (upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A sq) ≫
      (sectionStructuralLocalityIso A u' f' f₁' hf₁').hom =
      (upperStar (ModuleCat.{u + 1} A) r₁).leftDerivedFunctor.map
        (sectionStructuralLocalityIso A u f f₁ hf₁).hom ≫
      dualizingComplexBaseChangeMap A sq₁ := by
  subst f₁
  subst f₁'
  obtain ⟨N⟩ := nonempty_etaleCompactSupportNormalization A
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq₁
  let C := ModuleCat.{u + 1} A
  let a := (derivedEtaleLowerShriekUpperStarAdjunction C u inferInstance).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory C u).symm
  let a' := (derivedEtaleLowerShriekUpperStarAdjunction C u' inferInstance).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory C u').symm
  let α := etaleAmbientLeftComparison A N u f
    (HasCompactification.compactification f)
    (HasCompactification.compactification (u ≫ f))
  let α' := etaleAmbientLeftComparison A N u' f'
    (HasCompactification.compactification f')
    (HasCompactification.compactification (u' ≫ f'))
  let J := (leftDerivedUpperStarComp C r₁ u).symm ≪≫
    leftDerivedUpperStarComp C u' r (r₁ ≫ u) sqU.w
  have hm := locality_mate_naturality a
    (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction A (u ≫ f)) a'
    (rightDerivedUpperShriekAdjunction A f')
    (rightDerivedUpperShriekAdjunction A (u' ≫ f'))
    α α' (structural_locality A u f) (structural_locality A u' f')
    (structural_locality_counit A N u f) (structural_locality_counit A N u' f')
    J.hom (TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap A sq)))
    (TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap A sq₁)))
    (etaleAmbientLeftComparison_baseChange A N u f u' f' v r r₁ sq sqU sq₁) (𝟙_ _)
  have hn := (structural_locality A u' f').hom.naturality
    (leftDerivedUpperStarUnitIso C v).hom
  simp only [Functor.comp_map] at hn
  have ht := congrArg (fun z ↦ z ≫
    (rightDerivedUpperShriek A (u' ≫ f')).map
      (leftDerivedUpperStarUnitIso C v).hom) hm
  dsimp only [TwoSquare.mk, TwoSquare.natTrans] at ht
  change _ = _ at ht
  simp only [Category.assoc] at ht
  rw [← hn] at ht
  simpa only [dualizingComplexBaseChangeMap, sectionStructuralLocalityIso,
    structural_locality, sectionCoherencePullbackIso, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc,
    rightDerivedUpperShriekBaseChangeMap, dualizingComplex, C, J] using ht

private theorem section_pullback_locality_comp
    (A : Type (u + 1)) [CommRing A]
    {B B' X X' Y Y' : Scheme.{u}}
    (v : B' ⟶ B) (s : B ⟶ X) (s' : B' ⟶ X')
    (s₁ : B ⟶ Y) (s₁' : B' ⟶ Y')
    (u : Y ⟶ X) (u' : Y' ⟶ X') (r : X' ⟶ X) (r₁ : Y' ⟶ Y)
    (hs : v ≫ s = s' ≫ r) (hs₁ : v ≫ s₁ = s₁' ≫ r₁)
    (hu : s₁ ≫ u = s) (hu' : s₁' ≫ u' = s')
    (hr : r₁ ≫ u = u' ≫ r) (K : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s₁ u s hu.symm).hom.app K) ≫
      (sectionCoherencePullbackIso A v s₁ s₁' r₁ hs₁
        ((upperStar (ModuleCat.{u + 1} A) u).leftDerivedFunctor.obj K)).hom ≫
      (upperStar (ModuleCat.{u + 1} A) s₁').leftDerivedFunctor.map
        (sectionCoherencePullbackIso A r₁ u u' r hr K).hom =
    (sectionCoherencePullbackIso A v s s' r hs K).hom ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s₁' u' s' hu'.symm).hom.app
        ((upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K) := by
  let C := ModuleCat.{u + 1} A
  have ha := leftDerivedUpperStarComp_assoc'_app C v s₁ u (v ≫ s₁) s (v ≫ s)
    rfl hu.symm (by rw [Category.assoc, hu]) K
  have hb := leftDerivedUpperStarComp_assoc'_app C s₁' r₁ u (v ≫ s₁)
    (r₁ ≫ u) (v ≫ s) hs₁ rfl (by rw [Category.assoc, hu]) K
  have hc := leftDerivedUpperStarComp_assoc'_app C s₁' u' r s' (r₁ ≫ u) (v ≫ s)
    hu'.symm hr hs K
  dsimp only [C] at ha hb hc ⊢
  unfold sectionCoherencePullbackIso
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v s).hom.app K)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% ha, Iso.hom_inv_id_app_assoc, ← reassoc_of% hb]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact hc

end AlgebraicGeometry.Etale
