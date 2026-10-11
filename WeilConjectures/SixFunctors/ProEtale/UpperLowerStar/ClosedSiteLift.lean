/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftPushout
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!
# Lifting objects of the pro-étale site of a closed subscheme

Let `i : Z ⟶ X` be a closed immersion and `u : X.ProEt ⥤ Z.ProEt` base change along `i`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Blueprint `def-exc-closed-site-lift`, `lem-exc-closed-site-adjunction`: let `U ⊆ X` be an
affine open and `T` an affine weakly étale `Z`-scheme over `Z ∩ U` whose ring is ind-étale over
`Γ(Z ∩ U)`. Then `Y = Spec H_A(Γ(T))`, with `A = Γ(U)`, is a pro-affine-étale `X`-scheme whose
base change to `Z` is `T`, and every morphism `T ⟶ W ×_X Z` to the base change of an affine
`X`-scheme `W` over `U` with ind-étale ring comes from a morphism `Y ⟶ W`. -/
theorem exists_closedSiteLift (U : X.affineOpens) (T : Z.ProEt) [IsAffine T.left]
    (t : T.left ⟶ (i ⁻¹ᵁ U.1).toScheme) (ht : t ≫ (i ⁻¹ᵁ U.1).ι = T.hom)
    (hind : t.appTop.hom.IndEtale) :
    ∃ (Y : X.AffineProEt)
      (e : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
        ((AffineProEt.toProEt X).obj Y) ≅ T),
      ∀ (W : X.ProEt) [IsAffine W.left] (w : W.left ⟶ U.1.toScheme), w ≫ U.1.ι = W.hom →
        w.appTop.hom.IndEtale →
        ∀ φ : T ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj W,
          ∃ g : (AffineProEt.toProEt X).obj Y ⟶ W,
            (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).map g = e.hom ≫ φ := by
  classical
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine (i ⁻¹ᵁ U.1).toScheme := U.2.preimage i
  let π := (i ∣_ U.1).appTop
  have hπ : Function.Surjective π :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (i ∣_ U.1)).2
  let J := RingHom.ker π.hom
  let eq : Γ(U.1.toScheme, ⊤) ⧸ J ≃+* Γ((i ⁻¹ᵁ U.1).toScheme, ⊤) :=
    RingHom.quotientKerEquivOfSurjective hπ
  let _ : Algebra Γ(U.1.toScheme, ⊤) Γ(T.left, ⊤) := (π ≫ t.appTop).hom.toAlgebra
  let _ : Algebra (Γ(U.1.toScheme, ⊤) ⧸ J) Γ(T.left, ⊤) :=
    (t.appTop.hom.comp eq.toRingHom).toAlgebra
  have : IsScalarTower Γ(U.1.toScheme, ⊤) (Γ(U.1.toScheme, ⊤) ⧸ J) Γ(T.left, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change (π ≫ t.appTop) a = t.appTop (eq (Ideal.Quotient.mk J a))
      rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
      rfl
  have : Algebra.IndEtale (Γ(U.1.toScheme, ⊤) ⧸ J) Γ(T.left, ⊤) :=
    (RingHom.IndEtale.algebraMap_iff _ _).1
      (RingHom.IndEtale.isStableUnderBaseChange.localizationPreserves.away.respectsIso.2 _ _
        hind)
  let H := Algebra.ClosedLift Γ(U.1.toScheme, ⊤) Γ(T.left, ⊤)
  -- the pushout square of rings
  have hpo : IsPushout (CommRingCat.ofHom (algebraMap Γ(U.1.toScheme, ⊤) H)) π
      (CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom _ _).toRingHom) t.appTop :=
    (Algebra.ClosedLift.isPushout_reduction _ _ J).of_iso (Iso.refl _) (Iso.refl _)
      eq.toCommRingCatIso (Iso.refl _) ((Category.comp_id _).trans (Category.id_comp _).symm)
      (by ext a; exact RingHom.quotientKerEquivOfSurjective_apply_mk hπ a)
      ((Category.comp_id _).trans (Category.id_comp _).symm) (by ext a; rfl)
  -- the pullback square of schemes
  have hpb : IsPullback (T.left.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom _ _).toRingHom)) T.hom
      ((Spec.map (CommRingCat.ofHom (algebraMap Γ(U.1.toScheme, ⊤) H)) ≫
        U.1.toScheme.isoSpec.inv) ≫ U.1.ι) i := by
    rw [← ht]
    refine IsPullback.paste_vert ?_ (isPullback_morphismRestrict i U.1)
    refine (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).of_iso T.left.isoSpec.symm (Iso.refl _)
      (i ⁻¹ᵁ U.1).toScheme.isoSpec.symm U.1.toScheme.isoSpec.symm (by simp)
      (Scheme.isoSpec_inv_naturality t) (by simp) (Scheme.isoSpec_inv_naturality _)
  have hY : proAffineEtale ((Spec.map (CommRingCat.ofHom (algebraMap Γ(U.1.toScheme, ⊤) H)) ≫
      U.1.toScheme.isoSpec.inv) ≫ U.1.ι) := by
    rw [Category.assoc]
    refine proAffineEtale.comp_mem _ _ (proAffineEtale_Spec_iff.2 ?_)
      (proAffineEtale.of_isAffine _)
    exact (RingHom.IndEtale.algebraMap_iff _ _).2 inferInstance
  refine ⟨AffineProEt.mk _ hY, MorphismProperty.Over.isoMk hpb.isoPullback.symm
    hpb.isoPullback_inv_snd, fun W _ w hw hwind φ ↦ ?_⟩
  let _ : Algebra Γ(U.1.toScheme, ⊤) Γ(W.left, ⊤) := w.appTop.hom.toAlgebra
  have : Algebra.IndEtale Γ(U.1.toScheme, ⊤) Γ(W.left, ⊤) :=
    (RingHom.IndEtale.algebraMap_iff _ _).1 hwind
  let φ' : T.left ⟶ W.left := φ.left ≫ pullback.fst W.hom i
  have hφw : φ.left ≫ pullback.snd W.hom i = T.hom := MorphismProperty.Over.w φ
  have hφ' : φ' ≫ w = t ≫ (i ∣_ U.1) := by
    rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, hw, Category.assoc, morphismRestrict_ι,
      ← Category.assoc t, ht]
    simp only [pullback.condition]
    rw [← Category.assoc, hφw]
  let φa : Γ(W.left, ⊤) →ₐ[Γ(U.1.toScheme, ⊤)] Γ(T.left, ⊤) :=
    { φ'.appTop.hom with
      commutes' a := by
        have h2 : w.appTop ≫ φ'.appTop = π ≫ t.appTop := by
          rw [← Scheme.Hom.comp_appTop, hφ', Scheme.Hom.comp_appTop]
        exact congrArg (fun f ↦ f.hom a) h2 }
  obtain ⟨ψ, hψ⟩ := Algebra.ClosedLift.exists_toAlgHom_comp_eq _ φa
  refine ⟨MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
    W.left.isoSpec.inv) ?_, ?_⟩
  · have hb : w.appTop ≫ CommRingCat.ofHom ψ.toRingHom =
        CommRingCat.ofHom (algebraMap Γ(U.1.toScheme, ⊤) H) := by
      ext a
      exact ψ.commutes a
    have : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ W.left.isoSpec.inv ≫ W.hom =
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(U.1.toScheme, ⊤) H)) ≫
          U.1.toScheme.isoSpec.inv) ≫ U.1.ι := by
      rw [← hw, ← Scheme.isoSpec_inv_naturality_assoc, ← Spec.map_comp_assoc, hb,
        Category.assoc]
    exact this
  · ext1
    refine pullback.hom_ext ?_ ?_
    · rw [← cancel_epi hpb.isoPullback.hom]
      have hcomp : CommRingCat.ofHom ψ.toRingHom ≫
          CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom _ _).toRingHom = φ'.appTop := by
        ext a
        exact DFunLike.congr_fun hψ a
      simp only [MorphismProperty.Over.pullback_map_left, MorphismProperty.Comma.comp_left,
        MorphismProperty.Over.isoMk_hom_left, Iso.symm_hom, pullback.lift_fst, Category.assoc,
        Iso.hom_inv_id_assoc]
      have key : (T.left.isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom _ _).toRingHom)) ≫
          Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ W.left.isoSpec.inv = φ' := by
        rw [Category.assoc, ← Spec.map_comp_assoc, hcomp, Scheme.isoSpec_hom_naturality_assoc,
          Iso.hom_inv_id, Category.comp_id]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) hpb.isoPullback_hom_fst).trans key)
    · simp only [MorphismProperty.Over.pullback_map_left, MorphismProperty.Comma.comp_left,
        MorphismProperty.Over.isoMk_hom_left, Iso.symm_hom, pullback.lift_snd, Category.assoc]
      rw [hφw, hpb.isoPullback_inv_snd]
      rfl

omit [IsClosedImmersion i] in
/-- The ring of an affine scheme `V` over an affine open `U` of `S` is ind-étale over `Γ(U)` as
soon as `V ⟶ U ⟶ S` is pro-affine-étale. -/
lemma indEtale_appTop_of_proAffineEtale_comp {S V : Scheme.{u}} [IsAffine V] (U : S.affineOpens)
    (a : V ⟶ U.1.toScheme) (h : proAffineEtale (a ≫ U.1.ι)) : a.appTop.hom.IndEtale := by
  have : IsAffine U.1.toScheme := U.2
  exact proAffineEtale_iff_appTop.1 (MorphismProperty.of_postcomp (W := proAffineEtale)
    (W' := proAffineEtale) a U.1.ι (proAffineEtale.of_isAffine _) h)

/-- A morphism of schemes landing in an open `V` lifts through the inclusion of `V`. -/
noncomputable def liftToOpen {S Y : Scheme.{u}} (V : S.Opens) (g : Y ⟶ S) (h : ∀ y, g y ∈ V) :
    Y ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι g (by rw [Scheme.Opens.range_ι]; rintro _ ⟨y, rfl⟩; exact h y)

@[reassoc (attr := simp)]
lemma liftToOpen_ι {S Y : Scheme.{u}} (V : S.Opens) (g : Y ⟶ S) (h : ∀ y, g y ∈ V) :
    liftToOpen V g h ≫ V.ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- The base change to `Z` of a pro-affine-étale `X`-scheme, viewed as a functor from the affine
pro-étale site of `X` to the pro-étale site of `Z`. -/
noncomputable abbrev closedBaseChange : X.AffineProEt ⥤ Z.ProEt :=
  AffineProEt.toProEt X ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤ i

/-- Every affine pro-affine-étale `Z`-scheme is covered by base changes of pro-affine-étale
`X`-schemes: cover it by affine opens lying over affine opens `U` of `X` and lift these by
`AlgebraicGeometry.ProEtale.exists_closedSiteLift`. -/
lemma coverByImage_closedBaseChange_mem (c : Z.AffineProEt) :
    Sieve.coverByImage (closedBaseChange i) ((AffineProEt.toProEt Z).obj c) ∈
      ProEt.topology Z _ := by
  set T := (AffineProEt.toProEt Z).obj c
  have hT : proAffineEtale T.hom := c.prop
  have hU (p : T.left) : ∃ U ∈ X.affineOpens, i (T.hom p) ∈ U ∧ U ≤ ⊤ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (Set.mem_univ _)
  choose U hU hpU _ using hU
  have hV (p : T.left) : ∃ V ∈ T.left.affineOpens, p ∈ V ∧ V ≤ T.hom ⁻¹ᵁ (i ⁻¹ᵁ U p) :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.left.isBasis_affineOpens (hpU p)
  choose V hV hpV hVU using hV
  refine ProEt.mem_topology_of_openImmersion _ (fun p ↦ (V p).ι) (fun p ↦ ⟨p, by simpa using hpV p⟩)
    fun p ↦ ?_
  have : IsAffine (V p).toScheme := hV p
  have : IsAffine (ProEt.ofOpenImmersion T (V p).ι).left := hV p
  let U' : X.affineOpens := ⟨U p, hU p⟩
  let t : (V p).toScheme ⟶ (i ⁻¹ᵁ U'.1).toScheme :=
    liftToOpen _ ((V p).ι ≫ T.hom) fun y ↦ hVU p y.2
  have ht : t ≫ (i ⁻¹ᵁ U'.1).ι = (ProEt.ofOpenImmersion T (V p).ι).hom := liftToOpen_ι _ _ _
  have hind : t.appTop.hom.IndEtale := by
    refine indEtale_appTop_of_proAffineEtale_comp ⟨_, U'.2.preimage i⟩ t ?_
    rw [ht]
    exact proAffineEtale.comp_mem _ _ (proAffineEtale.of_isAffine _) hT
  obtain ⟨Y, e, -⟩ := exists_closedSiteLift i U' (ProEt.ofOpenImmersion T (V p).ι) t ht hind
  exact ⟨⟨Y, e.inv, e.hom ≫ ProEt.ofOpenImmersionHom T (V p).ι, by simp⟩⟩

/-- Blueprint `lem-exc-closed-site-adjunction`, the covering half: base change from the affine
pro-étale site of `X` to the pro-étale site of `Z` is cover dense. -/
instance isCoverDense_closedBaseChange :
    (closedBaseChange i).IsCoverDense (ProEt.topology Z) where
  is_cover T := by
    refine (ProEt.topology Z).transitive
      ((AffineProEt.toProEt Z).is_cover_of_isCoverDense _ T) _ fun T' f hf ↦ ?_
    obtain ⟨⟨c, l, m, rfl⟩⟩ := hf
    rw [Sieve.pullback_comp]
    refine (ProEt.topology Z).pullback_stable l
      ((ProEt.topology Z).superset_covering ?_ (coverByImage_closedBaseChange_mem i c))
    rintro V g ⟨⟨Y, l', m', rfl⟩⟩
    exact ⟨⟨Y, l', m' ≫ m, by simp⟩⟩

/-- The local step of `AlgebraicGeometry.ProEtale.isLocallyFull_closedBaseChange`: let
`f : Y₁ ×_X Z ⟶ Y₂ ×_X Z`, let `U ⊆ X` be an affine open, `W₁ ⊆ Y₁` and `W₂ ⊆ Y₂` affine opens
over `U`, and `V ⊆ Y₁ ×_X Z` an affine open mapping to `W₁` and, under `f`, to `W₂ ×_X Z`. Then
the inclusion of `V` lies in the image sieve of `f`: it factors through the base change of a
morphism `Y ⟶ Y₁` from the lift `Y` of `V`, along which `f` lifts to `Y ⟶ Y₂`. -/
lemma closedBaseChange_functorPushforward_imageSieve {Y₁ Y₂ : X.AffineProEt}
    (f : (closedBaseChange i).obj Y₁ ⟶ (closedBaseChange i).obj Y₂) (U : X.affineOpens)
    (W₁ : Y₁.left.Opens) (hW₁ : IsAffineOpen W₁) (hW₁U : W₁ ≤ Y₁.hom ⁻¹ᵁ U.1)
    (W₂ : Y₂.left.Opens) (hW₂ : IsAffineOpen W₂) (hW₂U : W₂ ≤ Y₂.hom ⁻¹ᵁ U.1)
    (V : (pullback Y₁.hom i).Opens) (hV : IsAffineOpen V)
    (hVW : V ≤ pullback.fst Y₁.hom i ⁻¹ᵁ W₁ ⊓ f.left ⁻¹ᵁ (pullback.fst Y₂.hom i ⁻¹ᵁ W₂)) :
    Sieve.functorPushforward (closedBaseChange i) ((closedBaseChange i).imageSieve f)
      (ProEt.ofOpenImmersionHom _ V.ι) := by
  let Q := (closedBaseChange i).obj Y₁
  have hf₂ : f.left ≫ pullback.snd Y₂.hom i = pullback.snd Y₁.hom i := MorphismProperty.Over.w f
  let T := ProEt.ofOpenImmersion Q V.ι
  have : IsAffine T.left := hV
  -- the closed fibre piece `T` and its lift
  let t : T.left ⟶ (i ⁻¹ᵁ U.1).toScheme :=
    liftToOpen _ (V.ι ≫ pullback.snd Y₁.hom i) fun y ↦ by
      rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ i,
        ← pullback.condition, Scheme.Hom.comp_apply]
      exact hW₁U (hVW y.2).1
  have ht : t ≫ (i ⁻¹ᵁ U.1).ι = T.hom := liftToOpen_ι _ _ _
  have hind : t.appTop.hom.IndEtale := by
    refine indEtale_appTop_of_proAffineEtale_comp ⟨_, U.2.preimage i⟩ t ?_
    rw [ht]
    exact proAffineEtale.comp_mem _ _ (proAffineEtale.of_isAffine _)
      (MorphismProperty.pullback_snd _ _ Y₁.prop)
  obtain ⟨Y, e, hlift⟩ := exists_closedSiteLift i U T t ht hind
  -- the affine opens `W₁ ⊆ Y₁` and `W₂ ⊆ Y₂` over `U`
  let W₁' := ProEt.ofOpenImmersion ((AffineProEt.toProEt X).obj Y₁) W₁.ι
  let W₂' := ProEt.ofOpenImmersion ((AffineProEt.toProEt X).obj Y₂) W₂.ι
  have : IsAffine W₁'.left := hW₁
  have : IsAffine W₂'.left := hW₂
  let w₁ : W₁'.left ⟶ U.1.toScheme := liftToOpen _ (W₁.ι ≫ Y₁.hom) fun y ↦ hW₁U y.2
  let w₂ : W₂'.left ⟶ U.1.toScheme := liftToOpen _ (W₂.ι ≫ Y₂.hom) fun y ↦ hW₂U y.2
  have hw₁ : w₁ ≫ U.1.ι = W₁'.hom := liftToOpen_ι _ _ _
  have hw₂ : w₂ ≫ U.1.ι = W₂'.hom := liftToOpen_ι _ _ _
  have hw₁ind : w₁.appTop.hom.IndEtale := by
    refine indEtale_appTop_of_proAffineEtale_comp U w₁ ?_
    rw [hw₁]
    exact proAffineEtale.comp_mem _ _ (proAffineEtale.of_isAffine _) Y₁.prop
  have hw₂ind : w₂.appTop.hom.IndEtale := by
    refine indEtale_appTop_of_proAffineEtale_comp U w₂ ?_
    rw [hw₂]
    exact proAffineEtale.comp_mem _ _ (proAffineEtale.of_isAffine _) Y₂.prop
  -- the morphisms from `T` to the base changes of `W₁` and `W₂`
  let a₁ : T.left ⟶ W₁.toScheme :=
    liftToOpen _ (V.ι ≫ pullback.fst Y₁.hom i) fun y ↦ (hVW y.2).1
  let a₂ : T.left ⟶ W₂.toScheme :=
    liftToOpen _ (V.ι ≫ f.left ≫ pullback.fst Y₂.hom i) fun y ↦ (hVW y.2).2
  let φ₁ : T ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj W₁' :=
    MorphismProperty.Over.homMk (pullback.lift a₁ (V.ι ≫ pullback.snd Y₁.hom i) (by
      change a₁ ≫ W₁.ι ≫ Y₁.hom = _
      simp [a₁, pullback.condition])) (pullback.lift_snd _ _ _)
  let φ₂ : T ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj W₂' :=
    MorphismProperty.Over.homMk (pullback.lift a₂ (V.ι ≫ pullback.snd Y₁.hom i) (by
      change a₂ ≫ W₂.ι ≫ Y₂.hom = _
      simp [a₂, pullback.condition, reassoc_of% hf₂])) (pullback.lift_snd _ _ _)
  obtain ⟨g₁, hg₁⟩ := hlift W₁' w₁ hw₁ hw₁ind φ₁
  obtain ⟨g₂, hg₂⟩ := hlift W₂' w₂ hw₂ hw₂ind φ₂
  have hφ₁ : φ₁ ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).map
      (ProEt.ofOpenImmersionHom ((AffineProEt.toProEt X).obj Y₁) W₁.ι) = ProEt.ofOpenImmersionHom Q V.ι := by
    ext1
    refine pullback.hom_ext ?_ ?_ <;> simp [φ₁, a₁, ProEt.ofOpenImmersionHom]
  have hφ₂ : φ₂ ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).map
      (ProEt.ofOpenImmersionHom ((AffineProEt.toProEt X).obj Y₂) W₂.ι) = ProEt.ofOpenImmersionHom Q V.ι ≫ f := by
    ext1
    refine pullback.hom_ext ?_ ?_
    · simp [φ₂, a₂, ProEt.ofOpenImmersionHom]
    · simp [φ₂, ProEt.ofOpenImmersionHom, hf₂]
  refine ⟨Y, (AffineProEt.toProEt X).preimage (g₁ ≫ ProEt.ofOpenImmersionHom ((AffineProEt.toProEt X).obj Y₁) W₁.ι),
    e.inv, ⟨(AffineProEt.toProEt X).preimage (g₂ ≫ ProEt.ofOpenImmersionHom ((AffineProEt.toProEt X).obj Y₂) W₂.ι), ?_⟩, ?_⟩
  · simp only [closedBaseChange, Functor.comp_map, Functor.map_preimage, Functor.map_comp, hg₁,
      hg₂, Category.assoc, hφ₁, hφ₂]
  · simp only [closedBaseChange, Functor.comp_map, Functor.map_preimage, Functor.map_comp, hg₁,
      Category.assoc, hφ₁, Iso.inv_hom_id_assoc]

/-- Blueprint `lem-exc-closed-site-adjunction`, the morphism half: base change from the affine
pro-étale site of `X` to the pro-étale site of `Z` is locally full. A morphism
`f : Y₁ ×_X Z ⟶ Y₂ ×_X Z` is, near every point, the base change of a morphism out of a lift
`Spec H_A(C̄)` of a small affine open `Spec C̄` of `Y₁ ×_X Z`
(`AlgebraicGeometry.ProEtale.closedBaseChange_functorPushforward_imageSieve`). -/
instance isLocallyFull_closedBaseChange :
    (closedBaseChange i).IsLocallyFull (ProEt.topology Z) where
  functorPushforward_imageSieve_mem {Y₁ Y₂} f := by
    have hf₂ : f.left ≫ pullback.snd Y₂.hom i = pullback.snd Y₁.hom i := MorphismProperty.Over.w f
    have key : f.left ≫ pullback.fst Y₂.hom i ≫ Y₂.hom = pullback.fst Y₁.hom i ≫ Y₁.hom := by
      rw [pullback.condition, reassoc_of% hf₂, pullback.condition]
    have hU (p : ↥(pullback Y₁.hom i)) : ∃ U ∈ X.affineOpens, Y₁.hom (pullback.fst Y₁.hom i p) ∈ U ∧ U ≤ ⊤ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (Set.mem_univ _)
    choose U hU hpU _ using hU
    have hW₁ (p : ↥(pullback Y₁.hom i)) : ∃ W ∈ Y₁.left.affineOpens, pullback.fst Y₁.hom i p ∈ W ∧
        W ≤ Y₁.hom ⁻¹ᵁ U p :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y₁.left.isBasis_affineOpens (hpU p)
    choose W₁ hW₁ hpW₁ hW₁U using hW₁
    have hW₂ (p : ↥(pullback Y₁.hom i)) : ∃ W ∈ Y₂.left.affineOpens, pullback.fst Y₂.hom i (f.left p) ∈ W ∧
        W ≤ Y₂.hom ⁻¹ᵁ U p := by
      refine TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y₂.left.isBasis_affineOpens ?_
      have h := congrArg (fun g ↦ g p) key
      simp only [Scheme.Hom.comp_apply] at h
      exact (Scheme.Hom.mem_preimage _).2 (h ▸ hpU p)
    choose W₂ hW₂ hpW₂ hW₂U using hW₂
    have hV (p : ↥(pullback Y₁.hom i)) : ∃ V ∈ (pullback Y₁.hom i).affineOpens, p ∈ V ∧
        V ≤ pullback.fst Y₁.hom i ⁻¹ᵁ W₁ p ⊓ f.left ⁻¹ᵁ (pullback.fst Y₂.hom i ⁻¹ᵁ W₂ p) :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (pullback Y₁.hom i).isBasis_affineOpens ⟨hpW₁ p, hpW₂ p⟩
    choose V hV hpV hVW using hV
    exact ProEt.mem_topology_of_openImmersion _ (fun p ↦ (V p).ι)
      (fun p ↦ ⟨p, by simpa using hpV p⟩) fun p ↦
        closedBaseChange_functorPushforward_imageSieve i f ⟨U p, hU p⟩ (W₁ p) (hW₁ p) (hW₁U p)
          (W₂ p) (hW₂ p) (hW₂U p) (V p) (hV p) (hVW p)

end ProEtale

end AlgebraicGeometry
