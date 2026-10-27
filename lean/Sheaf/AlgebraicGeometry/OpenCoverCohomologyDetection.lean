/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.OpenSmallRingedSiteCoherence
import Sheaf.CategoryTheory.ExactDerivedCohomologyCoherence
import Sheaf.AlgebraicGeometry.ZariskiCoverSliceModuleDetection
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Open-site cohomology comparison and vanishing detection

Source: Stacks Project, Tags 04IX, 00VR, 00XZ, 03EH, 010N and 015F
(blueprint: lem-pur-open-cover-cohomology-detection).
The Boolean parameter selects the small etale site (`false`) or small pro-etale site
(`true`). The helpers only dispatch to the recorded sites and sectionwise restrictions.
All module and coefficient objects live in the common universe `u + 1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u w v
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.OpenCoverCohomology

/-- The two existing small sites. Source: Stacks 03P0 and 098K
(blueprint: lem-pur-open-cover-cohomology-detection). -/
abbrev Site (T : Scheme.{u}) : Bool → Type (u + 1)
  | false => T.Etale
  | true => T.ProEt

/-- The inherited category of the selected site. Source: Stacks 03P0 and 098K
(blueprint: lem-pur-open-cover-cohomology-detection). -/
instance siteCategory (T : Scheme.{u}) : (b : Bool) → Category.{u} (Site T b)
  | false => inferInstanceAs (Category T.Etale)
  | true => inferInstanceAs (Category T.ProEt)

/-- The recorded topology of the selected site. Source: Stacks 03P0 and 098K
(blueprint: lem-pur-open-cover-cohomology-detection). -/
abbrev topology (T : Scheme.{u}) : (b : Bool) → GrothendieckTopology (Site T b)
  | false => T.smallEtaleTopology
  | true => Scheme.ProEt.topology T

/-- The existing small site forgetful functor. Source: Stacks 03P0 and 098K
(blueprint: lem-pur-open-cover-cohomology-detection). -/
def forget (T : Scheme.{u}) : (b : Bool) → Site T b ⥤ Scheme.{u}
  | false => Scheme.Etale.forget T ⋙ Over.forget T
  | true => Scheme.ProEt.forget T ⋙ Over.forget T

/-- An open subscheme as an object of either small site. Source: Stacks 025G and 098B
(blueprint: lem-pur-open-cover-cohomology-detection). -/
def openObject (T : Scheme.{u}) : (b : Bool) → T.Opens → Site T b
  | false, U => Scheme.Etale.mk U.ι
  | true, U => Scheme.ProEt.mk U.ι

/-- The terminal object, the scheme itself. Source: Stacks 03P0 and 098K
(blueprint: lem-pur-open-cover-cohomology-detection). -/
def terminalObject (T : Scheme.{u}) : (b : Bool) → Site T b
  | false => Scheme.Etale.mk (𝟙 T)
  | true => Scheme.ProEt.mk (𝟙 T)

/-- The morphism representing an open inclusion. Source: Stacks 00XZ
(blueprint: lem-pur-open-cover-cohomology-detection). -/
def openArrow (T : Scheme.{u}) : (b : Bool) → (U : T.Opens) →
    openObject T b U ⟶ terminalObject T b
  | false, U => MorphismProperty.Over.homMk U.ι (Category.comp_id _)
  | true, U => MorphismProperty.Over.homMk U.ι (Category.comp_id _)

/-- The existing equivalence of the open small site with the slice. Source: Stacks 00XZ
(blueprint: lem-pur-open-cover-cohomology-detection). -/
def localization (T : Scheme.{u}) : (b : Bool) → (U : T.Opens) →
    Over (openObject T b U) ≌ Site U.toScheme b
  | false, U => Scheme.Etale.overEquiv (Scheme.Etale.mk U.ι)
  | true, U => Scheme.ProEt.sliceEquiv T (Scheme.ProEt.mk U.ι)

/-- The morphism of site objects for nested opens. Source: Stacks 03EH
(blueprint: lem-pur-open-cover-cohomology-detection). -/
def nestedArrow (T : Scheme.{u}) : (b : Bool) → {W U : T.Opens} → (W ≤ U) →
    (openObject T b W ⟶ openObject T b U)
  | false, _, _, h => MorphismProperty.Over.homMk (T.homOfLE h)
      (T.homOfLE_ι h)
  | true, _, _, h => MorphismProperty.Over.homMk (T.homOfLE h)
      (T.homOfLE_ι h)

/-- The common-universe site is essentially small. Source: size convention, Stacks 03P0/098K
(blueprint: lem-pur-open-cover-cohomology-detection). -/
instance siteEssentiallySmall (T : Scheme.{u}) :
    (b : Bool) → EssentiallySmall.{u + 1} (Site T b)
  | false => inferInstance
  | true => inferInstance

/-- The constant commutative coefficient sheaf, using the recorded constant-sheaf functor.
Source: Stacks 00WH (blueprint: lem-pur-open-cover-cohomology-detection). -/
abbrev coefficients (T : Scheme.{u}) (b : Bool) (A : Type (u + 1)) [CommRing A] :=
  (constantSheaf (topology T b) CommRingCat.{u + 1}).obj (CommRingCat.of A)

/-- The underlying ring sheaf of the constant coefficients. Source: Stacks 04IX
(blueprint: lem-pur-open-cover-cohomology-detection). -/
abbrev rings (T : Scheme.{u}) (b : Bool) (A : Type (u + 1)) [CommRing A] :=
  (sheafCompose (topology T b) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (coefficients T b A)

/-- The recorded module category over the constant sheaf. Source: Stacks 04IX
(blueprint: lem-pur-open-cover-cohomology-detection). -/
abbrev Modules (T : Scheme.{u}) (b : Bool) (A : Type (u + 1)) [CommRing A] :=
  ringedSiteModules.{u + 1} (rings T b A)

/-- The recorded module category on the localized ringed site. Source: Stacks 04IX
(blueprint: lem-pur-open-cover-cohomology-detection). -/
abbrev LocalModules (T : Scheme.{u}) (b : Bool) (A : Type (u + 1)) [CommRing A]
    (U : T.Opens) := ringedSiteModules.{u + 1} ((rings T b A).over (openObject T b U))

/-- The existing sectionwise restriction functor. Source: Stacks 04IX(4)
(blueprint: lem-pur-open-cover-cohomology-detection). -/
abbrev restriction (T : Scheme.{u}) (b : Bool) (A : Type (u + 1)) [CommRing A]
    (U : T.Opens) : Modules T b A ⥤ LocalModules T b A U :=
  SheafOfModules.overFunctor.{u + 1} (rings T b A) (openObject T b U)

/-- Additivity from the recorded exact localized restriction. Source: Stacks 03DJ
(blueprint: lem-pur-open-cover-cohomology-detection). -/
instance restrictionAdditive (T : Scheme.{u}) (b : Bool) (A : Type (u + 1)) [CommRing A]
    (U : T.Opens) : (restriction T b A U).Additive :=
  (SheafOfModules.localizedSystemExact.{u + 1, u, u + 1}
    (coefficients T b A) (openObject T b U)).2.2.2.1

/-- Left exactness from the recorded localized restriction. Source: Stacks 03DJ
(blueprint: lem-pur-open-cover-cohomology-detection). -/
instance restrictionLimits (T : Scheme.{u}) (b : Bool) (A : Type (u + 1)) [CommRing A]
    (U : T.Opens) : PreservesFiniteLimits (restriction T b A U) :=
  (SheafOfModules.localizedSystemExact.{u + 1, u, u + 1}
    (coefficients T b A) (openObject T b U)).2.2.2.2.1

/-- Right exactness from the recorded localized restriction. Source: Stacks 03DJ
(blueprint: lem-pur-open-cover-cohomology-detection). -/
instance restrictionColimits (T : Scheme.{u}) (b : Bool) (A : Type (u + 1)) [CommRing A]
    (U : T.Opens) : PreservesFiniteColimits (restriction T b A U) :=
  (SheafOfModules.localizedSystemExact.{u + 1, u, u + 1}
    (coefficients T b A) (openObject T b U)).2.2.2.2.2


/-- Finite limits are those of the existing site categories. Source: Stacks 03P0/098K
(blueprint: lem-pur-open-cover-cohomology-detection). -/
instance siteFiniteLimits (T : Scheme.{u}) : (b : Bool) → HasFiniteLimits (Site T b)
  | false => inferInstance
  | true => inferInstance

/-- The structural morphism of a small-site object. Source: Stacks 03P0/098K
(blueprint: lem-pur-open-cover-cohomology-detection). -/
def structureMap (T : Scheme.{u}) : (b : Bool) → (V : Site T b) →
    ((forget T b).obj V ⟶ T)
  | false, V => V.hom
  | true, V => V.hom

/-- The arrow to the terminal site object. Source: Stacks 03P0/098K
(blueprint: lem-pur-open-cover-cohomology-detection). -/
def toTerminal (T : Scheme.{u}) : (b : Bool) → (V : Site T b) →
    (V ⟶ terminalObject T b)
  | false, V => MorphismProperty.Over.homMk V.hom (Category.comp_id _)
  | true, V => MorphismProperty.Over.homMk V.hom (Category.comp_id _)

/-- Composition with an open immersion on either site. Source: Stacks 00XZ
(blueprint: lem-pur-open-cover-cohomology-detection). -/
def siteMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (b : Bool) → Site X b ⥤ Site Y b
  | false => MorphismProperty.Over.map ⊤ (inferInstance : Etale f)
  | true => MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)

/-- The constant coefficient ring on the slice. Source: Stacks 00WH and 04IX
(blueprint: lem-pur-open-cover-cohomology-detection). -/
abbrev sliceCoefficients (T : Scheme.{u}) (b : Bool) (A : Type (u + 1)) [CommRing A]
    (U : T.Opens) :=
  (constantSheaf ((topology T b).over (openObject T b U)) CommRingCat.{u + 1}).obj
    (CommRingCat.of A)

/-- The canonical sheafification-localization comparison, retaining the constant unit.
Source: Stacks 00XR and 00WH (blueprint: lem-pur-open-cover-cohomology-detection). -/
def coefficientComparison (T : Scheme.{u}) (b : Bool) (A : Type (u + 1)) [CommRing A]
    (U : T.Opens) : sliceCoefficients T b A U ≅
      (coefficients T b A).over (openObject T b U) :=
  ((Over.forget (openObject T b U)).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{u + 1} ((topology T b).over (openObject T b U)) (topology T b)).app
      ((Functor.const (Site T b)ᵒᵖ).obj (CommRingCat.of A))

/-- The canonical comparison of constant rings for successive slice restriction.
Source: Stacks 00XR and 03EH (blueprint: lem-pur-open-cover-cohomology-detection). -/
def nestedCoefficientComparison (T : Scheme.{u}) (b : Bool) (A : Type (u + 1))
    [CommRing A] {W U : T.Opens} (h : W ≤ U) :
    sliceCoefficients T b A W ≅
      ((Over.map (nestedArrow T b h)).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((topology T b).over (openObject T b W))
        ((topology T b).over (openObject T b U))).obj (sliceCoefficients T b A U) :=
  ((Over.map (nestedArrow T b h)).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{u + 1} ((topology T b).over (openObject T b W))
      ((topology T b).over (openObject T b U))).app
        ((Functor.const (Over (openObject T b U))ᵒᵖ).obj (CommRingCat.of A))

private theorem sliceObject_ext {C : Type*} [Category C] (P : MorphismProperty C)
    {Z : C} {U : P.Over ⊤ Z} {V W : Over U}
    (h₀ : V.left.left = W.left.left) (h₁ : HEq V.left.hom W.left.hom)
    (h₂ : HEq V.hom.left W.hom.left) : V = W := by
  rcases V with ⟨⟨⟨v, ⟨⟨⟩⟩, fv⟩, pv⟩, ⟨⟨⟩⟩, hv⟩
  rcases W with ⟨⟨⟨w, ⟨⟨⟩⟩, fw⟩, pw⟩, ⟨⟨⟩⟩, hw⟩
  dsimp only at h₀ h₁ h₂
  cases h₀
  cases eq_of_heq h₁
  have hh : hv = hw := MorphismProperty.Over.Hom.ext (eq_of_heq h₂)
  cases hh
  rfl

private theorem sliceHom_hext {C : Type*} [Category C] (P : MorphismProperty C)
    {Z : C} {U : P.Over ⊤ Z} {V W V' W' : Over U}
    (hv : V = V') (hw : W = W') (f : V ⟶ W) (g : V' ⟶ W')
    (hf : HEq f.left.left g.left.left) : HEq f g := by
  subst V'
  subst W'
  apply heq_of_eq
  apply Over.OverMorphism.ext
  apply MorphismProperty.Over.Hom.ext
  exact eq_of_heq hf

private theorem sliceFunctor_ext {C D : Type*} [Category C] [Category D]
    (P : MorphismProperty C) {Z : C} {U : P.Over ⊤ Z} (F G : D ⥤ Over U)
    (h₀ : ∀ X, (F.obj X).left.left = (G.obj X).left.left)
    (h₁ : ∀ X, HEq (F.obj X).left.hom (G.obj X).left.hom)
    (h₂ : ∀ X, HEq (F.obj X).hom.left (G.obj X).hom.left)
    (hm : ∀ X Y (f : X ⟶ Y), HEq (F.map f).left.left (G.map f).left.left) : F = G := by
  have ho (X : D) : F.obj X = G.obj X := sliceObject_ext P (h₀ X) (h₁ X) (h₂ X)
  exact CategoryTheory.Functor.hext ho
    (fun X Y f ↦ sliceHom_hext P (ho X) (ho Y) _ _ (hm X Y f))

private def sliceInverse {C : Type*} [Category C] (P : MorphismProperty C)
    [P.IsStableUnderComposition] {Z : C} (U : P.Over ⊤ Z) : P.Over ⊤ U.left ⥤ Over U where
  obj V := Over.mk (MorphismProperty.Over.homMk
    (A := (MorphismProperty.Over.map ⊤ U.prop).obj V) V.hom rfl)
  map f := Over.homMk ((MorphismProperty.Over.map ⊤ U.prop).map f)
    (MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w f))

private theorem sliceInverse_comp {C : Type*} [Category C] (P : MorphismProperty C)
    [P.IsStableUnderComposition] {Z : C} {U V : P.Over ⊤ Z} (f : U ⟶ V) (hf : P f.left) :
    sliceInverse P U ⋙ Over.map f =
      MorphismProperty.Over.map ⊤ hf ⋙ sliceInverse P V := by
  refine sliceFunctor_ext P _ _ (fun _ ↦ rfl) ?_
    (fun _ ↦ HEq.rfl) (fun _ _ _ ↦ HEq.rfl)
  intro X
  apply heq_of_eq
  change X.hom ≫ U.hom = (X.hom ≫ f.left) ≫ V.hom
  rw [Category.assoc, MorphismProperty.Over.w f]

/-- Identification of the open small sites, their topologies and their normalized rings.
Source: Stacks 00XZ, 03EH, 00XR, 00WH, 04IX
(blueprint: lem-pur-open-cover-cohomology-detection).
Proof: use lem-weil-pbc-etale-site-localization-open or
lem-weil-proetale-weakly-etale-localization for the displayed equivalence and topology.
Both inverse functors compose the structure map with the open inclusion, hence their
nested-open composites agree. Apply lem-pur-ring-presheaf-sheafification-localization
to the constant presheaf. Its unit equation fixes every constant section and the
sheafification universal property makes this coefficient identification unique.
Applying that uniqueness a second time proves the nested coefficient equation. -/
theorem site_and_coefficients (T : Scheme.{u}) (b : Bool) (A : Type (u + 1))
    [CommRing A] [Finite A] :
    (∀ (U : T.Opens) (V : Site U.toScheme b) (S : Sieve V),
      S ∈ topology U.toScheme b V ↔
        S.functorPushforward (localization T b U).inverse ∈
          (topology T b).over (openObject T b U) ((localization T b U).inverse.obj V)) ∧
    (∀ U : T.Opens,
      (localization T b U).inverse ⋙ Over.forget (openObject T b U) ⋙ forget T b =
        forget U.toScheme b) ∧
    (∀ (U : T.Opens) (V : Site U.toScheme b),
      HEq (structureMap T b ((localization T b U).inverse.obj V).left)
        (structureMap U.toScheme b V ≫ U.ι)) ∧
    (∀ (W U : T.Opens) (h : W ≤ U),
      (localization T b W).inverse ⋙ Over.map (nestedArrow T b h) =
        siteMap (T.homOfLE h) b ⋙ (localization T b U).inverse) ∧
    (∀ (U : T.Opens) (V : Over (openObject T b U)),
      (toSheafify ((topology T b).over (openObject T b U))
          ((Functor.const (Over (openObject T b U))ᵒᵖ).obj (CommRingCat.of A))).app (op V) ≫
        (coefficientComparison T b A U).hom.hom.app (op V) =
      (toSheafify (topology T b)
          ((Functor.const (Site T b)ᵒᵖ).obj (CommRingCat.of A))).app (op V.left)) ∧
    (∀ U : T.Opens,
      ∃ (S : Sheaf (topology U.toScheme b) CommRingCat.{u + 1})
        (_hS : S.obj = (localization T b U).inverse.op ⋙
          ((coefficients T b A).over (openObject T b U)).obj)
        (c : coefficients U.toScheme b A ≅ S),
        ∀ V : Site U.toScheme b,
          HEq ((toSheafify (topology U.toScheme b)
            ((Functor.const (Site U.toScheme b)ᵒᵖ).obj (CommRingCat.of A))).app (op V) ≫
              c.hom.hom.app (op V))
            ((toSheafify (topology T b)
              ((Functor.const (Site T b)ᵒᵖ).obj (CommRingCat.of A))).app
                (op ((localization T b U).inverse.obj V).left))) ∧
    (∀ (W U : T.Opens) (h : W ≤ U),
      (nestedCoefficientComparison T b A h).hom ≫
        ((Over.map (nestedArrow T b h)).sheafPushforwardContinuous CommRingCat.{u + 1}
          ((topology T b).over (openObject T b W))
          ((topology T b).over (openObject T b U))).map
            (coefficientComparison T b A U).hom ≫
        (Sheaf.pushforwardOverMapIso (coefficients T b A) (nestedArrow T b h)).hom =
          (coefficientComparison T b A W).hom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U V S
    cases b
    · have hd := Scheme.Etale.overEquiv_inverse_isDenseSubsite (Scheme.Etale.mk U.ι)
      exact hd.functorPushforward_mem_iff.symm
    · have hd := Scheme.ProEt.sliceDense T (Scheme.ProEt.mk U.ι)
      exact hd.functorPushforward_mem_iff.symm
  · intro U
    cases b <;> rfl
  · intro U V
    cases b <;> exact HEq.rfl
  · intro W U h
    cases b
    · exact sliceInverse_comp (P := @Etale) (nestedArrow T false h)
        (inferInstance : Etale (T.homOfLE h))
    · exact sliceInverse_comp (P := @WeaklyEtale) (nestedArrow T true h)
        (inferInstance : WeaklyEtale (T.homOfLE h))
  · intro U V
    exact congrArg (fun f ↦ f.app (op V))
      ((Over.forget (openObject T b U)).toSheafify_pullbackSheafificationCompatibility
        CommRingCat.{u + 1} ((topology T b).over (openObject T b U)) (topology T b)
        ((Functor.const (Site T b)ᵒᵖ).obj (CommRingCat.of A)))
  · intro U
    let G := (localization T b U).inverse ⋙ Over.forget (openObject T b U)
    have : G.IsContinuous (topology U.toScheme b) (topology T b) := by
      cases b
      · change (MorphismProperty.Over.map ⊤
          (inferInstance : Etale U.ι)).IsContinuous _ _
        exact Scheme.Etale.purOpenCompositionContinuous U.ι
      · change (MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale U.ι)).IsContinuous _ _
        exact Scheme.ProEt.isContinuous_overMap _
    have : G.IsCocontinuous (topology U.toScheme b) (topology T b) := by
      cases b
      · change (MorphismProperty.Over.map ⊤
          (inferInstance : Etale U.ι)).IsCocontinuous _ _
        exact Scheme.Etale.purOpenCompositionCocontinuous U.ι
      · change (MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale U.ι)).IsCocontinuous _ _
        exact Scheme.ProEt.isCocontinuous_overMap _
    let S := (G.sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology U.toScheme b) (topology T b)).obj (coefficients T b A)
    let c : coefficients U.toScheme b A ≅ S :=
      (G.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
        (topology U.toScheme b) (topology T b)).app
          ((Functor.const (Site T b)ᵒᵖ).obj (CommRingCat.of A))
    refine ⟨S, rfl, c, fun V ↦ heq_of_eq ?_⟩
    exact congrArg (fun f ↦ f.app (op V))
      (G.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
        (topology U.toScheme b) (topology T b)
        ((Functor.const (Site T b)ᵒᵖ).obj (CommRingCat.of A)))
  · intro W U h
    apply Sheaf.hom_ext
    apply sheafify_hom_ext ((topology T b).over (openObject T b W))
      _ _ ((coefficients T b A).over (openObject T b W)).property
    apply NatTrans.ext
    funext V
    have hn := congrArg (fun f ↦ f.app V)
      ((Over.map (nestedArrow T b h)).toSheafify_pullbackSheafificationCompatibility
        CommRingCat.{u + 1} ((topology T b).over (openObject T b W))
          ((topology T b).over (openObject T b U))
        ((Functor.const (Over (openObject T b U))ᵒᵖ).obj (CommRingCat.of A)))
    have hU := congrArg (fun f ↦ f.app ((Over.map (nestedArrow T b h)).op.obj V))
      ((Over.forget (openObject T b U)).toSheafify_pullbackSheafificationCompatibility
        CommRingCat.{u + 1} ((topology T b).over (openObject T b U)) (topology T b)
        ((Functor.const (Site T b)ᵒᵖ).obj (CommRingCat.of A)))
    have hW := congrArg (fun f ↦ f.app V)
      ((Over.forget (openObject T b W)).toSheafify_pullbackSheafificationCompatibility
        CommRingCat.{u + 1} ((topology T b).over (openObject T b W)) (topology T b)
        ((Functor.const (Site T b)ᵒᵖ).obj (CommRingCat.of A)))
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hn hU hW
    change _ ≫ (_ ≫ _ ≫ 𝟙 _) = _
    simp only [Category.comp_id, ← Category.assoc, NatTrans.comp_app]
    erw [hn, hU, hW]
    rfl


/-- The Zariski covering and all of its base changes cover on both small sites and slices.
Source: Stacks 098B, 00VH, 00XZ
(blueprint: lem-pur-open-cover-cohomology-detection).
Proof: open immersions are etale (lem-weil-pbc-open-immersion-etale), and a jointly
surjective open family is an etale cover. Apply lem-pur-etale-proetale-cover for
the pro-etale case. The covering base-change axiom gives the displayed pullback
family on every V. On the scheme of V it is the inverse-image Zariski cover and
is therefore a cover in the same topology. The slice topology tests exactly the
underlying family, so it also covers the localized site. No finiteness is used. -/
theorem covering (T : Scheme.{u}) (b : Bool) {I : Type v} (U : I → T.Opens)
    (hU : ∀ x : T, ∃ i : I, x ∈ U i) :
    Sieve.ofArrows (fun i => openObject T b (U i)) (fun i => openArrow T b (U i)) ∈
      topology T b (terminalObject T b) ∧
    (∀ V : Site T b,
      Sieve.ofArrows
        (fun i => pullback (toTerminal T b V) (openArrow T b (U i)))
        (fun i => pullback.fst (toTerminal T b V) (openArrow T b (U i))) ∈
          topology T b V) ∧
    (∀ V : Site T b,
      Sieve.ofArrows
        (fun i => openObject ((forget T b).obj V) b ((structureMap T b V) ⁻¹ᵁ U i))
        (fun i => openArrow ((forget T b).obj V) b ((structureMap T b V) ⁻¹ᵁ U i)) ∈
          topology ((forget T b).obj V) b (terminalObject ((forget T b).obj V) b)) ∧
    (∀ V : Site T b,
      Sieve.ofArrows
        (fun i => Over.mk (pullback.fst (toTerminal T b V) (openArrow T b (U i))))
        (fun i => (Over.homMk
          (pullback.fst (toTerminal T b V) (openArrow T b (U i))) (Category.comp_id _) :
          Over.mk (pullback.fst (toTerminal T b V) (openArrow T b (U i))) ⟶
            Over.mk (𝟙 V))) ∈ (topology T b).over V (Over.mk (𝟙 V))) := by
  have base (S : Scheme.{u}) (W : I → S.Opens)
      (hW : ∀ x : S, ∃ i, x ∈ W i) :
      Sieve.ofArrows (fun i ↦ openObject S b (W i))
        (fun i ↦ openArrow S b (W i)) ∈ topology S b (terminalObject S b) := by
    cases b
    · exact (Scheme.zariskiCoverEtaleModuleDetection S W hW).1
    · exact Precoverage.generate_mem_toGrothendieck
        (Scheme.zariskiCoverProetaleModuleDetection S W hW).1
  have hb := base T U hU
  have hp (V : Site T b) :
      Sieve.ofArrows
        (fun i ↦ pullback (toTerminal T b V) (openArrow T b (U i)))
        (fun i ↦ pullback.fst (toTerminal T b V) (openArrow T b (U i))) ∈
          topology T b V := by
    rw [Sieve.ofArrows_eq_pullback_of_isPullback
      (fun i ↦ openArrow T b (U i))
      (fun i ↦ IsPullback.of_hasPullback (toTerminal T b V) (openArrow T b (U i)))]
    exact (topology T b).pullback_stable _ hb
  refine ⟨hb, hp, ?_, ?_⟩
  · intro V
    exact base _ _ (fun x ↦ hU (structureMap T b V x))
  · intro V
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact hp V

/-- Restriction keeps the exact same section modules and section maps.
Source: Stacks 04IX(4), 03DJ (blueprint: lem-pur-open-cover-cohomology-detection).
Proof: def-pur-localized-ringed-site gives both formulas definitionally; the
module structures are pulled back by the identity on the section rings.
lem-pur-site-restriction-module-adjunction-exact gives exactness. -/
theorem restriction_sections (T : Scheme.{u}) (b : Bool) (A : Type (u + 1))
    [CommRing A] [Finite A] (U : T.Opens) :
    (restriction T b A U).Additive ∧ PreservesFiniteLimits (restriction T b A U) ∧
    PreservesFiniteColimits (restriction T b A U) ∧
    (∀ (F : Modules T b A) (V : Over (openObject T b U)),
      ((restriction T b A U).obj F).val.obj (op V) = F.val.obj (op V.left)) ∧
    (∀ (F G : Modules T b A) (f : F ⟶ G) (V : Over (openObject T b U)),
      HEq (((restriction T b A U).map f).val.app (op V)) (f.val.app (op V.left))) := by
  exact ⟨inferInstance, inferInstance, inferInstance, fun _ _ ↦ rfl,
    fun _ _ _ _ ↦ HEq.rfl⟩

/-- The existing restriction between nested opens. Source: Stacks 03EH and 04IX
(blueprint: lem-pur-open-cover-cohomology-detection). -/
abbrev furtherRestriction (T : Scheme.{u}) (b : Bool) (A : Type (u + 1)) [CommRing A]
    {W U : T.Opens} (h : W ≤ U) : LocalModules T b A U ⥤ LocalModules T b A W :=
  SheafOfModules.overMap.{u + 1} (rings T b A) (nestedArrow T b h)

private theorem overMap_additive {C : Type*} [Category C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    {X Y : C} (f : X ⟶ Y) : (SheafOfModules.overMap.{w} R f).Additive :=
  ⟨fun {_ _} g h ↦ by ext V x; rfl⟩

private theorem overMap_limits {C : Type*} [Category C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    {X Y : C} (f : X ⟶ Y) :
    PreservesFiniteLimits (SheafOfModules.overMap.{w} R f) := by
  let S := R.over X
  let G := SheafOfModules.forget.{w} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (SheafOfModules.overMap.{w} R f ⋙ G) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{w} (R.over Y) ⋙ PresheafOfModules.toPresheaf _) ⋙
        (Functor.whiskeringLeft _ _ _).obj (Over.map f).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ G

/-- Exactness of successive open restriction.
Source: Stacks 03EH, 04IX and 03DJ (blueprint: lem-pur-open-cover-cohomology-detection).
Proof: further restriction evaluates a sectionwise linear map on the same domain.
Kernels are sectionwise. The topology on each slice tests the underlying coverings,
so restriction commutes with sheafification of cokernels. This gives finite limits
and colimits, as in lem-pur-site-restriction-module-adjunction-exact. -/
theorem furtherRestriction_exact (T : Scheme.{u}) (b : Bool) (A : Type (u + 1))
    [CommRing A] [Finite A] {W U : T.Opens} (h : W ≤ U) :
    (furtherRestriction T b A h).Additive ∧
    PreservesFiniteLimits (furtherRestriction T b A h) ∧
    PreservesFiniteColimits (furtherRestriction T b A h) := by
  exact ⟨overMap_additive _ _, overMap_limits _ _, inferInstance⟩

/-- Inherited additivity of successive restriction. Source: Stacks 03EH and 04IX
(blueprint: lem-pur-open-cover-cohomology-detection). -/
instance furtherAdditive (T : Scheme.{u}) (b : Bool) (A : Type (u + 1))
    [CommRing A] [Finite A] {W U : T.Opens} (h : W ≤ U) :
    (furtherRestriction T b A h).Additive := (furtherRestriction_exact T b A h).1

/-- Inherited left exactness of successive restriction. Source: Stacks 03EH and 04IX
(blueprint: lem-pur-open-cover-cohomology-detection). -/
instance furtherLimits (T : Scheme.{u}) (b : Bool) (A : Type (u + 1))
    [CommRing A] [Finite A] {W U : T.Opens} (h : W ≤ U) :
    PreservesFiniteLimits (furtherRestriction T b A h) :=
  (furtherRestriction_exact T b A h).2.1

/-- Inherited right exactness of successive restriction. Source: Stacks 03EH and 04IX
(blueprint: lem-pur-open-cover-cohomology-detection). -/
instance furtherColimits (T : Scheme.{u}) (b : Bool) (A : Type (u + 1))
    [CommRing A] [Finite A] {W U : T.Opens} (h : W ≤ U) :
    PreservesFiniteColimits (furtherRestriction T b A h) :=
  (furtherRestriction_exact T b A h).2.2


/-- The successive module restriction isomorphism is sectionwise the identity.
Source: Stacks 03EH and 04IX (blueprint: lem-pur-open-cover-cohomology-detection).
Proof: def-pur-localized-ringed-site gives the existing overFunctorMap. Its components
are the identity maps on the original section modules, so scalar transport agrees
with the nested coefficient comparison in site_and_coefficients. -/
theorem restriction_nested (T : Scheme.{u}) (b : Bool) (A : Type (u + 1))
    [CommRing A] [Finite A] {W U : T.Opens} (h : W ≤ U)
    (F : Modules T b A) (V : Over (openObject T b W)) :
    HEq (((SheafOfModules.overFunctorMap.{u + 1} (rings T b A)
      (nestedArrow T b h)).hom.app F).val.app (op V)) (𝟙 (F.val.obj (op V.left))) := by
  exact HEq.rfl

/-- Zero module sheaves are detected on any set-indexed open cover, including the empty one.
Source: Stacks 00VM, 00VR and 04IX (blueprint: lem-pur-open-cover-cohomology-detection).
Proof: for every object V, covering supplies V times_T U_i as a covering.
The restricted module being zero makes F(V times_T U_i) zero for every i.
The sheaf equalizer axiom in def-weil-pbc-sites-and-cohomology makes the map from
F(V) to the product of these zero modules injective. Hence F(V)=0 for every V,
and F is a zero object. Conversely sectionwise restriction preserves zero modules.
No stalks, points, finiteness of the cover or quasi-compactness of T are required. -/
theorem module_detection (T : Scheme.{u}) (b : Bool) (A : Type (u + 1))
    [CommRing A] [Finite A] {I : Type v} (U : I → T.Opens)
    (hU : ∀ x : T, ∃ i : I, x ∈ U i) (F : Modules T b A) :
    IsZero F ↔ ∀ i : I, IsZero ((restriction T b A (U i)).obj F) := by
  cases b
  · exact ((Scheme.zariskiCoverEtaleModuleDetection T U hU).2.2.1
      (coefficients T false A) F).2.2.1
  · exact ((Scheme.zariskiCoverProetaleModuleDetection T U hU).2.2.1
      (coefficients T true A) F).2.2.1

section Derived
variable (T : Scheme.{u}) (b : Bool) (A : Type (u + 1)) [CommRing A] [hFinite : Finite A]
  [HasDerivedCategory.{w} (Modules T b A)]
  [∀ U : T.Opens, HasDerivedCategory.{w} (LocalModules T b A U)]

include hFinite

/-- Termwise restriction on the ordinary unbounded derived categories.
Source: Stacks 015F (blueprint: lem-pur-open-cover-cohomology-detection). -/
abbrev derivedRestriction (U : T.Opens) :
    DerivedCategory (Modules T b A) ⥤ DerivedCategory (LocalModules T b A U) :=
  (restriction T b A U).mapDerivedCategory

/-- The kernel/image/quotient comparison descended through localization.
Source: Stacks 010N and 015F (blueprint: lem-pur-open-cover-cohomology-detection).
This is the existing canonical comparison, not an arbitrarily chosen isomorphism. -/
def chi (U : T.Opens) (a : ℤ) :
    DerivedCategory.homologyFunctor (Modules T b A) a ⋙ restriction T b A U ≅
      derivedRestriction T b A U ⋙ DerivedCategory.homologyFunctor (LocalModules T b A U) a :=
  (restriction T b A U).mapDerivedCategoryHomologyFunctorIso a

/-- The derived relocalization isomorphism induced by sectionwise identity.
Source: Stacks 03EH and 015F (blueprint: lem-pur-open-cover-cohomology-detection). -/
def derivedNestedIso {W U : T.Opens} (h : W ≤ U) :
    derivedRestriction T b A U ⋙ (furtherRestriction T b A h).mapDerivedCategory ≅
      derivedRestriction T b A W :=
  (Functor.mapDerivedCategoryCompIso (restriction T b A U)
    (furtherRestriction T b A h)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u + 1} (rings T b A) (nestedArrow T b h))

/-- All-derived-morphism naturality and normalization on every complex representative.
Source: Stacks 010N and 015F (blueprint: lem-pur-open-cover-cohomology-detection).
Proof: apply lem-weil-pbc-exact-functor-complex-cohomology to the exact sectionwise
restriction. Its inverse comparison is induced by the kernel, image and quotient maps.
lem-sf-exact-functor-derived-triangulated gives the termwise derived functor.
The homology functors factor through Q. Naturality for chain maps also gives the
square for the inverse of every quasi-isomorphism. These maps generate the localized
category, so the comparison is natural for all derived morphisms. The four factors
in the second clause are precisely that descent, fixing its normalization on Q(C).
There is no resolution or boundedness hypothesis. -/
theorem cohomology_comparison (U : T.Opens) (a : ℤ) :
    (∀ (K L : DerivedCategory (Modules T b A)) (f : K ⟶ L),
      (restriction T b A U).map ((DerivedCategory.homologyFunctor (Modules T b A) a).map f) ≫
        (chi T b A U a).hom.app L =
      (chi T b A U a).hom.app K ≫
        (DerivedCategory.homologyFunctor (LocalModules T b A U) a).map
          ((derivedRestriction T b A U).map f)) ∧
    (∀ C : CochainComplex (Modules T b A) ℤ,
      (chi T b A U a).hom.app (DerivedCategory.Q.obj C) =
        (restriction T b A U).map
          ((DerivedCategory.homologyFunctorFactors (Modules T b A) a).hom.app C) ≫
        ((restriction T b A U).mapHomologicalComplexHomologyIso (.up ℤ) a).inv.app C ≫
        (DerivedCategory.homologyFunctorFactors (LocalModules T b A U) a).inv.app
          (((restriction T b A U).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (DerivedCategory.homologyFunctor (LocalModules T b A U) a).map
          ((restriction T b A U).mapDerivedCategoryFactors.inv.app C)) := by
  cases hFinite
  exact ⟨fun _ _ f ↦ (chi T b A U a).hom.naturality f,
    (restriction T b A U).mapDerivedCategoryHomologyFunctorIso_hom_app_Q a⟩

/-- The cohomology comparisons agree with their nested-open composites.
Source: Stacks 010N and 03EH (blueprint: lem-pur-open-cover-cohomology-detection).
Proof: on a complex, both sides use the same map of cycles into the degree-a term
and the same quotient by boundaries. Uniqueness of the induced kernel and quotient
maps in lem-weil-pbc-exact-functor-complex-cohomology makes the two maps equal.
The coefficient comparisons agree by sheafification uniqueness. The displayed
sectionwise relocalization isomorphism and its termwise derived image supply the
transports on both sides. Descend from complex representatives through Q as in
cohomology_comparison, giving equality on every derived object. -/
theorem cohomology_nested {W U : T.Opens} (h : W ≤ U) (a : ℤ)
    (K : DerivedCategory (Modules T b A)) :
    (furtherRestriction T b A h).map ((chi T b A U a).hom.app K) ≫
      ((furtherRestriction T b A h).mapDerivedCategoryHomologyFunctorIso a).hom.app
        ((derivedRestriction T b A U).obj K) ≫
      (DerivedCategory.homologyFunctor (LocalModules T b A W) a).map
        ((derivedNestedIso T b A h).hom.app K) =
    (SheafOfModules.overFunctorMap.{u + 1} (rings T b A)
      (nestedArrow T b h)).hom.app
        ((DerivedCategory.homologyFunctor (Modules T b A) a).obj K) ≫
      (chi T b A W a).hom.app K := by
  exact (Functor.exactDerivedCohomologyCoherence (restriction T b A U)
    (furtherRestriction T b A h) a).2 (restriction T b A W)
      (SheafOfModules.overFunctorMap.{u + 1} (rings T b A) (nestedArrow T b h)) K

/-- Cohomology vanishing is detected on any set-indexed Zariski open cover, in either site.
Source: Stacks 00VM, 00VR, 04IX, 010N and 015F
(blueprint: lem-pur-open-cover-cohomology-detection).
Proof: first detect zero module sheaves by the sheaf equalizer axiom on the pulled-back
cover, as in module_detection. Apply it to H^a(K). The canonical chi isomorphisms
identify each restricted cohomology sheaf with H^a(D(r_U) K), proving both directions.
For the empty scheme and empty index set, the equalizer of the empty covering forces
every section module to be zero, so the same equivalence applies without exception. -/
theorem cohomology_detection {I : Type v} (U : I → T.Opens)
    (hU : ∀ x : T, ∃ i : I, x ∈ U i) (a : ℤ)
    (K : DerivedCategory (Modules T b A)) :
    IsZero ((DerivedCategory.homologyFunctor (Modules T b A) a).obj K) ↔
      ∀ i : I, IsZero ((DerivedCategory.homologyFunctor (LocalModules T b A (U i)) a).obj
        ((derivedRestriction T b A (U i)).obj K)) := by
  rw [module_detection T b A U hU]
  exact forall_congr' fun i ↦ ((chi T b A (U i) a).app K).isZero_iff

end Derived

/-- On the empty scheme every module sheaf is zero in both sites.
Source: Stacks 00VM, 00VR, empty-cover case
(blueprint: lem-pur-open-cover-cohomology-detection).
Proof: a scheme mapping to the empty scheme is empty. The empty family covers each
such object in the etale topology, hence in the pro-etale topology by
lem-pur-etale-proetale-cover. The sheaf axiom for the empty cover says each section
module is terminal and therefore zero. Thus the module sheaf is a zero object. -/
theorem empty_modules (T : Scheme.{u}) [IsEmpty T] (b : Bool) (A : Type (u + 1))
    [CommRing A] [Finite A] (F : Modules T b A) : IsZero F := by
  exact (module_detection T b A (fun i : PEmpty.{1} ↦ i.elim)
    (fun x ↦ isEmptyElim x) F).2 (fun i ↦ i.elim)

end AlgebraicGeometry.OpenCoverCohomology
