/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation

/-!
# Canonical coherent Kummer-nerve totalization

Source: direct-image proof paragraph (3), augmented Cech descent, and Stacks Tag 03OU
(blueprint: def-sfb-kummer-cech-descent).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped Simplicial
attribute [local irreducible] AlgebraicGeometry.ProEtale.CondensedRing.upperStar
attribute [local irreducible] AlgebraicGeometry.ProEtale.CondensedRing.lowerStar

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual coefficient module category on a scheme.
Source: direct-image proof paragraph (3), Cartesian coefficients
(blueprint: def-sfb-kummer-cech-descent). -/
abbrev KummerModules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- The unit-induced restriction between the sections over two schemes over W.
Both composition identifications are the published Cartesian coefficient identifications.
Source: direct-image proof paragraph (3), the actual covering nerve
(blueprint: def-sfb-kummer-cech-descent). -/
def overSectionsMap {W : Scheme.{u}} {V T : Over W} (f : V ⟶ T) :
    upperStar Λ T.hom ⋙ lowerStar Λ T.hom ⟶
      upperStar Λ V.hom ⋙ lowerStar Λ V.hom :=
  Functor.whiskerLeft (upperStar Λ T.hom)
    (Functor.whiskerRight (upperStarLowerStarAdjunction Λ f.left).unit
      (lowerStar Λ T.hom)) ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight
      ((upperStarComp Λ f.left T.hom).symm ≪≫ upperStarCongr Λ f.w)
      (lowerStar Λ f.left ⋙ lowerStar Λ T.hom)).hom ≫
    (Functor.isoWhiskerLeft (upperStar Λ V.hom)
      (lowerStarComp Λ f.left T.hom ≪≫ lowerStarCongr Λ f.w)).hom

-- The unit restriction before applying the structure-map pushforward.
private def sectionsRestriction {W X Y : Scheme.{u}} (f : X ⟶ Y)
    (kX : X ⟶ W) (kY : Y ⟶ W) (hf : f ≫ kY = kX) (M : KummerModules Λ W) :
    (upperStar Λ kY).obj M ⟶ (lowerStar Λ f).obj ((upperStar Λ kX).obj M) :=
  (upperStarLowerStarAdjunction Λ f).unit.app ((upperStar Λ kY).obj M) ≫
    (lowerStar Λ f).map ((upperStarComp Λ f kY).inv.app M ≫
      (upperStarCongr Λ hf).hom.app M)

private theorem sectionsRestriction_unit {W X Y : Scheme.{u}} (f : X ⟶ Y)
    (kX : X ⟶ W) (kY : Y ⟶ W) (hf : f ≫ kY = kX) (M : KummerModules Λ W) :
    (upperStarLowerStarAdjunction Λ kY).unit.app M ≫
        (lowerStar Λ kY).map (sectionsRestriction Λ f kX kY hf M) =
      (upperStarLowerStarAdjunction Λ kX).unit.app M ≫
        (lowerStarCongr Λ hf.symm).hom.app _ ≫
          (lowerStarComp Λ f kY).inv.app ((upperStar Λ kX).obj M) := by
  subst hf
  have hc : conjugateEquiv (upperStarLowerStarAdjunction Λ (f ≫ kY))
      ((upperStarLowerStarAdjunction Λ kY).comp (upperStarLowerStarAdjunction Λ f))
      (upperStarComp Λ f kY).inv = (lowerStarComp Λ f kY).inv := by
    rw [← conjugateIsoEquiv_apply_inv, conjugateIsoEquiv_upperStarComp]
  have h := unit_conjugateEquiv (upperStarLowerStarAdjunction Λ (f ≫ kY))
    ((upperStarLowerStarAdjunction Λ kY).comp (upperStarLowerStarAdjunction Λ f))
    (upperStarComp Λ f kY).inv M
  rw [hc, Adjunction.comp_unit_app] at h
  dsimp only [Functor.comp_obj, Functor.id_obj] at h ⊢
  simpa only [sectionsRestriction, upperStarCongr, lowerStarCongr, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.id_comp,
    Functor.map_comp, Functor.comp_map, Functor.comp_obj, Functor.id_obj,
    Category.assoc] using h.symm

private theorem sectionsRestriction_comp {W X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (kX : X ⟶ W) (kY : Y ⟶ W) (kZ : Z ⟶ W)
    (hf : f ≫ kY = kX) (hg : g ≫ kZ = kY) (hfg : (f ≫ g) ≫ kZ = kX)
    (M : KummerModules Λ W) :
    sectionsRestriction Λ (f ≫ g) kX kZ hfg M =
      sectionsRestriction Λ g kY kZ hg M ≫
        (lowerStar Λ g).map (sectionsRestriction Λ f kX kY hf M) ≫
          (lowerStarComp Λ f g).hom.app ((upperStar Λ kX).obj M) := by
  subst hf hg
  apply ((upperStarLowerStarAdjunction Λ kZ).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [sectionsRestriction_unit Λ (f ≫ g) _ kZ hfg]
  rw [Functor.map_comp,
    reassoc_of% (sectionsRestriction_unit Λ g _ kZ rfl M)]
  simp only [lowerStarCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  rw [Functor.map_comp]
  -- Move the restriction through the compositor before transposing it.
  have hn := (lowerStarComp Λ g kZ).inv.naturality
    (sectionsRestriction Λ f (f ≫ g ≫ kZ) (g ≫ kZ) rfl M)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [reassoc_of% (sectionsRestriction_unit Λ f _ (g ≫ kZ) rfl M)]
  simp only [lowerStarCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  apply congrArg (fun k ↦
    (upperStarLowerStarAdjunction Λ (f ≫ g ≫ kZ)).unit.app M ≫ k)
  have h := congrArg (fun e ↦ e.hom.app ((upperStar Λ (f ≫ g ≫ kZ)).obj M))
    (lowerStarComp_assoc Λ f g kZ)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.comp_obj, lowerStarCongr, eqToIso_refl,
    Iso.refl_hom, Category.id_comp, Category.comp_id] at h
  rw [← cancel_mono ((lowerStarComp Λ (f ≫ g) kZ).hom.app _ ≫
    (lowerStarCongr Λ hfg).hom.app _)]
  simp only [Category.assoc, lowerStarCongr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  rw [← h]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rfl

private theorem sectionsRestriction_id {W X : Scheme.{u}} (kX : X ⟶ W)
    (h : 𝟙 X ≫ kX = kX) (M : KummerModules Λ W) :
    sectionsRestriction Λ (𝟙 X) kX kX h M =
      (lowerStarId Λ X).inv.app ((upperStar Λ kX).obj M) := by
  apply ((upperStarLowerStarAdjunction Λ kX).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [sectionsRestriction_unit Λ (𝟙 X) kX kX h]
  congr 1
  have h' := congrArg (fun e ↦ e.hom.app ((upperStar Λ kX).obj M))
    (lowerStarComp_id_left Λ kX)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h'
  rw [← cancel_mono ((lowerStarComp Λ (𝟙 X) kX).hom.app _)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [h']
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    lowerStarCongr_symm]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private def sectionsMap {W X Y : Scheme.{u}} (f : X ⟶ Y)
    (kX : X ⟶ W) (kY : Y ⟶ W) (hf : f ≫ kY = kX) (M : KummerModules Λ W) :
    (lowerStar Λ kY).obj ((upperStar Λ kY).obj M) ⟶
      (lowerStar Λ kX).obj ((upperStar Λ kX).obj M) :=
  (lowerStar Λ kY).map (sectionsRestriction Λ f kX kY hf M) ≫
    (lowerStarComp Λ f kY).hom.app ((upperStar Λ kX).obj M) ≫
      (lowerStarCongr Λ hf).hom.app ((upperStar Λ kX).obj M)

private theorem sectionsMap_id {W X : Scheme.{u}} (kX : X ⟶ W)
    (h : 𝟙 X ≫ kX = kX) (M : KummerModules Λ W) :
    sectionsMap Λ (𝟙 X) kX kX h M = 𝟙 _ := by
  rw [sectionsMap, sectionsRestriction_id]
  rw [lowerStarComp_id_left]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Iso.symm_hom,
    Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.id_obj]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (lowerStarCongr Λ h).inv_hom_id_app _

private theorem sectionsMap_comp {W X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (kX : X ⟶ W) (kY : Y ⟶ W) (kZ : Z ⟶ W)
    (hf : f ≫ kY = kX) (hg : g ≫ kZ = kY) (hfg : (f ≫ g) ≫ kZ = kX)
    (M : KummerModules Λ W) :
    sectionsMap Λ (f ≫ g) kX kZ hfg M =
      sectionsMap Λ g kY kZ hg M ≫ sectionsMap Λ f kX kY hf M := by
  subst hf hg
  simp only [sectionsMap, sectionsRestriction_comp Λ f g _ _ _ rfl rfl hfg M,
    lowerStarCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    Functor.map_comp, Category.assoc]
  have h := congrArg (fun e ↦ e.hom.app ((upperStar Λ (f ≫ g ≫ kZ)).obj M))
    (lowerStarComp_assoc Λ f g kZ)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.comp_obj, Category.id_comp, lowerStarCongr,
    eqToIso_refl, Iso.refl_hom, Category.comp_id] at h
  rw [← h]
  rw [← (lowerStarComp Λ g kZ).hom.naturality_assoc]
  rfl

private theorem overSectionsMap_app {W : Scheme.{u}} {V T : Over W} (f : V ⟶ T)
    (M : KummerModules Λ W) :
    (overSectionsMap Λ f).app M = sectionsMap Λ f.left V.hom T.hom f.w M := by
  simp only [overSectionsMap, sectionsMap, sectionsRestriction, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.trans_hom,
    Iso.symm_hom, Functor.map_comp, Functor.comp_map, Category.assoc,
    Category.id_comp]

/-- Restriction of sections is contravariantly functorial on schemes over W.
Source: direct-image proof paragraph (3), augmented nerve
(blueprint: def-sfb-kummer-cech-descent).

Proof: for the identity use the identity upper/lower-star comparisons and the
identity adjunction. For a composite, the composite adjunction unit is the first
unit followed by the push-pull of the second. Apply the published composition
coherence of upper and lower stars. The two composites are equal by the unit
composition equation, with the same coefficient identifications throughout. -/
theorem overSectionsMap_laws (W : Scheme.{u}) :
    (∀ V : Over W, overSectionsMap Λ (𝟙 V) = 𝟙 _) ∧
    (∀ {V T U : Over W} (f : V ⟶ T) (g : T ⟶ U),
      overSectionsMap Λ (f ≫ g) = overSectionsMap Λ g ≫ overSectionsMap Λ f) := by
  constructor
  · intro V
    apply NatTrans.ext
    funext M
    rw [overSectionsMap_app]
    exact sectionsMap_id Λ V.hom (Over.w (𝟙 V)) M
  · intro V T U f g
    apply NatTrans.ext
    funext M
    simp only [NatTrans.comp_app, overSectionsMap_app]
    exact sectionsMap_comp Λ f.left g.left V.hom T.hom U.hom f.w g.w (f ≫ g).w M

/-- Sections over schemes over W, using the actual inverse/direct image adjunctions.
Source: direct-image proof paragraph (3), augmented nerve
(blueprint: def-sfb-kummer-cech-descent). -/
def overSections (W : Scheme.{u}) :
    (Over W)ᵒᵖ ⥤ (KummerModules Λ W ⥤ KummerModules Λ W) where
  obj V := upperStar Λ V.unop.hom ⋙ lowerStar Λ V.unop.hom
  map f := overSectionsMap Λ f.unop
  map_id V := (overSectionsMap_laws Λ W).1 V.unop
  map_comp f g := (overSectionsMap_laws Λ W).2 g.unop f.unop

/-- The actual augmented Cech nerve, regarded as schemes over the open W.
Source: direct-image proof paragraph (3), punctured Kummer cover
(blueprint: def-sfb-kummer-cech-descent). -/
def cechOver {T W : Scheme.{u}} (v : T ⟶ W) : SimplicialObject (Over W) where
  obj n := Over.mk ((Arrow.mk v).augmentedCechNerve.hom.app n)
  map f := Over.homMk ((Arrow.mk v).cechNerve.map f)
    ((Arrow.mk v).augmentedCechNerve.hom.naturality f)
  map_id n := by ext; exact (Arrow.mk v).cechNerve.map_id n
  map_comp f g := by ext; exact (Arrow.mk v).cechNerve.map_comp f g

/-- The actual augmentation projection in nerve degree n.
Source: direct-image proof paragraph (3), the actual punctured covering nerve
(blueprint: def-sfb-kummer-cech-descent). -/
def cechProjection {T W : Scheme.{u}} (v : T ⟶ W) (n : SimplexCategory) :
    (Arrow.mk v).cechNerve.obj (op n) ⟶ W :=
  WidePullback.base (fun _ : Fin (n.len + 1) ↦ v)


/-- One term of the actual Cech image, written without nested functor flips.
Source: direct-image proof paragraph (3), compatible resolutions
(blueprint: def-sfb-kummer-cech-descent). -/
def cechImageTerm {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W)
    (L : KummerModules Λ W) (n : SimplexCategory) : KummerModules Λ S :=
  (upperStar Λ s).obj ((lowerStar Λ a).obj
    ((lowerStar Λ ((cechOver v).obj (op n)).hom).obj
      ((upperStar Λ ((cechOver v).obj (op n)).hom).obj L)))

/-- The coherent cosimplicial module functor is formed before localization.
Source: direct-image proof paragraph (3), normalized Cech descent
(blueprint: def-sfb-kummer-cech-descent). -/
def cechImage {T W Y S : Scheme.{u}} (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W) :
    KummerModules Λ W ⥤ (SimplexCategory ⥤ KummerModules Λ S) :=
  (((cechOver v).rightOp ⋙ overSections Λ W) ⋙
    (Functor.whiskeringRight _ _ _).obj (lowerStar Λ a ⋙ upperStar Λ s)).flip

private theorem additive_flip
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive D] [Preadditive E] (F : C ⥤ D ⥤ E)
    [∀ c, (F.obj c).Additive] : F.flip.Additive where
  map_add := by
    intro X Y f g
    apply NatTrans.ext
    funext c
    exact (F.obj c).map_add

/-- The Cech image functor is additive.
Source: direct-image proof paragraph (3), compatible first-quadrant resolutions
(blueprint: def-sfb-kummer-cech-descent).

Proof: evaluate at every simplex. Its functor is a composite of the additive
Cartesian pullbacks and direct images. Addition of natural transformations is
componentwise, so these componentwise equalities prove additivity. -/
theorem cechImage_additive {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W) :
    (cechImage Λ a s v).Additive := by
  let F := (((cechOver v).rightOp ⋙ overSections Λ W) ⋙
    (Functor.whiskeringRight _ _ _).obj (lowerStar Λ a ⋙ upperStar Λ s))
  have h (n : SimplexCategory) : (F.obj n).Additive := by
    change ((upperStar Λ ((cechOver v).obj (op n)).hom ⋙
      lowerStar Λ ((cechOver v).obj (op n)).hom) ⋙
        (lowerStar Λ a ⋙ upperStar Λ s)).Additive
    infer_instance
  exact additive_flip F
attribute [instance] cechImage_additive

/-- Resolve the actual coherent Cech diagram, with its type fixed once.
Source: direct-image proof (3), compatible resolutions
(blueprint: def-sfb-kummer-cech-descent). -/
def kummerCechResolution {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W)
    (I : CochainComplex (KummerModules Λ W) ℕ) :
    CochainComplex (SimplexCategory ⥤ KummerModules Λ S) ℕ :=
  ((cechImage Λ a s v).mapHomologicalComplex (.up ℕ)).obj I

private theorem diagramGrothendieck
    {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] :
    IsGrothendieckAbelian.{u + 1} (SimplexCategory ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hSep : ObjectProperty.IsSeparating
      (.ofObj fun n : SimplexCategory ↦ (evaluationLeftAdjoint A n).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext n
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A n
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ n) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (SimplexCategory ⥤ A) := ⟨_, hSep.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{u + 1, u + 1} (SimplexCategory ⥤ A) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{u + 1, u + 1} (SimplexCategory ⥤ A) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exact {}

set_option linter.unusedSectionVars false in
/-- Cosimplicial module diagrams have their canonical Grothendieck structure.
Source: modules on sites and small functor categories, Tag 03DA
(blueprint: def-sfb-kummer-cech-descent).

Proof: kernels, cokernels and filtered colimits are computed componentwise.
Filtered colimits are exact. A generator is the sum over simplices of the left
Kan extensions of a generator in the module category along each object inclusion.
Smallness of the simplex category and existence of these sums give a generator. -/
theorem cosimplicialGrothendieck (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} ((SimplexCategory ⥤ KummerModules Λ S)) := by
  exact diagramGrothendieck (A := KummerModules Λ S)
attribute [instance] cosimplicialGrothendieck

/-- Derived totalization means the ordinary right-derived limit of the coherent
cosimplicial module diagram. On bounded-below objects it is the compatible
first-quadrant total, with the usual alternating-face sign convention.
Source: direct-image proof paragraph (3), coherent derived totalization
(blueprint: def-sfb-kummer-cech-descent). -/
def cechTotal (S : Scheme.{u}) :
    DerivedCategory (SimplexCategory ⥤ KummerModules Λ S) ⥤
      DerivedCategory (KummerModules Λ S) := by
  let L := (lim : (SimplexCategory ⥤ KummerModules Λ S) ⥤ KummerModules Λ S)
  haveI : L.Additive := Functor.additive_of_preserves_binary_products L
  exact L.rightDerivedFunctor



/-- The actual adjunction unit, with the section functor kept opaque to elaboration.
Source: direct-image proof paragraph (3), augmented covering nerve
(blueprint: def-sfb-kummer-cech-descent). -/
def overSectionUnit {W : Scheme.{u}} (V : Over W) :
    𝟭 (KummerModules Λ W) ⟶ (overSections Λ W).obj (op V) :=
  (upperStarLowerStarAdjunction Λ V.hom).unit


/-- Restrict sections by the actual unit in every nerve term.
Source: direct-image proof (3), augmented descent
(blueprint: def-sfb-kummer-cech-descent). -/
def cechAugmentationComponent {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W)
    (L : KummerModules Λ W) (n : SimplexCategory) :
    (upperStar Λ s).obj ((lowerStar Λ a).obj L) ⟶ cechImageTerm Λ a s v L n :=
  (upperStar Λ s).map ((lowerStar Λ a).map
    ((upperStarLowerStarAdjunction Λ ((cechOver v).obj (op n)).hom).unit.app L))

end AlgebraicGeometry.ProEtale.CondensedRing
