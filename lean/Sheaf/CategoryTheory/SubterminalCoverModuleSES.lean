module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Sheaf.CategoryTheory.SubterminalModuleLocalCalculus
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # The module short exact sequence of a binary subterminal cover

Source: Stacks Project, Cohomology, Tag 08BU, lemma-exact-sequence-lower-shriek;
the subterminal-site formulation is the local split calculation in the blueprint
(blueprint: lem-sp-subterminal-cover-module-ses).
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.SubterminalCover

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- Forget only commutativity of the given coefficient sheaf. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
abbrev ring : Sheaf J RingCat.{max c v r} :=
  (sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R

/-- The recorded category of modules over the given ring sheaf. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
abbrev modules := ringedSiteModules.{max c v r} (ring.{c, v, r} R)

/-- The composite `j_Z! j_Z*`, using the actual sheafified direct-sum extension.
Source: Stacks 08BU (blueprint: lem-sp-subterminal-cover-module-ses). -/
abbrev supported (Z : C) : modules.{c, v, r} R ⥤ modules.{c, v, r} R :=
  localizedSystemRestriction.{c, v, r} R Z ⋙ localizedSystemExtension.{c, v, r} R Z

/-- The canonical adjunction counit. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
def counit (Z : C) (F : modules.{c, v, r} R) : (supported.{c, v, r} R Z).obj F ⟶ F :=
  (localizedSystemAdjunction.{c, v, r} R Z).counit.app F

/-- The nested-open map is the transpose of the restricted unit, using the sectionwise
iterated-restriction comparison. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
def nested [HasPullbacks C] {W Z : C} (f : W ⟶ Z) (F : modules.{c, v, r} R) :
    (supported.{c, v, r} R W).obj F ⟶ (supported.{c, v, r} R Z).obj F :=
  ((localizedSystemAdjunction.{c, v, r} R W).homEquiv _ _).symm
    ((overFunctorMap (ring.{c, v, r} R) f).inv.app F ≫
      (overMap (ring.{c, v, r} R) f).map
        ((localizedSystemAdjunction.{c, v, r} R Z).unit.app
          ((localizedSystemRestriction.{c, v, r} R Z).obj F)) ≫
      (overFunctorMap (ring.{c, v, r} R) f).hom.app ((supported.{c, v, r} R Z).obj F))

/-- The canonical local component formulas, expressed without choosing a biproduct
comparison. Here `k` is extension from W inside Z: its adjunction characterizes it up
to unique counit-compatible isomorphism. The isomorphisms identify restriction of the
self-extension with identity, and restriction of both other extensions with `k(F|W)`.
The last four equations specify every component of the two local matrices.
Source: Stacks 08BU (blueprint: lem-sp-subterminal-cover-module-ses). -/
def localDescription [HasPullbacks C] (W Z T : C) (p : W ⟶ Z) (q : W ⟶ T) : Prop :=
  ∃ (k : ringedSiteModules.{max c v r} ((ring.{c, v, r} R).over W) ⥤
      ringedSiteModules.{max c v r} ((ring.{c, v, r} R).over Z))
    (adj : k ⊣ overMap (ring.{c, v, r} R) p)
    (eSelf : supported.{c, v, r} R Z ⋙ localizedSystemRestriction.{c, v, r} R Z ≅
      localizedSystemRestriction.{c, v, r} R Z)
    (eOther : supported.{c, v, r} R T ⋙ localizedSystemRestriction.{c, v, r} R Z ≅
      localizedSystemRestriction.{c, v, r} R W ⋙ k)
    (eOverlap : supported.{c, v, r} R W ⋙ localizedSystemRestriction.{c, v, r} R Z ≅
      localizedSystemRestriction.{c, v, r} R W ⋙ k),
    ∀ F : modules.{c, v, r} R,
      (localizedSystemRestriction.{c, v, r} R Z).map (counit.{c, v, r} R Z F) = eSelf.hom.app F ∧
      (localizedSystemRestriction.{c, v, r} R Z).map (counit.{c, v, r} R T F) =
        eOther.hom.app F ≫ k.map ((overFunctorMap (ring.{c, v, r} R) p).inv.app F) ≫
          adj.counit.app ((localizedSystemRestriction.{c, v, r} R Z).obj F) ∧
      (localizedSystemRestriction.{c, v, r} R Z).map (nested.{c, v, r} R p F) ≫ eSelf.hom.app F =
        eOverlap.hom.app F ≫ k.map ((overFunctorMap (ring.{c, v, r} R) p).inv.app F) ≫
          adj.counit.app ((localizedSystemRestriction.{c, v, r} R Z).obj F) ∧
      (localizedSystemRestriction.{c, v, r} R Z).map (nested.{c, v, r} R q F) ≫ eOther.hom.app F =
        eOverlap.hom.app F

variable [HasFiniteLimits C] (U V : C)

/-- Intersection of the two subterminals. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
abbrev overlap := U ⨯ V

/-- The first arrow has the sign convention `(i_U,-i_V)`. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
def first (F : modules.{c, v, r} R) : (supported.{c, v, r} R (overlap U V)).obj F ⟶
    (supported.{c, v, r} R U).obj F ⊞ (supported.{c, v, r} R V).obj F :=
  biprod.lift (nested.{c, v, r} R (prod.fst : U ⨯ V ⟶ U) F)
    (-nested.{c, v, r} R (prod.snd : U ⨯ V ⟶ V) F)

/-- The second arrow is the pair of canonical counits. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
def second (F : modules.{c, v, r} R) :
    (supported.{c, v, r} R U).obj F ⊞ (supported.{c, v, r} R V).obj F ⟶ F :=
  biprod.desc (counit.{c, v, r} R U F) (counit.{c, v, r} R V F)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem nested_naturality {W Z : C} (f : W ⟶ Z)
    (F G : modules.{c, v, r} R) (a : F ⟶ G) :
    (supported.{c, v, r} R W).map a ≫ nested.{c, v, r} R f G =
      nested.{c, v, r} R f F ≫ (supported.{c, v, r} R Z).map a := by
  let α := overFunctorMap.{max c v r} (ring.{c, v, r} R) f
  let T := overMap.{max c v r} (ring.{c, v, r} R) f
  let Q := localizedSystemRestriction.{c, v, r} R Z
  let adjW := localizedSystemAdjunction.{c, v, r} R W
  let adjZ := localizedSystemAdjunction.{c, v, r} R Z
  let t : localizedSystemRestriction.{c, v, r} R W ⟶
      supported.{c, v, r} R Z ⋙ localizedSystemRestriction.{c, v, r} R W :=
    α.inv ≫ Functor.whiskerLeft Q (Functor.whiskerRight adjZ.unit T) ≫
      Functor.whiskerLeft (supported.{c, v, r} R Z) α.hom
  change (localizedSystemExtension.{c, v, r} R W).map
      ((localizedSystemRestriction.{c, v, r} R W).map a) ≫ (adjW.homEquiv _ _).symm
        (t.app G) = (adjW.homEquiv _ _).symm (t.app F) ≫ (supported.{c, v, r} R Z).map a
  rw [← adjW.homEquiv_naturality_left_symm,
    ← adjW.homEquiv_naturality_right_symm]
  exact congrArg (adjW.homEquiv _ _).symm (t.naturality a)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem arrows_naturality (F G : modules.{c, v, r} R) (a : F ⟶ G) :
    (supported.{c, v, r} R (overlap U V)).map a ≫ first.{c, v, r} R U V G =
      first.{c, v, r} R U V F ≫
        biprod.map ((supported.{c, v, r} R U).map a) ((supported.{c, v, r} R V).map a) ∧
    biprod.map ((supported.{c, v, r} R U).map a) ((supported.{c, v, r} R V).map a) ≫
        second.{c, v, r} R U V G =
      second.{c, v, r} R U V F ≫ a := by
  constructor
  · apply biprod.hom_ext
    · simpa only [first, Category.assoc, biprod.lift_fst, biprod.map_fst,
        biprod.lift_fst_assoc] using
          nested_naturality.{c, v, r} R (prod.fst : U ⨯ V ⟶ U) F G a
    · simpa only [first, Category.assoc, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc, Preadditive.comp_neg, Preadditive.neg_comp] using
          congrArg Neg.neg (nested_naturality.{c, v, r} R
            (prod.snd : U ⨯ V ⟶ V) F G a)
  · apply biprod.hom_ext'
    · simpa only [second, counit, Category.assoc, biprod.inl_map_assoc,
        biprod.inl_desc, biprod.inl_desc_assoc, Functor.id_map] using
          (localizedSystemAdjunction.{c, v, r} R U).counit.naturality a
    · simpa only [second, counit, Category.assoc, biprod.inr_map_assoc,
        biprod.inr_desc, biprod.inr_desc_assoc, Functor.id_map] using
          (localizedSystemAdjunction.{c, v, r} R V).counit.naturality a

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem matrix_left {A : Type*} [Category A] [Abelian A]
    {L E : A} (i : L ⟶ E) :
    (ShortComplex.mk (biprod.lift i (-𝟙 L)) (biprod.desc (𝟙 E) i)
      (by simp)).ShortExact := by
  apply ShortComplex.Splitting.shortExact
  refine { r := -biprod.snd, s := biprod.inl, f_r := ?_, s_g := ?_, id := ?_ }
  · simp
  · simp
  · ext <;> simp

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem matrix_right {A : Type*} [Category A] [Abelian A]
    {L E : A} (i : L ⟶ E) :
    (ShortComplex.mk (biprod.lift (𝟙 L) (-i)) (biprod.desc i (𝟙 E))
      (by simp)).ShortExact := by
  apply ShortComplex.Splitting.shortExact
  refine { r := biprod.fst, s := biprod.inr, f_r := ?_, s_g := ?_, id := ?_ }
  · simp
  · simp
  · ext <;> simp

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem joint_shortExact {A B D : Type*}
    [Category A] [Abelian A] [Category B] [Abelian B] [Category D] [Abelian D]
    (P : A ⥤ B) (Q : A ⥤ D) [P.Additive] [Q.Additive]
    (hz : ∀ {X Y : A} (f : X ⟶ Y), f = 0 ↔ P.map f = 0 ∧ Q.map f = 0)
    (he : ∀ S : ShortComplex A, S.Exact ↔ (S.map P).Exact ∧ (S.map Q).Exact)
    (S : ShortComplex A) (hp : (S.map P).ShortExact) (hq : (S.map Q).ShortExact) :
    S.ShortExact := by
  have : Mono S.f := Preadditive.mono_of_cancel_zero _ fun g hg ↦ by
    apply (hz g).mpr
    constructor
    · let : Mono (P.map S.f) := hp.mono_f
      apply zero_of_comp_mono (P.map S.f)
      rw [← P.map_comp, hg, P.map_zero]
    · let : Mono (Q.map S.f) := hq.mono_f
      apply zero_of_comp_mono (Q.map S.f)
      rw [← Q.map_comp, hg, Q.map_zero]
  have : Epi S.g := Preadditive.epi_of_cancel_zero _ fun g hg ↦ by
    apply (hz g).mpr
    constructor
    · let : Epi (P.map S.g) := hp.epi_g
      apply zero_of_epi_comp (P.map S.g)
      rw [← P.map_comp, hg, P.map_zero]
    · let : Epi (Q.map S.g) := hq.epi_g
      apply zero_of_epi_comp (Q.map S.g)
      rw [← Q.map_comp, hg, Q.map_zero]
  exact ⟨(he S).mpr ⟨hp.exact, hq.exact⟩⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem local_shortExact (F : modules.{c, v, r} R)
    (h : first.{c, v, r} R U V F ≫ second.{c, v, r} R U V F = 0)
    (hU : localDescription.{c, v, r} R (overlap U V) U V prod.fst prod.snd)
    (hV : localDescription.{c, v, r} R (overlap U V) V U prod.snd prod.fst) :
    ((ShortComplex.mk (first.{c, v, r} R U V F) (second.{c, v, r} R U V F) h).map
      (localizedSystemRestriction.{c, v, r} R U)).ShortExact ∧
    ((ShortComplex.mk (first.{c, v, r} R U V F) (second.{c, v, r} R U V F) h).map
      (localizedSystemRestriction.{c, v, r} R V)).ShortExact := by
  constructor
  · obtain ⟨k, adj, es, eo, ew, hc⟩ := hU
    obtain ⟨hs, ho, hn, hm⟩ := hc F
    let P := localizedSystemRestriction.{c, v, r} R U
    let : P.Additive := localizedSystemRestrictionAdditive.{c, v, r} R U
    let : PreservesFiniteBiproducts P := Functor.preservesFiniteBiproductsOfAdditive P
    let : PreservesBinaryBiproducts P := preservesBinaryBiproducts_of_preservesBiproducts P
    let : PreservesFiniteLimits P := localizedSystemRestrictionLimits.{c, v, r} R U
    let : PreservesFiniteColimits P := localizedSystemRestrictionColimits.{c, v, r} R U
    let L := k.obj ((localizedSystemRestriction.{c, v, r} R (overlap U V)).obj F)
    let E := (localizedSystemRestriction.{c, v, r} R U).obj F
    let i : L ⟶ E := k.map ((overFunctorMap.{max c v r} (ring.{c, v, r} R)
      (prod.fst : U ⨯ V ⟶ U)).inv.app F) ≫
      adj.counit.app E
    change P.map (counit.{c, v, r} R U F) = es.hom.app F at hs
    change P.map (counit.{c, v, r} R V F) = eo.hom.app F ≫ i at ho
    change P.map (nested.{c, v, r} R (prod.fst : U ⨯ V ⟶ U) F) ≫
      es.hom.app F = ew.hom.app F ≫ i at hn
    change P.map (nested.{c, v, r} R (prod.snd : U ⨯ V ⟶ V) F) ≫
      eo.hom.app F = ew.hom.app F at hm
    let S := (ShortComplex.mk (first.{c, v, r} R U V F) (second.{c, v, r} R U V F) h).map P
    let T := ShortComplex.mk (biprod.lift i (-𝟙 L)) (biprod.desc (𝟙 E) i) (by simp)
    let e₂ := P.mapBiprod ((supported.{c, v, r} R U).obj F)
        ((supported.{c, v, r} R V).obj F) ≪≫ biprod.mapIso (es.app F) (eo.app F)
    let e : S ≅ T := ShortComplex.isoMk (ew.app F) e₂ (Iso.refl _) (by
      change ew.hom.app F ≫ biprod.lift i (-𝟙 L) =
        P.map (first.{c, v, r} R U V F) ≫
          ((P.mapBiprod ((supported.{c, v, r} R U).obj F)
        ((supported.{c, v, r} R V).obj F)).hom ≫ biprod.map (es.hom.app F) (eo.hom.app F))
      rw [← Category.assoc, first, biprod.map_lift_mapBiprod]
      apply biprod.hom_ext
      · simp only [Category.assoc]
        erw [biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
        exact hn.symm
      · simp only [Category.assoc]
        erw [biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
        rw [P.map_neg, Preadditive.comp_neg, Preadditive.neg_comp]
        erw [Category.comp_id]
        exact congrArg Neg.neg hm.symm) (by
      change ((P.mapBiprod ((supported.{c, v, r} R U).obj F)
        ((supported.{c, v, r} R V).obj F)).hom ≫ biprod.map (es.hom.app F) (eo.hom.app F)) ≫
        biprod.desc (𝟙 E) i = P.map (second.{c, v, r} R U V F)
      apply (cancel_epi (P.mapBiprod ((supported.{c, v, r} R U).obj F)
        ((supported.{c, v, r} R V).obj F)).inv).mp
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
        second, biprod.mapBiprod_inv_map_desc]
      apply biprod.hom_ext'
      · erw [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc, Category.comp_id]
        exact hs.symm
      · erw [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc]
        exact ho.symm)
    exact (ShortComplex.shortExact_iff_of_iso e).mpr (matrix_left i)
  · obtain ⟨k, adj, es, eo, ew, hc⟩ := hV
    obtain ⟨hs, ho, hn, hm⟩ := hc F
    let P := localizedSystemRestriction.{c, v, r} R V
    let : P.Additive := localizedSystemRestrictionAdditive.{c, v, r} R V
    let : PreservesFiniteBiproducts P := Functor.preservesFiniteBiproductsOfAdditive P
    let : PreservesBinaryBiproducts P := preservesBinaryBiproducts_of_preservesBiproducts P
    let : PreservesFiniteLimits P := localizedSystemRestrictionLimits.{c, v, r} R V
    let : PreservesFiniteColimits P := localizedSystemRestrictionColimits.{c, v, r} R V
    let L := k.obj ((localizedSystemRestriction.{c, v, r} R (overlap U V)).obj F)
    let E := (localizedSystemRestriction.{c, v, r} R V).obj F
    let i : L ⟶ E := k.map ((overFunctorMap.{max c v r} (ring.{c, v, r} R)
      (prod.snd : U ⨯ V ⟶ V)).inv.app F) ≫
      adj.counit.app E
    change P.map (counit.{c, v, r} R V F) = es.hom.app F at hs
    change P.map (counit.{c, v, r} R U F) = eo.hom.app F ≫ i at ho
    change P.map (nested.{c, v, r} R (prod.snd : U ⨯ V ⟶ V) F) ≫
      es.hom.app F = ew.hom.app F ≫ i at hn
    change P.map (nested.{c, v, r} R (prod.fst : U ⨯ V ⟶ U) F) ≫
      eo.hom.app F = ew.hom.app F at hm
    let S := (ShortComplex.mk (first.{c, v, r} R U V F) (second.{c, v, r} R U V F) h).map P
    let T := ShortComplex.mk (biprod.lift (𝟙 L) (-i)) (biprod.desc i (𝟙 E)) (by simp)
    let e₂ := P.mapBiprod ((supported.{c, v, r} R U).obj F)
        ((supported.{c, v, r} R V).obj F) ≪≫ biprod.mapIso (eo.app F) (es.app F)
    let e : S ≅ T := ShortComplex.isoMk (ew.app F) e₂ (Iso.refl _) (by
      change ew.hom.app F ≫ biprod.lift (𝟙 L) (-i) =
        P.map (first.{c, v, r} R U V F) ≫
          ((P.mapBiprod ((supported.{c, v, r} R U).obj F)
        ((supported.{c, v, r} R V).obj F)).hom ≫ biprod.map (eo.hom.app F) (es.hom.app F))
      rw [← Category.assoc, first, biprod.map_lift_mapBiprod]
      apply biprod.hom_ext
      · simp only [Category.assoc]
        erw [biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
        erw [Category.comp_id]
        exact hm.symm
      · simp only [Category.assoc]
        erw [biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
        rw [P.map_neg, Preadditive.comp_neg, Preadditive.neg_comp]
        exact congrArg Neg.neg hn.symm) (by
      change ((P.mapBiprod ((supported.{c, v, r} R U).obj F)
        ((supported.{c, v, r} R V).obj F)).hom ≫ biprod.map (eo.hom.app F) (es.hom.app F)) ≫
        biprod.desc i (𝟙 E) = P.map (second.{c, v, r} R U V F)
      apply (cancel_epi (P.mapBiprod ((supported.{c, v, r} R U).obj F)
        ((supported.{c, v, r} R V).obj F)).inv).mp
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
        second, biprod.mapBiprod_inv_map_desc]
      apply biprod.hom_ext'
      · erw [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc]
        exact ho.symm
      · erw [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc, Category.comp_id]
        exact hs.symm)
    exact (ShortComplex.shortExact_iff_of_iso e).mpr (matrix_right i)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem nested_eq {W Z : C} (f : W ⟶ Z) (F : modules.{c, v, r} R) :
    nested.{c, v, r} R f F = SubterminalLocal.nested.{c, v, r} R f F := by
  rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem local_descriptions
    (d : SubterminalLocal.Intersection.{c, v, r, max c v r} R U V
      (U ⨯ V) prod.fst prod.snd) :
    localDescription.{c, v, r} R (overlap U V) U V prod.fst prod.snd ∧
    localDescription.{c, v, r} R (overlap U V) V U prod.snd prod.fst := by
  constructor
  · let es : supported.{c, v, r} R U ⋙ localizedSystemRestriction.{c, v, r} R U ≅
        localizedSystemRestriction.{c, v, r} R U :=
      Functor.isoWhiskerLeft (localizedSystemRestriction.{c, v, r} R U) d.selfU ≪≫
      Functor.rightUnitor _
    let eo : supported.{c, v, r} R V ⋙ localizedSystemRestriction.{c, v, r} R U ≅
        localizedSystemRestriction.{c, v, r} R (U ⨯ V) ⋙ d.kU :=
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (localizedSystemRestriction.{c, v, r} R V) d.exchangeU ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (overFunctorMap.{max c v r} (ring.{c, v, r} R)
        (prod.snd : U ⨯ V ⟶ V)) d.kU
    let ew : supported.{c, v, r} R (U ⨯ V) ⋙ localizedSystemRestriction.{c, v, r} R U ≅
        localizedSystemRestriction.{c, v, r} R (U ⨯ V) ⋙ d.kU :=
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (localizedSystemRestriction.{c, v, r} R (U ⨯ V))
        (Functor.isoWhiskerRight d.composeU.symm (localizedSystemRestriction.{c, v, r} R U) ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft d.kU d.selfU ≪≫
          Functor.rightUnitor _)
    refine ⟨d.kU, d.adjU, es, eo, ew, ?_⟩
    intro F
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (SubterminalLocal.jstar.{c, v, r} R U).map
        ((SubterminalLocal.adj.{c, v, r} R U).counit.app F) =
          d.selfU.hom.app ((SubterminalLocal.jstar.{c, v, r} R U).obj F)
      apply (cancel_epi (d.selfU.inv.app _)).mp
      rw [Iso.inv_hom_id_app]
      rw [d.selfU_unit]
      exact (SubterminalLocal.adj.{c, v, r} R U).right_triangle_components F
    · change (SubterminalLocal.jstar.{c, v, r} R U).map
        ((SubterminalLocal.adj.{c, v, r} R V).counit.app F) = _
      dsimp only [eo, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Category.id_comp, Category.comp_id, Category.assoc]
      simp only [Category.id_comp, Category.assoc]
      convert d.exchangeU_counit F using 1
    · rw [nested_eq]
      dsimp only [es, ew, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.rightUnitor_hom_app, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Category.id_comp, Category.comp_id, Category.assoc]
      simp only [Category.id_comp, Category.assoc]
      exact d.nestedU_self F
    · have hx := d.nestedV_cross F
      rw [nested_eq]
      dsimp only [eo, ew, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.rightUnitor_hom_app, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      simp only [Category.id_comp]
      rw [← Category.assoc, hx]
      simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
      rw [d.kU.map_id]
  · let es : supported.{c, v, r} R V ⋙ localizedSystemRestriction.{c, v, r} R V ≅
        localizedSystemRestriction.{c, v, r} R V :=
      Functor.isoWhiskerLeft (localizedSystemRestriction.{c, v, r} R V) d.selfV ≪≫
      Functor.rightUnitor _
    let eo : supported.{c, v, r} R U ⋙ localizedSystemRestriction.{c, v, r} R V ≅
        localizedSystemRestriction.{c, v, r} R (U ⨯ V) ⋙ d.kV :=
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (localizedSystemRestriction.{c, v, r} R U) d.exchangeV ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (overFunctorMap.{max c v r} (ring.{c, v, r} R)
        (prod.fst : U ⨯ V ⟶ U)) d.kV
    let ew : supported.{c, v, r} R (U ⨯ V) ⋙ localizedSystemRestriction.{c, v, r} R V ≅
        localizedSystemRestriction.{c, v, r} R (U ⨯ V) ⋙ d.kV :=
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (localizedSystemRestriction.{c, v, r} R (U ⨯ V))
        (Functor.isoWhiskerRight d.composeV.symm (localizedSystemRestriction.{c, v, r} R V) ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft d.kV d.selfV ≪≫
          Functor.rightUnitor _)
    refine ⟨d.kV, d.adjV, es, eo, ew, ?_⟩
    intro F
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (SubterminalLocal.jstar.{c, v, r} R V).map
        ((SubterminalLocal.adj.{c, v, r} R V).counit.app F) =
          d.selfV.hom.app ((SubterminalLocal.jstar.{c, v, r} R V).obj F)
      apply (cancel_epi (d.selfV.inv.app _)).mp
      rw [Iso.inv_hom_id_app]
      rw [d.selfV_unit]
      exact (SubterminalLocal.adj.{c, v, r} R V).right_triangle_components F
    · change (SubterminalLocal.jstar.{c, v, r} R V).map
        ((SubterminalLocal.adj.{c, v, r} R U).counit.app F) = _
      dsimp only [eo, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Category.id_comp, Category.comp_id, Category.assoc]
      simp only [Category.id_comp, Category.assoc]
      convert d.exchangeV_counit F using 1
    · rw [nested_eq]
      dsimp only [es, ew, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.rightUnitor_hom_app, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Category.id_comp, Category.comp_id, Category.assoc]
      simp only [Category.id_comp, Category.assoc]
      convert d.nestedV_self F using 1 <;> rfl
    · have hx := d.nestedU_cross F
      rw [nested_eq]
      dsimp only [eo, ew, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.rightUnitor_hom_app, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      simp only [Category.id_comp]
      rw [← Category.assoc, hx]
      simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
      rw [d.kV.map_id]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The canonical binary-cover sequence, its naturality, and its termwise complex version.

Source: Stacks Project, Cohomology, Tag 08BU, proof of
lemma-exact-sequence-lower-shriek; blueprint subterminal-slice generalization
(blueprint: lem-sp-subterminal-cover-module-ses).

Proof:
1. Node `lem-sp-subterminal-module-local-calculus` identifies restricted extensions
with extension from the intersection: before sheafification, both are the same summands
with the same scalar and restriction maps. Restriction commutes with their sheafification.
2. Transpose a nested map followed by its counit. The triangle identity makes the
transpose the identity on `F|W`, proving both counit composites equal the W-counit.
Their difference is zero.
3. On U the component maps are `(i,-1)` and `(1,i)`; on V they are `(1,-i')` and
`(i',1)`. Compatibility of the local-calculus identifications with units and counits
identifies each component, including the identities, by its adjunction transpose.
4. On U the splitting is `s(y)=(y,0)`, `r(y,z)=-z`; on V it is
`s(z)=(0,z)`, `r(y,z)=y`. In both cases `ra=bs=1` and `ar+sb=1`, hence the
local sequences are short exact, without requiring i or i' invertible.
5. Joint detection of exactness by restriction to the covering U,V gives global
short exactness, including the endpoint mono and epi. No points of the topos are used.
6. Naturality of the unit, after taking W-transposes, gives naturality of nested maps;
naturality of the counit gives naturality of the second arrow. Apply these equations
to every differential and every component of a cochain map. Apply module short
exactness in each degree to obtain the claimed degreewise short exact sequence. -/
theorem shortExact [J.Subcanonical]
    [Mono (terminal.from U)] [Mono (terminal.from V)]
    (hcover : Sieve.ofArrows (fun b : Bool ↦ if b then U else V)
      (fun b ↦ terminal.from (if b then U else V)) ∈ J (⊤_ C)) :
    (∀ F : modules.{c, v, r} R,
      nested.{c, v, r} R (prod.fst : U ⨯ V ⟶ U) F ≫ counit.{c, v, r} R U F =
        counit.{c, v, r} R (overlap U V) F ∧
      nested.{c, v, r} R (prod.snd : U ⨯ V ⟶ V) F ≫ counit.{c, v, r} R V F =
        counit.{c, v, r} R (overlap U V) F ∧
      ∃ h : first.{c, v, r} R U V F ≫ second.{c, v, r} R U V F = 0,
        (ShortComplex.mk (first.{c, v, r} R U V F) (second.{c, v, r} R U V F) h).ShortExact) ∧
    (∀ (F G : modules.{c, v, r} R) (a : F ⟶ G),
      (supported.{c, v, r} R (overlap U V)).map a ≫ first.{c, v, r} R U V G =
        first.{c, v, r} R U V F ≫
          biprod.map ((supported.{c, v, r} R U).map a) ((supported.{c, v, r} R V).map a) ∧
      biprod.map ((supported.{c, v, r} R U).map a) ((supported.{c, v, r} R V).map a) ≫
          second.{c, v, r} R U V G =
        second.{c, v, r} R U V F ≫ a) ∧
    localDescription.{c, v, r} R (overlap U V) U V prod.fst prod.snd ∧
    localDescription.{c, v, r} R (overlap U V) V U prod.snd prod.fst ∧
    (∀ (K : CochainComplex (modules.{c, v, r} R) ℤ) (i j : ℤ),
      (supported.{c, v, r} R (overlap U V)).map (K.d i j) ≫ first.{c, v, r} R U V (K.X j) =
        first.{c, v, r} R U V (K.X i) ≫
          biprod.map ((supported.{c, v, r} R U).map (K.d i j))
            ((supported.{c, v, r} R V).map (K.d i j)) ∧
      biprod.map ((supported.{c, v, r} R U).map (K.d i j))
          ((supported.{c, v, r} R V).map (K.d i j)) ≫
          second.{c, v, r} R U V (K.X j) = second.{c, v, r} R U V (K.X i) ≫ K.d i j) ∧
    (∀ (K : CochainComplex (modules.{c, v, r} R) ℤ) (n : ℤ),
      ∃ h : first.{c, v, r} R U V (K.X n) ≫ second.{c, v, r} R U V (K.X n) = 0,
        (ShortComplex.mk (first.{c, v, r} R U V (K.X n))
          (second.{c, v, r} R U V (K.X n)) h).ShortExact) ∧
    (∀ (K L : CochainComplex (modules.{c, v, r} R) ℤ) (a : K ⟶ L) (n : ℤ),
      (supported.{c, v, r} R (overlap U V)).map (a.f n) ≫ first.{c, v, r} R U V (L.X n) =
        first.{c, v, r} R U V (K.X n) ≫
          biprod.map ((supported.{c, v, r} R U).map (a.f n))
            ((supported.{c, v, r} R V).map (a.f n)) ∧
      biprod.map ((supported.{c, v, r} R U).map (a.f n)) ((supported.{c, v, r} R V).map (a.f n)) ≫
          second.{c, v, r} R U V (L.X n) = second.{c, v, r} R U V (K.X n) ≫ a.f n) := by
  obtain ⟨⟨d⟩, _, hd⟩ :=
    SubterminalLocal.subterminal_module_local_calculus.{c, v, r, max c v r} R U V hcover
  obtain ⟨hU, hV⟩ := local_descriptions.{c, v, r} R U V d
  have hF (F : modules.{c, v, r} R) := by
    have h₁ : nested.{c, v, r} R (prod.fst : U ⨯ V ⟶ U) F ≫ counit.{c, v, r} R U F =
        counit.{c, v, r} R (overlap U V) F := d.nestedU_counit F
    have h₂ : nested.{c, v, r} R (prod.snd : U ⨯ V ⟶ V) F ≫ counit.{c, v, r} R V F =
        counit.{c, v, r} R (overlap U V) F := d.nestedV_counit F
    have h : first.{c, v, r} R U V F ≫ second.{c, v, r} R U V F = 0 := by
      simp [first, second, biprod.lift_desc, h₁, h₂]
    obtain ⟨hp, hq⟩ := local_shortExact.{c, v, r} R U V F h hU hV
    have hs := joint_shortExact (localizedSystemRestriction.{c, v, r} R U)
      (localizedSystemRestriction.{c, v, r} R V) (fun f ↦ hd.2.1 _ _ f) hd.2.2.1
      (ShortComplex.mk (first.{c, v, r} R U V F) (second.{c, v, r} R U V F) h) hp hq
    exact And.intro h₁ (And.intro h₂ (Exists.intro h hs))
  refine ⟨hF, arrows_naturality.{c, v, r} R U V, hU, hV, ?_, ?_, ?_⟩
  · intro K i j
    exact arrows_naturality.{c, v, r} R U V _ _ (K.d i j)
  · intro K n
    exact (hF (K.X n)).2.2
  · intro K L a n
    exact arrows_naturality.{c, v, r} R U V _ _ (a.f n)

end SheafOfModules.SubterminalCover
