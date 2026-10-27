/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
import Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact

/-!
# Coherence of the unbounded module direct-image compositor

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-cocycle.proof.md, "Refinement isomorphisms"; Stacks Project,
Tag 0D6E (blueprint: lem-sfb-module-derived-compositor-coherence).

The comparisons below specialize the existing total-right-derived universal construction
to the actual module-object pushforwards. Their K-injective normalization identifies them
with the ringed-topos comparisons transported through the internal/sectionwise module
equivalence: both are uniquely characterized by compatibility with the resolution units.
The derived categories are ordinary unbounded categories, with the published universe
convention: Scheme.{u}, abelian coefficients in u + 1, and the induced derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

private lemma derivedComp_post
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) {H H' : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] [H'.Additive]
    [F.PreservesKInjectiveComplexes] (e : F ⋙ G ≅ H) (d : H ≅ H') :
    Functor.rightDerivedFunctorCompIso' F G (e ≪≫ d) =
      Functor.rightDerivedFunctorCompIso' F G e ≪≫ Functor.rightDerivedFunctorNatIso d := by
  apply Iso.ext
  simp [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans_comp]

private lemma derivedId_eq
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C] :
    (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso C =
      Functor.rightDerivedFunctorIdIso C := by
  apply Iso.ext
  apply (𝟭 C).rightDerivedFunctor.rightDerived_ext (𝟭 C).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
  ext K : 2
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app, ← Category.assoc,
    Functor.rightDerivedFunctorIdIso_fac_app]
  have hf := congr_app (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  erw [hf]
  have h := congrArg (fun e ↦ e.hom.app K) (Functor.mapDerivedCategoryIdIso_factorsh C)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app_eq_id] at h
  erw [Category.comp_id, Category.comp_id, DerivedCategory.Qh.map_id,
    Category.comp_id] at h
  erw [h, Iso.inv_hom_id_app]

private lemma derivedId_objQ
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C] (I : CochainComplex C ℤ) [I.IsKInjective] :
    (Functor.rightDerivedFunctorIdIso C).hom.app (DerivedCategory.Q.obj I) =
      ((𝟭 C).rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app I) := by
  have hn := (Functor.rightDerivedFunctorIdIso C).hom.naturality
    ((DerivedCategory.quotientCompQhIso C).inv.app I)
  dsimp only [Functor.id_map] at hn
  rw [← cancel_mono ((DerivedCategory.quotientCompQhIso C).inv.app I), ← hn]
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_inv, Iso.app_hom, asIso_inv, Category.assoc]
  congr 1
  rw [← cancel_epi ((𝟭 C).rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ _).obj I)), IsIso.hom_inv_id_assoc]
  erw [Functor.rightDerivedFunctorIdIso_fac_app]
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
  dsimp only [Functor.id_obj]
  erw [Iso.hom_inv_id_app, Category.comp_id]
  have hi := Functor.mapHomotopyCategoryIdIso_hom_app_eq_id C (.up ℤ)
    ((HomotopyCategory.quotient _ _).obj I)
  rw [Functor.mapHomotopyCategoryIdIso_hom_app] at hi
  have hq := congrArg (fun t ↦ DerivedCategory.Qh.map t) hi
  conv_rhs at hq => erw [CategoryTheory.Functor.map_id]
  exact hq.symm

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical comparison `R(gf)_* ≅ Rf_* ⋙ Rg_*`, in inverse-compositor direction.
The existing exact inverse-image adjunction supplies K-injective preservation; the
comparison is the universal derived comparison of the existing ordinary compositor.
Source: Stacks 0D6E and blueprint det-sf-comp-coherence-cocycle, Refinement isomorphisms
(blueprint: lem-sfb-module-derived-compositor-coherence). -/
noncomputable def moduleDerivedCompositor {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (lowerStar Λ (f ≫ g)).rightDerivedFunctor ≅
      (lowerStar Λ f).rightDerivedFunctor ⋙ (lowerStar Λ g).rightDerivedFunctor :=
  letI := (upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes
  (Functor.rightDerivedFunctorCompIso' (lowerStar Λ f) (lowerStar Λ g)
    (lowerStarComp Λ f g)).symm

/-- The canonical comparison `R(1_T)_* ≅ 1`, induced by the sectionwise identity
pushforward. Right derivation of the ordinary identity comparison is followed by the
canonical identification of the derived identity with the identity functor.
Source: Stacks 0D6E and blueprint det-sf-comp-coherence-cocycle, Refinement isomorphisms
(blueprint: lem-sfb-module-derived-compositor-coherence). -/
noncomputable def moduleDerivedIdentity (T : Scheme.{u}) :
    (lowerStar Λ (𝟙 T)).rightDerivedFunctor ≅
      𝟭 (DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ T))) :=
  Functor.rightDerivedFunctorNatIso (lowerStarId Λ T) ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The successive resolution identifications for `Rg_* Rf_*` on a K-injective `I`.
Since the exact inverse-image adjunction makes `f_* I` K-injective, the second
identification uses that very complex, with no additional resolution or arbitrary choice.
Source: Stacks 0D6E, normalization with the identity resolution of `f_* I`
(blueprint: lem-sfb-module-derived-compositor-coherence). -/
noncomputable def moduleDerivedIteratedObjIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ) [I.IsKInjective] :
    ((lowerStar Λ f).rightDerivedFunctor ⋙ (lowerStar Λ g).rightDerivedFunctor).obj
        (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj
        (((lowerStar Λ f ⋙ lowerStar Λ g).mapHomologicalComplex (.up ℤ)).obj I) :=
  letI := (upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes
  (lowerStar Λ g).rightDerivedFunctor.mapIso
      ((lowerStar Λ f).rightDerivedFunctorObjQIso I) ≪≫
    (lowerStar Λ g).rightDerivedFunctorObjQIso
      (((lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I)

/-- On a K-injective representative the derived compositor is the inverse of the
termwise module compositor, after the canonical resolution identifications.
Source: Stacks 0D6E and blueprint det-sf-comp-coherence-cocycle, Refinement isomorphisms
(blueprint: lem-sfb-module-derived-compositor-coherence).

Proof plan: (1) use lem-sfb-internal-module-operations-transport and lem-sfb-eta-comp
to identify the coefficient actions and ordinary compositors under the section-module
equivalence; lem-sfb-section-ring-lax-pushforward-coherence gives their composition
and identity compatibility. (2) Exact module inverse image and its adjunction imply
K-injective preservation by lem-weil-pbc-right-adjoint-preserves-kinjective.
The resolution-compatible equivalence of lem-pd-section-derived-pushpull-normalization
identifies the total derived functors. (3) In the normalization of
lem-weil-pbc-ringed-topoi-derived-pushforward-composition choose the identity resolution
of f_* I. Its comparison is the identity after the ordinary compositor, so undoing
that identification gives exactly the inverse termwise compositor displayed here. -/
theorem module_derived_compositor_normalization (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ) [I.IsKInjective] :
    (moduleDerivedCompositor Λ f g).app (DerivedCategory.Q.obj I) ≪≫
        moduleDerivedIteratedObjIso Λ f g I =
      (lowerStar Λ (f ≫ g)).rightDerivedFunctorObjQIso I ≪≫
        DerivedCategory.Q.mapIso
          (((Functor.mapHomologicalComplexCompIso (lowerStarComp Λ f g) (.up ℤ)).symm).app
            I) := by
  have _ := hΛ
  let := (upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes
  apply Iso.ext
  simp only [moduleDerivedCompositor, Functor.rightDerivedFunctorCompIso', Iso.trans_inv,
    Iso.symm_inv,
    moduleDerivedIteratedObjIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.mapIso_hom, Category.assoc]
  erw [CategoryTheory.UnboundedSectionsLocalization.compIso_objQ
    (lowerStar Λ f) (lowerStar Λ g) I]
  rw [Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans_app_Q_obj]
  congr 2

/-- Associativity of the normalized module-object derived compositor, including
functor associators and transport along associativity of scheme-map composition.
Source: Stacks 0D6E and blueprint det-sf-comp-coherence-cocycle, Refinement isomorphisms
(blueprint: lem-sfb-module-derived-compositor-coherence).

Proof plan: (1)-(3) identify the ordinary and derived sectionwise pushforwards and
normalize on K-injectives as in module_derived_compositor_normalization. (4) Apply
lem-pur-ringed-derived-composition-cocycle to the four ringed topoi. Conjugate the
two composites by the resolution-compatible equivalences supplied by
lem-pd-section-derived-pushpull-normalization. The intermediate comparison isomorphisms
cancel; naturality moves the remaining comparisons past each compositor. The sectionwise
cocycle identifies the results. Faithfulness of the derived equivalence then identifies
the original transformations. The displayed associator and lowerStarCongr account for
both functor parentheses and equality of the two composite scheme maps. -/
theorem module_derived_compositor_coherence (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    moduleDerivedCompositor Λ (f ≫ g) h ≪≫
        Functor.isoWhiskerRight (moduleDerivedCompositor Λ f g)
          (lowerStar Λ h).rightDerivedFunctor ≪≫
        Functor.associator (lowerStar Λ f).rightDerivedFunctor
          (lowerStar Λ g).rightDerivedFunctor (lowerStar Λ h).rightDerivedFunctor =
      Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ (Category.assoc f g h)) ≪≫
        moduleDerivedCompositor Λ f (g ≫ h) ≪≫
        Functor.isoWhiskerLeft (lowerStar Λ f).rightDerivedFunctor
          (moduleDerivedCompositor Λ g h) := by
  have _ := hΛ
  let := (upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes
  let := (upperStarLowerStarAdjunction Λ g).preservesKInjectiveComplexes
  let := (upperStarLowerStarAdjunction Λ (f ≫ g)).preservesKInjectiveComplexes
  have ho := congrArg (fun e ↦ e.hom) (lowerStarComp_assoc Λ f g h)
  have hc := Functor.rightDerivedFunctorCompIso'_assoc
    (lowerStar Λ f) (lowerStar Λ g) (lowerStar Λ h)
    (lowerStar Λ (f ≫ g)) (lowerStar Λ (g ≫ h)) (lowerStar Λ (f ≫ g ≫ h))
    (lowerStarComp Λ f g) (lowerStarComp Λ g h)
    (lowerStarComp Λ (f ≫ g) h ≪≫ lowerStarCongr Λ (Category.assoc f g h))
    (lowerStarComp Λ f (g ≫ h)) (by
      apply NatTrans.ext
      funext M
      have hm := congr_app ho M
      simpa using hm.symm)
  rw [derivedComp_post] at hc
  have hci :
      Functor.isoWhiskerRight
          (Functor.rightDerivedFunctorCompIso' (lowerStar Λ f) (lowerStar Λ g)
            (lowerStarComp Λ f g)) (lowerStar Λ h).rightDerivedFunctor ≪≫
        Functor.rightDerivedFunctorCompIso' (lowerStar Λ (f ≫ g)) (lowerStar Λ h)
          (lowerStarComp Λ (f ≫ g) h) ≪≫
        Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ (Category.assoc f g h)) =
      Functor.isoWhiskerLeft (lowerStar Λ f).rightDerivedFunctor
          (Functor.rightDerivedFunctorCompIso' (lowerStar Λ g) (lowerStar Λ h)
            (lowerStarComp Λ g h)) ≪≫
        Functor.rightDerivedFunctorCompIso' (lowerStar Λ f) (lowerStar Λ (g ≫ h))
          (lowerStarComp Λ f (g ≫ h)) := Iso.ext hc
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi
    ((Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ (Category.assoc f g h))).inv.app
      M)).1
  have hi := congrArg (fun e ↦ e.inv.app M) hci
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Category.assoc] at hi
  simp only [moduleDerivedCompositor, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, Category.comp_id]
  simpa only [Iso.inv_hom_id_app_assoc, Category.assoc] using hi

set_option linter.unusedSectionVars false in
/-- The identity comparison is induced by the termwise sectionwise identity.
Source: Stacks 0D6E and blueprint det-sf-comp-coherence-cocycle, Refinement isomorphisms
(blueprint: lem-sfb-module-derived-compositor-coherence).

Proof plan: step (5) of the node uses the identity normalization in
lem-pur-ringed-derived-composition-cocycle. The ordinary internal/sectionwise comparison
identifies the identity maps. The resolution-unit compatibility of
lem-pd-section-derived-pushpull-normalization identifies their derived comparisons.
Choosing the identity resolution of a K-injective I gives the displayed formula;
the last factor identifies the termwise identity functor with the identity complex. -/
theorem module_derived_identity_normalization (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) (T : Scheme.{u})
    (I : CochainComplex
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ T)) ℤ) [I.IsKInjective] :
    (moduleDerivedIdentity Λ T).app (DerivedCategory.Q.obj I) =
      (lowerStar Λ (𝟙 T)).rightDerivedFunctorObjQIso I ≪≫
        DerivedCategory.Q.mapIso
          ((NatIso.mapHomologicalComplex (lowerStarId Λ T) (.up ℤ)).app I) ≪≫
        DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app I) := by
  have _ := hΛ
  apply Iso.ext
  simp only [moduleDerivedIdentity, derivedId_eq, Iso.app_hom,
    Iso.trans_hom, NatTrans.comp_app, Functor.rightDerivedFunctorNatIso]
  rw [derivedId_objQ, ← Category.assoc,
    Functor.rightDerivedFunctorNatTrans_app_Q_obj]
  simp only [Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rfl

/-- Both identity compositor constraints become identities under the canonical
identity comparison and scheme-map equality identifications.
Source: Stacks 0D6E and blueprint det-sf-comp-coherence-cocycle, Refinement isomorphisms
(blueprint: lem-sfb-module-derived-compositor-coherence).

Proof plan: step (5) applies both unit equations of
lem-pur-ringed-derived-composition-cocycle. Identify its identity comparison with
moduleDerivedIdentity using module_derived_identity_normalization and resolution
compatibility. Transport the equations through the derived internal/sectionwise
equivalence, cancelling the intermediate comparison isomorphisms exactly as in step
(4). Faithfulness gives both displayed laws, including the two functor unitors.
Only exact inverse image and small-site derived categories are used, with no
properness, density, Noetherian or field assumption. -/
theorem module_derived_compositor_units (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleDerivedCompositor Λ (𝟙 X) f ≪≫
        Functor.isoWhiskerRight (moduleDerivedIdentity Λ X)
          (lowerStar Λ f).rightDerivedFunctor ≪≫
        Functor.leftUnitor (lowerStar Λ f).rightDerivedFunctor =
      Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ (Category.id_comp f))) ∧
    (moduleDerivedCompositor Λ f (𝟙 Y) ≪≫
        Functor.isoWhiskerLeft (lowerStar Λ f).rightDerivedFunctor
          (moduleDerivedIdentity Λ Y) ≪≫
        Functor.rightUnitor (lowerStar Λ f).rightDerivedFunctor =
      Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ (Category.comp_id f))) := by
  have _ := hΛ
  let := (upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes
  let := (upperStarLowerStarAdjunction Λ (𝟙 X)).preservesKInjectiveComplexes
  constructor
  · have he : lowerStarComp Λ (𝟙 X) f ≪≫ lowerStarCongr Λ (Category.id_comp f) =
        Functor.isoWhiskerRight (lowerStarId Λ X) (lowerStar Λ f) ≪≫
          Functor.leftUnitor (lowerStar Λ f) := by
      rw [lowerStarComp_id_left]
      simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
    have hc := Functor.rightDerivedFunctorCompIso'_hom_of_iso_id_left
      (lowerStar Λ (𝟙 X)) (lowerStar Λ f) (lowerStarId Λ X)
    rw [← he, derivedComp_post] at hc
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (cancel_epi
      ((Functor.rightDerivedFunctorCompIso' (lowerStar Λ (𝟙 X)) (lowerStar Λ f)
        (lowerStarComp Λ (𝟙 X) f)).hom.app M)).1
    have hm := congr_app hc M
    simp only [moduleDerivedCompositor, moduleDerivedIdentity,
      derivedId_eq, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Iso.hom_inv_id_app_assoc]
    simpa using hm.symm
  · have he : lowerStarComp Λ f (𝟙 Y) ≪≫ lowerStarCongr Λ (Category.comp_id f) =
        Functor.isoWhiskerLeft (lowerStar Λ f) (lowerStarId Λ Y) ≪≫
          Functor.rightUnitor (lowerStar Λ f) := by
      rw [lowerStarComp_id_right]
      simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
    have hc := Functor.rightDerivedFunctorCompIso'_hom_of_iso_id_right
      (lowerStar Λ f) (lowerStar Λ (𝟙 Y)) (lowerStarId Λ Y)
    rw [← he, derivedComp_post] at hc
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (cancel_epi
      ((Functor.rightDerivedFunctorCompIso' (lowerStar Λ f) (lowerStar Λ (𝟙 Y))
        (lowerStarComp Λ f (𝟙 Y))).hom.app M)).1
    have hm := congr_app hc M
    simp only [moduleDerivedCompositor, moduleDerivedIdentity,
      derivedId_eq, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Category.assoc, Iso.hom_inv_id_app_assoc]
    simpa using hm.symm

end AlgebraicGeometry.ProEtale.CondensedRing
