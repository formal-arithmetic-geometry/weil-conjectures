/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import all Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import Sheaf.AlgebraicGeometry.ProEtaleConstantModuleComparisonLocalization
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalAdjunctionUnit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate

/-!
# Normalized derived global sections after ordinary pro-etale direct image

Source: Stacks Project, sites-cohomology.tex, Tags 0D6H and 0D6E;
K-injective normalization and open-unit calculation in derived.tex, Tags 070Y and 0DVC
(blueprint: lem-pur-proetale-direct-image-global-evaluation).

The section functor and its terminal-object comparison are the published ordinary
constant-ring constructions. All derived images below are the actual finite-level
sectionwise direct image, without completion or a constructibility restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
section
attribute [-instance]
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme

/-- The recorded tensor-unit-normalized adjunction, with the right functor written
as the sectionwise constant-module direct image used at finite level.
Source: Stacks, modules on sites, lemma-adjoint-push-pull-modules
(blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleOrdinaryModuleAdjunction (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingPullback A f ⊣ proEtaleConstantModuleDirectImage f A :=
  (proEtaleConstantRingAdjunction A f).ofNatIsoRight (proEtaleUnitLerayDirectImageIso A f)

/-- The actual finite direct image preserves K-injectives, since the recorded
inverse image is exact. Source: Stacks Tag 08BJ
(blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
instance proEtaleOrdinaryDirectImage_preservesKInjective (A : Type u)
    [CommRing A] [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleConstantModuleDirectImage f A).PreservesKInjectiveComplexes :=
  (proEtaleOrdinaryModuleAdjunction A f).preservesKInjectiveComplexes

/-- The ordinary derived adjunction on the exact finite-coefficient presentation.
Source: Stacks Tag 0DVC (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleOrdinaryDerivedAdjunction (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingDerivedPullback A f ⊣ proEtaleConstantDerivedDirectImage f A :=
  (proEtaleOrdinaryModuleAdjunction A f).mapDerivedCategoryRightDerivedAdjunction

/-- The canonical finite composition comparison in ordinary constant-ring modules.
It is the conjugate of the published inverse-image composition isomorphism, through
exactly the derived adjunctions of the finite direct image; thus it is the canonical
ringed-topos comparison of Tag 0D6E, with orientation R(gf)_* -> Rg_* Rf_*.
Source: Stacks Tag 0D6E (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleOrdinaryDirectImageComposition (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantDerivedDirectImage (f ≫ g) A ≅
      proEtaleConstantDerivedDirectImage f A ⋙ proEtaleConstantDerivedDirectImage g A :=
  conjugateIsoEquiv (proEtaleOrdinaryDerivedAdjunction A (f ≫ g))
    ((proEtaleOrdinaryDerivedAdjunction A g).comp (proEtaleOrdinaryDerivedAdjunction A f))
    (proEtaleConstantRingPullbackComposition f g A)

/-- Fix abelian-group sheafification at the published coefficient universe.
Source: Stacks Tag 07A5 (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
private noncomputable local instance (priority := 5000) globalEvaluation_sheafify
    (X : Scheme.{u}) : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

/-- Use the published locally-bijective characterization at that same universe.
Source: Stacks Tag 07A5 (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
private noncomputable local instance (priority := 5000) globalEvaluation_locallyBijective
    (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

/-- Finiteness of the conventions' coefficient ring, supplied by its published quotient
construction. Source: blueprint def-pur-conventions, A = O_E/(varpi^n)
(blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
instance purityGlobalEvaluation_finiteRing (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- Derived final-object evaluation in the same localization universes as the published
unit--Leray construction. Source: Stacks Tag 0D6H
(blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
abbrev proEtaleGlobalEvaluationSections (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u}) :=
  @Functor.rightDerivedFunctor.{u+2,u+2,u+1,u+1,u+2,u+1} _ _ _ _ _ _
    (proEtaleRingModules_hasDerivedCategory X (proEtaleConstantRing X A))
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
    (proEtaleUnitLeraySections A X) inferInstance
    (proEtaleRingModules_hasKInjectiveResolutions X (proEtaleConstantRing X A))

/-- The canonical K-injective evaluation isomorphism in those fixed localization universes.
Source: Stacks Tag 070Y (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
abbrev proEtaleGlobalEvaluationSectionsObj (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u})
    (J : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    [J.IsKInjective] :=
  @Functor.rightDerivedFunctorObjQIso.{u+2,u+2,u+1,u+1,u+2,u+1} _ _ _ _ _ _
    (proEtaleRingModules_hasDerivedCategory X (proEtaleConstantRing X A))
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
    (proEtaleRingModules_hasKInjectiveResolutions X (proEtaleConstantRing X A))
    (proEtaleUnitLeraySections A X) inferInstance J inferInstance

/-- The finite direct image on K-injectives, using its published standard localization.
Source: Stacks Tag 070Y (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
abbrev proEtaleGlobalEvaluationImageObj (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    [J.IsKInjective] :=
  @Functor.rightDerivedFunctorObjQIso.{u+2,u+2,u+1,u+1,u+2,u+2} _ _ _ _ _ _
    (proEtaleRingModules_hasDerivedCategory X (proEtaleConstantRing X A))
    (proEtaleRingModules_hasDerivedCategory Y (proEtaleConstantRing Y A))
    (proEtaleRingModules_hasKInjectiveResolutions X (proEtaleConstantRing X A))
    (proEtaleConstantModuleDirectImage f A) inferInstance J inferInstance

/-- The published terminal-object comparison, written for the actual finite direct image.
Source: Stacks Tag 0D6H (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleGlobalEvaluationTerminal (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantModuleDirectImage f A ⋙ proEtaleUnitLeraySections A Y ≅
      proEtaleUnitLeraySections A X :=
  isoWhiskerRight (proEtaleUnitLerayDirectImageIso A f).symm
    (proEtaleUnitLeraySections A Y) ≪≫ proEtaleUnitLerayTerminalIso A f

/-- The canonical comparison, derived from evaluation at the final object. The universal
right-derived compositor fixes the comparison on K-injectives and all derived morphisms.
Source: Stacks Tags 0D6H and 0D6E
(blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleGlobalEvaluation (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantDerivedDirectImage f A ⋙
        (proEtaleGlobalEvaluationSections A Y) ≅
      (proEtaleGlobalEvaluationSections A X) :=
  letI := proEtaleRingModules_hasKInjectiveResolutions X (proEtaleConstantRing X A)
  letI := proEtaleRingModules_hasKInjectiveResolutions Y (proEtaleConstantRing Y A)
  Functor.rightDerivedFunctorCompIso' (proEtaleConstantModuleDirectImage f A)
    (proEtaleUnitLeraySections A Y) (proEtaleGlobalEvaluationTerminal A f)

/-- The natural isomorphism on precisely D^+(X_proet,A), with every derived morphism.
Source: Stacks Tag 0D6H (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleGlobalEvaluationPlus (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  isoWhiskerLeft (@DerivedCategory.Plus.ι
    (proEtaleRingModules X (proEtaleConstantRing X P.Ring)) _ _
    (proEtaleRingModules_hasDerivedCategory X (proEtaleConstantRing X P.Ring)))
    (proEtaleGlobalEvaluation P.Ring f)

/-- The normalized identity inverse image. The source theorem specifies every section
of its module comparison, its termwise extension, and its localization, so the extracted
isomorphism is determined by that normalization rather than by bare existence.
Source: blueprint lem-pur-proetale-derived-pullback-identity
(blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleGlobalEvaluationPullbackId (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u}) : proEtaleConstantRingDerivedPullback A (𝟙 X) ≅ 𝟭 _ :=
  (proEtaleDerivedPullback_identity X A).choose_spec.2.2.choose_spec.2.choose_spec.2.2
    |>.choose_spec.2.choose

/-- The canonical identity direct-image comparison is the mate of the section-normalized
identity inverse image, for the same ordinary adjunction as the composition comparison.
Source: Stacks Tag 0D6E (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleGlobalEvaluationDirectImageId (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u}) : proEtaleConstantDerivedDirectImage (𝟙 X) A ≅ 𝟭 _ :=
  conjugateIsoEquiv (proEtaleOrdinaryDerivedAdjunction A (𝟙 X)) (Adjunction.id)
    (proEtaleGlobalEvaluationPullbackId A X).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem globalEvaluation_obj
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) (J : CochainComplex C ℤ) [J.IsKInjective] :
    (Functor.rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Q.obj J) =
      G.rightDerivedFunctor.map (F.rightDerivedFunctorObjQIso J).hom ≫
        (G.rightDerivedFunctorObjQIso
          ((F.mapHomologicalComplex (.up ℤ)).obj J)).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app J) ≫
        (H.rightDerivedFunctorObjQIso J).inv := by
  let K := (HomotopyCategory.quotient _ (.up ℤ)).obj J
  have h := NatTrans.congr_app (unitLerayFac e) K
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K =
      𝟙 _ := by
    have h' := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) K
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h'
    exact h'
  have : IsIso (G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K)) :=
    inferInstanceAs (IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj J))))
  dsimp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at h
  rw [hi] at h
  erw [DerivedCategory.Qh.map_id] at h
  repeat erw [Category.id_comp] at h
  repeat erw [Category.comp_id] at h
  simp only [Category.assoc] at h
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, asIso_hom, asIso_inv]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]
  rw [← cancel_epi (G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K))]
  dsimp only [K]
  rw [← Functor.map_comp_assoc, IsIso.hom_inv_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← cancel_epi (G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K))]
  erw [IsIso.hom_inv_id_assoc]
  exact h


section MateTransport
variable {C D E : Type*} [Category C] [Category D] [Category E]
  {Lf : D ⥤ C} {Lg : E ⥤ D} {Lc : E ⥤ C}
  {F F' : C ⥤ D} {G G' : D ⥤ E} {H H' : C ⥤ E}
  (af : Lf ⊣ F) (ag : Lg ⊣ G) (ac : Lc ⊣ H)
  (ef : F ≅ F') (eg : G ≅ G') (ec : H ≅ H')
  (a : Lc ⟶ Lg ⋙ Lf)
private theorem mateTransport :
    conjugateEquiv ((ag.ofNatIsoRight eg).comp (af.ofNatIsoRight ef))
      (ac.ofNatIsoRight ec) a =
      Functor.whiskerRight ef.inv G' ≫ Functor.whiskerLeft F eg.inv ≫
        conjugateEquiv (ag.comp af) ac a ≫ ec.hom := by
  have hc (M : C) :
      ((ag.ofNatIsoRight eg).comp (af.ofNatIsoRight ef)).counit.app M =
        (Lg ⋙ Lf).map (G'.map (ef.inv.app M) ≫ eg.inv.app (F.obj M)) ≫
          (ag.comp af).counit.app M := by
    simp only [Adjunction.comp_counit_app, Adjunction.ofNatIsoRight_counit,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_map,
      Functor.map_comp, Category.assoc]
    have hn := ag.counit.naturality (ef.inv.app M)
    have he := eg.inv.naturality (ef.inv.app M)
    simp only [Functor.comp_map, Functor.id_map] at hn he
    rw [← Lf.map_comp_assoc (ag.counit.app _) (ef.inv.app M), ← hn]
    simpa only [Lf.map_comp, Lg.map_comp, Category.assoc] using
      (congrArg (fun t ↦ Lf.map (Lg.map t) ≫
        Lf.map (ag.counit.app (F.obj M)) ≫ af.counit.app M) he).symm
  apply NatTrans.ext
  funext M
  let t := G'.map (ef.inv.app M) ≫ eg.inv.app (F.obj M)
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  rw [hc, ← H'.map_comp]
  rw [← ec.hom.naturality]
  rw [H.map_comp, H.map_comp]
  simp only [Category.assoc]
  rw [← H.map_comp_assoc]
  erw [← a.naturality t]
  rw [H.map_comp, Category.assoc]
  erw [← ac.unit.naturality_assoc t]
  simp only [t, Functor.comp_obj, Functor.id_map, Category.assoc]

end MateTransport

private lemma comp_unit_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (T : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app T =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj T) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app T) := by
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app T =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) T
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, hi]
  erw [DerivedCategory.Qh.map_id]
  dsimp
  simp only [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedComp
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory B] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions B]
    (F : C ⥤ D) (G : D ⥤ B) (H : B ⥤ E) (K : C ⥤ B) (J : D ⥤ E) (L : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive] [J.Additive] [L.Additive]
    [F.PreservesKInjectiveComplexes] [G.PreservesKInjectiveComplexes]
    [K.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ K) (a : G ⋙ H ≅ J) (b : F ⋙ J ≅ L) (c : K ⋙ H ≅ L)
    (he : ∀ M : C, H.map (e.hom.app M) ≫ c.hom.app M =
      a.hom.app (F.obj M) ≫ b.hom.app M) :
    Functor.whiskerRight (Functor.rightDerivedFunctorCompIso' F G e).hom
        H.rightDerivedFunctor ≫ (Functor.rightDerivedFunctorCompIso' K H c).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft F.rightDerivedFunctor (Functor.rightDerivedFunctorCompIso' G H a).hom ≫
        (Functor.rightDerivedFunctorCompIso' F J b).hom := by
  let d := Functor.rightDerivedFunctorCompIso' F G e
  have : (F ⋙ G).PreservesKInjectiveComplexes := ⟨fun T _ => by
    change CochainComplex.IsKInjective
      ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj T))
    infer_instance⟩
  let i := Functor.isoWhiskerRight (Functor.rightDerivedFunctorCompIso F G)
    H.rightDerivedFunctor
  let α := Functor.rightDerivedFunctorCompUnit (F ⋙ G) H ≫
    Functor.whiskerLeft DerivedCategory.Qh i.hom
  have : ((F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) ⋙ H.rightDerivedFunctor
      ).IsRightDerivedFunctor α (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    (Functor.isRightDerivedFunctor_iff_of_iso
      (Functor.rightDerivedFunctorCompUnit (F ⋙ G) H) α
      (HomotopyCategory.quasiIso _ (.up ℤ)) i rfl).mp inferInstance
  refine Functor.rightDerived_ext _ α (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _ ?_
  ext T : 2
  have hα : α.app T =
      H.rightDerivedFunctorUnit.app
          ((G.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj T)) ≫
        H.rightDerivedFunctor.map ((Functor.rightDerivedFunctorCompUnit F G).app T) := by
    dsimp only [α, i, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    rw [comp_unit_app]
    erw [Category.assoc, ← Functor.map_comp]
    congr 2
    simp [Functor.rightDerivedFunctorCompIso]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, hα, Category.assoc]
  dsimp only [Functor.comp_obj]
  erw [Category.id_comp]
  have hfg := NatTrans.congr_app (unitLerayFac e) T
  have hc := NatTrans.congr_app (unitLerayFac c) T
  have ha := NatTrans.congr_app (unitLerayFac a)
    ((F.mapHomotopyCategory (.up ℤ)).obj T)
  have hb := NatTrans.congr_app (unitLerayFac b) T
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hfg hc ha hb
  rw [comp_unit_app] at hc ha hb
  have hn := H.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app T)
  have hna := (Functor.rightDerivedFunctorCompIso' G H a).hom.naturality
    (F.rightDerivedFunctorUnit.app T)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hna
  change H.rightDerivedFunctorUnit.app _ ≫
      H.rightDerivedFunctor.map ((Functor.rightDerivedFunctorCompUnit F G).app T) ≫
      H.rightDerivedFunctor.map (d.hom.app (DerivedCategory.Qh.obj T)) ≫
      (Functor.rightDerivedFunctorCompIso' K H c).hom.app (DerivedCategory.Qh.obj T) =
    H.rightDerivedFunctorUnit.app _ ≫
      H.rightDerivedFunctor.map ((Functor.rightDerivedFunctorCompUnit F G).app T) ≫
      (Functor.rightDerivedFunctorCompIso' G H a).hom.app
        (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj T)) ≫
      (Functor.rightDerivedFunctorCompIso' F J b).hom.app (DerivedCategory.Qh.obj T)
  rw [← Functor.map_comp_assoc, hfg, Functor.map_comp]
  simp only [Category.assoc] at hc ha hb ⊢
  erw [← reassoc_of% hn]
  erw [hc]
  rw [comp_unit_app, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hna, reassoc_of% ha, hb]
  rw [← DerivedCategory.Qh.map_comp_assoc, ← DerivedCategory.Qh.map_comp_assoc]
  congr 2
  obtain ⟨T, rfl⟩ := HomotopyCategory.quotient_obj_surjective T
  have ht : (H.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app T) ≫
      (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app T =
    (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj T) ≫
      (NatTrans.mapHomologicalComplex b.hom (.up ℤ)).app T := by
    ext n : 1
    exact he (T.X n)
  have hq := (HomotopyCategory.quotient E (.up ℤ)).congr_map ht
  simp only [NatTrans.mapHomotopyCategory_app,
    HomotopyCategory.quotient_obj_as, Functor.mapHomotopyCategory_map,
    Functor.map_comp] at hq ⊢
  exact hq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedIdentity
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions C]
    (L F : C ⥤ C) (G : C ⥤ E) [L.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [F.PreservesKInjectiveComplexes]
    (a : L ⊣ F) (e : F ⋙ G ≅ G) (α : L ≅ 𝟭 C)
    (β : L.mapDerivedCategory ≅ 𝟭 (DerivedCategory C))
    (hβ : ∀ I : CochainComplex C ℤ,
      β.hom.app (DerivedCategory.Q.obj I) = L.mapDerivedCategoryFactors.hom.app I ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I))
    (h : whiskerRight a.unit G ≫ whiskerLeft L e.hom ≫ whiskerRight α.hom G = 𝟙 G) :
    (Functor.rightDerivedFunctorCompIso' F G e).hom =
      whiskerRight (conjugateIsoEquiv a.mapDerivedCategoryRightDerivedAdjunction
        Adjunction.id β.symm).hom G.rightDerivedFunctor := by
  let d := conjugateIsoEquiv a.mapDerivedCategoryRightDerivedAdjunction Adjunction.id β.symm
  have hd (K : DerivedCategory C) : d.inv.app K =
      a.mapDerivedCategoryRightDerivedAdjunction.unit.app K ≫
        F.rightDerivedFunctor.map (β.hom.app K) := by
    simpa only [d, conjugateIsoEquiv_apply_inv, Iso.symm_inv, Adjunction.id_unit,
      NatTrans.id_app, Category.id_comp, Functor.id_obj] using
        unit_conjugateEquiv Adjunction.id a.mapDerivedCategoryRightDerivedAdjunction β.hom K
  apply NatTrans.ext
  funext K
  obtain ⟨I, hI, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have heq : (Functor.rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Q.obj I) =
      G.rightDerivedFunctor.map (d.hom.app (DerivedCategory.Q.obj I)) := by
    have hc := unitLerayChain a e I I ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I)
    rw [← hβ] at hc
    have hn := (Functor.rightDerivedFunctorCompIso' F G e).hom.naturality
      (β.hom.app (DerivedCategory.Q.obj I))
    dsimp only [Functor.comp_map] at hn
    erw [← hn, ← G.rightDerivedFunctor.map_comp_assoc, ← hd] at hc
    have hh : (NatTrans.mapHomologicalComplex
        (whiskerRight a.unit G ≫ whiskerLeft L e.hom) (.up ℤ)).app I ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I) = 𝟙 _ := by
      ext n : 1
      change (G.map (a.unit.app (I.X n)) ≫ e.hom.app (L.obj (I.X n))) ≫
        G.map (α.hom.app (I.X n)) = 𝟙 _
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
        NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f,
        Functor.mapHomologicalComplex_obj_X,
        Functor.comp_obj, Functor.id_obj,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        NatTrans.id_app, Category.assoc] using congr_app h (I.X n)
    erw [hh, DerivedCategory.Q.map_id, Category.id_comp, Iso.hom_inv_id] at hc
    apply (cancel_epi (G.rightDerivedFunctor.map (d.inv.app _))).mp
    rw [← G.rightDerivedFunctor.map_comp, d.inv_hom_id_app,
      G.rightDerivedFunctor.map_id]
    exact hc.symm
  apply (cancel_epi ((F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).map i.inv)).mp
  rw [(Functor.rightDerivedFunctorCompIso' F G e).hom.naturality, heq]
  simp only [Functor.whiskerRight_app, Functor.comp_map]
  rw [← G.rightDerivedFunctor.map_comp, ← G.rightDerivedFunctor.map_comp]
  exact G.rightDerivedFunctor.congr_map (d.hom.naturality i.inv).symm





private theorem directIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : Y.ProEtᵒᵖ)
    (m : M.val.obj ((proEtaleBaseChange f).op.obj W)) :
    ((proEtaleUnitLerayDirectImageIso A f).hom.app M).val.app W m = m :=
  by
  rfl

private theorem directIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : Y.ProEtᵒᵖ)
    (m : ((proEtaleConstantModuleDirectImage f A).obj M).val.obj W) :
    ((proEtaleUnitLerayDirectImageIso A f).inv.app M).val.app W m = m :=
  by
  rfl
attribute [local irreducible] proEtaleUnitLerayDirectImageIso


section SectionRealization
variable (A : Type u) [CommRing A] [Finite A]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarUnit_bijective (X : Scheme.{u})
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (W : X.ProEtᵒᵖ) :
    Function.Bijective (sfIntrinsicRealizationUnit X A M W) := by
  let α := ProEtale.finiteCoefficientIntrinsicScalarMap X A
  let N := (ProEtale.finiteCoefficientModulePresheaf X.ProEt
    (ULift.{u + 1, u} A)).obj M.obj
  let η := (PresheafOfModules.sheafificationAdjunction α).unit.app N
  have : IsIso η := by
    dsimp only [η, α, N]
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})).obj
        M).property
  have : IsIso (η.app W) := inferInstanceAs
    (IsIso ((PresheafOfModules.evaluation _ W).map η))
  exact ConcreteCategory.bijective_of_isIso (η.app W)

private def sectionRealization (X : Scheme.{u})
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : X.ProEtᵒᵖ)
    (m : ((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.obj W) : M.val.obj W :=
  ((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M).val.app W
    (sfIntrinsicRealizationUnit X A ((sfIntrinsicModuleEquivalence X A).inverse.obj M) W m)

set_option backward.isDefEq.respectTransparency false in
private theorem sectionRealization_bijective (X : Scheme.{u})
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : X.ProEtᵒᵖ) :
    Function.Bijective (sectionRealization A X M W) := by
  have : IsIso (((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M).val.app W) :=
    inferInstanceAs (IsIso ((SheafOfModules.evaluation _ W).map
      ((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M)))
  exact (ConcreteCategory.bijective_of_isIso
    (((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M).val.app W)).comp
      (scalarUnit_bijective A X _ W)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarUnit_naturality (X : Scheme.{u})
    {M N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (f : M ⟶ N) (W : X.ProEtᵒᵖ) (m : M.obj.obj W) :
    sfIntrinsicRealizationUnit X A N W (f.hom.app W m) =
      (((sfIntrinsicModuleEquivalence X A).functor.map f).val.app W)
        (sfIntrinsicRealizationUnit X A M W m) := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun h ↦ h.app W)
      ((PresheafOfModules.sheafificationAdjunction
        (ProEtale.finiteCoefficientIntrinsicScalarMap X A)).unit.naturality
          ((ProEtale.finiteCoefficientModulePresheaf X.ProEt
            (ULift.{u + 1, u} A)).map f.hom))) m

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionRealization_naturality (X : Scheme.{u})
    {M N : proEtaleRingModules X (proEtaleConstantRing X A)}
    (f : M ⟶ N) (W : X.ProEtᵒᵖ)
    (m : ((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.obj W) :
    sectionRealization A X N W
        (((sfIntrinsicModuleEquivalence X A).inverse.map f).hom.app W m) =
      f.val.app W (sectionRealization A X M W m) := by
  unfold sectionRealization
  rw [scalarUnit_naturality]
  exact ConcreteCategory.congr_hom
    (congrArg (fun h ↦ h.val.app W)
      ((sfIntrinsicModuleEquivalence X A).counitIso.hom.naturality f)) _
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionRealization_functor (X : Scheme.{u})
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (W : X.ProEtᵒᵖ)
    (m : ((sfIntrinsicModuleEquivalence X A).inverse.obj
      ((sfIntrinsicModuleEquivalence X A).functor.obj M)).obj.obj W) :
    sectionRealization A X ((sfIntrinsicModuleEquivalence X A).functor.obj M) W m =
      sfIntrinsicRealizationUnit X A M W
        (((sfIntrinsicModuleEquivalence X A).unitIso.inv.app M).hom.app W m) := by
  unfold sectionRealization
  have he := (sfIntrinsicModuleEquivalence X A).counit_app_functor M
  change (sfIntrinsicModuleEquivalence X A).counitIso.hom.app
      ((sfIntrinsicModuleEquivalence X A).functor.obj M) = _ at he
  rw [he]
  exact (scalarUnit_naturality A X
    ((sfIntrinsicModuleEquivalence X A).unitIso.inv.app M) W m).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionRealization_restrict (X : Scheme.{u})
    (M : proEtaleRingModules X (proEtaleConstantRing X A))
    {V W : X.ProEtᵒᵖ} (f : V ⟶ W)
    (m : ((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.obj V) :
    sectionRealization A X M W
        (((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.map f m) =
      M.val.map f (sectionRealization A X M V m) := by
  unfold sectionRealization
  have hu : sfIntrinsicRealizationUnit X A
      ((sfIntrinsicModuleEquivalence X A).inverse.obj M) W
      (((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.map f m) =
      (((sfIntrinsicModuleEquivalence X A).functor.obj
        ((sfIntrinsicModuleEquivalence X A).inverse.obj M)).val.map f)
        (sfIntrinsicRealizationUnit X A
          ((sfIntrinsicModuleEquivalence X A).inverse.obj M) V m) :=
    PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction
        (ProEtale.finiteCoefficientIntrinsicScalarMap X A)).unit.app
        ((ProEtale.finiteCoefficientModulePresheaf X.ProEt
          (ULift.{u + 1, u} A)).obj ((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj)) f m
  exact (congrArg (fun x ↦
    ((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M).val.app W x) hu).trans
      (PresheafOfModules.naturality_apply
        ((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M).val f _)

private def sectionDirectImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantModuleDirectImage f A ⋙ (sfIntrinsicModuleEquivalence Y A).inverse ≅
      (sfIntrinsicModuleEquivalence X A).inverse ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f :=
  isoWhiskerRight (sfIntrinsicModuleEquivalence X A).counitIso.symm
      (proEtaleConstantModuleDirectImage f A ⋙ (sfIntrinsicModuleEquivalence Y A).inverse) ≪≫
    isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
      (isoWhiskerRight (sfIntrinsicDirectImageComparison f A)
        (sfIntrinsicModuleEquivalence Y A).inverse) ≪≫
    isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
      (Functor.associator
          (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
          (sfIntrinsicModuleEquivalence Y A).functor
          (sfIntrinsicModuleEquivalence Y A).inverse ≪≫
        isoWhiskerLeft (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
          (sfIntrinsicModuleEquivalence Y A).unitIso.symm ≪≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightUnitor)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionDirectImageIso_normalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : Y.ProEtᵒᵖ)
    (m : ((sfIntrinsicModuleEquivalence Y A).inverse.obj
      ((proEtaleConstantModuleDirectImage f A).obj M)).obj.obj W) :
    sectionRealization A X M ((proEtaleBaseChange f).op.obj W)
        (((sectionDirectImageIso A f).hom.app M).hom.app W m) =
      sectionRealization A Y ((proEtaleConstantModuleDirectImage f A).obj M) W m := by
  let N := (sfIntrinsicModuleEquivalence X A).inverse.obj M
  let t := (proEtaleConstantModuleDirectImage f A).map
    ((sfIntrinsicModuleEquivalence X A).counitIso.inv.app M)
  let z := (((sfIntrinsicModuleEquivalence Y A).inverse.map t).hom.app W) m
  let e := (sfIntrinsicDirectImageComparison f A).hom.app N
  let y := (((sfIntrinsicModuleEquivalence Y A).inverse.map e).hom.app W) z
  have h1 := sectionRealization_naturality A Y t W m
  have h2 := sectionRealization_naturality A Y e W z
  have h3 := sectionRealization_functor A Y
    ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj N) W y
  let r := sectionRealization A Y ((proEtaleConstantModuleDirectImage f A).obj M) W m
  have hc : sfIntrinsicRealizationUnit Y A
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj N) W
      (((sectionDirectImageIso A f).hom.app M).hom.app W m) =
      e.val.app W (t.val.app W r) := by
    have hδ : (sectionDirectImageIso A f).hom.app M =
        (sfIntrinsicModuleEquivalence Y A).inverse.map t ≫
          (sfIntrinsicModuleEquivalence Y A).inverse.map e ≫
            (sfIntrinsicModuleEquivalence Y A).unitIso.inv.app
              ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj N) := by
      dsimp only [sectionDirectImageIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
        Functor.associator_hom_app]
      simp only [Category.id_comp]
      rfl
    rw [hδ]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      CategoryTheory.comp_apply]
    change sfIntrinsicRealizationUnit Y A
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj N) W
      (((sfIntrinsicModuleEquivalence Y A).unitIso.inv.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj N)).hom.app W y) =
      e.val.app W (t.val.app W r)
    erw [← h3, h2, h1]
    rfl
  obtain ⟨a, ha⟩ := (scalarUnit_bijective A X N
    ((proEtaleBaseChange f).op.obj W)).surjective (t.val.app W r)
  have hn := (sfIntrinsicDirectImageComparison_existsUnique f A).exists.choose_spec N W a
  have hd : ((sectionDirectImageIso A f).hom.app M).hom.app W m = a := by
    apply (scalarUnit_bijective A Y
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj N) W).injective
    exact hc.trans ((congrArg (fun s ↦ e.val.app W s) ha.symm).trans hn)
  rw [hd]
  unfold sectionRealization
  rw [ha]
  change ((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M).val.app
      ((proEtaleBaseChange f).op.obj W)
      (((sfIntrinsicModuleEquivalence X A).counitIso.inv.app M).val.app
        ((proEtaleBaseChange f).op.obj W) r) = r
  simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    CategoryTheory.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
    CategoryTheory.id_apply, t, r, sectionRealization, Functor.id_obj,
    SheafOfModules.pushforward_map_val, PresheafOfModules.pushforward_map_app_apply,
    proEtaleConstantModuleDirectImage] using
      ConcreteCategory.congr_hom
      (congrArg (fun h ↦ h.val.app ((proEtaleBaseChange f).op.obj W))
        ((sfIntrinsicModuleEquivalence X A).counitIso.inv_hom_id_app M))
      (show M.val.obj ((proEtaleBaseChange f).op.obj W) from r)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem terminal_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleGlobalEvaluationTerminal A f =
      isoWhiskerRight (sectionDirectImageIso A f)
          (Sheaf.Γ (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≪≫
        isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
          (proEtaleUnitLerayFixedTerminalIso A f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [proEtaleGlobalEvaluationTerminal, proEtaleUnitLerayTerminalIso,
    sectionDirectImageIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Equivalence.funInvIdAssoc_hom_app, Functor.rightUnitor_hom_app,
    Functor.map_comp, Category.assoc]
  rw [← (proEtaleUnitLeraySections A Y).map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Functor.associator_hom_app, proEtaleUnitLeraySections, Functor.comp_map]
  let Γ := Sheaf.Γ (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  let N := (sfIntrinsicModuleEquivalence X A).inverse.obj M
  let F := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
  erw [Γ.map_id (((F ⋙ (sfIntrinsicModuleEquivalence Y A).functor) ⋙
    (sfIntrinsicModuleEquivalence Y A).inverse).obj N), Γ.map_id (F.obj N)]
  rfl

private def globalSectionRealization (X : Scheme.{u})
    (M : proEtaleRingModules X (proEtaleConstantRing X A))
    (m : (proEtaleUnitLeraySections A X).obj M) :
    M.val.obj (op (⊤_ X.ProEt)) :=
  sectionRealization A X M _
    ((Sheaf.ΓNatIsoSheafSections (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) terminalIsTerminal).hom.app
        ((sfIntrinsicModuleEquivalence X A).inverse.obj M) m)

set_option backward.isDefEq.respectTransparency false in
private theorem globalSectionRealization_bijective (X : Scheme.{u})
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    Function.Bijective (globalSectionRealization A X M) :=
  (sectionRealization_bijective A X M _).comp
    (ConcreteCategory.bijective_of_isIso
      ((Sheaf.ΓNatIsoSheafSections (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) terminalIsTerminal).hom.app
          ((sfIntrinsicModuleEquivalence X A).inverse.obj M)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem globalSectionRealization_naturality (X : Scheme.{u})
    {M N : proEtaleRingModules X (proEtaleConstantRing X A)} (f : M ⟶ N)
    (m : (proEtaleUnitLeraySections A X).obj M) :
    globalSectionRealization A X N ((proEtaleUnitLeraySections A X).map f m) =
      f.val.app (op (⊤_ X.ProEt)) (globalSectionRealization A X M m) := by
  unfold globalSectionRealization
  have hn := ConcreteCategory.congr_hom
    ((Sheaf.ΓNatIsoSheafSections (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) terminalIsTerminal).hom.naturality
        ((sfIntrinsicModuleEquivalence X A).inverse.map f)) m
  simp only [CategoryTheory.comp_apply] at hn
  erw [hn]
  exact sectionRealization_naturality A X f _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem terminal_normalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules X (proEtaleConstantRing X A))
    (m : (proEtaleUnitLeraySections A Y).obj
      ((proEtaleConstantModuleDirectImage f A).obj M)) :
    globalSectionRealization A X M ((proEtaleGlobalEvaluationTerminal A f).hom.app M m) =
      M.val.map (PreservesTerminal.iso (proEtaleBaseChange f)).inv.op
        (globalSectionRealization A Y ((proEtaleConstantModuleDirectImage f A).obj M) m) := by
  have hΓ : (proEtaleGlobalEvaluationTerminal A f).hom.app M ≫
      (Sheaf.ΓNatIsoSheafSections (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) terminalIsTerminal).hom.app
          ((sfIntrinsicModuleEquivalence X A).inverse.obj M) =
      (Sheaf.ΓNatIsoSheafSections (ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) terminalIsTerminal).hom.app
          ((sfIntrinsicModuleEquivalence Y A).inverse.obj
            ((proEtaleConstantModuleDirectImage f A).obj M)) ≫
        ((sectionDirectImageIso A f).hom.app M).hom.app (op (⊤_ Y.ProEt)) ≫
          ((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.map
            (PreservesTerminal.iso (proEtaleBaseChange f)).inv.op := by
    rw [terminal_eq]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      proEtaleUnitLerayFixedTerminalIso, NatIso.ofComponents_hom_app,
      Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [reassoc_of% ((Sheaf.ΓNatIsoSheafSections (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) terminalIsTerminal).hom.naturality
        ((sectionDirectImageIso A f).hom.app M))]
    rfl
  unfold globalSectionRealization
  have hv := ConcreteCategory.congr_hom hΓ m
  simp only [CategoryTheory.comp_apply] at hv
  erw [hv]
  erw [sectionRealization_restrict, sectionDirectImageIso_normalization]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem terminal_composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : proEtaleConstantModuleDirectImage f A ⋙ proEtaleConstantModuleDirectImage g A ≅
      proEtaleConstantModuleDirectImage (f ≫ g) A)
    (hd : ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : Z.ProEtᵒᵖ)
      (m : ((proEtaleConstantModuleDirectImage f A ⋙
        proEtaleConstantModuleDirectImage g A).obj M).val.obj W),
      (d.hom.app M).val.app W m =
        M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app W.unop).op m)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    (proEtaleUnitLeraySections A Z).map (d.hom.app M) ≫
        (proEtaleGlobalEvaluationTerminal A (f ≫ g)).hom.app M =
      (proEtaleGlobalEvaluationTerminal A g).hom.app
          ((proEtaleConstantModuleDirectImage f A).obj M) ≫
        (proEtaleGlobalEvaluationTerminal A f).hom.app M := by
  ext m
  apply (globalSectionRealization_bijective A X M).injective
  change globalSectionRealization A X M
      ((proEtaleGlobalEvaluationTerminal A (f ≫ g)).hom.app M
        ((proEtaleUnitLeraySections A Z).map (d.hom.app M) m)) =
    globalSectionRealization A X M
      ((proEtaleGlobalEvaluationTerminal A f).hom.app M
        ((proEtaleGlobalEvaluationTerminal A g).hom.app _ m))
  rw [terminal_normalization, globalSectionRealization_naturality, hd,
    terminal_normalization, terminal_normalization]
  change M.val.map (PreservesTerminal.iso (proEtaleBaseChange (f ≫ g))).inv.op
      (M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app (⊤_ Z.ProEt)).op _) =
    M.val.map (PreservesTerminal.iso (proEtaleBaseChange f)).inv.op
      (M.val.map ((proEtaleBaseChange f).map
        (PreservesTerminal.iso (proEtaleBaseChange g)).inv).op _)
  rw [← M.val.map_comp_apply, ← M.val.map_comp_apply, ← op_comp, ← op_comp]
  have ht : (PreservesTerminal.iso (proEtaleBaseChange (f ≫ g))).inv ≫
      (MorphismProperty.Over.pullbackComp f g).hom.app (⊤_ Z.ProEt) =
      (PreservesTerminal.iso (proEtaleBaseChange f)).inv ≫
        (proEtaleBaseChange f).map (PreservesTerminal.iso (proEtaleBaseChange g)).inv :=
    ((terminalIsTerminal.isTerminalObj (proEtaleBaseChange g)).isTerminalObj
      (proEtaleBaseChange f)).hom_ext _ _
  rw [ht]
  rfl


end SectionRealization

private def globalEvaluation_moduleComp (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantModuleDirectImage f A ⋙ proEtaleConstantModuleDirectImage g A ≅
      proEtaleConstantModuleDirectImage (f ≫ g) A :=
  isoWhiskerRight (proEtaleUnitLerayDirectImageIso A f).symm
      (proEtaleConstantModuleDirectImage g A) ≪≫
    isoWhiskerLeft (proEtaleConstantRingPushforward A f)
      (proEtaleUnitLerayDirectImageIso A g).symm ≪≫
    (proEtaleConstantRingModulePullbackComposition f g A).choose_spec.choose ≪≫
    proEtaleUnitLerayDirectImageIso A (f ≫ g)

private theorem globalEvaluation_moduleComp_mate (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (globalEvaluation_moduleComp A f g).hom =
      conjugateEquiv ((proEtaleOrdinaryModuleAdjunction A g).comp
        (proEtaleOrdinaryModuleAdjunction A f))
        (proEtaleOrdinaryModuleAdjunction A (f ≫ g))
        (proEtaleConstantRingModulePullbackComposition f g A).choose.hom := by
  rw [proEtaleOrdinaryModuleAdjunction, proEtaleOrdinaryModuleAdjunction,
    proEtaleOrdinaryModuleAdjunction, mateTransport]
  have h := congrArg Iso.hom
    (proEtaleConstantRingModulePullbackComposition f g A).choose_spec.choose_spec.2
  simp only [conjugateIsoEquiv_apply_hom] at h
  simp only [globalEvaluation_moduleComp, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  rw [h]

private theorem globalEvaluation_derivedComp (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Functor.rightDerivedFunctorCompIso' (proEtaleConstantModuleDirectImage f A)
      (proEtaleConstantModuleDirectImage g A) (globalEvaluation_moduleComp A f g)).hom =
      (proEtaleOrdinaryDirectImageComposition A f g).inv := by
  have h := Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (proEtaleOrdinaryModuleAdjunction A f) (proEtaleOrdinaryModuleAdjunction A g)
    (proEtaleOrdinaryModuleAdjunction A (f ≫ g)) (globalEvaluation_moduleComp A f g)
    (proEtaleConstantRingModulePullbackComposition f g A).choose
    (globalEvaluation_moduleComp_mate A f g)
  rw [← proEtaleConstantRingPullbackComposition_eq_mapModuleComparison] at h
  exact h

private theorem directImage_map_sections (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : proEtaleRingModules X (proEtaleConstantRing X A)} (a : M ⟶ N)
    (W : Y.ProEtᵒᵖ) (m : M.val.obj ((proEtaleBaseChange f).op.obj W)) :
    (((proEtaleConstantModuleDirectImage f A).map a).val.app W) m =
      a.val.app ((proEtaleBaseChange f).op.obj W) m := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- The coefficient transports require comparing nested pushforward module actions.
private theorem globalEvaluation_moduleComp_section (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : Z.ProEtᵒᵖ)
    (m : ((proEtaleConstantModuleDirectImage f A ⋙
      proEtaleConstantModuleDirectImage g A).obj M).val.obj W) :
    ((globalEvaluation_moduleComp A f g).hom.app M).val.app W m =
      M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app W.unop).op m := by
  dsimp only [globalEvaluation_moduleComp, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    CategoryTheory.comp_apply]
  rw [directIso_hom (f ≫ g) A M W]
  erw [directIso_inv g A ((proEtaleConstantRingPushforward A f).obj M) W]
  have hm := directImage_map_sections A g
    ((proEtaleUnitLerayDirectImageIso A f).inv.app M) W m
  erw [hm]
  erw [directIso_inv f A M ((proEtaleBaseChange g).op.obj W)]
  exact (proEtaleConstantRingModulePullbackComposition f g A).choose_spec.choose_spec.1
    M W.unop m


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem concreteComposition (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : proEtaleDerivedCategory X A) :
    (proEtaleGlobalEvaluation A (f ≫ g)).hom.app K =
      (proEtaleGlobalEvaluationSections A Z).map
          ((proEtaleOrdinaryDirectImageComposition A f g).hom.app K) ≫
        (proEtaleGlobalEvaluation A g).hom.app
          ((proEtaleConstantDerivedDirectImage f A).obj K) ≫
        (proEtaleGlobalEvaluation A f).hom.app K := by
  have h := derivedComp (proEtaleConstantModuleDirectImage f A)
    (proEtaleConstantModuleDirectImage g A) (proEtaleUnitLeraySections A Z)
    (proEtaleConstantModuleDirectImage (f ≫ g) A)
    (proEtaleUnitLeraySections A Y) (proEtaleUnitLeraySections A X)
    (globalEvaluation_moduleComp A f g) (proEtaleGlobalEvaluationTerminal A g)
    (proEtaleGlobalEvaluationTerminal A f) (proEtaleGlobalEvaluationTerminal A (f ≫ g))
    (terminal_composition A f g (globalEvaluation_moduleComp A f g)
      (globalEvaluation_moduleComp_section A f g))
  rw [globalEvaluation_derivedComp] at h
  have hh := congr_app h K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hh
  change (proEtaleGlobalEvaluationSections A Z).map
      ((proEtaleOrdinaryDirectImageComposition A f g).inv.app K) ≫
      (proEtaleGlobalEvaluation A (f ≫ g)).hom.app K =
    (proEtaleGlobalEvaluation A g).hom.app
      ((proEtaleConstantDerivedDirectImage f A).obj K) ≫
      (proEtaleGlobalEvaluation A f).hom.app K at hh
  rw [← hh, ← (proEtaleGlobalEvaluationSections A Z).map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]


private theorem globalEvaluation_identityUnit (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u})
    (eM : proEtaleIdentityTransportedInverseImage X A ≅ 𝟭 _)
    (heM : ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEt)
      (m : M.val.obj (op U)),
      (eM.inv.app M).val.app (op U) m = proEtaleIdentityModuleCoprojection X A M U m)
    (α : proEtaleConstantRingPullback A (𝟙 X) ≅ 𝟭 _)
    (hα : ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEtᵒᵖ)
      (m : M.val.obj U), (α.inv.app M).val.app U m =
        proEtaleIdentityPullbackTmul X A M U ((eM.inv.app M).val.app U m) 1) :
    whiskerRight (proEtaleOrdinaryModuleAdjunction A (𝟙 X)).unit
        (proEtaleUnitLeraySections A X) ≫
      whiskerLeft (proEtaleConstantRingPullback A (𝟙 X))
        (proEtaleGlobalEvaluationTerminal A (𝟙 X)).hom ≫
      whiskerRight α.hom (proEtaleUnitLeraySections A X) = 𝟙 _ := by
  have hu (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEt)
      (m : M.val.obj (op U)) :
      ((proEtaleConstantRingPullback A (𝟙 X)).obj M).val.map
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U).op
          (((proEtaleOrdinaryModuleAdjunction A (𝟙 X)).unit.app M).val.app (op U) m) =
        (α.inv.app M).val.app (op U) m := by
    let p := MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X
    let N := (proEtaleModuleInverseImage (𝟙 X) (proEtaleConstantRing X A)).obj M
    let z := ((SheafOfModules.pullbackPushforwardAdjunction
      (proEtaleModelRingUnit (𝟙 X) (proEtaleConstantRing X A))).unit.app
        ((proEtaleModuleToModel ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing X A))).obj M)).val.app (AsSmall.up.op.obj (op U)) m
    have hz : N.val.map (p.hom.app U).op ((eM.inv.app M).val.app (op U) m) = z := by
      rw [heM]
      change N.val.map (p.hom.app U).op (N.val.map (p.inv.app U).op z) = z
      rw [← N.val.map_comp_apply, ← op_comp, p.hom_inv_id_app, op_id]
      exact ConcreteCategory.congr_hom (N.val.map_id _) z
    have hn := PresheafOfModules.naturality_apply (eM.inv.app M).val
      (p.hom.app U).op m
    have hη : ((proEtaleOrdinaryModuleAdjunction A (𝟙 X)).unit.app M).val.app (op U) m =
        (α.inv.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj U))
          (M.val.map (p.hom.app U).op m) := by
      have hsz : (eM.inv.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj U))
          (M.val.map (p.hom.app U).op m) = z := by
        exact hn.trans hz
      rw [hα]
      change _ = proEtaleIdentityPullbackTmul X A M _
        ((eM.inv.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj U))
          (M.val.map (p.hom.app U).op m)) 1
      rw [hsz]
      change ((proEtaleUnitLerayDirectImageIso A (𝟙 X)).hom.app
          ((proEtaleConstantRingPullback A (𝟙 X)).obj M)).val.app (op U)
          (((proEtaleConstantRingAdjunction A (𝟙 X)).unit.app M).val.app (op U) m) = _
      rw [directIso_hom]
      exact proEtaleRingModuleAdjunction_normalized (𝟙 X)
        (proEtaleConstantRing X A) (proEtaleConstantRing X A)
        (proEtaleConstantRingComparison (𝟙 X) A) M U m
    rw [hη]
    have hnat := PresheafOfModules.naturality_apply (α.inv.app M).val
      (p.inv.app U).op (M.val.map (p.hom.app U).op m)
    exact hnat.symm.trans (by
      change (α.inv.app M).val.app (op U)
        (M.val.map (p.inv.app U).op (M.val.map (p.hom.app U).op m)) = _
      rw [← M.val.map_comp_apply, ← op_comp, p.inv_hom_id_app, op_id]
      exact congrArg (fun x ↦ (α.inv.app M).val.app (op U) x)
        (ConcreteCategory.congr_hom (M.val.map_id _) m))
  apply NatTrans.ext
  funext M
  ext m
  apply (globalSectionRealization_bijective A X M).injective
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.id_app, CategoryTheory.comp_apply, CategoryTheory.id_apply]
  erw [globalSectionRealization_naturality, terminal_normalization,
    globalSectionRealization_naturality]
  have hp : (PreservesTerminal.iso (proEtaleBaseChange (𝟙 X))).inv =
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app (⊤_ X.ProEt) :=
    (terminalIsTerminal.isTerminalObj (proEtaleBaseChange (𝟙 X))).hom_ext _ _
  erw [hp, hu]
  have hh := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.val.app (op (⊤_ X.ProEt))) (α.inv_hom_id_app M))
    (globalSectionRealization A X M m)
  change (α.hom.app M).val.app (op (⊤_ X.ProEt))
      ((α.inv.app M).val.app (op (⊤_ X.ProEt)) (globalSectionRealization A X M m)) = _
  change (α.hom.app M).val.app (op (⊤_ X.ProEt))
      ((α.inv.app M).val.app (op (⊤_ X.ProEt)) (globalSectionRealization A X M m)) = _ at hh
  exact hh





set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem concreteIdentity (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u}) :
    (proEtaleGlobalEvaluation A (𝟙 X)).hom =
      whiskerRight (proEtaleGlobalEvaluationDirectImageId A X).hom
        (proEtaleGlobalEvaluationSections A X) := by
  let hM := (proEtaleDerivedPullback_identity X A).choose_spec.2.2
  let eM := hM.choose
  let hα := hM.choose_spec.2
  let α := hα.choose
  let hb := hα.choose_spec.2.2
  let b := hb.choose
  let hγ := hb.choose_spec.2
  have hβ (I : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ) :
      (proEtaleGlobalEvaluationPullbackId A X).hom.app (DerivedCategory.Q.obj I) =
        (proEtaleConstantRingPullback A (𝟙 X)).mapDerivedCategoryFactors.hom.app I ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I) := by
    have hi : b.hom.app I =
        (NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I := by
      ext n : 1
      exact hb.choose_spec.1 I n
    have hh := hγ.choose_spec I
    rw [hi] at hh
    exact hh
  exact derivedIdentity _ _ _ (proEtaleOrdinaryModuleAdjunction A (𝟙 X))
    (proEtaleGlobalEvaluationTerminal A (𝟙 X)) α
    (proEtaleGlobalEvaluationPullbackId A X) hβ
    (globalEvaluation_identityUnit A X eM hM.choose_spec.1 α hα.choose_spec.2.1)


variable (P : WeilConjectures.PurityFiniteSetting.{u})
  {T Y W : Scheme.{u}}
  [T.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [W.Over (Spec (.of P.field.k))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison is the identity of final-object section complexes, through the
canonical K-injective identifications. Source: Stacks Tags 0D6H and 070Y
(blueprint: lem-pur-proetale-direct-image-global-evaluation).

Proof: specialize the canonical right-derived compositor factorization to the
K-injective complex J. Both derived units are invertible because the direct image
preserves K-injectives. Cancel them and identify the factors with the published
K-injective evaluation isomorphisms. -/
theorem proEtaleDirectImageGlobalEvaluation (f : T ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))]
    (J : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) ℤ)
    [J.IsKInjective] (_hJ : ∃ a : ℤ, J.IsStrictlyGE a) :
    (proEtaleGlobalEvaluation P.Ring f).hom.app (DerivedCategory.Q.obj J) =
      (proEtaleGlobalEvaluationSections P.Ring Y).map
          (proEtaleGlobalEvaluationImageObj P.Ring f J).hom ≫
        ((proEtaleGlobalEvaluationSectionsObj P.Ring Y)
          (((proEtaleConstantModuleDirectImage f P.Ring).mapHomologicalComplex
            (.up ℤ)).obj J)).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (proEtaleGlobalEvaluationTerminal P.Ring f).hom (.up ℤ)).app J) ≫
        ((proEtaleGlobalEvaluationSectionsObj P.Ring T) J).inv := by
  let := proEtaleRingModules_hasKInjectiveResolutions T (proEtaleConstantRing T P.Ring)
  let := proEtaleRingModules_hasKInjectiveResolutions Y (proEtaleConstantRing Y P.Ring)
  exact globalEvaluation_obj (proEtaleConstantModuleDirectImage f P.Ring)
    (proEtaleUnitLeraySections P.Ring Y) (proEtaleGlobalEvaluationTerminal P.Ring f) J
/-- Compatibility with the specified derived shift comparisons, on D^+.
Source: Stacks Tag 05SU (blueprint: lem-pur-proetale-direct-image-global-evaluation).
Proof: shift a bounded-below K-injective representative J by n. Shifts preserve
K-injectivity since Hom(M,J[n]) = Hom(M[-n],J) for acyclic M. Evaluation and direct
image act termwise, so both differentials acquire exactly the same factor (-1)^n.
The preceding resolution normalization and its transition naturality identify this
calculation with the already specified derived-functor shift comparisons. -/
theorem proEtaleDirectImageGlobalEvaluation_shift (f : T ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))]
    (L : @DerivedCategory.Plus (proEtaleRingModules T (proEtaleConstantRing T P.Ring))
      _ _ (proEtaleRingModules_hasDerivedCategory T (proEtaleConstantRing T P.Ring)))
    (n : ℤ) :
    ((proEtaleConstantDerivedDirectImage f P.Ring ⋙
        (proEtaleGlobalEvaluationSections P.Ring Y)).commShiftIso n).hom.app
          L.obj ≫ (shiftFunctor _ n).map ((proEtaleGlobalEvaluation P.Ring f).hom.app L.obj) =
      (proEtaleGlobalEvaluation P.Ring f).hom.app (L.obj⟦n⟧) ≫
        ((proEtaleGlobalEvaluationSections P.Ring T).commShiftIso n).hom.app
          L.obj := by
  let := proEtaleRingModules_hasKInjectiveResolutions T (proEtaleConstantRing T P.Ring)
  let := proEtaleRingModules_hasKInjectiveResolutions Y (proEtaleConstantRing Y P.Ring)
  have := CategoryTheory.canonical_unit_commShift
    (proEtaleConstantModuleDirectImage f P.Ring)
  have := CategoryTheory.canonical_unit_commShift (proEtaleUnitLeraySections P.Ring Y)
  have := CategoryTheory.canonical_unit_commShift (proEtaleUnitLeraySections P.Ring T)
  have h := Functor.commShift_rightDerivedFunctorCompIso'_hom
    (proEtaleConstantModuleDirectImage f P.Ring) (proEtaleUnitLeraySections P.Ring Y)
    (proEtaleGlobalEvaluationTerminal P.Ring f)
  let : NatTrans.CommShift (proEtaleGlobalEvaluation P.Ring f).hom ℤ := h
  exact NatTrans.shift_app_comm (proEtaleGlobalEvaluation P.Ring f).hom n L.obj

/-- The final-object comparison agrees with the canonical direct-image compositor.
Source: Stacks Tag 0D6E (blueprint: lem-pur-proetale-direct-image-global-evaluation).
Proof: the normalized module direct-image compositor acts by fibre-product restriction.
The two terminal restrictions agree by uniqueness of arrows to the terminal object.
The universal right-derived compositor transports this equality to derived functors.
The module-comparison localization theorem and adjunction conjugation identify its
compositor with the inverse of the specified ordinary direct-image comparison. -/
theorem proEtaleDirectImageGlobalEvaluation_comp (f : T ⟶ Y) (g : Y ⟶ W)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    (L : @DerivedCategory.Plus (proEtaleRingModules T (proEtaleConstantRing T P.Ring))
      _ _ (proEtaleRingModules_hasDerivedCategory T (proEtaleConstantRing T P.Ring))) :
    (proEtaleGlobalEvaluation P.Ring (f ≫ g)).hom.app L.obj =
      (proEtaleGlobalEvaluationSections P.Ring W).map
          ((proEtaleOrdinaryDirectImageComposition P.Ring f g).hom.app L.obj) ≫
        (proEtaleGlobalEvaluation P.Ring g).hom.app
          ((proEtaleConstantDerivedDirectImage f P.Ring).obj L.obj) ≫
        (proEtaleGlobalEvaluation P.Ring f).hom.app L.obj := by
  exact concreteComposition P.Ring f g L.obj

set_option linter.unusedSectionVars false in
/-- Identity normalization, after the canonical identity direct-image identification.
Source: Stacks Tag 0D6E (blueprint: lem-pur-proetale-direct-image-global-evaluation).
Proof: the published coprojection and tensor-unit formulas show that the ordinary
unit, terminal evaluation and identity inverse-image comparison compose to the identity.
The unit-Leray chain formula on K-injectives identifies the derived comparison with
the mate of the same localized identity comparison; naturality extends to all objects. -/
theorem proEtaleDirectImageGlobalEvaluation_id
    (L : @DerivedCategory.Plus (proEtaleRingModules T (proEtaleConstantRing T P.Ring))
      _ _ (proEtaleRingModules_hasDerivedCategory T (proEtaleConstantRing T P.Ring))) :
    (proEtaleGlobalEvaluation P.Ring (𝟙 T)).hom.app L.obj =
      (proEtaleGlobalEvaluationSections P.Ring T).map
        ((proEtaleGlobalEvaluationDirectImageId P.Ring T).hom.app L.obj) := by
  exact congr_app (concreteIdentity P.Ring T) L.obj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The open-unit composite is restriction, including its resolution map. This equation
uses an arbitrary K-injective resolution of j^*I, so it characterizes the actual derived
restriction without assuming inverse image preserves K-injectives.
Source: Stacks Tags 0DVC and 09BN
(blueprint: lem-pur-proetale-direct-image-global-evaluation).
Proof: cancel the direct-image identification and its inverse in the transported
ordinary unit followed by terminal evaluation. This gives exactly the published
unit-Leray section unit. Apply the existing unit-Leray chain formula to I, H and v.
Its representative formula is the asserted equality, without another resolution. -/
theorem proEtaleDirectImageGlobalEvaluation_open
    {U : Scheme.{u}} [U.Over (Spec (.of P.field.k))] (j : U ⟶ T)
    [j.IsOver (Spec (.of P.field.k))] [IsOpenImmersion j]
    (I : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) ℤ)
    (H : CochainComplex (proEtaleRingModules U (proEtaleConstantRing U P.Ring)) ℤ)
    [I.IsKInjective] [H.IsKInjective]
    (_hI : ∃ a : ℤ, I.IsStrictlyGE a) (_hH : ∃ a : ℤ, H.IsStrictlyGE a)
    (v : ((proEtaleConstantRingPullback P.Ring j).mapHomologicalComplex (.up ℤ)).obj I ⟶ H)
    [QuasiIso v] :
    (proEtaleGlobalEvaluationSections P.Ring T).map
        ((proEtaleOrdinaryDerivedAdjunction P.Ring j).unit.app (DerivedCategory.Q.obj I)) ≫
      (proEtaleGlobalEvaluation P.Ring j).hom.app
        ((proEtaleConstantRingDerivedPullback P.Ring j).obj (DerivedCategory.Q.obj I)) ≫
      (proEtaleGlobalEvaluationSections P.Ring U).map
        ((proEtaleConstantRingPullback P.Ring j).mapDerivedCategoryFactors.hom.app I ≫
          DerivedCategory.Q.map v) =
    ((proEtaleGlobalEvaluationSectionsObj P.Ring T) I).hom ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (proEtaleUnitLeraySectionUnit P.Ring j)
          (.up ℤ)).app I ≫
          ((proEtaleUnitLeraySections P.Ring U).mapHomologicalComplex (.up ℤ)).map v) ≫
      ((proEtaleGlobalEvaluationSectionsObj P.Ring U) H).inv := by
  let := proEtaleRingModules_hasKInjectiveResolutions T (proEtaleConstantRing T P.Ring)
  let := proEtaleRingModules_hasKInjectiveResolutions U (proEtaleConstantRing U P.Ring)
  have hunit :
      whiskerRight (proEtaleOrdinaryModuleAdjunction P.Ring j).unit
          (proEtaleUnitLeraySections P.Ring T) ≫
        whiskerLeft (proEtaleConstantRingPullback P.Ring j)
          (proEtaleGlobalEvaluationTerminal P.Ring j).hom =
      proEtaleUnitLeraySectionUnit P.Ring j := by
    apply NatTrans.ext
    funext M
    simp only [proEtaleOrdinaryModuleAdjunction, proEtaleGlobalEvaluationTerminal,
      proEtaleUnitLeraySectionUnit, Adjunction.ofNatIsoRight_unit,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← (proEtaleUnitLeraySections P.Ring T).map_comp_assoc
      ((proEtaleUnitLerayDirectImageIso P.Ring j).hom.app _)
      ((proEtaleUnitLerayDirectImageIso P.Ring j).inv.app _), Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have h := unitLerayChain (proEtaleOrdinaryModuleAdjunction P.Ring j)
    (proEtaleGlobalEvaluationTerminal P.Ring j) I H v
  rw [hunit] at h
  exact h.symm
/-- The third arrow is identified with its given sign and the given shift comparison.
Together with naturality at the first two arrows, this identifies the global-sections
triangles, in particular for a support-localization triangle.
Source: Stacks Tags 0D6H and 05SU
(blueprint: lem-pur-proetale-direct-image-global-evaluation).
Proof: use naturality of ell at the triangle's actual third morphism d. Apply the shift
compatibility above to its first vertex B. Substitution gives the displayed square,
whose shifted comparison is ell_B[1]. The first two squares are ordinary naturality.
The derived functors are triangulated, so this compares the distinguished triangles
with their existing third arrows, rather than choosing new connecting morphisms. -/
theorem proEtaleDirectImageGlobalEvaluation_third (f : T ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))]
    (B D : @DerivedCategory.Plus (proEtaleRingModules T (proEtaleConstantRing T P.Ring))
      _ _ (proEtaleRingModules_hasDerivedCategory T (proEtaleConstantRing T P.Ring)))
    (d : D.obj ⟶ B.obj⟦(1 : ℤ)⟧) :
    (proEtaleGlobalEvaluationSections P.Ring Y).map
        ((proEtaleConstantDerivedDirectImage f P.Ring).map d) ≫
      ((proEtaleConstantDerivedDirectImage f P.Ring ⋙
        (proEtaleGlobalEvaluationSections P.Ring Y)).commShiftIso (1 : ℤ)).hom.app
          B.obj ≫
      (shiftFunctor _ (1 : ℤ)).map ((proEtaleGlobalEvaluation P.Ring f).hom.app B.obj) =
    (proEtaleGlobalEvaluation P.Ring f).hom.app D.obj ≫
      (proEtaleGlobalEvaluationSections P.Ring T).map d ≫
      ((proEtaleGlobalEvaluationSections P.Ring T).commShiftIso (1 : ℤ)).hom.app
        B.obj := by
  rw [proEtaleDirectImageGlobalEvaluation_shift P f B (1 : ℤ)]
  simpa only [Functor.comp_map, Category.assoc] using
    (reassoc_of% ((proEtaleGlobalEvaluation P.Ring f).hom.naturality d))
      (((proEtaleGlobalEvaluationSections P.Ring T).commShiftIso (1 : ℤ)).hom.app B.obj)

end AlgebraicGeometry.Scheme

end
