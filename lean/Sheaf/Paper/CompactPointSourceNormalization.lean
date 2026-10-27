/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import WeilConjectures.SixFunctors.Finite.Exact
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # The section-one compact source at a closed rational point

Source: Stacks Project, Tags 03QP, 03QT, 03QU, 03FD, 0D6E, 05TD and 06XS;
blueprint thm-pur-rank-one-thom, Step 2
(blueprint: lem-pur-compact-point-source-normalization).

The restriction, counit, closed unit and section arrows are the actual canonical maps.
The comparison is characterized uniquely by the image of the constant sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale.CompactPointSource

/-- The constant coefficient sheaf, using the existing constant-sheaf functor.
Source: Stacks 03QT (blueprint: lem-pur-compact-point-source-normalization). -/
abbrev coefficients (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

/-- The published derived global-sections functor specialized to the coefficient category.
This names the specialization once, so its instance arguments are shared by all maps below.
Source: Stacks 0D6E (blueprint: lem-pur-compact-point-source-normalization). -/
def derivedSections (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  rightDerivedGlobalSections (ModuleCat.{u + 1} A) Y

/-- Degree-zero sheaves followed by the published derived-sections functor.
Source: Stacks 05TD (blueprint: lem-pur-compact-point-source-normalization). -/
def sheafDerivedSections (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  DerivedCategory.singleFunctor _ 0 ⋙ derivedSections A Y

/-- The canonical restriction of the point pushforward through the open immersion.
The pasting isomorphism identifies the fibre products, and the restriction counit
is the identity on the corresponding sections.
Source: Stacks 03QP, sectionwise direct image
(blueprint: lem-pur-compact-point-source-normalization). -/
def restrictionIso (A : Type (u + 1)) [CommRing A]
    {S U Y : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ Y) [IsOpenImmersion j] :
    (upperStar (ModuleCat.{u + 1} A) j).obj
        ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj (coefficients A S)) ≅
      (lowerStar (ModuleCat.{u + 1} A) i).obj (coefficients A S) :=
  (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).app _ ≪≫
    (openImmersionRestriction (ModuleCat.{u + 1} A) j).mapIso
      ((lowerStarComp (ModuleCat.{u + 1} A) i j).app (coefficients A S)).symm ≪≫
    asIso ((openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).counit.app
      ((lowerStar (ModuleCat.{u + 1} A) i).obj (coefficients A S)))

/-- The actual extension-by-zero counit under the canonical restriction identification.
Source: Stacks, extension-by-zero adjunction
(blueprint: lem-pur-compact-point-source-normalization). -/
def counit (A : Type (u + 1)) [CommRing A]
    {S U Y : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ Y) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (coefficients A S)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj (coefficients A S) :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).map
      (restrictionIso A i j).inv ≫
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).counit.app _

/-- The inverse-image/direct-image unit at the constant coefficient sheaf, with its
canonical constant-pullback identification.
Source: Stacks, inverse-image adjunction
(blueprint: lem-pur-compact-point-source-normalization). -/
def closedUnit (A : Type (u + 1)) [CommRing A]
    {S Y : Scheme.{u}} (k : S ⟶ Y) :
    coefficients A Y ⟶ (lowerStar (ModuleCat.{u + 1} A) k).obj (coefficients A S) :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) k).unit.app (coefficients A Y) ≫
    (lowerStar (ModuleCat.{u + 1} A) k).map
      ((constantSheafCompUpperStarIso A k).hom.app (ModuleCat.of A A))

/-- The natural augmentation from degree-zero sections to derived sections, obtained
from the published right-derived-functor unit, with the single-complex comparisons.
Source: Stacks 05TD and 0D6E
(blueprint: lem-pur-compact-point-source-normalization). -/
def sectionsAugmentation (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        ((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj F) ⟶
      (sheafDerivedSections A Y).obj F :=
  (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app _ ≫
    DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
      (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ) 0).inv.app F) ≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u + 1} A)).inv.app
      (((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (.up ℤ)).obj ((CochainComplex.singleFunctor _ 0).obj F)) ≫
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor _ 0).obj F)) ≫
    (derivedSections A Y).map
      ((DerivedCategory.quotientCompQhIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))).hom.app
          ((CochainComplex.singleFunctor _ 0).obj F)) ≫
    (derivedSections A Y).map
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app F)

/-- Send a specified module of sections to its derived-sections augmentation.
Source: Stacks 05TD (blueprint: lem-pur-compact-point-source-normalization). -/
def fromSections (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (a : ModuleCat.of A A ⟶ (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj F) :
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj (ModuleCat.of A A) ⟶
      (sheafDerivedSections A Y).obj F :=
  (DerivedCategory.singleFunctor _ 0).map a ≫ sectionsAugmentation A Y F

/-- The constant-section map into derived global sections.
Source: Stacks 05TD, constant sections and derived augmentation
(blueprint: lem-pur-compact-point-source-normalization). -/
def constantSection (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj (ModuleCat.of A A) ⟶
      (sheafDerivedSections A Y).obj (coefficients A Y) :=
  fromSections A Y (coefficients A Y)
    ((constantSheafΓAdj Y.smallEtaleTopology (ModuleCat.{u + 1} A)).unit.app
      (ModuleCat.of A A))

/-- The section-normalized arrow to the derived sections of the point pushforward.
It first takes constant sections on S, then the inverse of the canonical direct-image
sections comparison. In degree zero it sends each a to the same section a on S.
Source: Stacks 03QP, 03QT and 05TD
(blueprint: lem-pur-compact-point-source-normalization). -/
def pointSection (A : Type (u + 1)) [CommRing A]
    {S Y : Scheme.{u}} (k : S ⟶ Y) :
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj (ModuleCat.of A A) ⟶
      (sheafDerivedSections A Y).obj ((lowerStar (ModuleCat.{u + 1} A) k).obj (coefficients A S)) :=
  fromSections A Y ((lowerStar (ModuleCat.{u + 1} A) k).obj (coefficients A S))
    ((constantSheafΓAdj S.smallEtaleTopology (ModuleCat.{u + 1} A)).unit.app
        (ModuleCat.of A A) ≫
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} A) k).inv.app (coefficients A S))

/-- The specified derived compact-to-ordinary map, induced by the actual counit e.
Its source is RΓ(Y,j_!G), the compact-support object for the chosen (j,q).
Source: Stacks, extension-by-zero adjunction and Tag 0D6E
(blueprint: lem-pur-compact-point-source-normalization). -/
def derivedCounitIso (A : Type (u + 1)) [CommRing A]
    {S U Y : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ Y) [IsOpenImmersion j]
    [IsIso (counit A i j)] :
    (sheafDerivedSections A Y).obj ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
            ((lowerStar (ModuleCat.{u + 1} A) i).obj (coefficients A S))) ≅
      (sheafDerivedSections A Y).obj
        ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj (coefficients A S)) :=
  (sheafDerivedSections A Y).mapIso (asIso (counit A i j))

/-- The specified derived map RΓ(u) composed with the constant-section map η.
Source: Stacks 05TD, naturality of the augmentation
(blueprint: lem-pur-compact-point-source-normalization). -/
def unitSection (A : Type (u + 1)) [CommRing A]
    {S Y : Scheme.{u}} (k : S ⟶ Y) :
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj (ModuleCat.of A A) ⟶
      (sheafDerivedSections A Y).obj ((lowerStar (ModuleCat.{u + 1} A) k).obj (coefficients A S)) :=
  constantSection A Y ≫
    (sheafDerivedSections A Y).map (closedUnit A k)

-- Keep the formal naturality calculation abstract, so the kernel does not unfold
-- the large concrete sheafification instances while checking its coherence maps.
private def singleSectionsAugmentation
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (H : C ⥤ D) [H.Additive] (M : C) :
    (DerivedCategory.singleFunctor D 0).obj (H.obj M) ⟶
      H.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M) :=
  (DerivedCategory.singleFunctorIsoCompQ D 0).hom.app _ ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).inv.app M) ≫
    (DerivedCategory.quotientCompQhIso D).inv.app
      ((H.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M)) ≫
    H.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C _).obj ((CochainComplex.singleFunctor C 0).obj M)) ≫
    H.rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso C).hom.app
        ((CochainComplex.singleFunctor C 0).obj M)) ≫
    H.rightDerivedFunctor.map ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app M)

private def singleSectionsAugmentationNatTrans
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (H : C ⥤ D) [H.Additive] :
    H ⋙ DerivedCategory.singleFunctor D 0 ⟶
      DerivedCategory.singleFunctor C 0 ⋙ H.rightDerivedFunctor :=
  Functor.whiskerLeft H (DerivedCategory.singleFunctorIsoCompQ D 0).hom ≫
    Functor.whiskerRight
      (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).inv DerivedCategory.Q ≫
    Functor.whiskerLeft
      (CochainComplex.singleFunctor C 0 ⋙ H.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D).inv ≫
    Functor.whiskerLeft
      (CochainComplex.singleFunctor C 0 ⋙ HomotopyCategory.quotient C (.up ℤ))
      H.rightDerivedFunctorUnit ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (CochainComplex.singleFunctor C 0)
        (DerivedCategory.quotientCompQhIso C).hom) H.rightDerivedFunctor ≫
    Functor.whiskerRight (DerivedCategory.singleFunctorIsoCompQ C 0).inv H.rightDerivedFunctor

private theorem generic_sectionsAugmentation_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (H : C ⥤ D) [H.Additive] {M N : C} (f : M ⟶ N) :
    (DerivedCategory.singleFunctor D 0).map (H.map f) ≫
        singleSectionsAugmentation H N =
      singleSectionsAugmentation H M ≫
        H.rightDerivedFunctor.map ((DerivedCategory.singleFunctor C 0).map f) :=
  (singleSectionsAugmentationNatTrans H).naturality f

private theorem singleSectionsAugmentation_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (H : C ⥤ D) [H.Additive] (M : C)
    [IsIso (H.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C _).obj ((CochainComplex.singleFunctor C 0).obj M)))] :
    IsIso (singleSectionsAugmentation H M) := by
  unfold singleSectionsAugmentation
  infer_instance

private theorem sectionsAugmentation_eq_core
    (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    sectionsAugmentation A Y F =
      singleSectionsAugmentation (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)) F :=
  rfl

private theorem sectionsAugmentation_naturality
    (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)} (f : F ⟶ G) :
    (DerivedCategory.singleFunctor _ 0).map
        ((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).map f) ≫
        sectionsAugmentation A Y G =
      sectionsAugmentation A Y F ≫ (sheafDerivedSections A Y).map f := by
  rw [sectionsAugmentation_eq_core, sectionsAugmentation_eq_core]
  exact generic_sectionsAugmentation_naturality
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)) f

private theorem composite_unit_isIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (L : C ⥤ D) (G : D ⥤ E) [L.Additive] [G.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L.PreservesKInjectiveComplexes]
    [PreservesFiniteLimits (L ⋙ G)] [PreservesFiniteColimits (L ⋙ G)]
    (X : HomotopyCategory C (.up ℤ)) :
    IsIso (G.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj X)) := by
  have h : (L ⋙ G).rightDerivedFunctorUnit.app X ≫
      (Functor.rightDerivedFunctorCompIso L G).hom.app (DerivedCategory.Qh.obj X) =
      (Functor.rightDerivedFunctorCompUnit L G).app X := by
    simp [Functor.rightDerivedFunctorCompIso]
  have hi : IsIso ((Functor.rightDerivedFunctorCompUnit L G).app X) := by
    rw [← h]
    infer_instance
  dsimp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at hi
  simpa only [Category.comp_id, Category.id_comp, isIso_comp_left_iff,
    isIso_comp_right_iff] using hi

private theorem point_sections_exact
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (A : Type (u + 1)) [CommRing A] :
    PreservesFiniteColimits
      (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  have := (constantSheafΓAdj (Spec (.of Ω)).smallEtaleTopology
    (ModuleCat.{u + 1} A)).isEquivalence_right_of_isEquivalence_left
  infer_instance

private theorem point_constant_unit_isIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (A : Type (u + 1)) [CommRing A] :
    IsIso ((constantSheafΓAdj (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} A)).unit.app (ModuleCat.of A A)) := by
  infer_instance

private theorem eval_eq_res
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (D : Type*) [Category D] [HasWeakSheafify J D] [HasTerminal C]
    {T : C} (hT : IsTerminal T) (F : Sheaf J D) :
    (Sheaf.ΓNatIsoSheafSections J D hT).hom.app F = F.ΓRes (Opposite.op T) := by
  simp only [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv,
    Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  dsimp
  erw [Adjunction.homEquiv_counit]
  erw [Adjunction.homEquiv_unit]
  simp [constantSheafAdj, Adjunction.comp_unit_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem lowerStar_sections_normalization
    (A : Type (u + 1)) [CommRing A] {S Y : Scheme.{u}} (k : S ⟶ Y)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} A) k).hom.app F ≫
        (Sheaf.ΓNatIsoSheafSections _ _ (isTerminalOverPullbackObjMkId k)).hom.app F =
      (Sheaf.ΓNatIsoSheafSections _ _
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)).hom.app
          ((lowerStar (ModuleCat.{u + 1} A) k).obj F) := by
  let T := (MorphismProperty.Over.pullback @Etale ⊤ k).obj (Scheme.Etale.mk (𝟙 Y))
  let t : T ⟶ ⊤_ S.Etale := terminal.from T
  have hr : F.ΓRes (Opposite.op T) =
      F.ΓRes (Opposite.op (⊤_ S.Etale)) ≫ F.obj.map t.op :=
    (F.ΓRes_map t.op).symm
  simp only [lowerStarCompGlobalSectionsIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, NatTrans.comp_app, Iso.symm_hom, Category.assoc, eval_eq_res]
  rw [hr]
  rw [← Category.assoc ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app F),
    ← eval_eq_res _ _ terminalIsTerminal F, Iso.inv_hom_id_app, Category.id_comp]
  change _ ≫ F.obj.map (PreservesTerminal.iso k.Etale).inv.op ≫ F.obj.map t.op = _
  rw [← Functor.map_comp, ← op_comp]
  have he : t ≫ (PreservesTerminal.iso k.Etale).inv =
      k.Etale.map (terminal.from (Scheme.Etale.mk (𝟙 Y))) := by
    exact (terminalIsTerminal.isTerminalObj k.Etale).hom_ext _ _
  rw [he]
  exact (((lowerStar (ModuleCat.{u + 1} A) k).obj F).ΓRes_map
    (terminal.from (Scheme.Etale.mk (𝟙 Y))).op)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 50000 in
-- The composite adjunction compares two terminal-object evaluations.
private theorem ordinary_unit_sections
    (A : Type (u + 1)) [CommRing A] {S Y : Scheme.{u}} (k : S ⟶ Y) :
    (constantSheafΓAdj Y.smallEtaleTopology (ModuleCat.{u + 1} A)).unit.app
        (ModuleCat.of A A) ≫
        (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).map (closedUnit A k) ≫
        (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} A) k).hom.app
          (coefficients A S) =
      (constantSheafΓAdj S.smallEtaleTopology (ModuleCat.{u + 1} A)).unit.app
        (ModuleCat.of A A) := by
  let C := ModuleCat.{u + 1} A
  let M := ModuleCat.of A A
  let TY := Scheme.Etale.mk (𝟙 Y)
  let aY := constantSheafAdj Y.smallEtaleTopology C
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)
  let b := upperStarLowerStarAdjunction C k
  let aS := constantSheafAdj S.smallEtaleTopology C
    (isTerminalOverPullbackObjMkId k)
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((aY.comp b).ofNatIsoRight (NatIso.ofComponents (fun _ ↦ Iso.refl _))) aS M
  have hh : aY.unit.app M ≫
      ((sheafSections Y.smallEtaleTopology C).obj (Opposite.op TY)).map
        (closedUnit A k) = aS.unit.app M := by
    simpa [aY, aS, b, closedUnit, constantSheafCompUpperStarIso,
      Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit, Functor.map_comp] using h
  apply (cancel_mono
    ((Sheaf.ΓNatIsoSheafSections _ _ (isTerminalOverPullbackObjMkId k)).hom.app
      (coefficients A S))).1
  simp only [Category.assoc]
  rw [lowerStar_sections_normalization]
  let eY := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology C
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)
  let eS := Sheaf.ΓNatIsoSheafSections S.smallEtaleTopology C
    (isTerminalOverPullbackObjMkId k)
  let ηY := (constantSheafΓAdj Y.smallEtaleTopology C).unit.app M
  let ηS := (constantSheafΓAdj S.smallEtaleTopology C).unit.app M
  have hn := eY.hom.naturality (closedUnit A k)
  have hY := Adjunction.unit_rightAdjointUniq_hom_app
    (constantSheafΓAdj Y.smallEtaleTopology C) aY M
  have hS := Adjunction.unit_rightAdjointUniq_hom_app
    (constantSheafΓAdj S.smallEtaleTopology C) aS M
  calc
    _ = (ηY ≫ eY.hom.app (coefficients A Y)) ≫
        ((sheafSections Y.smallEtaleTopology C).obj (op TY)).map (closedUnit A k) := by
      simpa only [Category.assoc] using congrArg (fun t ↦ ηY ≫ t) hn
    _ = aY.unit.app M ≫
        ((sheafSections Y.smallEtaleTopology C).obj (op TY)).map (closedUnit A k) := by
      rw [show ηY ≫ eY.hom.app (coefficients A Y) = aY.unit.app M from hY]
    _ = aS.unit.app M := hh
    _ = ηS ≫ eS.hom.app (coefficients A S) := hS.symm

private theorem pointSection_isIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (A : Type (u + 1)) [CommRing A]
    {Y : Scheme.{u}} (k : Spec (.of Ω) ⟶ Y) [IsFinite k] :
    IsIso (pointSection A k) := by
  let L := lowerStar (ModuleCat.{u + 1} A) k
  let Γ := Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  let : PreservesFiniteColimits
      (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    point_sections_exact Ω A
  let : PreservesFiniteColimits (L ⋙ Γ) :=
    preservesFiniteColimits_of_natIso (lowerStarCompGlobalSectionsIso _ k).symm
  let : L.PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) k).preservesKInjectiveComplexes
  let K := (CochainComplex.singleFunctor _ 0).obj (coefficients A (Spec (.of Ω)))
  have hi := composite_unit_isIso L Γ ((HomotopyCategory.quotient _ _).obj K)
  have hi' : IsIso (Γ.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj
        ((CochainComplex.singleFunctor _ 0).obj (L.obj (coefficients A (Spec (.of Ω))))))) :=
    (NatTrans.isIso_app_iff_of_iso Γ.rightDerivedFunctorUnit
      ((HomotopyCategory.quotient _ _).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app
          (coefficients A (Spec (.of Ω)))))).mp hi
  have : IsIso (sectionsAugmentation A Y (L.obj (coefficients A (Spec (.of Ω))))) := by
    rw [sectionsAugmentation_eq_core]
    exact singleSectionsAugmentation_isIso Γ _
  have := point_constant_unit_isIso Ω A
  dsimp only [pointSection, fromSections]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem unitSection_eq_pointSection
    (A : Type (u + 1)) [CommRing A] {S Y : Scheme.{u}} (k : S ⟶ Y) :
    unitSection A k = pointSection A k := by
  have h : (constantSheafΓAdj Y.smallEtaleTopology (ModuleCat.{u + 1} A)).unit.app
        (ModuleCat.of A A) ≫
        (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).map (closedUnit A k) =
      (constantSheafΓAdj S.smallEtaleTopology (ModuleCat.{u + 1} A)).unit.app
        (ModuleCat.of A A) ≫
        (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} A) k).inv.app
          (coefficients A S) := by
    apply (cancel_mono
      ((lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} A) k).hom.app
        (coefficients A S))).1
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app, Category.comp_id]
    exact ordinary_unit_sections A k
  dsimp only [unitSection, constantSection, pointSection, fromSections]
  rw [Category.assoc, ← sectionsAugmentation_naturality, ← Category.assoc,
    ← Functor.map_comp, h]

/-- The closed rational point has its unique section-one-normalized derived comparison,
and the actual counit obeys the two specified map equations.
Source: Stacks 03QP, 03QT, 03QU, 03FD, 0D6E, 05TD and 06XS;
blueprint thm-pur-rank-one-thom, Step 2
(blueprint: lem-pur-compact-point-source-normalization).

Proof (postponed in stage 2).
1. The composite k=i≫j is finite since it is a closed immersion: on an affine open
it is induced by a quotient R→R/I, generated by 1 as an R-module; the empty inverse
image causes no exception (def-weil-closed-immersion, def-weil-finite-integral-morphism).
2. Choose a nonnegative injective resolution of A_S using
lem-weil-pbc-module-sheaves-enough-injectives and
lem-weil-pbc-left-exact-injective-resolution-degree-zero. Apply
lem-trf-derived-sections-finite-pushforward-modules: finite direct image is exact,
preserves injectives, and its derived-sections comparison is the termwise sections
identification Γ(Y,k_*I)=Γ(S,I).
3. By lem-weil-pbc-geometric-point-cohomology and
lem-weil-pbc-constant-sheaf-geometric-stalk, sections of A_S are A, by the actual
constant-section map, and positive cohomology vanishes. Transfer this to module
cohomology by lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison.
Thus the pointSection arrow is an isomorphism. Its inverse is β. Its degree-zero
map sends the section a to a. Uniqueness follows from
lem-weil-pbc-derived-single-fully-faithful applied to endomorphisms of A[0].
4. Naturality of the right-derived augmentation, using
lem-weil-pbc-right-derived-plus-injective and lem-kun-rgamma-unbounded-bounded,
computes H⁰(RΓ(u)η) by the actual sheaf unit: u sends each constant a on Y to the
same constant a on S. Hence H⁰(β RΓ(u)η)=id, and the same single-complex full
faithfulness upgrades this to equality in D(A).
5. For h=RΓ(e), e is assumed invertible, so h is invertible. Set λ=inv(h≫β.hom).
Then λ≫h=β.inv. Step 4 gives RΓ(u)η=β.inv, hence λ≫h=RΓ(u)η. This uses exactly
the counit of j_!⊣j⁻¹ under restrictionIso, and allows no scalar rescaling. -/
theorem compactPointSourceNormalization
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U Y : Scheme.{u}} (q : Y ⟶ Spec (.of Ω)) [IsProper q] [IsNoetherian Y]
    (j : U ⟶ Y) [IsOpenImmersion j] (i : Spec (.of Ω) ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion (i ≫ j)]
    (_hqk : (i ≫ j) ≫ q = 𝟙 (Spec (.of Ω))) [IsIso (counit A i j)] :
    ∃! β : (sheafDerivedSections A Y).obj ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj
            (coefficients A (Spec (.of Ω)))) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj (ModuleCat.of A A),
      pointSection A (i ≫ j) ≫ β.hom = 𝟙 _ ∧
      unitSection A (i ≫ j) ≫ β.hom = 𝟙 _ ∧
      inv ((derivedCounitIso A i j).hom ≫ β.hom) ≫ (derivedCounitIso A i j).hom =
        unitSection A (i ≫ j) := by
  have := pointSection_isIso Ω A (i ≫ j)
  let β := (asIso (pointSection A (i ≫ j))).symm
  refine ⟨β, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact IsIso.hom_inv_id _
  · rw [unitSection_eq_pointSection]
    exact IsIso.hom_inv_id _
  · rw [unitSection_eq_pointSection]
    change inv ((derivedCounitIso A i j).hom ≫ inv (pointSection A (i ≫ j))) ≫
      (derivedCounitIso A i j).hom = pointSection A (i ≫ j)
    simp only [IsIso.inv_comp, IsIso.inv_inv, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
  · intro β' hβ'
    apply Iso.ext
    apply (cancel_epi (pointSection A (i ≫ j))).1
    exact hβ'.1.trans (IsIso.hom_inv_id _).symm

end AlgebraicGeometry.Etale.CompactPointSource
