module

public import Sheaf.AlgebraicGeometry.SupportTriangleConstruction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.SupportsExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp

/-! # Injective support and restriction models

Source: Stacks Project, etale-cohomology.tex, Tags 09XP and 09XQ, and
sites-cohomology.tex, Tag 093X (blueprint: lem-pur-support-injective-exact-models).

The sheaf row is the published support row. The natural section comparison is
normalized by the kernel inclusion; the right comparison is the direct-image formula.
All derived models use the published right-derived units and exact factorizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStar lowerStar upperStarLowerStarAdjunction
  finiteClosedUpperShriek

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def finiteKernelIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U : Scheme.{u}} (j : U ⟶ X) :
    finiteSupportedSections A j ≅ sectionsWithSupport (ModuleCat.{u + 1} A) j :=
  NatIso.ofComponents (fun M ↦ PreservesKernel.iso ((evaluation _ _).obj M)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit) (by
      intro M N f
      apply equalizer.hom_ext
      simp only [sectionsWithSupport, PreservesKernel.iso_hom, Category.assoc,
        kernel.lift_ι]
      have hc (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
          kernelComparison (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit
              ((evaluation _ _).obj P) ≫
            kernel.ι ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app P) =
          (finiteSupportedSectionsι A j).app P :=
        kernelComparison_comp_ι _ _
      rw [hc, ← Category.assoc, hc]
      exact (finiteSupportedSectionsι A j).naturality f)

set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteShriekPreservesInjectives
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    (finiteClosedUpperShriek A i j).PreservesInjectiveObjects := by
  let e : finiteClosedUpperShriek A i j ≅ closedUpperShriek (ModuleCat.{u + 1} A) i j :=
    by
      unfold finiteClosedUpperShriek closedUpperShriek
      exact Functor.isoWhiskerRight (finiteKernelIso A j) _
  let adj := (lowerStarClosedUpperShriekAdjunction (R := A) i j hPair).ofNatIsoRight e.symm
  have : PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} A) i) := inferInstance
  exact adj.preservesInjectiveObjects_of_preservesFiniteLimits

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def openSectionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    upperStar (ModuleCat.{u + 1} A) j ⋙
        Sheaf.Γ (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A) ≅
      (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj
        (op (Scheme.ProEt.mk j)) :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _
    (Scheme.ProEt.isTerminalMkId U)) ≪≫
  Functor.isoWhiskerRight (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j)
    ((sheafSections _ _).obj (op (Scheme.ProEt.mk (𝟙 U)))) ≪≫
  NatIso.ofComponents (fun M ↦ M.obj.mapIso
    (MorphismProperty.Over.isoMk (Iso.refl U) (by simp) :
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
        (Scheme.ProEt.mk (𝟙 U)) ≅ Scheme.ProEt.mk j).symm.op) (by
      intro M N f
      exact (f.hom.naturality _).symm)

attribute [local irreducible] openSectionIso Sheaf.ΓNatIsoSheafSections
attribute [local semireducible] lowerStar

set_option backward.isDefEq.respectTransparency.types false in
private theorem openSectionIso_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app M) ≫
      (globalSectionsLowerStarIso (ModuleCat.{u + 1} A) j).hom.app
        ((upperStar (ModuleCat.{u + 1} A) j).obj M) ≫
      (openSectionIso A j).hom.app M =
    (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A) (Scheme.ProEt.isTerminalMkId X)).hom.app M ≫
      M.obj.map (MorphismProperty.Over.homMk j (Category.comp_id j) :
        Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)).op := by
  let D := ModuleCat.{u + 1} A
  let η := (upperStarLowerStarAdjunction D j).unit
  let γ := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) D
    (Scheme.ProEt.isTerminalMkId X)
  let P := (upperStar D j).obj M
  let γU := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology U) D
    (Scheme.ProEt.isTerminalMkId U)
  let V := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj
    (Scheme.ProEt.mk (𝟙 X))
  let e₀ := overPullbackObjMkIdIso j
  let t := upperStarIsoOpenImmersionRestriction D j
  let e₁ : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
      (Scheme.ProEt.mk (𝟙 U)) ≅ Scheme.ProEt.mk j :=
    MorphismProperty.Over.isoMk (Iso.refl U) (by simp)
  unfold openSectionIso globalSectionsLowerStarIso
  dsimp only [Iso.trans, Iso.symm,
    Functor.isoWhiskerLeft, Functor.isoWhiskerRight, NatTrans.comp_app,
    Functor.whiskerLeft, Functor.whiskerRight, NatIso.ofComponents, Functor.mapIso,
    Functor.whiskeringLeft, Functor.whiskeringRight, NatTrans.vcomp, Iso.refl]
  simp only [Category.assoc, Category.id_comp,
    Iso.inv_hom_id_app_assoc]
  erw [γ.hom.naturality_assoc]
  congr 1
  change (η.app M).hom.app (op (Scheme.ProEt.mk (𝟙 X))) ≫
      P.obj.map e₀.inv.op ≫
      (t.hom.app M).hom.app (op (Scheme.ProEt.mk (𝟙 U))) ≫ _ = _
  rw [(t.hom.app M).hom.naturality_assoc]
  have hu := congrArg (fun f ↦ f.hom.app (op (Scheme.ProEt.mk (𝟙 X))))
    ((upperStarLowerStarAdjunction D j).unit_leftAdjointUniq_hom_app
      (openImmersionRestrictionLowerStarAdjunction D j) M)
  change (η.app M).hom.app (op (Scheme.ProEt.mk (𝟙 X))) ≫
    (t.hom.app M).hom.app (op V) = _ at hu
  rw [← Category.assoc]
  change ((η.app M).hom.app (op (Scheme.ProEt.mk (𝟙 X))) ≫
    (t.hom.app M).hom.app (op V)) ≫ _ = _
  rw [hu]
  change M.obj.map _ ≫ M.obj.map _ ≫ M.obj.map _ = M.obj.map _
  rw [← M.obj.map_comp, ← M.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact (Scheme.ProEt.isTerminalMkId X).hom_ext _ _

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def supportSectionComponent
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj
        ((finiteClosedUpperShriek A i j ⋙ lowerStar (ModuleCat.{u + 1} A) i).obj M) ≅
      kernel (M.obj.map (MorphismProperty.Over.homMk j (Category.comp_id j) :
        Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)).op) := by
  let D := ModuleCat.{u + 1} A
  let Γ := Sheaf.Γ (Scheme.ProEt.topology X) D
  let η := (upperStarLowerStarAdjunction D j).unit
  let γ := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) D
    (Scheme.ProEt.isTerminalMkId X)
  have := finiteSupportedClosedComparison_isIso A i j hPair
  let e₀ := Γ.mapIso ((asIso (finiteSupportedClosedComparison A i j)).app M).symm
  let e₁ := Γ.mapIso (PreservesKernel.iso ((evaluation _ _).obj M) η) ≪≫
    PreservesKernel.iso Γ (η.app M)
  let e₂ := kernel.mapIso (Γ.map (η.app M))
    (M.obj.map (MorphismProperty.Over.homMk j (Category.comp_id j) :
      Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)).op)
    (γ.app M)
    ((globalSectionsLowerStarIso D j).app ((upperStar D j).obj M) ≪≫
      (openSectionIso A j).app M) (openSectionIso_unit A j M)
  exact e₀ ≪≫ e₁ ≪≫ e₂

attribute [local irreducible] supportSectionComponent

set_option backward.isDefEq.respectTransparency.types false in
private theorem supportSectionComponent_ι
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (supportSectionComponent A i j hPair M).hom ≫
        kernel.ι (M.obj.map (MorphismProperty.Over.homMk j (Category.comp_id j) :
          Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)).op) =
      (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
          ((supportModelInclusion A i j hPair).app M) ≫
        (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} A) (Scheme.ProEt.isTerminalMkId X)).hom.app M := by
  let D := ModuleCat.{u + 1} A
  let Γ := Sheaf.Γ (Scheme.ProEt.topology X) D
  let η := (upperStarLowerStarAdjunction D j).unit
  let γ := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) D
    (Scheme.ProEt.isTerminalMkId X)
  have := finiteSupportedClosedComparison_isIso A i j hPair
  let q := asIso (finiteSupportedClosedComparison A i j)
  unfold supportSectionComponent
  simp only [Iso.trans_hom, Functor.mapIso_hom, PreservesKernel.iso_hom,
    Category.assoc, kernel.mapIso_hom, kernel.lift_ι]
  have hk : kernelComparison η ((evaluation _ _).obj M) ≫ kernel.ι (η.app M) =
      (finiteSupportedSectionsι A j).app M := kernelComparison_comp_ι _ _
  have hΓ : kernelComparison (η.app M) Γ ≫ kernel.ι (Γ.map (η.app M)) =
      Γ.map (kernel.ι (η.app M)) := kernelComparison_comp_ι _ _
  rw [reassoc_of% hΓ,
    ← Γ.map_comp_assoc (kernelComparison η ((evaluation _ _).obj M)) (kernel.ι (η.app M)),
    hk]
  change Γ.map (q.inv.app M) ≫ Γ.map ((finiteSupportedSectionsι A j).app M) ≫ _ = _
  rw [← Γ.map_comp_assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def supportSectionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    (finiteClosedUpperShriek A i j ⋙ lowerStar (ModuleCat.{u + 1} A) i) ⋙
        Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ≅
      Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
        (MorphismProperty.Over.homMk j (Category.comp_id j) :
          Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)) :=
  NatIso.ofComponents (supportSectionComponent A i j hPair) (by
    intro M N f
    apply equalizer.hom_ext
    change _ ≫ (supportSectionComponent A i j hPair N).hom ≫ kernel.ι _ =
      (supportSectionComponent A i j hPair M).hom ≫ _ ≫ kernel.ι _
    rw [supportSectionComponent_ι A i j hPair N]
    change _ = (supportSectionComponent A i j hPair M).hom ≫
      kernel.map _ _ (f.hom.app _) (f.hom.app _) (f.hom.naturality _) ≫ kernel.ι _
    simp only [kernel.map, kernel.lift_ι]
    rw [reassoc_of% (supportSectionComponent_ι A i j hPair M)]
    change (Sheaf.Γ _ _).map _ ≫ _ = _
    rw [← Category.assoc, ← Functor.map_comp,
      (supportModelInclusion A i j hPair).naturality, Functor.map_comp, Category.assoc]
    exact congrArg ((Sheaf.Γ _ _).map ((supportModelInclusion A i j hPair).app M) ≫ ·)
      ((Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).hom.naturality f))

set_option backward.isDefEq.respectTransparency.types false in
private theorem supportSectionIso_ι
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (supportSectionIso A i j hPair).hom.app M ≫
        kernel.ι (M.obj.map (MorphismProperty.Over.homMk j (Category.comp_id j) :
          Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)).op) =
      (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
          ((supportModelInclusion A i j hPair).app M) ≫
        (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} A) (Scheme.ProEt.isTerminalMkId X)).hom.app M := by
  unfold supportSectionIso
  exact supportSectionComponent_ι A i j hPair M

attribute [local irreducible] supportSectionIso

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def derivedSupportComparisonIso
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory B] [EnoughInjectives C] [EnoughInjectives D] [EnoughInjectives E]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B) (S : C ⥤ B)
    [F.Additive] [G.Additive] [H.Additive] [S.Additive]
    [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects]
    (a : (F ⋙ G) ⋙ H ≅ S) :
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus ≅
      S.rightDerivedFunctorPlus :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorPlusCompIso F G).symm
      H.rightDerivedFunctorPlus ≪≫
    Functor.rightDerivedFunctorPlusCompIso' (F ⋙ G) H a

attribute [local irreducible] derivedSupportComparisonIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedSupportComparison_fac
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory B] [EnoughInjectives C] [EnoughInjectives D] [EnoughInjectives E]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B) (S : C ⥤ B)
    [F.Additive] [G.Additive] [H.Additive] [S.Additive]
    [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects]
    (a : (F ⋙ G) ⋙ H ≅ S) (K : HomotopyCategory.Plus C) :
    H.rightDerivedFunctorPlusUnit.app
        (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
      H.rightDerivedFunctorPlus.map
        (G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K)) ≫
      H.rightDerivedFunctorPlus.map
        (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K)) ≫
      (derivedSupportComparisonIso F G H S a).hom.app
          (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso a).hom.app K) ≫
        S.rightDerivedFunctorPlusUnit.app K := by
  have hfg := Functor.rightDerivedFunctorPlusCompIso_fac_app F G K
  rw [Functor.rightDerivedFunctorPlusCompUnit_app] at hfg
  have hfac := congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac (F ⋙ G) H a) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightDerivedFunctorPlusCompUnit_app] at hfac
  unfold derivedSupportComparisonIso
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerRight_app]
  rw [← H.rightDerivedFunctorPlus.map_comp_assoc]
  erw [Category.id_comp]
  rw [← H.rightDerivedFunctorPlus.map_comp_assoc, ← hfg, Category.assoc]
  erw [Iso.hom_inv_id_app, Category.comp_id]
  have hc : (Functor.mapHomotopyCategoryPlusCompIso a).hom.app K =
      (NatTrans.mapHomotopyCategoryPlus a.hom).app K := by
    apply (HomotopyCategory.Plus.ι B).map_injective
    rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
    change (Functor.mapHomotopyCategoryCompIso a (.up ℤ)).hom.app K.obj = _
    obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective K.obj
    rw [← hL]
    rfl
  rw [hc]
  let p := (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K
  have hp : p = 𝟙 _ := Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app F G K
  have hu := H.rightDerivedFunctorPlusUnit.naturality p
  simp only [Functor.comp_map, hp] at hu
  erw [CategoryTheory.Functor.map_id] at hu
  erw [CategoryTheory.Functor.map_id] at hu
  erw [CategoryTheory.Functor.map_id] at hu
  erw [CategoryTheory.Functor.map_id] at hu
  erw [Category.id_comp, Category.comp_id] at hu
  erw [← hu]
  simpa only [Category.assoc] using hfac



set_option backward.isDefEq.respectTransparency.types false in
private theorem supportModelSequence_shortExact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j))
    (I : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] :
    (supportModelSequence A i j hPair I.obj).ShortExact := by
  obtain ⟨f, g, hf, hg, w, hex⟩ := shortExact_sectionsWithSupport A i j hPair I.obj
  have hf' : f = (supportModelSequence A i j hPair I.obj).f := by
    ext n : 1
    have := finiteSupportedClosedComparison_isIso A i j hPair
    apply (cancel_epi ((finiteSupportedClosedComparison A i j).app (I.obj.X n))).1
    change _ ≫ f.f n = _ ≫
      ((asIso (finiteSupportedClosedComparison A i j)).inv.app (I.obj.X n) ≫ _)
    change (asIso (finiteSupportedClosedComparison A i j)).hom.app (I.obj.X n) ≫
      f.f n = (asIso (finiteSupportedClosedComparison A i j)).hom.app (I.obj.X n) ≫
        (asIso (finiteSupportedClosedComparison A i j)).inv.app (I.obj.X n) ≫ _
    rw [Iso.hom_inv_id_app_assoc]
    exact hf n
  have hg' : g = (supportModelSequence A i j hPair I.obj).g := by
    ext n : 1
    exact hg n
  subst f
  subst g
  exact hex

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical sheaf row is degreewise short exact, all four models are bounded
below and injective, and their section complexes compute the stated derived objects.
The existential section comparison `a` is uniquely normalized by kernel inclusion.
Its being a natural isomorphism includes compatibility with differentials and all
chain maps. The published row fixes both canonical sheaf arrows.

Source: Stacks Project, Tags 09XP, 09XQ and 093X
(blueprint: lem-pur-support-injective-exact-models).

Proof, following the six steps of the node:
1. The exact left adjoints j_!, j^*, i^*, and i_* have right adjoints j^*, j_*,
   i_*, and i^!_0. Apply lem-sp-right-adjoint-preserves-injectives, using
   lem-weil-pbc-proetale-ringed-open-closed and lem-sf-ringed-closed-kernel-adjoint.
   Additivity preserves the lower bound.
2. Apply lem-pur-support-exact. The closed unit identifies its kernel inclusion
   with f, while g is the open adjunction unit.
3. The localization of the open site identifies inverse image with slice restriction:
   the inverse-image indexing category has the initial object given by the open
   monomorphism. Use lem-weil-pbc-proetale-ringed-open-comparison and
   lem-weil-proetale-weakly-etale-localization. The direct-image formula identifies
   the unit with restriction. Tag 093X, in lem-pur-ringed-site-injective-mono-restriction,
   makes this restriction surjective on every injective term. Evaluation preserves
   kernels, giving a with its inclusion normalization and the short exact section row.
4. The module categories have enough injectives by lem-weil-pbc-ring-sheaves-grothendieck
   and lem-sp-grothendieck-enough-injectives. Apply
   lem-weil-pbc-right-derived-plus-injective to i^!_0 and j_*; exact i_* and j^*
   preserve quasi-isomorphisms by lem-weil-pbc-exact-functor-complex-cohomology.
   The bounded-below injectives are K-injective by
   lem-weil-pbc-bounded-below-injectives-kinjective; comparison with unbounded
   replacements is a homotopy equivalence by lem-weil-pbc-kinjective-hom-derived.
5. Apply the same right-derived computation to global sections of E, I and j^*I,
   and to the kernel-of-restriction functor of def-pur-support-cohomology on I.
   The natural isomorphism a identifies the two supported computations, giving e.
6. Naturality of the open unit gives the g square; restricting it to kernels gives
   the f square. Evaluation gives the section squares. The comparison a and all
   right-derived units are natural transformations, so the model identifications
   respect all chain maps without choices of splittings. -/
theorem supportInjectiveExactModels
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    ∃ a : (finiteClosedUpperShriek A i j ⋙ lowerStar (ModuleCat.{u + 1} A) i) ⋙
        Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ≅
      Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
        (MorphismProperty.Over.homMk j (Category.comp_id j) :
          Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)),
      (∀ M, a.hom.app M ≫ kernel.ι (M.obj.map
          (MorphismProperty.Over.homMk j (Category.comp_id j) :
            Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)).op) =
        (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
            ((supportModelInclusion A i j hPair).app M) ≫
          (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} A) (Scheme.ProEt.isTerminalMkId X)).hom.app M) ∧
      ∃ c : upperStar (ModuleCat.{u + 1} A) j ⋙
          Sheaf.Γ (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A) ≅
        (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj
          (op (Scheme.ProEt.mk j)),
        (∀ M, (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
            ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app M) ≫
          (globalSectionsLowerStarIso (ModuleCat.{u + 1} A) j).hom.app
            ((upperStar (ModuleCat.{u + 1} A) j).obj M) ≫ c.hom.app M =
          (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} A) (Scheme.ProEt.isTerminalMkId X)).hom.app M ≫
              M.obj.map (MorphismProperty.Over.homMk j (Category.comp_id j) :
                Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)).op) ∧
      ∃ e : (finiteClosedUpperShriek A i j).rightDerivedFunctorPlus ⋙
          (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus ⋙
          (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus ≅
        (Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
          (MorphismProperty.Over.homMk j (Category.comp_id j) :
            Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X))).rightDerivedFunctorPlus,
        ∀ (I : CochainComplex.Plus
            (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
          [∀ n : ℤ, Injective (I.obj.X n)],
          (Sheaf.Γ (Scheme.ProEt.topology X)
              (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit.app
            ((lowerStar (ModuleCat.{u + 1} A) i).mapHomotopyCategoryPlus.obj
              ((finiteClosedUpperShriek A i j).mapHomotopyCategoryPlus.obj
                ((HomotopyCategory.Plus.quotient _).obj I))) ≫
          (Sheaf.Γ (Scheme.ProEt.topology X)
              (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
            ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlusUnit.app
              ((finiteClosedUpperShriek A i j).mapHomotopyCategoryPlus.obj
                ((HomotopyCategory.Plus.quotient _).obj I))) ≫
          (Sheaf.Γ (Scheme.ProEt.topology X)
              (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
            ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus.map
              ((finiteClosedUpperShriek A i j).rightDerivedFunctorPlusUnit.app
                ((HomotopyCategory.Plus.quotient _).obj I))) ≫
          e.hom.app (DerivedCategory.Plus.Q.obj I) =
          DerivedCategory.Plus.Qh.map
            ((Functor.mapHomotopyCategoryPlusCompIso a).hom.app
              ((HomotopyCategory.Plus.quotient _).obj I)) ≫
          (Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
            (MorphismProperty.Over.homMk j (Category.comp_id j) :
              Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X))).rightDerivedFunctorPlusUnit.app
                ((HomotopyCategory.Plus.quotient _).obj I) ∧
          (supportModelSequence A i j hPair I.obj).ShortExact ∧
          (∀ n : ℤ, ((supportModelSequence A i j hPair I.obj).map
            (HomologicalComplex.eval _ (.up ℤ) n)).ShortExact) ∧
          (∀ n : ℤ, (I.obj.IsStrictlyGE n →
            (supportedSectionsComplex A i j hPair I.obj).IsStrictlyGE n ∧
            CochainComplex.IsStrictlyGE (supportCComplex A j I.obj) n ∧
            CochainComplex.IsStrictlyGE
              (((finiteClosedUpperShriek A i j).mapHomologicalComplex (.up ℤ)).obj I.obj) n ∧
            CochainComplex.IsStrictlyGE
              (((upperStar (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj I).obj) n)) ∧
          (∀ n : ℤ, Injective ((supportedSectionsComplex A i j hPair I.obj).X n) ∧
            Injective ((supportCComplex A j I.obj).X n) ∧
            Injective (((upperStar (ModuleCat.{u + 1} A) j).obj (I.obj.X n))) ∧
            Injective ((finiteClosedUpperShriek A i j).obj (I.obj.X n))) ∧
          IsIso ((finiteClosedUpperShriek A i j).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient _).obj I)) ∧
          IsIso ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlusUnit.app
            ((upperStar (ModuleCat.{u + 1} A) j).mapHomotopyCategoryPlus.obj
              ((HomotopyCategory.Plus.quotient _).obj I))) ∧
          IsIso ((Sheaf.Γ (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit.app
              ((HomotopyCategory.Plus.quotient _).obj I)) ∧
          IsIso ((Sheaf.Γ (Scheme.ProEt.topology U)
            (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit.app
              ((upperStar (ModuleCat.{u + 1} A) j).mapHomotopyCategoryPlus.obj
                ((HomotopyCategory.Plus.quotient _).obj I))) ∧
          IsIso ((Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} A)
            (MorphismProperty.Over.homMk j (Category.comp_id j) :
              Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X))).rightDerivedFunctorPlusUnit.app
                ((HomotopyCategory.Plus.quotient _).obj I)) ∧
          IsIso ((Sheaf.Γ (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit.app
              ((lowerStar (ModuleCat.{u + 1} A) i).mapHomotopyCategoryPlus.obj
                ((finiteClosedUpperShriek A i j).mapHomotopyCategoryPlus.obj
                  ((HomotopyCategory.Plus.quotient _).obj I)))) ∧
          IsIso ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlusUnit.app
            ((finiteClosedUpperShriek A i j).mapHomotopyCategoryPlus.obj
              ((HomotopyCategory.Plus.quotient _).obj I))) ∧
            (∀ n : ℤ, Function.Surjective
              ((I.obj.X n).obj.map
                (MorphismProperty.Over.homMk j (Category.comp_id j) :
                  Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)).op)) ∧
            (∀ n : ℤ, Function.Injective
                (kernel.ι ((I.obj.X n).obj.map
                  (MorphismProperty.Over.homMk j (Category.comp_id j) :
                    Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)).op)) ∧
              Function.Exact
                (kernel.ι ((I.obj.X n).obj.map
                  (MorphismProperty.Over.homMk j (Category.comp_id j) :
                    Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)).op))
                ((I.obj.X n).obj.map
                  (MorphismProperty.Over.homMk j (Category.comp_id j) :
                    Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)).op)) ∧
            (∀ (I' : CochainComplex.Plus
                (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) (t : I ⟶ I'),
              ((finiteClosedUpperShriek A i j ⋙ lowerStar (ModuleCat.{u + 1} A) i
                ).mapHomologicalComplex (.up ℤ)).map t.hom ≫
                  (supportModelSequence A i j hPair I'.obj).f =
                    (supportModelSequence A i j hPair I.obj).f ≫ t.hom ∧
              t.hom ≫ (supportModelSequence A i j hPair I'.obj).g =
                (supportModelSequence A i j hPair I.obj).g ≫
                  ((upperStar (ModuleCat.{u + 1} A) j ⋙ lowerStar (ModuleCat.{u + 1} A) j
                  ).mapHomologicalComplex (.up ℤ)).map t.hom) := by
  let D := ModuleCat.{u + 1} A
  let F := finiteClosedUpperShriek A i j
  let G := lowerStar D i
  let H := Sheaf.Γ (Scheme.ProEt.topology X) D
  let a := supportSectionIso A i j hPair
  let c := openSectionIso A j
  let : F.PreservesInjectiveObjects := finiteShriekPreservesInjectives A i j hPair
  let : G.PreservesInjectiveObjects :=
    (upperStarLowerStarAdjunction D i).preservesInjectiveObjects_of_preservesFiniteLimits
  let : (lowerStar D j).PreservesInjectiveObjects :=
    (upperStarLowerStarAdjunction D j).preservesInjectiveObjects_of_preservesFiniteLimits
  let : (upperStar D j).PreservesInjectiveObjects :=
    (openImmersionLowerShriekUpperStarAdjunction D j
      ).preservesInjectiveObjects_of_preservesFiniteLimits
  let e : F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⋙
      H.rightDerivedFunctorPlus ≅
      (Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X) D
        (MorphismProperty.Over.homMk j (Category.comp_id j) :
          Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X))).rightDerivedFunctorPlus :=
    derivedSupportComparisonIso F G H _ a
  refine ⟨a, ?_, c, openSectionIso_unit A j, e, ?_⟩
  · intro M
    exact supportSectionIso_ι A i j hPair M
  intro I hI
  have hS := supportModelSequence_shortExact A i j hPair I
  have hFinj : ∀ n : ℤ, Injective
      ((F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient _).obj I)).obj.as.X n) :=
    fun n ↦ inferInstanceAs (Injective (F.obj (I.obj.X n)))
  have hGFinj : ∀ n : ℤ, Injective
      ((G.mapHomotopyCategoryPlus.obj
        (F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient _).obj I))).obj.as.X n) :=
    fun n ↦ inferInstanceAs (Injective (G.obj (F.obj (I.obj.X n))))
  have hJinj : ∀ n : ℤ, Injective
      (((upperStar D j).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient _).obj I)).obj.as.X n) :=
    fun n ↦ inferInstanceAs (Injective ((upperStar D j).obj (I.obj.X n)))
  have hSn (n : ℤ) :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hS n
  refine ⟨?_, hS, hSn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact derivedSupportComparison_fac F G H _ a
      ((HomotopyCategory.Plus.quotient _).obj I)
  · intro n hn
    have := hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · change CochainComplex.IsStrictlyGE
        ((G.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj I.obj)) n
      infer_instance
    · change CochainComplex.IsStrictlyGE
        (((upperStar D j ⋙ lowerStar D j).mapHomologicalComplex (.up ℤ)).obj I.obj) n
      infer_instance
    · infer_instance
    · change CochainComplex.IsStrictlyGE
        (((upperStar D j).mapHomologicalComplex (.up ℤ)).obj I.obj) n
      infer_instance
  · intro n
    change Injective (G.obj (F.obj (I.obj.X n))) ∧
      Injective ((lowerStar D j).obj ((upperStar D j).obj (I.obj.X n))) ∧ _
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  · infer_instance
  · infer_instance
  · infer_instance
  · infer_instance
  · infer_instance
  · infer_instance
  · infer_instance
  · intro n
    let M := I.obj.X n
    let η := (upperStarLowerStarAdjunction D j).unit.app M
    let γ := (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) D
      (Scheme.ProEt.isTerminalMkId X)).hom.app M
    let r := M.obj.map (MorphismProperty.Over.homMk j (Category.comp_id j) :
      Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)).op
    have : IsSplitEpi η :=
      isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective D j M
    have : Epi (γ ≫ r) := by
      rw [show γ ≫ r = H.map η ≫ (globalSectionsLowerStarIso D j).hom.app
          ((upperStar D j).obj M) ≫ c.hom.app M from (openSectionIso_unit A j M).symm]
      infer_instance
    exact (ModuleCat.epi_iff_surjective r).1 (epi_of_epi γ r)
  · intro n
    let r := (I.obj.X n).obj.map
      (MorphismProperty.Over.homMk j (Category.comp_id j) :
        Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X)).op
    let S := ShortComplex.kernelSequence r
    have hs : S.Exact := S.exact_of_f_is_kernel (kernelIsKernel r)
    exact ⟨(ModuleCat.mono_iff_injective (kernel.ι r)).1 inferInstance,
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hs⟩
  · intro I' t
    constructor
    · ext n : 1
      exact (supportModelInclusion A i j hPair).naturality (t.hom.f n)
    · ext n : 1
      exact (upperStarLowerStarAdjunction D j).unit.naturality (t.hom.f n)

end AlgebraicGeometry.ProEtale
