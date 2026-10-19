/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-!
# Canonical tensor comparison for condensed module inverse image

Source: Stacks Project, Tags 03EL and 0G7D; the totalization and K-flat descent in
steps 3--7 of the open/closed internal-Hom calculation
(blueprint: def-sfb-condensed-pullback-tensor-comparison).

The coequalizer equation determines the ordinary comparison. The equation on every
summand of the total tensor complex then determines its unbounded derived comparison.
The choices below are from unique, fully normalized objects, never arbitrary isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

private theorem existsUnique_mapModComapTensorComparison
    {C : Type w₁} {D : Type w₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [BraidedCategory C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    [MonoidalCategory D] [BraidedCategory D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
    {R : C} [MonObj R] [IsCommMonObj R] {S : D} [MonObj S] [IsCommMonObj S]
    (ψ : S ⟶ F.obj R) [IsMonHom ψ] [IsIso ψ] (M N : Mod C R) :
    let r := F.mapMod R ⋙ Mod.comap ψ
    ∃! e : r.obj (M ⊗ N) ≅ r.obj M ⊗ r.obj N,
      Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) ≫ e.hom.hom =
        Mod.tensorObjπ (r.obj M) (r.obj N) := by
  let r := F.mapMod R ⋙ Mod.comap ψ
  let e := Mod.comapTensorIso ψ ((F.mapMod R).obj M) ((F.mapMod R).obj N) ≪≫
    (Mod.comap ψ).mapIso (F.mapModTensorIso M N)
  have he : Mod.tensorObjπ (r.obj M) (r.obj N) ≫ e.hom.hom =
      Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) := by
    dsimp only [r, Functor.comp_obj, e, Iso.trans_hom, Functor.mapIso_hom,
      Mod.comp_hom']
    rw [← Category.assoc, Mod.tensorπ_comapTensorIso_hom_hom]
    exact F.tensorπ_mapModTensorIso_hom_hom M N
  have hn : Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) ≫
      e.inv.hom = Mod.tensorObjπ (r.obj M) (r.obj N) := by
    rw [← Category.assoc, ← he, Category.assoc]
    change _ ≫ (e.hom ≫ e.inv).hom = _
    simp only [e.hom_inv_id, Mod.id_hom', Category.comp_id]
  refine ⟨e.symm, hn, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Mod.hom_ext
  apply (cancel_epi e.hom.hom).mp
  apply (cancel_epi (Mod.tensorObjπ (r.obj M) (r.obj N))).mp
  simp only [← Category.assoc]
  rw [he]
  simpa only [r, Iso.symm_hom, Category.assoc] using he'.trans hn.symm

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Small colimits for the total tensor complexes, obtained by universe shrinking.
Source: Stacks Tag 06YL (blueprint: def-sfb-condensed-pullback-tensor-comparison). -/
noncomputable instance supportModules_smallColimits (X : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (supportModules Λ X) :=
  hasColimitsOfSizeShrink (supportModules Λ X)

/-- Direct small-diagram colimits, using exactly the existing shrunken colimit instance.
Source: Stacks Tag 06YL (blueprint: def-sfb-condensed-pullback-tensor-comparison). -/
instance (priority := 10000) supportModules_smallDiagramColimit
    (X : Scheme.{u}) {J : Type} [Category.{0} J] (D : J ⥤ supportModules Λ X) :
    HasColimit D :=
  (supportModules_smallColimits Λ X).has_colimits_of_shape J |>.has_colimit D

/-- Existence of the coproducts defining total tensor, with no search for larger colimits.
Source: Stacks Tag 06YL (blueprint: def-sfb-condensed-pullback-tensor-comparison). -/
instance (priority := 10000) supportModules_complexHasTensor (X : Scheme.{u})
    (A B : CochainComplex (supportModules Λ X) ℤ) : HomologicalComplex.HasTensor A B :=
  fun _ ↦ (supportModules_smallColimits Λ X).has_colimits_of_shape _ |>.has_colimit _

/-- The support inverse image is the recorded extension-of-scalars inverse image, via
extension along the invertible coefficient map alpha.
Source: Stacks Tag 09AA (blueprint: def-sfb-condensed-pullback-tensor-comparison). -/
noncomputable def supportPullbackIsoUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    supportPullback Λ f ≅ upperStar Λ f :=
  Functor.isoWhiskerLeft ((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).symm

/-- The normalized ordinary tensor comparison exists uniquely as a module isomorphism.
Source: Stacks Tag 03EL (blueprint: def-sfb-condensed-pullback-tensor-comparison).
Proof: inverse image preserves the balanced-tensor coequalizer and the abelian-sheaf
tensor. Transport the action along alpha. The displayed equation is the universal
balanced bilinear generator formula, giving existence and uniqueness; the inverse is
obtained from the inverse abelian-sheaf tensor comparison. -/
theorem existsUnique_supportTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : supportModules Λ Y) :
    ∃! e : (supportPullback Λ f).obj (M ⊗ N) ≅
      (supportPullback Λ f).obj M ⊗ (supportPullback Λ f).obj N,
      Functor.LaxMonoidal.μ (ProEtale.upperStar Ab.{u + 1} f) M.X N.X ≫
        (ProEtale.upperStar Ab.{u + 1} f).map (Mod.tensorObjπ M N) ≫ e.hom.hom =
          Mod.tensorObjπ ((supportPullback Λ f).obj M) ((supportPullback Λ f).obj N) := by
  exact existsUnique_mapModComapTensorComparison
    (ProEtale.upperStar Ab.{u + 1} f) (asIso (condensedPullbackHom Λ f)).inv M N

/-- Ordinary pullback-tensor comparison, fixed by its balanced generator formula.
Source: Stacks Tag 03EL (blueprint: def-sfb-condensed-pullback-tensor-comparison). -/
noncomputable def supportTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : supportModules Λ Y) :
    (supportPullback Λ f).obj (M ⊗ N) ≅
      (supportPullback Λ f).obj M ⊗ (supportPullback Λ f).obj N :=
  Classical.choose (ExistsUnique.exists (existsUnique_supportTensorComparison Λ f M N))

private noncomputable instance supportPullbackMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (supportPullback Λ f).Monoidal := by
  unfold supportPullback
  infer_instance

private theorem supportTensorComparison_eq_δ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : supportModules Λ Y) :
    (supportTensorComparison Λ f M N).hom =
      Functor.OplaxMonoidal.δ (supportPullback Λ f) M N := by
  let F := ProEtale.upperStar Ab.{u + 1} f
  let ψ := (asIso (condensedPullbackHom Λ f)).inv
  let r := F.mapMod (condensedRingObj Λ Y) ⋙ Mod.comap ψ
  let e := (Functor.Monoidal.μIso r M N).symm
  have he : Mod.tensorObjπ (r.obj M) (r.obj N) ≫ e.inv.hom =
      Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) := by
    change Mod.tensorObjπ (r.obj M) (r.obj N) ≫
      (Mod.comapTensorIso ψ ((F.mapMod _).obj M) ((F.mapMod _).obj N) ≪≫
        (Mod.comap ψ).mapIso (F.mapModTensorIso M N)).hom.hom = _
    dsimp only [r, Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom, Mod.comp_hom']
    rw [← Category.assoc, Mod.tensorπ_comapTensorIso_hom_hom]
    exact F.tensorπ_mapModTensorIso_hom_hom M N
  have hn : Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) ≫
      e.hom.hom = Mod.tensorObjπ (r.obj M) (r.obj N) := by
    rw [← Category.assoc, ← he, Category.assoc]
    change _ ≫ (e.inv ≫ e.hom).hom = _
    simp only [e.inv_hom_id, Mod.id_hom', Category.comp_id]
  have hchoose := Classical.choose_spec
    (ExistsUnique.exists (existsUnique_supportTensorComparison Λ f M N))
  have hEq := (existsUnique_supportTensorComparison Λ f M N).unique hchoose hn
  exact congrArg Iso.hom hEq

/-- The localization square for a tensor comparison, with its tensor objects and maps
supplied explicitly. Source: Stacks Tag 0G7D
(blueprint: def-sfb-condensed-pullback-tensor-comparison). -/
def SupportTensorDescentSquare
    {C : Type w₁} {D : Type w₂} {E : Type w₃} {F : Type w₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    (Q : C ⥤ D) (Q' : E ⥤ F) (r : C ⥤ E) (s : D ⥤ F)
    (fac : Q ⋙ s ≅ r ⋙ Q') (AB : C) (rArB : E) (S : D) (T V : F)
    (μ : S ⟶ Q.obj AB) (μ' : V ⟶ Q'.obj rArB) (τ : T ⟶ V)
    (d : r.obj AB ⟶ rArB) (e : s.obj S ≅ T) : Prop :=
  s.map μ ≫ fac.hom.app AB ≫ Q'.map d = e.hom ≫ τ ≫ μ'

/-- The summand normalization, for an additive functor between monoidal categories.
Source: Stacks Tag 06YL (blueprint: def-sfb-condensed-pullback-tensor-comparison). -/
def SupportComplexTensorEquations
    {C : Type w₁} {D : Type w₂} [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (r : C ⥤ D) [r.Additive]
    (t : ∀ M N : C, r.obj (M ⊗ N) ⟶ r.obj M ⊗ r.obj N)
    (A B : CochainComplex C ℤ)
    (d : (r.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj A B) ⟶
      HomologicalComplex.tensorObj ((r.mapHomologicalComplex (.up ℤ)).obj A)
        ((r.mapHomologicalComplex (.up ℤ)).obj B)) : Prop :=
  ∀ (p q n : ℤ) (h : p + q = n),
    r.map (HomologicalComplex.ιTensorObj A B p q n h) ≫ d.f n =
      t (A.X p) (B.X q) ≫
        HomologicalComplex.ιTensorObj ((r.mapHomologicalComplex (.up ℤ)).obj A)
          ((r.mapHomologicalComplex (.up ℤ)).obj B) p q n h

/-- The summand equations specialized to the canonical ordinary pullback comparison.
Source: Stacks Tag 06YL (blueprint: def-sfb-condensed-pullback-tensor-comparison). -/
def SupportComplexTensorNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (supportModules Λ Y) ℤ)
    (d : ((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.tensorObj A B) ⟶
      HomologicalComplex.tensorObj
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A)
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj B)) : Prop :=
  SupportComplexTensorEquations (supportPullback Λ f)
    (fun M N ↦ (supportTensorComparison Λ f M N).hom) A B d

/-- The summand comparisons determine a unique chain map.
Source: Stacks Tag 06YL (blueprint: def-sfb-condensed-pullback-tensor-comparison).
Proof: inverse image preserves the coproduct over p+q=n. Define the component by the
ordinary tensor comparison on each summand. Naturality with respect to both differentials
and additivity give the chain-map equation with its usual sign. The coproduct universal
property proves uniqueness degree by degree. -/
theorem existsUnique_supportComplexTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (supportModules Λ Y) ℤ) :
    ∃! d : ((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.tensorObj A B) ⟶
      HomologicalComplex.tensorObj
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A)
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj B),
      SupportComplexTensorNormalization Λ f A B d := by
  let r := supportPullback Λ f
  let : PreservesColimitsOfSize.{0, 0} r :=
    (supportPullbackAdjunction Λ f).leftAdjoint_preservesColimits
  let d := HomologicalComplex.mapBifunctorComparison
    (Functor.OplaxMonoidal.δNatTrans r) (.up ℤ) A B
  have hd : ∀ (p q n : ℤ) (h : p + q = n),
      r.map (HomologicalComplex.ιTensorObj A B p q n h) ≫ d.f n =
        (supportTensorComparison Λ f (A.X p) (B.X q)).hom ≫
          HomologicalComplex.ιTensorObj
            ((r.mapHomologicalComplex (.up ℤ)).obj A)
            ((r.mapHomologicalComplex (.up ℤ)).obj B) p q n h := by
    intro p q n h
    rw [supportTensorComparison_eq_δ]
    exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      (Functor.OplaxMonoidal.δNatTrans r) (.up ℤ) A B p q n h
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map r
  intro p q h
  exact (hd' p q n h).trans (hd p q n h).symm

/-- The total-complex comparison fixed by its ordinary tensor summands.
Source: Stacks Tag 06YL (blueprint: def-sfb-condensed-pullback-tensor-comparison). -/
noncomputable def supportComplexTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (supportModules Λ Y) ℤ) :
    ((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.tensorObj A B) ⟶
      HomologicalComplex.tensorObj
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A)
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj B) :=
  Classical.choose (ExistsUnique.exists (existsUnique_supportComplexTensorComparison Λ f A B))

/-- The type of candidate derived pullback tensor comparison families.
Source: Stacks Tag 0G7D (blueprint: def-sfb-condensed-pullback-tensor-comparison). -/
def SupportDerivedTensorComparisonFamily {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ∀ K M : DerivedCategory (supportModules Λ Y),
    (supportPullback Λ f).mapDerivedCategory.obj (((derivedTensor Λ Y).obj K).obj M) ≅
      ((derivedTensor Λ X).obj ((supportPullback Λ f).mapDerivedCategory.obj K)).obj
        ((supportPullback Λ f).mapDerivedCategory.obj M)

/-- Naturality and the localization square on total-complex representatives.
Source: Stacks Tags 06YL and 0G7D
(blueprint: def-sfb-condensed-pullback-tensor-comparison).
The tensor maps are those of the existing derivedTensor functors and lax localization. -/
def SupportDerivedTensorNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : SupportDerivedTensorComparisonFamily Λ f) : Prop :=
  (∀ (K K' M M' : DerivedCategory (supportModules Λ Y)) (a : K ⟶ K') (b : M ⟶ M'),
    (supportPullback Λ f).mapDerivedCategory.map
        (((derivedTensor Λ Y).map a).app M ≫ ((derivedTensor Λ Y).obj K').map b) ≫
        (e K' M').hom =
      (e K M).hom ≫
        ((derivedTensor Λ X).map ((supportPullback Λ f).mapDerivedCategory.map a)).app
          ((supportPullback Λ f).mapDerivedCategory.obj M) ≫
        ((derivedTensor Λ X).obj ((supportPullback Λ f).mapDerivedCategory.obj K')).map
          ((supportPullback Λ f).mapDerivedCategory.map b)) ∧
  ∀ A B : CochainComplex (supportModules Λ Y) ℤ,
    SupportTensorDescentSquare
      (DerivedCategory.Q (C := supportModules Λ Y))
      (DerivedCategory.Q (C := supportModules Λ X))
      ((supportPullback Λ f).mapHomologicalComplex (.up ℤ))
      (supportPullback Λ f).mapDerivedCategory
      (supportPullback Λ f).mapDerivedCategoryFactors
      (HomologicalComplex.tensorObj A B)
      (HomologicalComplex.tensorObj
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A)
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj B))
      (((derivedTensor Λ Y).obj (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B))
      (((derivedTensor Λ X).obj
        ((supportPullback Λ f).mapDerivedCategory.obj (DerivedCategory.Q.obj A))).obj
          ((supportPullback Λ f).mapDerivedCategory.obj (DerivedCategory.Q.obj B)))
      (((derivedTensor Λ X).obj
        (DerivedCategory.Q.obj
          (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A))).obj
        (DerivedCategory.Q.obj
          (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj B)))
      (@Functor.LaxMonoidal.μ _ _ _ _ _ _
        (DerivedCategory.Q (C := supportModules Λ Y)) (laxMonoidal_Q Λ Y) A B)
      (@Functor.LaxMonoidal.μ _ _ _ _ _ _
        (DerivedCategory.Q (C := supportModules Λ X)) (laxMonoidal_Q Λ X)
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A)
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj B))
      (((derivedTensor Λ X).map
        ((supportPullback Λ f).mapDerivedCategoryFactors.hom.app A)).app
          ((supportPullback Λ f).mapDerivedCategory.obj (DerivedCategory.Q.obj B)) ≫
        ((derivedTensor Λ X).obj
          (DerivedCategory.Q.obj
            (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A))).map
          ((supportPullback Λ f).mapDerivedCategoryFactors.hom.app B))
      (supportComplexTensorComparison Λ f A B)
      (e (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B))

/-- The normalized derived comparison exists uniquely.
Source: Stacks Tags 03EL, 06YS and 0G7D
(blueprint: def-sfb-condensed-pullback-tensor-comparison).
Proof: sum the ordinary comparison over p+q=n. Naturality intertwines the two
differentials, including (-1)^p on the second. Inverse image preserves coproducts,
flat terms and K-flat resolutions. Compute both sides on these resolutions; the
summand maps give an isomorphism. Descend along the two K-flat localization
equivalences. The localization tensor maps give the displayed square on arbitrary
complexes. Its restriction to K-flat pairs, where those maps are invertible, determines
every component uniquely; the factorization isomorphisms extend this to all objects. -/
theorem existsUnique_supportDerivedTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : SupportDerivedTensorComparisonFamily Λ f,
      SupportDerivedTensorNormalization Λ f e := by
  sorry

/-- Derived pullback-tensor comparison with the specified total-complex normalization.
Source: Stacks Tag 0G7D (blueprint: def-sfb-condensed-pullback-tensor-comparison). -/
noncomputable def supportDerivedTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SupportDerivedTensorComparisonFamily Λ f :=
  Classical.choose (ExistsUnique.exists (existsUnique_supportDerivedTensorComparison Λ f))

end AlgebraicGeometry.ProEtale.CondensedRing
