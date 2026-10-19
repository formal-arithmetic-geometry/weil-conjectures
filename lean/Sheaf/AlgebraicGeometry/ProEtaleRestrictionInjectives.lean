/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Pro-etale restriction preserves injectives

Source: Weil conjectures blueprint, `sec-proper-base-change/sk-thm-properbasechange`,
node `lem-weil-pbc-proetale-restriction-injectives`
(blueprint: lem-weil-pbc-proetale-restriction-injectives).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Restriction adds maps sectionwise, so its map-add field is reflexivity.
Source: blueprint node `lem-weil-pbc-proetale-restriction-injectives`, proof step 2
(blueprint: lem-weil-pbc-proetale-restriction-injectives). -/
instance proEtaleLocalizationRestriction_additive {X Y : Scheme.{u}} (f : Y ⟶ X)
    (h : WeaklyEtale f) (Λ : Type (u + 1)) [Ring Λ] :
    (ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) f h).Additive where
  map_add := rfl

/-- The composite of restriction and terminal evaluation adds morphisms sectionwise.
Source: blueprint node `lem-weil-pbc-proetale-restriction-injectives`, proof step 4
(blueprint: lem-weil-pbc-proetale-restriction-injectives). -/
instance proEtaleLocalizationGlobalSections_additive {X Y : Scheme.{u}} (f : Y ⟶ X)
    (h : WeaklyEtale f) (Λ : Type (u + 1)) [Ring Λ] :
    (ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) f h ⋙
      ProEtale.globalSectionsFunctor (ModuleCat.{u + 1} Λ) Y).Additive where
  map_add := rfl

/-- The sectionwise comparison evaluates restriction at the identity of `W`.
Its components are the sheaf maps along the canonical identity-underlying-scheme
isomorphism from `W` to the image of that terminal object under composition with `W.hom`.
Source: blueprint node `lem-weil-pbc-proetale-restriction-injectives`, proof step 4;
Stacks Project, `proetale.tex`, small-site localization and derived sections
(blueprint: lem-weil-pbc-proetale-restriction-injectives). -/
noncomputable def proEtaleLocalizationSectionsIso {X : Scheme.{u}} (W : X.ProEt)
    (Λ : Type (u + 1)) [Ring Λ] :
    ProEtale.sectionsFunctor (ModuleCat.{u + 1} Λ) W ≅
      ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop ⋙
        ProEtale.globalSectionsFunctor (ModuleCat.{u + 1} Λ) W.left :=
  let e : W ≅ (MorphismProperty.Over.map ⊤ W.prop).obj
      (MorphismProperty.Over.mk ⊤ (𝟙 W.left) (MorphismProperty.id_mem _ W.left)) :=
    MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _)
  NatIso.ofComponents (fun G ↦ G.obj.mapIso e.op)
    (fun φ ↦ (φ.hom.naturality e.inv.op).symm)

/-- Localization at any weakly etale object identifies the sites. Restriction of left
constant-coefficient module sheaves is exact, preserves injectives, and identifies
unbounded derived evaluation with derived global sections after derived restriction.
The last equation specifies the comparison by the sectionwise identification and the
units of the total right derived functors; thus it is the canonical comparison.

Source: blueprint node `lem-weil-pbc-proetale-restriction-injectives`, order 1280;
Stacks Project, `proetale.tex`, small site; `sites-cohomology.tex`, cohomology of an open
(blueprint: lem-weil-pbc-proetale-restriction-injectives).

Proof plan:
1. Compose weakly etale maps (`lem-weil-pbc-ind-etale-stability`). Conversely use
   `WeaklyEtale.of_comp` (`lem-trf-weakly-etale-between-objects`). These inverse assignments
   keep the underlying schemes and morphisms. The fpqc finite-affine covering condition
   is unchanged, giving the slice equivalence with coverings and terminal object.
2. Restrict the constant coefficient presheaf and sheafify on the slice; its ring sheaf
   is the same constant ring sheaf on `W`. For finite coefficients this is also the
   continuous-functions presentation of `def-weil-pbc-proetale-modules`, via its recorded
   realization. Form the sum indexed by lifts using `def-weil-extension-by-zero-presheaf`
   and sheafify (`def-weil-presheaf-modules-sheafification`). Maps out of the sum are
   exactly maps to restriction, giving the adjunction. The etale special case is
   `def-weil-pbc-etale-sum-extension`; no etale hypothesis is imposed here.
3. `lem-weil-pbc-site-restriction-injectives` gives exactness of the underlying abelian
   extension and restriction. Kernels and sheafified cokernels of modules are detected
   after forgetting the action (`def-weil-sheaf-of-modules-category`). Thus the module
   functors are exact, for any ring. Apply `lem-sp-right-adjoint-preserves-injectives`
   to extension left adjoint to restriction, without forgetting injectivity.
4. Use `lem-weil-pbc-ring-sheaves-grothendieck` and
   `lem-weil-pbc-kinjective-functorial-existence` for an unbounded K-injective resolution.
   Exactness makes its restricted augmentation a quasi-isomorphism, and
   `lem-weil-pbc-right-adjoint-preserves-kinjective` makes the restriction K-injective.
   In each integer degree, evaluating at the terminal slice object is evaluation at `W`;
   the same identity holds on differentials, chain maps, and homotopies. By
   `lem-weil-pbc-kinjective-hom-derived` this descends to the canonical natural derived
   comparison, characterized by the displayed unit equation, independently of resolutions.
   For commutative rings it is the ordinary uncompleted operation of
   `def-weil-pbc-proetale-operations`. No boundedness assumption is used. -/
theorem proEtale_restriction_injectives (X : Scheme.{u}) (W : X.ProEt)
    (Λ : Type (u + 1)) [Ring Λ] :
    (∃ e : Over W ≌ W.left.ProEt,
      (∀ T : Over W, (e.functor.obj T).left = T.left.left) ∧
      (∀ T : Over W, HEq (e.functor.obj T).hom T.hom.left) ∧
      (∀ (T T' : Over W) (f : T ⟶ T'), HEq (e.functor.map f).left f.left.left) ∧
      (∀ V : W.left.ProEt, (e.inverse.obj V).left.left = V.left) ∧
      (∀ V : W.left.ProEt, HEq (e.inverse.obj V).hom.left V.hom) ∧
      (∀ (V V' : W.left.ProEt) (f : V ⟶ V'), HEq (e.inverse.map f).left.left f.left) ∧
      (∀ (V : W.left.ProEt) (S : Sieve V),
        S ∈ Scheme.ProEt.topology W.left V ↔
          S.functorPushforward e.inverse ∈ (Scheme.ProEt.topology X).over W
            (e.inverse.obj V))) ∧
    (PreservesFiniteLimits
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop)) ∧
    (PreservesFiniteColimits
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop)) ∧
    (∀ (I : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
      (_ : Injective I),
      Injective ((ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop).obj I)) ∧
    (∃ α : (ProEtale.sectionsFunctor (ModuleCat.{u + 1} Λ) W).rightDerivedFunctor ≅
        (ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop).rightDerivedFunctor ⋙
          (ProEtale.globalSectionsFunctor (ModuleCat.{u + 1} Λ) W.left).rightDerivedFunctor,
      (ProEtale.sectionsFunctor (ModuleCat.{u + 1} Λ) W).rightDerivedFunctorUnit ≫
          Functor.whiskerLeft DerivedCategory.Qh α.hom =
        Functor.whiskerRight
            (NatTrans.mapHomotopyCategory (proEtaleLocalizationSectionsIso W Λ).hom
              (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
          Functor.rightDerivedFunctorCompUnit
            (ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop)
            (ProEtale.globalSectionsFunctor (ModuleCat.{u + 1} Λ) W.left)) := by
  -- The concrete slice equivalence already fixes every underlying scheme and arrow.
  have hs := Scheme.ProEt.sliceDense X W
  let e := Scheme.ProEt.sliceEquiv X W
  have he : ∃ e : Over W ≌ W.left.ProEt,
      (∀ T : Over W, (e.functor.obj T).left = T.left.left) ∧
      (∀ T : Over W, HEq (e.functor.obj T).hom T.hom.left) ∧
      (∀ (T T' : Over W) (f : T ⟶ T'), HEq (e.functor.map f).left f.left.left) ∧
      (∀ V : W.left.ProEt, (e.inverse.obj V).left.left = V.left) ∧
      (∀ V : W.left.ProEt, HEq (e.inverse.obj V).hom.left V.hom) ∧
      (∀ (V V' : W.left.ProEt) (f : V ⟶ V'), HEq (e.inverse.map f).left.left f.left) ∧
      (∀ (V : W.left.ProEt) (S : Sieve V),
        S ∈ Scheme.ProEt.topology W.left V ↔
          S.functorPushforward e.inverse ∈ (Scheme.ProEt.topology X).over W
            (e.inverse.obj V)) := by
    refine ⟨e, (fun _ ↦ rfl), (fun _ ↦ HEq.rfl), (fun _ _ _ ↦ HEq.rfl),
      (fun _ ↦ rfl), (fun _ ↦ HEq.rfl), (fun _ _ _ ↦ HEq.rfl), ?_⟩
    intro V S
    exact (e.inverse.functorPushforward_mem_iff
      (Scheme.ProEt.topology W.left) ((Scheme.ProEt.topology X).over W)).symm
  -- Work directly with module-valued sheaves, including noncommutative coefficients.
  let A := ModuleCat.{u + 1} Λ
  let F := ProEtale.localizationRestriction A W.hom W.prop
  let G := ProEtale.globalSectionsFunctor A W.left
  let J := MorphismProperty.Over.map ⊤ W.prop
  have hJ : J.IsContinuous (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap W.prop
  have hFa : F.Additive := proEtaleLocalizationRestriction_additive W.hom W.prop Λ
  let L := Functor.sheafPullbackConstruction.sheafPullback J A
    (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology X)
  let adj : L ⊣ F := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous J A
    (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology X)
  have hF : PreservesFiniteLimits F := by
    dsimp [F, ProEtale.localizationRestriction]
    infer_instance
  have hFc : PreservesFiniteColimits F := by
    have := (ProEtale.localizationRestrictionLowerStarAdjunction A W.hom W.prop).isLeftAdjoint
    exact inferInstance
  -- This Kan extension is a sum over lifts; no monomorphism assumption is needed.
  have hlan := SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian A
    (P := @WeaklyEtale) W.prop
  have hL : PreservesFiniteLimits L :=
    comp_preservesFiniteLimits (sheafToPresheaf _ A) (J.op.lan ⋙ presheafToSheaf _ A)
  have hLa : L.Additive := adj.left_adjoint_additive
  have hLc := adj.isLeftAdjoint
  have hK : F.PreservesKInjectiveComplexes := adj.preservesKInjectiveComplexes
  refine ⟨he, hF, hFc, ?_, ?_⟩
  · intro I hI
    exact Functor.PreservesInjectiveObjects.injective_obj (F := F) hI
  · -- Derive the sectionwise comparison and use the unbounded composition theorem.
    refine ⟨Functor.rightDerivedFunctorNatIso (proEtaleLocalizationSectionsIso W Λ) ≪≫
      Functor.rightDerivedFunctorCompIso F G, ?_⟩
    simp only [Iso.trans_hom, Functor.whiskerLeft_comp, ← Category.assoc]
    simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
      Functor.rightDerivedFunctorCompIso, Functor.rightDerivedUnique, F, G, A]

end AlgebraicGeometry
