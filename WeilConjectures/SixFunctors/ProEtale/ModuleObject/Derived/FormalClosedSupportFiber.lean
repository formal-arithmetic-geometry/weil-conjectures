/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteLocallyProjective
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructureAux

/-!
# Fibre-first sections with support in a closed subscheme

Source: blueprint, `sk-lem-formal-closed-support`, statement (1)--(2), and its proof
paragraphs Adjunction, Comparison with the fibre, and The stratum formula
(blueprint: sk-lem-formal-closed-support).

A natural distinguished fibre triangle specifies the fibre of the canonical open
restriction unit. Its closed inverse image is the functor R in the statement. The
comparison with the right derived sheaf-support functor is a conclusion. No functor
is defined by choosing data from an unproved existence assertion.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing


private noncomputable def supportGlobalSectionsIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (lowerStar Λ f).rightDerivedFunctor ⋙
        (preadditiveCoyoneda.obj (op (Mod.regular (condensedRingObj Λ X)))).rightDerivedFunctor ≅
      (preadditiveCoyoneda.obj (op (Mod.regular (condensedRingObj Λ Y)))).rightDerivedFunctor := by
  have : (lowerStar Λ f).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes
  let e : lowerStar Λ f ⋙ preadditiveCoyoneda.obj
      (op (Mod.regular (condensedRingObj Λ X))) ≅
      preadditiveCoyoneda.obj (op (Mod.regular (condensedRingObj Λ Y))) :=
    (Adjunction.preadditiveCoyonedaObjIso (upperStarLowerStarAdjunction Λ f)
      (Mod.regular (condensedRingObj Λ X))).symm ≪≫
      (preadditiveCoyoneda.mapIso (upperStarRegularIso Λ f).op).symm
  exact Functor.rightDerivedFunctorCompIso' _ _ e

set_option maxHeartbeats 8000000 in
-- The nested derived functors require additional elaboration heartbeats.
private theorem supportClosedGlobalHomIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z V X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : V ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    let := closedSupport_lowerStarExact Λ i j hij
    Nonempty ((lowerStar Λ i).mapDerivedCategory.op ⋙ derivedHom Λ X ⋙
        (Functor.whiskeringRight _ _ _).obj
          (preadditiveCoyoneda.obj
            (op (Mod.regular (condensedRingObj Λ X)))).rightDerivedFunctor ≅
      derivedHom Λ Z ⋙
        (Functor.whiskeringRight _ _ _).obj
          (preadditiveCoyoneda.obj
            (op (Mod.regular (condensedRingObj Λ Z)))).rightDerivedFunctor ⋙
        (Functor.whiskeringLeft _ _ _).obj (closedSupport Λ i j).rightDerivedFunctor) := by
  let := closedSupport_lowerStarExact Λ i j hij
  let ΓX := (preadditiveCoyoneda.obj
    (op (Mod.regular (condensedRingObj Λ X)))).rightDerivedFunctor
  let ΓZ := (preadditiveCoyoneda.obj
    (op (Mod.regular (condensedRingObj Λ Z)))).rightDerivedFunctor
  let eΓ : (lowerStar Λ i).mapDerivedCategory ⋙ ΓX ≅ ΓZ :=
    Functor.isoWhiskerRight (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.symm ΓX ≪≫
      supportGlobalSectionsIso Λ i
  obtain ⟨p, o, c, hp, ho, hc, hn, hcn⟩ := openClosedInternalHomFormulas Λ i j hij
  let e (P : (DerivedCategory (supportModules Λ Z))ᵒᵖ) :
      (derivedHom Λ X).obj ((lowerStar Λ i).mapDerivedCategory.op.obj P) ⋙ ΓX ≅
        (closedSupport Λ i j).rightDerivedFunctor ⋙ (derivedHom Λ Z).obj P ⋙ ΓZ :=
    NatIso.ofComponents (fun K ↦ ΓX.mapIso (c P.unop K) ≪≫
      eΓ.app (((derivedHom Λ Z).obj P).obj
        ((closedSupport Λ i j).rightDerivedFunctor.obj K))) (by
      intro K K' f
      have h := hcn P.unop P.unop K K' (𝟙 _) f
      rw [(lowerStar Λ i).mapDerivedCategory.map_id, op_id,
        (derivedHom Λ X).map_id, NatTrans.id_app, Category.id_comp, op_id,
        (derivedHom Λ Z).map_id, NatTrans.id_app, Category.id_comp] at h
      have h' : ((derivedHom Λ X).obj ((lowerStar Λ i).mapDerivedCategory.op.obj P)).map f ≫
          (c P.unop K').hom = (c P.unop K).hom ≫
          (lowerStar Λ i).mapDerivedCategory.map
            (((derivedHom Λ Z).obj P).map ((closedSupport Λ i j).rightDerivedFunctor.map f)) := by
        change ((derivedHom Λ X).obj ((lowerStar Λ i).mapDerivedCategory.op.obj P)).map f ≫
          (c P.unop K').hom = (c P.unop K).hom ≫
          (lowerStar Λ i).mapDerivedCategory.map
            (((derivedHom Λ Z).obj P).map ((closedSupport Λ i j).rightDerivedFunctor.map f)) at h
        exact h
      dsimp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom]
      rw [← Category.assoc, ← ΓX.map_comp, h', ΓX.map_comp, Category.assoc]
      simpa only [Functor.comp_map, Category.assoc, Iso.app_hom] using congrArg (ΓX.map (c P.unop K).hom ≫ ·)
        (eΓ.hom.naturality (((derivedHom Λ Z).obj P).map
          ((closedSupport Λ i j).rightDerivedFunctor.map f))))
  refine ⟨NatIso.ofComponents e ?_⟩
  intro P P' f
  ext K
  have h := hcn P.unop P'.unop K K f.unop (𝟙 _)
  rw [((derivedHom Λ X).obj _).map_id, Category.comp_id,
    (closedSupport Λ i j).rightDerivedFunctor.map_id,
    ((derivedHom Λ Z).obj _).map_id, Category.comp_id] at h
  have h' : ((derivedHom Λ X).map ((lowerStar Λ i).mapDerivedCategory.op.map f)).app K ≫
      (c P'.unop K).hom = (c P.unop K).hom ≫
      (lowerStar Λ i).mapDerivedCategory.map
        (((derivedHom Λ Z).map f).app
          ((closedSupport Λ i j).rightDerivedFunctor.obj K)) := by
    change ((derivedHom Λ X).map ((lowerStar Λ i).mapDerivedCategory.op.map f)).app K ≫
      (c P'.unop K).hom = (c P.unop K).hom ≫
      (lowerStar Λ i).mapDerivedCategory.map
        (((derivedHom Λ Z).map f).app
          ((closedSupport Λ i j).rightDerivedFunctor.obj K)) at h
    exact h
  change ΓX.map _ ≫ (ΓX.map (c P'.unop K).hom ≫ eΓ.hom.app _) =
    (ΓX.map (c P.unop K).hom ≫ eΓ.hom.app _) ≫ ΓZ.map _
  rw [← Category.assoc, ← ΓX.map_comp, h', ΓX.map_comp, Category.assoc]
  have hn := eΓ.hom.naturality (((derivedHom Λ Z).map f).app
    ((closedSupport Λ i j).rightDerivedFunctor.obj K))
  simpa only [Functor.comp_map, Category.assoc, Iso.app_hom, Opposite.unop_op] using
    congrArg (ΓX.map (c P.unop K).hom ≫ ·) hn

set_option maxHeartbeats 8000000 in
-- The nested derived functors require additional elaboration heartbeats.
/-- The fibre-defined local cohomology is the right derived sheaf-support functor,
with its derived global Hom adjunction and finite locally projective stratum formula.
Source: blueprint `sk-lem-formal-closed-support`, statement (1)--(2)
(blueprint: sk-lem-formal-closed-support).

The existential F, inclusion and boundary present the natural fibre of the specified
unit, rather than an unspecified map K -> Rj_*j^*K. The composite
`F ⋙ (upperStar Λ i).mapDerivedCategory` is the fibre followed by the recorded exact i^*.
The first comparison therefore asserts that this
fibre-defined R is R of `closedSupport Λ i j`, the recorded definition
`supportKernel Λ j ⋙ supportPullback Λ i` of i^* ker(id -> j_*j^*). Its existing
`closedSupport_additive` instance supplies additivity without a theorem-node dependency.
Global sections are Hom from the regular coefficient module, namely the existing
preadditiveCoyoneda functor. Global RHom is internal derived Hom followed by its right
derived functor, exactly the global-sections convention of zeroth hypercohomology.
All comparisons are natural isomorphisms of functors on the whole unbounded category.
The tensor in the last comparison is the existing relative derived tensor: for finite
locally projective L its dual is flat, so it computes the ordinary tensor in (5.1).

Proof plan, following the five steps of the node:
1. Finite type over k makes X Noetherian; the open complement is quasi-compact. Open-closed
   localization identifies the kernel of the open unit with a closed direct image. A map
   from i_*N factors uniquely through that kernel, giving the sheaf-support adjunction
   (det-lem-formal-closed-support-sheaves and sk-prop-sf-open-closed-triangle).
2. Resolve by a K-injective complex with injective terms (Stacks 079P). Exactness of i_*
   makes its right adjoint preserve K-injectives. Termwise adjunction identifies the global
   Hom complexes and therefore their global derived Hom functors
   (lem-pur-kinjective-degreewise-existence, det-lem-formal-closed-support-derived).
3. For injective I, extend j_!j^*I -> I along j_!j^*I -> j_*j^*I. Open full faithfulness
   makes the extension a section of the open unit. The degreewise short exact sequences
   give the natural fibre triangle of that unit. Apply exact i^* and i^*i_* = id to compare
   its closed inverse image with the right derived kernel functor
   (det-lem-formal-closed-support-derived).
4. For a_!L = i_*u_!L, apply the closed adjunction and then exact u_! adjoint to u^*.
   Exactness implies that u^* preserves K-injectives, so these adjunctions identify RHom
   (def-sfb-module-open-lower-shriek-adjunction and the K-injective adjunction criterion).
5. Locally L is a retract of a finite free module. Evaluation identifies sheaf Hom(L,-)
   with L-dual tensor -, and both L and its dual are flat by this same retract calculation.
   The internal-Hom sections model identifies global derived Hom with derived sections of
   this tensor. Adjunction and evaluation are natural, yielding (5.1) for unbounded K
   (lem-sfb-ringed-site-finite-retract-dual-exact and
   lem-sfb-derived-internal-hom-sections-model).
-/
theorem formalClosedSupportFiberAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Z V : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : V ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (_hij : Set.range j = (Set.range i)ᶜ) :
    ∃ (F : DerivedCategory (supportModules Λ X) ⥤ DerivedCategory (supportModules Λ X))
      (ι : F ⟶ 𝟭 (DerivedCategory (supportModules Λ X)))
      (δ : (upperStar Λ j).mapDerivedCategory ⋙ (lowerStar Λ j).rightDerivedFunctor ⟶
        F ⋙ shiftFunctor (DerivedCategory (supportModules Λ X)) (1 : ℤ)),
      (∀ K : DerivedCategory (supportModules Λ X),
        Triangle.mk (ι.app K)
          ((upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app K)
          (δ.app K) ∈ Pretriangulated.distinguishedTriangles) ∧
      Nonempty (F ⋙ (upperStar Λ i).mapDerivedCategory ≅
        (closedSupport Λ i j).rightDerivedFunctor) ∧
      (Exists fun [_hclosed : PreservesFiniteColimits (lowerStar Λ i)] ↦
        Nonempty ((lowerStar Λ i).mapDerivedCategory ⊣
          F ⋙ (upperStar Λ i).mapDerivedCategory) ∧
        Nonempty
          ((lowerStar Λ i).mapDerivedCategory.op ⋙ derivedHom Λ X ⋙
              (Functor.whiskeringRight _ _ _).obj
                (preadditiveCoyoneda.obj
                  (op (Mod.regular (condensedRingObj Λ X)))).rightDerivedFunctor ≅
            derivedHom Λ Z ⋙
              (Functor.whiskeringRight _ _ _).obj
                (preadditiveCoyoneda.obj
                  (op (Mod.regular (condensedRingObj Λ Z)))).rightDerivedFunctor ⋙
              (Functor.whiskeringLeft _ _ _).obj
                (F ⋙ (upperStar Λ i).mapDerivedCategory))) ∧
      (∀ {S : Scheme.{u}} [S.Over (Spec (.of k))]
        (uS : S ⟶ Z) [IsOpenImmersion uS] [uS.IsOver (Spec (.of k))]
        (L : supportModules Λ S), IsFiniteLocallyProjective Λ S L →
        Nonempty
          ((derivedHom Λ X).obj
              (op ((DerivedCategory.singleFunctor (supportModules Λ X) 0).obj
                ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ uS).obj L)))) ⋙
              (preadditiveCoyoneda.obj
                (op (Mod.regular (condensedRingObj Λ X)))).rightDerivedFunctor ≅
            (F ⋙ (upperStar Λ i).mapDerivedCategory) ⋙ (upperStar Λ uS).mapDerivedCategory ⋙
              (derivedTensor Λ S).obj
                ((DerivedCategory.singleFunctor (supportModules Λ S) 0).obj
                  ((ihom L).obj (𝟙_ (supportModules Λ S)))) ⋙
              (preadditiveCoyoneda.obj
                (op (Mod.regular (condensedRingObj Λ S)))).rightDerivedFunctor)) := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : QuasiCompact j := inferInstance
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    simp only [_hij, compl_compl]
  let := closedSupport_lowerStarExact Λ i j hij
  obtain ⟨hAdd, adj, _, _, ⟨δ, hδ⟩, _⟩ :=
    formal_closed_support_derived Λ ℓ k _hΛ i j _hij
  let := hAdd
  let R := (closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor
  let F := R ⋙ (lowerStar Λ i).mapDerivedCategory
  let eR : R ≅ (closedSupport Λ i j).rightDerivedFunctor :=
    adj.mapDerivedCategoryRightDerivedAdjunction.rightAdjointUniq
      (closedSupportDerivedAdjunction Λ i j hij)
  have hc := (condensedSupportDerivedLocalization Λ i j hij).2.1
  have : IsIso (closedPullbackDerivedAdjunction Λ i).counit :=
    NatIso.isIso_of_isIso_app _
  let eI : (lowerStar Λ i).mapDerivedCategory ⋙ (upperStar Λ i).mapDerivedCategory ≅ 𝟭 _ :=
    Functor.isoWhiskerLeft (lowerStar Λ i).mapDerivedCategory
      (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ i)).symm ≪≫
      asIso (closedPullbackDerivedAdjunction Λ i).counit
  let e : F ⋙ (upperStar Λ i).mapDerivedCategory ≅
      (closedSupport Λ i j).rightDerivedFunctor :=
    Functor.isoWhiskerLeft R eI ≪≫ eR
  obtain ⟨eG⟩ := supportClosedGlobalHomIso Λ i j hij
  refine ⟨F, adj.mapDerivedCategoryRightDerivedAdjunction.counit, δ, hδ,
    ⟨e⟩, ⟨inferInstance, ⟨(closedSupportDerivedAdjunction Λ i j hij).ofNatIsoRight e.symm⟩,
      ⟨eG ≪≫ ?_⟩⟩, ?_⟩
  · exact Functor.isoWhiskerLeft
      (derivedHom Λ Z ⋙ (Functor.whiskeringRight _ _ _).obj
        (preadditiveCoyoneda.obj
          (op (Mod.regular (condensedRingObj Λ Z)))).rightDerivedFunctor)
      ((Functor.whiskeringLeft _ _ _).mapIso e.symm)
  · intro S _ uS _ _ L hL
    have : TopologicalSpace.NoetherianSpace Z :=
      i.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
    have : TopologicalSpace.NoetherianSpace S :=
      uS.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    have : QuasiCompact uS := inferInstance
    let A := (DerivedCategory.singleFunctor (supportModules Λ S) 0).obj L
    let B := (DerivedCategory.singleFunctor (supportModules Λ Z) 0).obj
      ((openImmersionLowerShriek Λ uS).obj L)
    let e₁ := ((lowerStar Λ i).mapDerivedCategorySingleFunctor 0).app
      ((openImmersionLowerShriek Λ uS).obj L)
    let e₂ := ((openImmersionLowerShriek Λ uS).mapDerivedCategorySingleFunctor 0).app L
    let ΓX := (preadditiveCoyoneda.obj
      (op (Mod.regular (condensedRingObj Λ X)))).rightDerivedFunctor
    let ΓZ := (preadditiveCoyoneda.obj
      (op (Mod.regular (condensedRingObj Λ Z)))).rightDerivedFunctor
    let ΓS := (preadditiveCoyoneda.obj
      (op (Mod.regular (condensedRingObj Λ S)))).rightDerivedFunctor
    let eΓ : (lowerStar Λ i).mapDerivedCategory ⋙ ΓX ≅ ΓZ :=
      Functor.isoWhiskerRight
        (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.symm ΓX ≪≫
      supportGlobalSectionsIso Λ i
    let ec := Functor.isoWhiskerRight
      ((derivedHom Λ X).mapIso e₁.op ≪≫ closedDerivedHomIso Λ i j hij B) ΓX ≪≫
      Functor.isoWhiskerLeft
        ((closedSupport Λ i j).rightDerivedFunctor ⋙ (derivedHom Λ Z).obj (op B)) eΓ
    let eo := Functor.isoWhiskerRight
      ((derivedHom Λ Z).mapIso e₂.op ≪≫ openDerivedHomIso Λ uS A) ΓZ ≪≫
      Functor.isoWhiskerLeft
        ((supportPullback Λ uS).mapDerivedCategory ⋙ (derivedHom Λ S).obj (op A))
        (supportGlobalSectionsIso Λ uS)
    let ed := Functor.isoWhiskerRight
      (finiteProjectiveDerivedHomIso Λ S L (finiteLocallyProjective_isDualizable Λ S L hL)) ΓS
    exact ⟨ec ≪≫ Functor.isoWhiskerLeft (closedSupport Λ i j).rightDerivedFunctor eo ≪≫
      Functor.isoWhiskerLeft ((closedSupport Λ i j).rightDerivedFunctor ⋙
        (supportPullback Λ uS).mapDerivedCategory) ed ≪≫
      Functor.isoWhiskerRight e.symm
        ((supportPullback Λ uS).mapDerivedCategory ⋙
          (derivedTensor Λ S).obj
            ((DerivedCategory.singleFunctor (supportModules Λ S) 0).obj
              ((ihom L).obj (𝟙_ (supportModules Λ S)))) ⋙ ΓS) ≪≫
      Functor.isoWhiskerLeft (F ⋙ (upperStar Λ i).mapDerivedCategory)
        (Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ uS)) _)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
