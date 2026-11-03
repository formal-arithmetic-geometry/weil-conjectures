/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomConePairingDefs
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.Constructible
public import WeilConjectures.Algebra.Homology.DerivedFreeModuleHomology
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleConstructibleMappingContinuityData
public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleConstructibleMappingModelSkeleton
public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleDerivedImageHomAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.HomColimitExtension
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleConstructibleBoundedBelowHomColimit

/-! # Constructible derived mapping continuity on affine ind-etale limits

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.3.14 and
proof of Lemma 6.3.16, pp. 47--48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity).

The comparison is the localization of the map out of the termwise filtered
colimit of compatible complex representatives. It is not a categorical colimit
assertion in the triangulated category. The representatives retain both the
transition maps and the legs of the evaluation-defined pullback comparison.
All constructions use the ordinary constant-coefficient small etale category.

## Main statements

* `constructible_mapping_continuity`: the canonical comparison is invertible.
* `comparison_cofinal`: the canonical cofinal comparison triangle.
* `comparison_naturality`: system maps, coefficient maps and base restriction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (K M : DerivedCategoryModule A X)

/-- Global RHom of the two exact inverse images along a scheme over X.
This is the existing RΓ of the existing derived internal Hom.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def value (T : Over X) : DerivedCategory (ModuleCat.{u + 1} A) :=
  ((ExternalRHom.globalHom A T.left).obj
    (op ((ExternalRHom.pull A T.hom).obj K))).obj
      ((ExternalRHom.pull A T.hom).obj M)

/-- Pullback of derived morphisms, transported along the canonical composition
isomorphisms for inverse image. Its source is the evaluation transpose already
provided by ExternalRHom.restriction; no map or isomorphism is chosen.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def pullback {T S : Over X} (f : T ⟶ S) : value A K M S ⟶ value A K M T :=
  ExternalRHom.restriction A f.left
      ((ExternalRHom.pull A S.hom).obj K) ((ExternalRHom.pull A S.hom).obj M) ≫
    ((ExternalRHom.globalHom A T.left).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
        f.w.symm).hom.app K).op).app
          ((ExternalRHom.pull A f.left).obj ((ExternalRHom.pull A S.hom).obj M)) ≫
    ((ExternalRHom.globalHom A T.left).obj
      (op ((ExternalRHom.pull A T.hom).obj K))).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
          f.w.symm).inv.app M)

/-- The two coefficient variances of the existing global Hom bifunctor.
Source: Bhatt--Scholze 6.3.16, naturality of RHom
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def coefficientMap {K' M' : DerivedCategoryModule A X}
    (α : K' ⟶ K) (β : M ⟶ M') (T : Over X) :
    value A K M T ⟶ value A K' M' T :=
  ((ExternalRHom.globalHom A T.left).map
      ((ExternalRHom.pull A T.hom).map α).op).app
        ((ExternalRHom.pull A T.hom).obj M) ≫
    ((ExternalRHom.globalHom A T.left).obj
      (op ((ExternalRHom.pull A T.hom).obj K'))).map
        ((ExternalRHom.pull A T.hom).map β)

/-- Compatible strict representatives for the global RHom diagram and its
pullback cocone. The two equations normalize every transition and every leg
against the canonical pullback of morphisms. This is computational input for an
exact filtered colimit, not an assumed continuity isomorphism.
Source: Bhatt--Scholze 6.3.16, p. 48; the node's proof, Steps 2--6
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
structure Model where
  diagram : Iᵒᵖ ⥤ CochainComplex (ModuleCat.{u + 1} A) ℤ
  cocone : Cocone diagram
  stage : ∀ i : I, (DerivedCategory.Q.obj (diagram.obj (op i))) ≅ value A K M (D.obj i)
  apex : DerivedCategory.Q.obj cocone.pt ≅ value A K M c.pt
  transition : ∀ {i j : I} (f : i ⟶ j),
    DerivedCategory.Q.map (diagram.map f.op) ≫ (stage i).hom =
      (stage j).hom ≫ pullback A K M (D.map f)
  leg : ∀ i : I,
    DerivedCategory.Q.map (cocone.ι.app (op i)) ≫ apex.hom =
      (stage i).hom ≫ pullback A K M (c.π.app i)

/-- The canonical comparison, computed by the exact colimit of complexes and
then localized. The normalization in Model fixes its pullback legs.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def comparison (P : Model A K M D c) :
    DerivedCategory.Q.obj (colimit P.diagram) ⟶ value A K M c.pt :=
  DerivedCategory.Q.map (colimit.desc P.diagram P.cocone) ≫ P.apex.hom

variable {I : Type (u + 1)} [SmallCategory I]
variable (D : I ⥤ Over X) (c : Cone D)

variable {J : Type (u + 1)} [SmallCategory J]
variable (E : J ⥤ Over X) (d : Cone E) (r : J ⥤ I)

variable (K' M' : DerivedCategoryModule A X) (α : K' ⟶ K) (β : M ⟶ M')

end AlgebraicGeometry.Etale.IndEtaleMapping

namespace AlgebraicGeometry.Etale.IndEtaleMapping

private def isColimit_of_normalization
    {C : Type*} [Category C] {L : Type*} [Category L]
    {B E : L ⥤ C} (b : Cocone B) (e : Cocone E)
    (stage : ∀ i : L, B.obj i ≅ E.obj i) (apex : b.pt ≅ e.pt)
    (transition : ∀ {i j : L} (f : i ⟶ j),
      B.map f ≫ (stage j).hom = (stage i).hom ≫ E.map f)
    (leg : ∀ i : L, b.ι.app i ≫ apex.hom = (stage i).hom ≫ e.ι.app i)
    (he : IsColimit e) : IsColimit b := by
  let δ : B ≅ E := NatIso.ofComponents stage (fun f ↦ transition f)
  let γ : b ≅ (Cocone.precompose δ.hom).obj e := Cocone.ext apex leg
  exact ((IsColimit.precomposeHomEquiv δ e).symm he).ofIsoColimit γ.symm

private theorem isIso_localized_desc_of_cohomology
    (B : Iᵒᵖ ⥤ CochainComplex (ModuleCat.{u + 1} A) ℤ) (b : Cocone B)
    [IsCofiltered I]
    (h : ∀ q : ℤ, Nonempty (IsColimit
      ((DerivedCategory.Q ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).mapCocone b))) :
    IsIso (DerivedCategory.Q.map (colimit.desc B b)) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) q
  obtain ⟨hq⟩ := h q
  let hb : IsColimit (H.mapCocone b) :=
    IsColimit.mapCoconeEquiv
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) q) hq
  let hc := isColimitOfPreserves H (colimit.isColimit B)
  have hdesc : hc.desc (H.mapCocone b) = H.map (colimit.desc B b) := by
    apply hc.hom_ext
    intro i
    change H.map (colimit.ι B i) ≫ _ = H.map (colimit.ι B i) ≫ _
    exact (hc.fac (H.mapCocone b) i).trans (by
      simp only [← Functor.map_comp, colimit.ι_desc]
      rfl)
  have hi := hc.nonempty_isColimit_iff_isIso_desc.1 ⟨hb⟩
  rw [hdesc] at hi
  exact hi

/-- The global-Hom square of one strict direct-image transition: a map of
representatives normalized against `imagePullback g` goes, after global Hom and
`imageHomIso`, to the evaluation-defined `pullback g`. -/
private theorem imageHomIso_stage_square {T S : Over X} (g : T ⟶ S)
    {Y Z : DerivedCategoryModule A X} (w : Y ⟶ Z) (sS : Y ≅ imageValue A M S)
    (sT : Z ≅ imageValue A M T) (h : w ≫ sT.hom = sS.hom ≫ imagePullback A M g) :
    ((ExternalRHom.globalHom A X).obj (op K)).map w ≫
        (((ExternalRHom.globalHom A X).obj (op K)).mapIso sT ≪≫ imageHomIso A M K T).hom =
      (((ExternalRHom.globalHom A X).obj (op K)).mapIso sS ≪≫ imageHomIso A M K S).hom ≫
        pullback A K M g := by
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc,
    imageHomIso_naturality A K M g, pullback]
  simp only [Category.assoc]

/-- Auxiliary comparison-isomorphism statement for a fixed compatible model.
Source: Bhatt--Scholze, Lemmas 6.3.14 and 6.3.16, pp. 47--48
(blueprint: lem-per-ind-etale-constructible-mapping-model-comparison).

Proof:
1. Filtered colimits of A-module complexes are exact, so the cohomology of the
   colimit of `P.diagram` is the colimit of the cohomologies. By the `transition`
   and `leg` equations, the stage isomorphisms identify `H^q` of the comparison
   with the canonical map `colim_i H^q value(U_i) → H^q value(U)` induced by
   `pullback`, which does not depend on `P`. A map in `D(A)` is invertible iff
   it is so on every `H^q`, so it suffices to treat one model.
2. For the injective model built from `N_i = j_{i,*} j_i^* I`, with `I` a
   bounded-below injective representative of `M` (node proof, Step 2),
   relative direct-image continuity (Stacks 0GIU) makes `colim N_i → N_U` a
   derived isomorphism; fixed-site constructible bounded-below Hom continuity
   (6.3.14) then gives `colim RHom_X(K, N_i) ≅ RHom_X(K, N_U)`, and
   derived adjunction identifies these with the global RHom on `U_i` and `U` and
   the maps with `pullback`. -/
theorem constructible_mapping_model_comparison_isIso [Finite A] [IsAffine X]
    [IsNoetherian X] [IsCofiltered I]
    (hc : IsLimit ((Over.forget X).mapCone c))
    (haffine : ∀ i : I, IsAffine (D.obj i).left)
    (hetale : ∀ i : I, Etale (D.obj i).hom)
    (hfp : ∀ i : I, LocallyOfFinitePresentation (D.obj i).hom)
    (htransition : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left)
    (hK : DerivedCategory.isBoundedConstructible A X K)
    (hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K)
    (hM : ∃ a : ℤ, M.IsGE a) (P : Model A K M D c) :
    IsIso (comparison A K M D c P) := by
  obtain ⟨N, a, hbound, hN⟩ := derivedImageModel_exists_continuous A M D c hc
    haffine hetale hfp htransition hM
  let F := (ExternalRHom.globalHom A X).obj (op K)
  let S := N.diagram ⋙ DerivedCategory.Q ⋙ F
  let t := (DerivedCategory.Q ⋙ F).mapCocone N.cocone
  let φ (i : I) : S.obj (op i) ≅ value A K M (D.obj i) :=
    F.mapIso (N.stage i) ≪≫ imageHomIso A M K (D.obj i)
  let ψ : t.pt ≅ value A K M c.pt := F.mapIso N.apex ≪≫ imageHomIso A M K c.pt
  have hφ {i j : I} (f : i ⟶ j) :
      S.map f.op ≫ (φ i).hom = (φ j).hom ≫ pullback A K M (D.map f) :=
    imageHomIso_stage_square A K M (D.map f) _ (N.stage j) (N.stage i) (N.transition f)
  have hψ (i : I) :
      t.ι.app (op i) ≫ ψ.hom = (φ i).hom ≫ pullback A K M (c.π.app i) :=
    imageHomIso_stage_square A K M (c.π.app i) _ (N.stage i) N.apex (N.leg i)
  have hcohomology (q : ℤ) : Nonempty (IsColimit
      ((DerivedCategory.Q ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).mapCocone P.cocone)) := by
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q
    let G := DerivedCategory.Q ⋙ F ⋙ H
    obtain ⟨hcol⟩ := constructibleGlobalHom_cohomology_isColimit A X K hK hTor
      N.diagram a (fun i ↦ hbound i.unop) q
    have := hN
    let e : (G.mapCocone (colimit.cocone N.diagram)) ≅ G.mapCocone N.cocone :=
      Cocone.ext (asIso ((F ⋙ H).map
        (DerivedCategory.Q.map (colimit.desc N.diagram N.cocone)))) (by
        intro i
        change G.map (colimit.ι N.diagram i) ≫
          G.map (colimit.desc N.diagram N.cocone) = _
        rw [← Functor.map_comp, colimit.ι_desc]
        rfl)
    let ht : IsColimit (H.mapCocone t) := hcol.ofIsoColimit e
    let δ (i : Iᵒᵖ) : DerivedCategory.Q.obj (P.diagram.obj i) ≅ S.obj i :=
      P.stage i.unop ≪≫ (φ i.unop).symm
    let γ : DerivedCategory.Q.obj P.cocone.pt ≅ t.pt := P.apex ≪≫ ψ.symm
    have hδ {i j : Iᵒᵖ} (f : i ⟶ j) :
        DerivedCategory.Q.map (P.diagram.map f) ≫ (δ j).hom =
          (δ i).hom ≫ S.map f := by
      apply (cancel_mono (φ j.unop).hom).1
      dsimp only [δ, Iso.trans_hom, Iso.symm_hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      have hf := hφ f.unop
      change S.map f ≫ (φ j.unop).hom = _ at hf
      rw [hf]
      simp only [Iso.inv_hom_id_assoc]
      exact P.transition f.unop
    have hγ (i : Iᵒᵖ) :
        DerivedCategory.Q.map (P.cocone.ι.app i) ≫ γ.hom =
          (δ i).hom ≫ t.ι.app i := by
      apply (cancel_mono ψ.hom).1
      dsimp only [γ, δ, Iso.trans_hom, Iso.symm_hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      have hi := hψ i.unop
      change t.ι.app i ≫ ψ.hom = _ at hi
      rw [hi]
      simp only [Iso.inv_hom_id_assoc]
      exact P.leg i.unop
    exact ⟨isColimit_of_normalization
      (H.mapCocone (DerivedCategory.Q.mapCocone P.cocone)) (H.mapCocone t)
      (fun i ↦ H.mapIso (δ i)) (H.mapIso γ)
      (fun f ↦ by simpa only [Functor.map_comp, Functor.comp_map,
        Functor.mapIso_hom, S] using congrArg H.map (hδ f))
      (fun i ↦ by simpa only [Functor.map_comp, Functor.mapIso_hom,
        Functor.mapCocone_ι_app] using congrArg H.map (hγ i)) ht⟩
  have := isIso_localized_desc_of_cohomology A P.diagram P.cocone hcohomology
  dsimp only [comparison]
  infer_instance

/-- A compatible map of strict representatives, including reindexing. The
scheme maps form a map of inverse systems and its map on the limit cones.
The strict cocone square and both normalization equations say that the chain
maps represent those very pullbacks, including their coherence.
Taking r to be the identity covers system maps. Taking it cofinal covers
refinements. Taking E to be the base-changed system along an affine etale
X' → X covers base restriction, with the composition comparisons in pullback.
Source: Bhatt--Scholze 6.3.16 and the node's proof, Step 7
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
structure ModelMap (P : Model A K M D c) (Q : Model A K' M' E d)
    (η : E ⟶ r ⋙ D) (v : d.pt ⟶ c.pt) where
  cone_square : ∀ j : J, v ≫ c.π.app (r.obj j) = d.π.app j ≫ η.app j
  stages : r.op ⋙ P.diagram ⟶ Q.diagram
  apex : P.cocone.pt ⟶ Q.cocone.pt
  square : ∀ j : J,
    P.cocone.ι.app (op (r.obj j)) ≫ apex = stages.app (op j) ≫ Q.cocone.ι.app (op j)
  stage_normalization : ∀ j : J,
    DerivedCategory.Q.map (stages.app (op j)) ≫ (Q.stage j).hom =
      (P.stage (r.obj j)).hom ≫ pullback A K M (η.app j) ≫
        coefficientMap A K M α β (E.obj j)
  apex_normalization : DerivedCategory.Q.map apex ≫ Q.apex.hom =
    P.apex.hom ≫ pullback A K M v ≫ coefficientMap A K M α β d.pt

end AlgebraicGeometry.Etale.IndEtaleMapping
