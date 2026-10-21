/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.CondensedClosedCostalkDerivedContinuity
import Sheaf.CategoryTheory.ExactDerivedAdjunctionBounds
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Bounded-below continuity of closed support and open direct image

Source: Stacks Project, Tag 09BM; the support triangles in Hemo--Richarz--Scholbach,
(3.3)--(3.4), Lemma 3.4; bounded direct-image continuity in the blueprint
`det-pe-bounded-continuity-direct-image`
(blueprint: lem-sfb-closed-support-bounded-continuity).

The comparisons use termwise colimits of functorial K-injective models. They are the
localizations of `colimit.post` for the resolution followed by the underived functor.
Thus every leg is the image of a leg of the original complex colimit cocone. No
categorical colimit of a diagram in the triangulated derived category is substituted.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

-- Natural isomorphisms identify the comparison maps, including their cocone legs.
private theorem comparison_ofNatIso
    {C A I : Type*} [Category* C] [Category* A] [Category I]
    [HasColimitsOfShape I A] (D : I ⥤ C) (c : Cocone D)
    {F G : C ⥤ A} (e : F ≅ G)
    [IsIso (colimit.desc (D ⋙ F) (F.mapCocone c))] :
    IsIso (colimit.desc (D ⋙ G) (G.mapCocone c)) := by
  have heq : colimMap (Functor.whiskerLeft D e.hom) ≫
      colimit.desc (D ⋙ G) (G.mapCocone c) =
    colimit.desc (D ⋙ F) (F.mapCocone c) ≫ e.hom.app c.pt := by
    apply colimit.hom_ext
    intro s
    simp only [ι_colimMap_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
    exact (e.hom.naturality (c.ι.app s)).symm
  have hi : IsIso (colimMap (Functor.whiskerLeft D e.hom)) :=
    inferInstanceAs (IsIso (colim.map (Functor.whiskerLeft D e.hom)))
  have : IsIso (colimMap (Functor.whiskerLeft D e.hom) ≫
      colimit.desc (D ⋙ G) (G.mapCocone c)) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_left (colimMap (Functor.whiskerLeft D e.hom)) _

-- Exact colimits commute with homology, so preserve objectwise quasi-isomorphisms.
private theorem quasiIso_colimMap
    {A I : Type*} [Category* A] [Abelian A] [Category I]
    [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    {D E : I ⥤ CochainComplex A ℤ} (α : D ⟶ E)
    (hα : ∀ i, QuasiIso (α.app i)) : QuasiIso (colimMap α) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor A (.up ℤ) q
  have (i : I) : IsIso ((Functor.whiskerRight α H).app i) := by
    have := hα i
    exact inferInstanceAs (IsIso (HomologicalComplex.homologyMap (α.app i) q))
  have : IsIso (Functor.whiskerRight α H) := NatIso.isIso_of_isIso_app _
  have heq : colimit.post D H ≫ H.map (colimMap α) =
      colimMap (Functor.whiskerRight α H) ≫ colimit.post E H := by
    apply colimit.hom_ext
    intro i
    simp only [colimit.ι_post_assoc, ι_colimMap_assoc, colimit.ι_post]
    rw [← H.map_comp, ι_colimMap, H.map_comp]
    rfl
  have : IsIso (colimit.post D H ≫ H.map (colimMap α)) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_left (colimit.post D H) (H.map (colimMap α))

-- For strictly bounded inputs, the good-truncation cocone is an actual colimit.
private theorem comparison_of_strict_cocone
    {A B I : Type*} [Category* A] [Abelian A] [Category* B] [Category I]
    [HasColimitsOfShape I A] [HasColimitsOfShape I B]
    (D : I ⥤ CochainComplex A ℤ) (a : ℤ) (hD : ∀ s, (D.obj s).IsStrictlyGE a)
    (G : CochainComplex A ℤ ⥤ B)
    [IsIso (AlgebraicGeometry.ProEtale.condensedContinuityComparison D a G)] :
    IsIso (colimit.post D G) := by
  let π := Functor.whiskerLeft D ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A)
  have (s : I) : IsIso (π.app s) := by
    have := hD s
    exact inferInstanceAs (IsIso ((D.obj s).πTruncGE a))
  have : IsIso π := NatIso.isIso_of_isIso_app π
  let c := AlgebraicGeometry.ProEtale.condensedContinuityCocone D a
  have hc : IsColimit c :=
    (IsColimit.precomposeHomEquiv (asIso π) (colimit.cocone _)).2
      (colimit.isColimit _)
  have : IsIso (colimit.desc D c) :=
    (colimit.isColimit D).coconePointUniqueUpToIso hc |>.isIso_hom
  have : IsIso (colimit.post D G ≫ G.map (colimit.desc D c)) := by
    rw [colimit.post_desc]
    exact inferInstanceAs
      (IsIso (AlgebraicGeometry.ProEtale.condensedContinuityComparison D a G))
  exact IsIso.of_isIso_comp_right (colimit.post D G) (G.map (colimit.desc D c))

-- Good truncation extends continuity from strict to cohomological lower bounds.
private theorem comparison_of_cohomological_bound
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {B I : Type*} [Category* B] [Category I]
    [HasColimitsOfShape I A] [HasExactColimitsOfShape I A] [HasColimitsOfShape I B]
    (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (hD : ∀ s, (DerivedCategory.Q.obj (D.obj s)).IsGE a)
    (F : DerivedCategory A ⥤ B)
    (hF : ∀ (E : I ⥤ CochainComplex A ℤ), (∀ s, (E.obj s).IsStrictlyGE a) →
      IsIso (AlgebraicGeometry.ProEtale.condensedContinuityComparison E a
        (DerivedCategory.Q ⋙ F))) :
    IsIso (colimit.post D (DerivedCategory.Q ⋙ F)) := by
  let E : I ⥤ CochainComplex A ℤ := D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A
  let α : D ⟶ E :=
    Functor.whiskerLeft D ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A)
  have hα (s : I) : QuasiIso (α.app s) := by
    apply (CochainComplex.quasiIso_πTruncGE_iff _ a).2
    exact (DerivedCategory.isGE_Q_obj_iff _ a).1 (hD s)
  let G := DerivedCategory.Q ⋙ F
  have (s : I) : IsIso ((Functor.whiskerRight α G).app s) := by
    have := hα s
    change IsIso (F.map (DerivedCategory.Q.map (α.app s)))
    infer_instance
  have : IsIso (Functor.whiskerRight α G) := NatIso.isIso_of_isIso_app _
  have := quasiIso_colimMap α hα
  have : IsIso (G.map (colimMap α)) := by
    change IsIso (F.map (DerivedCategory.Q.map (colimMap α)))
    infer_instance
  have hE (s : I) : (E.obj s).IsStrictlyGE a := by
    change ((D.obj s).truncGE a).IsStrictlyGE a
    infer_instance
  have := hF E hE
  have : IsIso (colimit.post E G) := comparison_of_strict_cocone E a hE G
  have heq : colimit.post D G ≫ G.map (colimMap α) =
      colimMap (Functor.whiskerRight α G) ≫ colimit.post E G := by
    apply colimit.hom_ext
    intro s
    simp only [colimit.ι_post_assoc, ι_colimMap_assoc, colimit.ι_post]
    rw [← G.map_comp, ι_colimMap, G.map_comp]
    rfl
  have : IsIso (colimit.post D G ≫ G.map (colimMap α)) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_right (colimit.post D G) (G.map (colimMap α))

-- Both arrows are natural: the resolution augmentation and the derived unit.
private noncomputable def resolutionDerivedIso
    {A : Type v} [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    [HasDerivedCategory.{w} A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] :
    DerivedCategory.Q ⋙ F.rightDerivedFunctor ≅
      CochainComplex.kInjectiveResolutionFunctor.{u} A ⋙
        F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  let R := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let α : R ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      R ⋙ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    Functor.whiskerLeft R
      (Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
          (DerivedCategory.quotientCompQhIso B).inv ≫
        Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).inv
          DerivedCategory.Qh ≫
        Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
          F.rightDerivedFunctorUnit ≫
        Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom F.rightDerivedFunctor)
  have : IsIso α := by
    have (K : CochainComplex A ℤ) : IsIso (α.app K) := by
      dsimp [α]
      infer_instance
    exact NatIso.isIso_of_isIso_app α
  let γ : DerivedCategory.Q (C := A) ⟶ R ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (CochainComplex.toKInjectiveResolution.{u} A) DerivedCategory.Q
  have : IsIso γ := by
    have (K : CochainComplex A ℤ) : IsIso (γ.app K) := by
      have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u} A).app K) :=
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A K).2
      change IsIso (DerivedCategory.Q.map
        ((CochainComplex.toKInjectiveResolution.{u} A).app K))
      infer_instance
    exact NatIso.isIso_of_isIso_app γ
  exact Functor.isoWhiskerRight (asIso γ) F.rightDerivedFunctor ≪≫ (asIso α).symm

-- Homology detects quasi-isomorphisms and preserves the filtered termwise colimit.
private theorem resolutionComparison_isIso
    {A : Type v} [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    [HasDerivedCategory.{w} A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive]
    {I : Type*} [Category I] [HasColimitsOfShape I B] [HasExactColimitsOfShape I B]
    [HasColimitsOfShape I A]
    (D : I ⥤ CochainComplex A ℤ)
    (h : ∀ q : ℤ, IsIso (colimit.desc
      (D ⋙ DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q)
      ((DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor B q).mapCocone (colimit.cocone D)))) :
    IsIso (DerivedCategory.Q.map (colimit.post D
      (CochainComplex.kInjectiveResolutionFunctor.{u} A ⋙
        F.mapHomologicalComplex (.up ℤ)))) := by
  let M := CochainComplex.kInjectiveResolutionFunctor.{u} A ⋙
    F.mapHomologicalComplex (.up ℤ)
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso, quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor B (.up ℤ) q
  let e : DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor B q ≅ M ⋙ H :=
    Functor.isoWhiskerRight (resolutionDerivedIso F) (DerivedCategory.homologyFunctor B q) ≪≫
      Functor.isoWhiskerLeft M (DerivedCategory.homologyFunctorFactors B q)
  have := h q
  have hh : IsIso (colimit.post D (M ⋙ H)) :=
    comparison_ofNatIso D (colimit.cocone D) e
  have : IsIso (colimit.post (D ⋙ M) H ≫ H.map (colimit.post D M)) := by
    rw [colimit.post_post]
    exact hh
  exact IsIso.of_isIso_comp_left (colimit.post (D ⋙ M) H) (H.map (colimit.post D M))

attribute [local irreducible] CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option synthInstance.maxHeartbeats 100000 in
-- Colimits of these internal-module complexes need a larger typeclass search budget.
set_option synthInstance.maxSize 4096 in
/-- Closed support and open direct image commute with filtered colimits sharing a
cohomological lower bound, and preserve that lower bound.
Source: Stacks Project, Tag 09BM; Hemo--Richarz--Scholbach, (3.3)--(3.4), Lemma 3.4;
the blueprint bounded-continuity direct-image proof
(blueprint: lem-sfb-closed-support-bounded-continuity).

`closedSupport` is the recorded kernel construction, whose total right derivation is
the right adjoint of closed direct image. Each comparison below is formed in complexes
and then localized. Functorial K-injective resolution represents the total right derived
functor on every input and every cocone leg, including the colimit complex itself.
Exactness of filtered sheaf colimits makes this independent of representative choices.

Proof plan:
1. Use def-weil-pbc-internal-abelian-sheaf-module-equivalence to identify internal modules
with modules over the section-ring sheaf, including their ordinary derived localizations.
2. By lem-pc-module-filtered-colimits-tensor, filtered sheaf colimits are exact. Apply this
to the kernel/image sequences defining cohomology: cohomology commutes with filtered
colimits. Hence these colimits preserve quasi-isomorphisms and common lower bounds.
3. The noetherian topology makes every open quasi-compact, hence j is qcqs. The
recollement resolution models give left t-exactness of Rj_* and Ri^! at every integer c.
4. Apply good truncation at c functorially. Its projection is a quasi-isomorphism on
inputs with vanishing cohomology below c. Cokernels commute with colimits, so truncation
also commutes with the termwise colimit, retaining the comparisons of the original cocone.
5. Apply det-pe-bounded-continuity-direct-image to j and the truncated diagram. Compute
on the same source-module K-injective resolutions as the full module pushforward.
Restriction of scalars along B_T -> j_* B_U changes neither cohomology nor colimits;
lem-weil-pbc-module-sheaves-colimits-forgetful reflects the resulting isomorphisms.
6. Apply lem-sf-derived-homology-long-exact and exact i^* to the natural triangle
i_*Ri^!K -> K -> Rj_*j^*K ->. Using i^*i_* = id gives five consecutive terms
H^(q-1)(i^*K), H^(q-1)(i^*Rj_*j^*K), H^q(Ri^!K), H^q(i^*K), H^q(i^*Rj_*j^*K).
The connecting arrows are natural because they come from the natural fourth triangle map.
7. Compare the filtered colimit of these sequences for N_t with the sequence for colim N.
Both rows are exact. The four outer comparisons are invertible: exact colimit-preserving
i^*, j^* handle the ordinary terms, and step 5 handles Rj_*j^*N_t with the same bound c.
8. Apply lem-weil-pbc-five-lemma to obtain invertibility of the middle comparison in
every degree. The derived localization then makes the closed-support comparison an
isomorphism. All comparisons were induced by the original cocone. No upper bound,
constructibility, structure-sheaf noetherianity or cohomological dimension was used.
-/
theorem closedSupport_bounded_continuity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {T Z U : Scheme.{u}} [TopologicalSpace.NoetherianSpace T]
    (i : Z ⟶ T) [IsClosedImmersion i] (j : U ⟶ T) [IsOpenImmersion j]
    (_hij : Set.range j = (Set.range i)ᶜ) (c : ℤ) :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (N : I ⥤ CochainComplex (supportModules Λ T) ℤ),
      (∀ t : I, (DerivedCategory.Q.obj (N.obj t)).IsGE c) →
      IsIso (DerivedCategory.Q.map (colimit.post N
        (CochainComplex.kInjectiveResolutionFunctor.{u + 1} (supportModules Λ T) ⋙
          (closedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ))))) ∧
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (V : I ⥤ CochainComplex (supportModules Λ U) ℤ),
      (∀ t : I, (DerivedCategory.Q.obj (V.obj t)).IsGE c) →
      IsIso (DerivedCategory.Q.map (colimit.post V
        (CochainComplex.kInjectiveResolutionFunctor.{u + 1} (supportModules Λ U) ⋙
          (lowerStar Λ j).mapHomologicalComplex (ComplexShape.up ℤ))))) ∧
    (∀ K : DerivedCategory (supportModules Λ T), K.IsGE c →
      ((closedSupport Λ i j).rightDerivedFunctor.obj K).IsGE c) ∧
    (∀ K : DerivedCategory (supportModules Λ U), K.IsGE c →
      ((lowerStar Λ j).rightDerivedFunctor.obj K).IsGE c) := by
  classical
  -- Reuse the support-triangle argument through the closed-costalk continuity theorem.
  -- The helpers above retain the original cocone and the prescribed resolution functor.
  have : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    rw [_hij, compl_compl]
  let := closedSupport_lowerStarExact Λ i j hij
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I _ _ N hN
    refine resolutionComparison_isIso (closedSupport Λ i j) N (fun q ↦ ?_)
    refine comparison_of_cohomological_bound N c hN
      ((closedSupport Λ i j).rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ q) ?_
    intro E hE
    exact ProEtale.condensed_closed_costalk_derived_continuity T Λ i
      (closedSupport Λ i j) (closedSupportAdjunction Λ i j hij) E c hE q
  · intro I _ _ V hV
    refine resolutionComparison_isIso (lowerStar Λ j) V (fun q ↦ ?_)
    refine comparison_of_cohomological_bound V c hV
      ((lowerStar Λ j).rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ q) ?_
    intro E hE
    exact ProEtale.condensed_qcqs_pushforward_continuity Λ j E c
      (fun s n hn ↦ by
        have := hE s
        exact (E.obj s).isZero_of_isGE c n hn) q
  · intro K hK
    have := hK
    exact CategoryTheory.exactDerivedAdjunction_isGE (lowerStar Λ i)
      (lowerStar Λ i).mapDerivedCategory (lowerStar Λ i).mapDerivedCategoryFactors
      (closedSupportDerivedAdjunction Λ i j hij) K c
  · intro K hK
    have := hK
    exact CategoryTheory.exactDerivedAdjunction_isGE (supportPullback Λ j)
      (supportPullback Λ j).mapDerivedCategory
      (supportPullback Λ j).mapDerivedCategoryFactors
      (closedSupportOpenDerivedAdjunction Λ j) K c

end AlgebraicGeometry.ProEtale.CondensedRing
