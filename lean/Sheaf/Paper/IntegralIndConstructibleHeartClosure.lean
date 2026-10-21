/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F5
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Paper.IntegralConstantModelHeartClosure
import Sheaf.SixFunctors.IntegralExtHomContinuity
import Mathlib.CategoryTheory.Limits.Indization.Category
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.YonedaDerivedExtComparison
import WeilConjectures.CategoryTheory.PushoutShortExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Sheaf.Paper.IndHeartFullFaithfulness
import all Sheaf.Paper.IndHeartCanonicalPresentation
import all Sheaf.Paper.IndHeartKernelsCokernels
import all Sheaf.Paper.IndConstructibleExtensions
import all Sheaf.Paper.IndConstructibleFilteredColimits
import all Sheaf.Paper.CoefficientHeartSmall
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Closure of the integral ind-constructible heart

Source: blueprint main-20261015, integral compactness proof step 9 and integral proper
sums proof steps 7 and 11 (blueprint: lem-sfb-integral-ind-heart-closure).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

private lemma finiteConstantLocalModel_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨HasZeroObject.zero.choose, ?_, ⟨?_⟩⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  · exact ((CondensedRing.upperStar Λ _).map_isZero hM).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))

-- The one-stratum stratification works also when the scheme is empty.
private lemma finiteConstantStratified_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsFiniteConstantStratified Λ X M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  exact ⟨S, fun a ↦ finiteConstantLocalModel_of_isZero Λ _ _
    ((CondensedRing.upperStar Λ (S.immersion a)).map_isZero hM)⟩

private lemma constantModelConstructible_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
  classical
  unfold IsConstantModelConstructible
  split
  · exact finiteConstantStratified_of_isZero Λ X M hM
  · exact fun U _ ↦ finiteConstantStratified_of_isZero Λ _ _
      ((CondensedRing.upperStar Λ U.ι).map_isZero hM)

private lemma constantModelConstructible_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have hs (T : Scheme.{u})
      {A B : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
      (e : A ≅ B) (hA : IsFiniteConstantStratified Λ T A) :
      IsFiniteConstantStratified Λ T B := by
    obtain ⟨S, hS⟩ := hA
    refine ⟨S, fun a ↦ ?_⟩
    obtain ⟨𝒰, h𝒰⟩ := hS a
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (𝒰.f i)).mapIso
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e)).symm ≪≫ eP⟩⟩
  classical
  unfold IsConstantModelConstructible at *
  split_ifs at * with h
  · exact hs X e hM
  · exact fun U hU ↦ hs U.toScheme ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

private lemma constantModelConstructible_single
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    constantModelBoundedConstructible Λ X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n
    exact constantModelConstructible_of_iso Λ X
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · apply constantModelConstructible_of_isZero
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ 0 n hn
    · exact DerivedCategory.isZero_of_isLE _ 0 n hn

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The cofinality argument for a filtered presentation by finitely presentable objects.
Source: canonical-presentation proof, Cofinality paragraph.
(blueprint: det-ind-heart-canonical-presentation). -/
private theorem final_constructiblePresentation
    {C : Type*} [Category.{u + 1} C] (P : ObjectProperty C)
    (hP : ∀ A : P.FullSubcategory, IsFinitelyPresentable.{u + 1} A.obj)
    {B : C} {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (pres : P.ColimitOfShape I B) : pres.toCostructuredArrow.Final := by
  classical
  rw [Functor.final_iff_of_isFiltered]
  constructor
  · intro f
    have : IsFinitelyPresentable.{u + 1} (P.ι.obj f.left) := hP f.left
    obtain ⟨i, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit f.hom
    exact ⟨i, ⟨CostructuredArrow.homMk (ObjectProperty.homMk g) hg⟩⟩
  · intro f i g h
    have : IsFinitelyPresentable.{u + 1} (P.ι.obj f.left) := hP f.left
    obtain ⟨j, a, b, hab⟩ := IsFinitelyPresentable.exists_eq_of_isColimit pres.isColimit
      g.left.hom h.left.hom ((CostructuredArrow.w g).trans (CostructuredArrow.w h).symm)
    refine ⟨_, a ≫ IsFiltered.coeqHom a b, ?_⟩
    apply CostructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    change g.left.hom ≫ pres.diag.map (a ≫ IsFiltered.coeqHom a b) =
      h.left.hom ≫ pres.diag.map (a ≫ IsFiltered.coeqHom a b)
    calc
      _ = (g.left.hom ≫ pres.diag.map a) ≫ pres.diag.map (IsFiltered.coeqHom a b) := by
        rw [pres.diag.map_comp, Category.assoc]
      _ = (h.left.hom ≫ pres.diag.map b) ≫ pres.diag.map (IsFiltered.coeqHom a b) := by
        rw [hab]
      _ = h.left.hom ≫ pres.diag.map (b ≫ IsFiltered.coeqHom a b) := by
        rw [pres.diag.map_comp, Category.assoc]
      _ = h.left.hom ≫ pres.diag.map (a ≫ IsFiltered.coeqHom a b) := by
        rw [IsFiltered.coeq_condition a b]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Assemble a canonical colimit from essential smallness and finite presentation.
Source: canonical-presentation proof, Essential smallness and Colimit paragraphs.
(blueprint: det-ind-heart-canonical-presentation). -/
private theorem canonicalPresentation_of_finitePresentation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (hsmall : EssentiallySmall.{u + 1}
      (ObjectProperty.FullSubcategory (IsConstantModelConstructible Λ X)))
    (hfp : ∀ A : ObjectProperty.FullSubcategory (IsConstantModelConstructible Λ X),
      IsFinitelyPresentable.{u + 1} A.obj) :
    IndHeartCanonicalPresentationAssertions Λ X := by
  classical
  intro B hB
  have := hsmall
  obtain ⟨I, hI, hfI, pres, hp⟩ := hB
  let : SmallCategory I := hI
  have : IsFiltered I := hfI
  let p : ObjectProperty.ColimitOfShape (IsConstantModelConstructible Λ X) I B :=
    ⟨pres, hp⟩
  have := final_constructiblePresentation (IsConstantModelConstructible Λ X) hfp p
  refine ⟨inferInstance, IsFiltered.of_final p.toCostructuredArrow, ?_, ?_⟩
  · exact ⟨(Functor.Final.isColimitWhiskerEquiv (F := p.toCostructuredArrow) _).1
      (IsColimit.ofIsoColimit p.isColimit (Cocone.ext (Iso.refl _)))⟩
  · intro J _ _ q
    exact final_constructiblePresentation (IsConstantModelConstructible Λ X) hfp q

private theorem integral_sheaf_ext_continuity
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))
    (hC : IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X C)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (M : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))
    (c : Cocone M) (hc : IsColimit c) (q : ℤ) :
    IsIso (colimit.desc _
      (((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
        preadditiveCoyoneda.obj
          (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj C))).mapCocone c))) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
  let S := CochainComplex.singleFunctor A 0
  let K := M ⋙ S
  let G := DerivedCategory.Q ⋙ shiftFunctor _ q ⋙
    preadditiveCoyoneda.obj (Opposite.op ((DerivedCategory.singleFunctor A 0).obj C))
  have : Fact (ringChar k).Prime := ⟨by
    rw [ringChar.eq k p₀]
    exact (CharP.char_is_prime_or_zero k p₀).resolve_right hp₀.ne'⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by rw [ringChar.eq k p₀]; exact hpℓ⟩
  let Xo : Over (Spec (.of k)) := Over.mk (X ↘ Spec (.of k))
  have : LocallyOfFiniteType Xo.hom := inferInstanceAs
    (LocallyOfFiniteType (X ↘ Spec (.of k)))
  have : QuasiCompact Xo.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  have : IsSeparated Xo.hom := inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  have h := CondensedRing.integralExtHomContinuous (k := k) (E := E.val) (X := Xo)
    ((DerivedCategory.singleFunctor A 0).obj C)
    (constantModelConstructible_single _ X C hC) K 0
    (fun i r hr ↦ HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (M.obj i) r
      (ne_of_lt hr)) q
  change IsIso (colimit.post K G) at h
  have : PreservesColimit M S := by
    change PreservesColimit M (HomologicalComplex.single A (.up ℤ) 0)
    infer_instance
  have : IsIso (colimit.desc K (S.mapCocone c)) := by
    change IsIso ((colimit.isColimit K).coconePointUniqueUpToIso
      (isColimitOfPreserves S hc)).hom
    infer_instance
  change IsIso (colimit.desc (K ⋙ G) (G.mapCocone (S.mapCocone c)))
  rw [← colimit.post_desc]
  infer_instance

/-- The filtered-colimit closure of integral constructibles is a weak Serre class
and is closed under ambient small coproducts. This is a statement in the abelian
module category; it involves neither derived truncations nor localizing subcategories.

Source: blueprint main-20261015, det-prop-int-compactness-compact, proof steps 1--7
and 9; det-prop-int-compactness-direct-sums, proof steps 7 and 11.
(blueprint: lem-sfb-integral-ind-heart-closure).

Proof: integral constant-model heart closure gives ambient kernels, cokernels and
extensions of constructibles. Bounded-below integral Hom and Ext-one continuity
makes the filtered-colimit realization fully faithful. Present a morphism between
two realized diagrams on the filtered category of constructible squares. Exact
filtered colimits identify its ambient kernel and cokernel with the colimits of
the constructible kernels and cokernels. For an extension, pull it back to each
constructible quotient stage. Ext-one continuity lifts its class to an extension
by one constructible kernel stage. Push that extension out to later kernel stages;
these constructible extensions have colimit the pulled-back extension. Taking the
filtered colimit over the quotient stages recovers the original extension. The zero
scalar model on one stratum is constructible. Finite sums are constructible by split
extensions. A coproduct is the filtered colimit of its finite subsums; take the
filtered category of finite tuples of constructible presentation stages to flatten
these presentations into one small filtered constructible diagram. Its cocones are
exactly families of maps from the summands, so it presents the original coproduct.
The empty family uses the zero model. -/
theorem integralIndConstructibleHeartClosure
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    let Λ := Profinite.padicIntegersRingObj ℓ E
    let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
    let P := ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
    P.ContainsZero ∧ P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels ∧
      P.IsClosedUnderExtensions ∧
      (∀ (I : Type (u + 1)) (M : I → A) (c : Cofan M), IsColimit c →
        (∀ i, P (M i)) → P c.pt) := by
  classical
  let Λ := Profinite.padicIntegersRingObj ℓ E
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let H : ObjectProperty A := IsConstantModelConstructible Λ X
  let P := H.ind.{u + 1}
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  have hzero : H.ContainsZero := ⟨⟨0, isZero_zero A, constantModelConstructible_of_isZero Λ X 0
    (isZero_zero A)⟩⟩
  have : H.IsClosedUnderIsomorphisms := constructible_iso Λ X
  obtain ⟨hk, he⟩ := isConstantModelConstructible_serre_padicIntegers X ℓ ⟨E.val, E.property⟩
  have hker : H.IsClosedUnderKernels := ⟨fun _ ⟨f, _, hf, hH⟩ ↦
    H.prop_of_iso (hf.conePointUniqueUpToIso (kernelIsKernel f)).symm
      (hk _ _ f hH.1 hH.2).1⟩
  have hcoker : H.IsClosedUnderCokernels := ⟨fun _ ⟨f, _, hf, hH⟩ ↦
    H.prop_of_iso (hf.coconePointUniqueUpToIso (cokernelIsCokernel f)).symm
      (hk _ _ f hH.1 hH.2).2⟩
  have hext : H.IsClosedUnderExtensions := ⟨fun hS h1 h3 ↦ he _ hS h1 h3⟩
  have hfp : H ≤ ObjectProperty.isFinitelyPresentable.{u + 1} A := by
    intro C hC
    let S := DerivedCategory.singleFunctor A 0
    apply finitelyPresentable_of_continuity
      (S ⋙ shiftFunctor _ (0 : ℤ)) C (S.obj C) ((shiftFunctorZero _ ℤ).app (S.obj C))
    intro J _ _ M
    exact integral_sheaf_ext_continuity ℓ E k p₀ hp₀ hpℓ X C hC M
      (colimit.cocone M) (colimit.isColimit M) 0
  have : H.IsClosedUnderBinaryProducts := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro _ ⟨D, hD⟩
    exact H.prop_of_iso (biprod.isoProd (D.obj ⟨WalkingPair.left⟩)
      (D.obj ⟨WalkingPair.right⟩) ≪≫
        (HasLimit.isoOfNatIso (diagramIsoPair D)).symm)
      (H.prop_biprod (hD ⟨WalkingPair.left⟩) (hD ⟨WalkingPair.right⟩))
  have : H.IsClosedUnderFiniteProducts := ObjectProperty.IsClosedUnderFiniteProducts.mk'
  have : Abelian H.FullSubcategory := inferInstance
  have : HasFiniteBiproducts H.FullSubcategory :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasBinaryBiproducts H.FullSubcategory :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : PreservesFiniteColimits H.ι := by
    have := H.preservesCokernels_ι
    exact Functor.preservesFiniteColimits_of_preservesCokernels H.ι
  have hsmall : EssentiallySmall.{u + 1} H.FullSubcategory := by
    have : ObjectProperty.EssentiallySmall.{u + 1} H := by
      change ObjectProperty.EssentiallySmall.{u + 1} (IsConstantModelConstructible Λ X)
      rw [show IsConstantModelConstructible Λ X = IsFiniteConstantStratified Λ X by
        funext M
        exact if_pos ⟨inferInstance, inferInstance⟩]
      exact stratifiedModelsSmall Λ X
    infer_instance
  have hpres := canonicalPresentation_of_finitePresentation Λ X hsmall
    (fun C ↦ hfp C.obj C.property)
  have hkc := assertions_of_closure Λ X hsmall ⟨inferInstance⟩ inferInstance
    hker hcoker hpres
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨0, isZero_zero A, ObjectProperty.le_ind H 0
      (constantModelConstructible_of_isZero Λ X 0 (isZero_zero A))⟩⟩
  · refine ⟨fun _ ⟨f, _, hf, hP⟩ ↦ ?_⟩
    exact P.prop_of_iso (hf.conePointUniqueUpToIso (kernelIsKernel f)).symm
      (hkc _ _ f hP.1 hP.2).2.2.2.2.2.2.2.1
  · refine ⟨fun _ ⟨f, _, hf, hP⟩ ↦ ?_⟩
    exact P.prop_of_iso (hf.coconePointUniqueUpToIso (cokernelIsCokernel f)).symm
      (hkc _ _ f hP.1 hP.2).2.2.2.2.2.2.2.2
  · refine ⟨fun {T} hT h1 h3 ↦ ?_⟩
    apply ind_extension_of_finitelyPresentable H hfp ?_ T hT h1 h3
    intro C hC J _ _ N pres hp ξ
    apply ext_stage_of_comparison C pres _ ξ
    exact integral_sheaf_ext_continuity ℓ E k p₀ hp₀ hpℓ X C hC pres.diag
      (Cocone.mk N pres.ι) pres.isColimit 1
  · intro I M c hc hM
    exact ind_coproduct H hfp (constructible_finite_coproduct Λ X) I M c hc hM

end AlgebraicGeometry.ProEtale
