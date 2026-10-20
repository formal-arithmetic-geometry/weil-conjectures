/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E7
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

import all Sheaf.Paper.IntegralConstantModelHeartClosure
import all Sheaf.Paper.IndHeartRealization
import Sheaf.SixFunctors.IntegralExtHomContinuity
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

import all Sheaf.Paper.IndHeartFullFaithfulness
import all Sheaf.Paper.IntegralWindowCoproductComparison
import all Sheaf.Paper.CoefficientHeartSmall
import all Sheaf.Paper.IndConstructibleExtensions
import all Sheaf.Paper.IndHeartKernelsCokernels
import all Sheaf.Paper.IndConstructibleFilteredColimits
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Sheaf.Paper.IndHeartCanonicalPresentation
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-! Integral compactness: an intermediate argument from blueprint main-20261015,
sec-six-functors-basics/sk-prop-int-compactness/sk-prop-int-compactness-compact.proof.md. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

open MonoidalCategory MonObj CondensedRing

private theorem integral_single_preserves_filtered
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (C : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
    (J : Type (u + 1)) [SmallCategory J] [IsFiltered J]
    (M : J ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) (q : ℤ) :
    PreservesColimit M (DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
      preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor _ 0).obj C.obj))) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
  let S := (DerivedCategory.singleFunctor A 0).obj C.obj
  let Y := preadditiveCoyoneda.obj (op S)
  have : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  have hCS : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X S := by
    refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
    intro n
    by_cases hn : n = 0
    · subst n
      exact constant_model_iso _ X
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app C.obj).symm C.property
    · apply constantModelConstructible_of_isZero
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.isZero_of_isGE S 0 n hn
      · exact DerivedCategory.isZero_of_isLE S 0 n hn
  have hchar : ringChar k = p := ringChar.eq k p
  have : NeZero p := ⟨by omega⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have : Fact (ringChar k).Prime := ⟨by simpa [hchar] using Fact.out (p := p.Prime)⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by simpa [hchar] using hpℓ⟩
  have hcont (J : Type (u + 1)) [SmallCategory J] [IsFiltered J]
      (D : J ⥤ CochainComplex A ℤ)
      (hb : ∃ b : ℤ, ∀ i r, r < b → IsZero ((D.obj i).X r)) :
      IsIso (colimit.desc _
        ((DerivedCategory.Q ⋙ shiftFunctor _ q ⋙ Y).mapCocone (colimit.cocone D))) := by
    obtain ⟨b, hb⟩ := hb
    let Z : Over (Spec (.of k)) := Over.mk (X ↘ Spec (.of k))
    let : LocallyOfFiniteType Z.hom :=
      show LocallyOfFiniteType (X ↘ Spec (.of k)) from inferInstance
    let : QuasiCompact Z.hom := show QuasiCompact (X ↘ Spec (.of k)) from inferInstance
    let : IsSeparated Z.hom := show IsSeparated (X ↘ Spec (.of k)) from inferInstance
    have hc := CondensedRing.integralExtHomContinuous (X := Z)
      S hCS D b hb q
    exact hc
  let T := CochainComplex.singleFunctor A 0
  have : PreservesColimitsOfShape J T :=
    inferInstanceAs (PreservesColimitsOfShape J
      (HomologicalComplex.single A (ComplexShape.up ℤ) 0))
  let F := DerivedCategory.Q ⋙ shiftFunctor _ q ⋙ Y
  have hb (i : J) (r : ℤ) (hr : r < 0) : IsZero (((M ⋙ T).obj i).X r) := by
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have : IsIso (colimit.post (M ⋙ T) F) := hcont J (M ⋙ T) ⟨0, hb⟩
  have : PreservesColimit (M ⋙ T) F := preservesColimit_of_isIso_post F _
  have : PreservesColimit M (T ⋙ F) := comp_preservesColimit T F
  have : PreservesColimit M ((T ⋙ DerivedCategory.Q) ⋙ shiftFunctor _ q ⋙ Y) :=
    preservesColimit_of_natIso M
      (Functor.associator T DerivedCategory.Q (shiftFunctor _ q ⋙ Y)).symm
  exact preservesColimit_of_natIso M
    (Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ A 0).symm
      (shiftFunctor _ q ⋙ Y))

private theorem integral_fp
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (C : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X) :
    IsFinitelyPresentable.{u + 1} C.obj := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
  let S := (DerivedCategory.singleFunctor A 0).obj C.obj
  apply finitelyPresentable_of_continuity (DerivedCategory.singleFunctor A 0)
    C.obj S (Iso.refl _)
  intro J _ _ M
  have : PreservesColimit M (DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor _ (0 : ℤ) ⋙
      preadditiveCoyoneda.obj (op S)) :=
    integral_single_preserves_filtered ℓ E k p hp hpℓ X C J M 0
  have : PreservesColimit M ((DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor _ (0 : ℤ)) ⋙
      preadditiveCoyoneda.obj (op S)) :=
    preservesColimit_of_natIso M (Functor.associator _ _ _).symm
  have : PreservesColimit M (DerivedCategory.singleFunctor A 0 ⋙
      preadditiveCoyoneda.obj (op S)) := preservesColimit_of_natIso M
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (DerivedCategory.singleFunctor A 0)
        (shiftFunctorZero (DerivedCategory A) ℤ) ≪≫ Functor.rightUnitor _)
      (preadditiveCoyoneda.obj (op S)))
  infer_instance

private theorem kernel_cokernel_closure
    {A : Type*} [Category A] [Abelian A] (P : ObjectProperty A)
    [P.IsClosedUnderIsomorphisms]
    (hkc : ∀ (M N : A) (f : M ⟶ N), P M → P N → P (kernel f) ∧ P (cokernel f)) :
    P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels := by
  constructor
  · constructor
    intro M hM
    obtain ⟨f, fork, hfork, h⟩ := hM
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hfork)
      (hkc _ _ f h.1 h.2).1
  · constructor
    intro M hM
    obtain ⟨f, cofork, hcofork, h⟩ := hM
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hcofork)
      (hkc _ _ f h.1 h.2).2

private theorem exact_inclusion
    {A : Type*} [Category A] [Abelian A] (P : ObjectProperty A)
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] :
    Nonempty (Abelian P.FullSubcategory) ∧ PreservesFiniteLimits P.ι ∧
      PreservesFiniteColimits P.ι := by
  have : P.IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨F, hF⟩
    exact P.prop_of_iso (biprod.isoProd _ _ ≪≫ (HasLimit.isoOfNatIso (diagramIsoPair F)).symm)
      (P.prop_biprod (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)))
  have : P.IsClosedUnderFiniteProducts := .mk'
  let : Abelian P.FullSubcategory := inferInstance
  have : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) P.ι := fun f ↦ P.preservesKernels_ι f
  have : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) P.ι := fun f ↦ P.preservesCokernels_ι f
  exact ⟨⟨inferInstance⟩, Functor.preservesFiniteLimits_of_preservesKernels P.ι,
    Functor.preservesFiniteColimits_of_preservesCokernels P.ι⟩

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- The integral Ind realization and its ambient exact structure.
Source: blueprint main-20261015, sk-prop-int-compactness-compact.proof.md,
paragraph (1), steps 1--7 (blueprint: lem-integral-ind-heart-realization).

Proof: The integral heart is essentially small, replete and abelian with the ambient
kernels and cokernels. Integral Ext continuity in degree zero identifies Hom from each
constructible sheaf into a filtered colimit with the filtered colimit of Hom. Extend
its inclusion along Ind.yoneda by filtered colimits. Computing Hom out of a colimit as
a limit proves full faithfulness and identifies the essential image with H.ind.
Present an Ind arrow at a common filtered index. Exactness of filtered colimits
identifies its kernel and cokernel with the colimits of the constructible kernels and
cokernels; hence realization is exact. Finite sums use products of filtered indices,
and arbitrary sums are filtered colimits of finite partial sums, including the empty
sum. For an extension, pull back to each constructible quotient stage; Ext^1
continuity lifts its class to an extension by a constructible kernel stage. Its
pushouts over the filtered undercategory have constructible middle terms, and their
colimit is the pulled-back extension. Taking the quotient-stage colimit recovers the
original extension, by exact filtered colimits and the short five lemma. This proves
extension closure. Finite limits and colimits of Ind are induced by those in the
abelian constructible heart. Coefficient identifications must use the actual O_E
condensed ring in this statement. -/
theorem integralIndHeartRealization
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    :
    let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
    let H : ObjectProperty A := IsConstantModelConstructible
      (Profinite.padicIntegersRingObj ℓ E) X
    H.IsClosedUnderIsomorphisms ∧ H.ind.{u + 1}.ContainsZero ∧
    H.ind.{u + 1}.IsClosedUnderKernels ∧ H.ind.{u + 1}.IsClosedUnderCokernels ∧
    H.ind.{u + 1}.IsClosedUnderExtensions ∧
    (∀ I : Type (u + 1), H.ind.{u + 1}.IsClosedUnderColimitsOfShape (Discrete I)) ∧
    HasFiniteLimits (Ind H.FullSubcategory) ∧ HasFiniteColimits (Ind H.FullSubcategory) ∧
    ∃ Φ : Ind H.FullSubcategory ⥤ A,
      Nonempty (Ind.yoneda ⋙ Φ ≅ H.ι) ∧ PreservesFilteredColimits.{u + 1} Φ ∧
      PreservesFiniteLimits Φ ∧ PreservesFiniteColimits Φ ∧ Φ.Full ∧ Φ.Faithful ∧
      Φ.essImage = H.ind.{u + 1} := by
  classical
  dsimp only
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let H : ObjectProperty A := IsConstantModelConstructible Λ X
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  have hfp (C : H.FullSubcategory) : IsFinitelyPresentable.{u + 1} C.obj :=
    integral_fp ℓ E k p hp hpℓ X C
  have hsmall : ObjectProperty.EssentiallySmall.{u + 1} H := by
    change ObjectProperty.EssentiallySmall.{u + 1} (IsConstantModelConstructible Λ X)
    rw [show IsConstantModelConstructible Λ X = IsFiniteConstantStratified Λ X by
      funext M
      exact if_pos ⟨inferInstance, inferInstance⟩]
    exact stratifiedModelsSmall Λ X
  let : ObjectProperty.EssentiallySmall.{u + 1} H := hsmall
  have : EssentiallySmall.{u + 1} H.FullSubcategory := inferInstance
  let : H.IsClosedUnderIsomorphisms := ⟨fun e h ↦ constant_model_iso Λ X e h⟩
  let : H.ContainsZero := ⟨_, isZero_zero A,
    constantModelConstructible_of_isZero Λ X _ (isZero_zero A)⟩
  obtain ⟨hkc, he⟩ := isConstantModelConstructible_serre_padicIntegers X ℓ ⟨E.val, E.property⟩
  obtain ⟨hK, hC⟩ := kernel_cokernel_closure H hkc
  let : H.IsClosedUnderKernels := hK
  let : H.IsClosedUnderCokernels := hC
  let : H.IsClosedUnderExtensions := ⟨fun hS h₁ h₃ ↦ he _ hS h₁ h₃⟩
  obtain ⟨hAb, hlim, hcolim⟩ := exact_inclusion H
  let : Abelian H.FullSubcategory := hAb.some
  let : PreservesFiniteLimits H.ι := hlim
  let : PreservesFiniteColimits H.ι := hcolim
  have hfinal {B : A} {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
      (pres : H.ColimitOfShape I B) : pres.toCostructuredArrow.Final := by
    rw [Functor.final_iff_of_isFiltered]
    constructor
    · intro f
      have : IsFinitelyPresentable.{u + 1} (H.ι.obj f.left) := hfp f.left
      obtain ⟨i, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit f.hom
      exact ⟨i, ⟨CostructuredArrow.homMk (ObjectProperty.homMk g) hg⟩⟩
    · intro f i g h
      have : IsFinitelyPresentable.{u + 1} (H.ι.obj f.left) := hfp f.left
      obtain ⟨j, a, b, hab⟩ := IsFinitelyPresentable.exists_eq_of_isColimit pres.isColimit
        g.left.hom h.left.hom ((CostructuredArrow.w g).trans (CostructuredArrow.w h).symm)
      refine ⟨_, a ≫ IsFiltered.coeqHom a b, ?_⟩
      apply CostructuredArrow.hom_ext
      apply ObjectProperty.hom_ext
      change g.left.hom ≫ pres.diag.map (a ≫ IsFiltered.coeqHom a b) =
        h.left.hom ≫ pres.diag.map (a ≫ IsFiltered.coeqHom a b)
      calc
        _ = (g.left.hom ≫ pres.diag.map a) ≫ pres.diag.map
            (IsFiltered.coeqHom a b) := by
          rw [pres.diag.map_comp, Category.assoc]
        _ = (h.left.hom ≫ pres.diag.map b) ≫ pres.diag.map
            (IsFiltered.coeqHom a b) := by rw [hab]
        _ = h.left.hom ≫ pres.diag.map (b ≫ IsFiltered.coeqHom a b) := by
          rw [pres.diag.map_comp, Category.assoc]
        _ = h.left.hom ≫ pres.diag.map (a ≫ IsFiltered.coeqHom a b) := by
          rw [IsFiltered.coeq_condition a b]
  have hpres : IndHeartCanonicalPresentationAssertions Λ X := by
    intro B hB
    obtain ⟨I, hI, hfI, pres, hp⟩ := hB
    let : SmallCategory I := hI
    let : IsFiltered I := hfI
    let q : H.ColimitOfShape I B := ⟨pres, hp⟩
    let : q.toCostructuredArrow.Final := hfinal q
    refine ⟨inferInstance, IsFiltered.of_final q.toCostructuredArrow, ?_, ?_⟩
    · exact ⟨(Functor.Final.isColimitWhiskerEquiv (F := q.toCostructuredArrow) _).1
        (IsColimit.ofIsoColimit q.isColimit (Cocone.ext (Iso.refl _)))⟩
    · intro J _ _ r
      exact hfinal r
  have hker := assertions_of_closure Λ X inferInstance hAb hcolim
    inferInstance inferInstance hpres
  let : H.ind.{u + 1}.ContainsZero := ⟨_, isZero_zero A,
    H.le_ind _ (constantModelConstructible_of_isZero Λ X _ (isZero_zero A))⟩
  let : H.ind.{u + 1}.IsClosedUnderKernels := ⟨by
    intro M hM
    obtain ⟨f, fork, hfork, h⟩ := hM
    exact H.ind.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hfork)
      (hker _ _ f h.1 h.2).2.2.2.2.2.2.2.1⟩
  let : H.ind.{u + 1}.IsClosedUnderCokernels := ⟨by
    intro M hM
    obtain ⟨f, cofork, hcofork, h⟩ := hM
    exact H.ind.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hcofork)
      (hker _ _ f h.1 h.2).2.2.2.2.2.2.2.2⟩
  have hExt : H.ind.{u + 1}.IsClosedUnderExtensions := by
    constructor
    intro S hS hN hB
    apply ind_extension_of_finitelyPresentable H (fun M hM ↦ hfp ⟨M, hM⟩) ?_
      S hS hN hB
    intro C hC J _ _ N pres _ ξ
    apply ext_stage_of_comparison C pres _ ξ
    let F := DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor _ (1 : ℤ) ⋙
      preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj C))
    have : PreservesColimit pres.diag F :=
      integral_single_preserves_filtered ℓ E k p hp hpℓ X ⟨C, hC⟩ J pres.diag 1
    exact ((colimit.isColimit _).nonempty_isColimit_iff_isIso_desc).mp
      ⟨isColimitOfPreserves F pres.isColimit⟩
  let := hExt
  have hsum (I : Type (u + 1)) : H.ind.{u + 1}.IsClosedUnderColimitsOfShape (Discrete I) :=
    .mk' (by
      rintro _ ⟨F, hF⟩
      let K : I → A := fun i ↦ F.obj ⟨i⟩
      let c : Cofan K := Cofan.mk (colimit F) (fun i ↦ colimit.ι F ⟨i⟩)
      have hc : IsColimit c := by
        let e : Discrete.functor K ≅ F := Discrete.natIso (fun _ ↦ Iso.refl _)
        apply IsColimit.ofIsoColimit
          ((IsColimit.precomposeHomEquiv e (colimit.cocone F)).symm (colimit.isColimit F))
        exact Cocone.ext (Iso.refl _) (fun i ↦ by simp [e, c])
      exact ind_coproduct H (fun C hC ↦ hfp ⟨C, hC⟩)
        (constructible_finite_coproduct Λ X) I K c hc (fun i ↦ hF ⟨i⟩))
  let Φ := IndRealization.functor H.ι
  let hff := IndRealization.fullyFaithful H.ι hfp
  let : Φ.Full := hff.full
  let : Φ.Faithful := hff.faithful
  have him : Φ.essImage = H.ind.{u + 1} :=
    funext (fun M ↦ propext (CategoryTheory.realization_essImage H M))
  obtain ⟨_, hli, hci⟩ := exact_inclusion H.ind.{u + 1}
  have : PreservesFiniteLimits Φ.essImage.ι := by rw [him]; exact hli
  have : PreservesFiniteColimits Φ.essImage.ι := by rw [him]; exact hci
  have : PreservesFiniteLimits Φ :=
    preservesFiniteLimits_of_natIso (Functor.toEssImageCompι Φ)
  have : PreservesFiniteColimits Φ :=
    preservesFiniteColimits_of_natIso (Functor.toEssImageCompι Φ)
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, hExt, hsum,
    inferInstance, inferInstance, Φ, ⟨IndRealization.yonedaIso H.ι⟩, ?_,
    inferInstance, inferInstance, inferInstance, inferInstance, him⟩
  exact inferInstance

end AlgebraicGeometry.ProEtale
