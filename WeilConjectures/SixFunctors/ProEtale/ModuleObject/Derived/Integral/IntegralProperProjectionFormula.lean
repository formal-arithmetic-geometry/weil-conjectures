/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralTensorInverseImage
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperProjectionFormulaBounded
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.AlgebraicGeometry.Integral.Proper.IntegralProperDirectSums
import WeilConjectures.CategoryTheory.Triangulated.LocalizingDetermination
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingProjection

/-!
# The integral proper projection formula

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-pf-adic/
sk-thm-sf-pf-adic-projection.md, clauses (1)--(2)
(blueprint: lemma-projection-formula-integral-coefficients--1).

All operations are the ordinary unbounded module-object derived operations.
The localizing closures use ambient small sums and the constant-model
constructibility predicate recorded by definition-constructible-sheaves.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
attribute [local instance 30000] instCategoryDerivedCategory CategoryTheory.Mod.instCategory
attribute [local instance 1]
  AlgebraicGeometry.ProEtale.CondensedRing.ProjectionMorphismData.category

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open AlgebraicGeometry.Scheme

-- The upstream closure uses the Hom universe for its coproducts. Every existing
-- larger coproduct has Hom-small nonzero support, so it has the same closure.
private theorem coproduct_small_support.{w, v, u₂, v₂}
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [LocallySmall.{w} D]
    {I : Type v} (K : I → D) (t : Cofan K) (ht : IsColimit t) :
    Small.{w} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : t.pt ⟶ K i := ht.desc (Cofan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) : t.inj j ≫ p i = Pi.single (M := fun j ↦ K j ⟶ K i) i (𝟙 (K i)) j :=
    ht.fac (Cofan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective (f := fun i : {i // ¬ IsZero (K i)} ↦ p i.val ≫ t.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ t.inj i.val ≫ f ≫ p i.val) hij
  have hi : t.inj i.val ≫ p i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : t.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

private theorem localizing_large.{v, w}
    {C : Type w} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) [P.IsLocalizing] : IsLocalizingSubcategory P := by
  classical
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I F hF hmem
  let := hF
  let K : I → C := fun i ↦ F.obj ⟨i⟩
  let t : Cofan K := Cofan.mk (colimit F) (fun i ↦ colimit.ι F ⟨i⟩)
  let c (s : Cofan K) : Cocone F :=
    { pt := s.pt
      ι := Discrete.natTrans (fun i ↦ s.inj i.as) }
  have ht : IsColimit t := by
    refine Cofan.IsColimit.mk t (fun s ↦ colimit.desc F (c s)) ?_ ?_
    · intro s i
      exact colimit.ι_desc (c s) ⟨i⟩
    · intro s m hm
      apply colimit.hom_ext (F := F)
      intro ⟨i⟩
      exact (hm i).trans (colimit.ι_desc (c s) ⟨i⟩).symm
  let J := {i // ¬ IsZero (K i)}
  have : Small.{v} J := coproduct_small_support.{v, w, w, v} K t ht
  let : P.IsClosedUnderColimitsOfShape (Discrete J) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (equivShrink J)).symm
  let U : J → C := fun i ↦ K i.val
  let r : Cofan U := Cofan.mk t.pt (fun i ↦ t.inj i.val)
  have hr : IsColimit r := by
    refine Cofan.IsColimit.mk r (fun s ↦ ht.desc (Cofan.mk s.pt
      (fun i ↦ if hi : ¬ IsZero (K i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
    · intro s i
      obtain ⟨i, hi⟩ := i
      change t.ι.app (Discrete.mk i) ≫ _ = _
      rw [ht.fac]
      simp only [Cofan.mk_ι_app, dite_eq_left hi]
    · intro s m hm
      apply ht.hom_ext
      intro ⟨i⟩
      rw [ht.fac]
      by_cases hi : ¬ IsZero (K i)
      · simpa only [r, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dite_eq_left hi]
          using hm ⟨i, hi⟩
      · exact (not_not.mp hi).eq_of_src _ _
  exact P.prop_of_isColimit (F := Discrete.functor U) (c := r) hr
    (fun i ↦ hmem i.as.val)

private theorem localizing_small.{v}
    {C : Type (v + 1)} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (hP : IsLocalizingSubcategory P) : P.IsLocalizing := by
  let := hP.1
  let := hP.2.1
  refine { isClosedUnderColimitsOfShape_discrete := fun J ↦ ?_ }
  let : P.IsClosedUnderColimitsOfShape (Discrete (ULift.{v + 1} J)) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
      rintro _ ⟨F, hF⟩
      exact hP.2.2 F inferInstance (fun i ↦ hF ⟨i⟩))
  exact ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
    (Discrete.equivalence Equiv.ulift)

private theorem canonical_sums_preserved.{v, w, w'}
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v} D]
    (P : ObjectProperty C) (F : C ⥤ D)
    (h : ∀ (I : Type v) (K : I → C), (∀ i, P (K i)) →
      ∃ c : Cofan K, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c))) :
    F.PreservesCoproductsOn.{v} P := by
  intro I G c hc hG
  let K : I → C := fun i ↦ G.obj ⟨i⟩
  obtain ⟨c', ⟨hc'⟩, ⟨hFc'⟩⟩ := h I K (fun i ↦ hG ⟨i⟩)
  have : PreservesColimit (Discrete.functor K) F :=
    preservesColimit_of_preserves_colimit_cocone hc' hFc'
  have : PreservesColimit G F := preservesColimit_of_iso_diagram
    (K₁ := Discrete.functor K) (K₂ := G) F (Discrete.natIsoFunctor (F := G)).symm
  exact ⟨isColimitOfPreserves F hc⟩

private theorem localizing_inverseImage
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (hP : IsLocalizingSubcategory P) (F : C ⥤ C)
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsLeftAdjoint] :
    IsLocalizingSubcategory (P.inverseImage F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I G hG h
  let := hG
  have hcol : P (colimit (G ⋙ F)) := hP.2.2 (G ⋙ F) inferInstance h
  exact P.prop_of_iso (preservesColimitIso F G).symm hcol

private theorem localizing_tensor_closed
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T T' : C ⥤ C ⥤ C) (heq : T = T')
    [∀ A : C, (T'.obj A).CommShift ℤ]
    [∀ A : C, (T'.flip.obj A).CommShift ℤ]
    [∀ A : C, (T'.obj A).IsTriangulated]
    [∀ A : C, (T'.flip.obj A).IsTriangulated]
    [∀ A : C, (T'.obj A).IsLeftAdjoint]
    [∀ A : C, (T'.flip.obj A).IsLeftAdjoint]
    (S : ObjectProperty C) (hL : IsLocalizingSubcategory (localizingClosure S))
    (h : ∀ A B, S A → S B → S ((T.obj A).obj B)) :
    ∀ A B, localizingClosure S A → localizingClosure S B →
      localizingClosure S ((T.obj A).obj B) := by
  subst T'
  let L := localizingClosure S
  have hSL : S ≤ L := fun K hK P _ hSP ↦ hSP K hK
  have hright (B) (hB : S B) : ∀ A, L A → L ((T.obj A).obj B) := by
    intro A hA
    exact hA (L.inverseImage (T.flip.obj B))
      (localizing_inverseImage L hL (T.flip.obj B))
      (fun K hK ↦ hSL _ (h K B hK hB))
  intro A B hA hB
  exact hB (L.inverseImage (T.obj A))
    (localizing_inverseImage L hL (T.obj A))
    (fun M hM ↦ hright M hM A hA)

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (p : X ⟶ Y)
private theorem canonical_projection_isIso
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    : IsIso (moduleObjectProjectionMap Λ p K L) ↔
      IsIso (((projectionMap Λ p).app K).app L) := by
  change IsIso ((((derivedUpperStarLowerStarAdjunction Λ p).rightAdjointProjectionMap
    (T_C := derivedTensor Λ X) (T_D := derivedTensor Λ Y)
    (leftDerivedUpperStarTensor Λ p)).app K).app L) ↔ _
  change IsIso ((((derivedUpperStarLowerStarAdjunction Λ p).rightAdjointProjectionMap
    (T_C := derivedTensor Λ X) (T_D := derivedTensor Λ Y)
    (leftDerivedUpperStarTensor Λ p)).app K).app L) ↔
    IsIso ((((derivedUpperStarLowerStarAdjunction Λ p).rightAdjointProjectionMap
    (T_C := derivedTensor Λ X) (T_D := derivedTensor Λ Y)
    (leftDerivedUpperStarTensor Λ p)).app K).app L)
  exact Iff.rfl

attribute [local irreducible] moduleObjectProjectionMap moduleObjectProjectionData
  projectionMap derivedTensor

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The bounded integral proper projection formula, tensor closure of the localizing
categories on every standing scheme, and the projection formula on those closures.
Source: blueprint sk-thm-sf-pf-adic-projection, clauses (1)--(2)
(blueprint: lemma-projection-formula-integral-coefficients--1).

Proof:
1. A standing scheme is quasi-compact and locally Noetherian. The integral
constructibility comparison identifies the adopted generators with the stated
constant-model generators. Apply the existing bounded proper projection formula
in the category of schemes over `Spec k`.
2. Tensor in either variable is exact and a left adjoint. The inverse image of a
localizing subcategory under it is therefore localizing. Bounded integral tensor
closure and two applications of minimality prove tensor closure on the stated
localizing category, using its existing localizing-closure existence theorem.
3. Compare the two coproduct-universe conventions. For an existing coproduct,
its nonzero summands embed into the endomorphism set of its vertex by their
coordinate idempotents. Thus its nonzero support is Hom-small. Restrict the
coproduct to this support and shrink it; the omitted zero summands contribute
unique maps. This identifies the two localizing closures by minimality.
4. Choose the existing uniform fibre-dimension bound. Field base change does not
increase the dimension, so the integral proper-direct-sums theorem gives proper
pushforward stability and preservation of the required coproduct cofans.
5. Apply the existing two-variable localizing determination theorem to the
canonical projection map. Its shift compatibility and exactness are those proved
in the adopted `ProjectionMapShift` implementation. Bounded pullback and tensor
stability are supplied by `integralTensorInverseImage`; step 1 supplies the
isomorphism on generators. The resulting map is definitionally the stated
module-object projection map.
-/
theorem integralProperProjectionFormula (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    (∀ (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)))
      (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y L →
      IsIso (moduleObjectProjectionMap (Profinite.padicIntegersRingObj ℓ E.val) p K L)) ∧
    (∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))]
      (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) T))),
      localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) T) K →
      localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) T) L →
      localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) T)
        (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) T).obj K).obj L)) ∧
    (∀ (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)))
      (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y))),
      localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X) K →
      localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y) L →
      IsIso (moduleObjectProjectionMap (Profinite.padicIntegersRingObj ℓ E.val) p K L)) := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  have hbc (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))] :
      boundedConstructible (condensedRingObj Λ T) = constantModelBoundedConstructible Λ T := by
    let : IsLocallyNoetherian T :=
      LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
    let : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace
      (T ↘ Spec (.of k))
    exact (adicConstructibilityPredicateComparison ℓ T Λ
      (IsEllAdicCoefficient.integral E.val)).2
  have hbounded : ∀ K L, constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ Y L →
      IsIso (moduleObjectProjectionMap Λ p K L) := by
    intro K L hK hL
    let p' : Over.mk (X ↘ Spec (.of k)) ⟶ Over.mk (Y ↘ Spec (.of k)) :=
      Over.homMk p (CategoryTheory.comp_over p (Spec (.of k)))
    let : LocallyOfFiniteType (Over.mk (X ↘ Spec (.of k))).hom :=
      (inferInstance : LocallyOfFiniteType (X ↘ Spec (.of k)))
    let : QuasiCompact (Over.mk (X ↘ Spec (.of k))).hom :=
      (inferInstance : QuasiCompact (X ↘ Spec (.of k)))
    let : IsSeparated (Over.mk (X ↘ Spec (.of k))).hom :=
      (inferInstance : IsSeparated (X ↘ Spec (.of k)))
    let : LocallyOfFiniteType (Over.mk (Y ↘ Spec (.of k))).hom :=
      (inferInstance : LocallyOfFiniteType (Y ↘ Spec (.of k)))
    let : QuasiCompact (Over.mk (Y ↘ Spec (.of k))).hom :=
      (inferInstance : QuasiCompact (Y ↘ Spec (.of k)))
    let : IsSeparated (Over.mk (Y ↘ Spec (.of k))).hom :=
      (inferInstance : IsSeparated (Y ↘ Spec (.of k)))
    let : IsProper p'.left := (inferInstance : IsProper p)
    apply projection_bounded ℓ E.val p' K L
    · change boundedConstructible (condensedRingObj Λ X) K
      rwa [hbc X]
    · change boundedConstructible (condensedRingObj Λ Y) L
      rwa [hbc Y]
  refine ⟨hbounded, ?_, ?_⟩
  · intro T _ _ _ _ K L hK hL
    let : BraidedCategory (DerivedCategory (Mod
        (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :=
      Classical.choice (DerivedCategory.nonempty_braidedCategory _)
    apply localizing_tensor_closed (derivedTensor Λ T) (MonoidalCategory.curriedTensor _)
      (by unfold derivedTensor; rfl)
      (constantModelBoundedConstructible Λ T)
      (localizingClosure_exists Λ T _).2.2.2.1 ?_ K L hK hL
    intro A B hA hB
    rw [← hbc T] at hA hB ⊢
    exact (integralTensorInverseImage ℓ E k (𝟙 T)).2.1 A B hA hB
  · intro K L hK hL
    have heq (T : Scheme.{u}) [T.Over (Spec (.of k))]
        [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))] :
        localizingBoundedConstructible Λ T =
          localizingClosure (constantModelBoundedConstructible Λ T) := by
      change (boundedConstructible (condensedRingObj Λ T)).localizingClosure = _
      rw [hbc T]
      apply le_antisymm
      · let := localizing_small
            (localizingClosure (constantModelBoundedConstructible Λ T))
            (localizingClosure_exists Λ T
              (constantModelBoundedConstructible Λ T)).2.2.2.1
        exact ObjectProperty.localizingClosure_le (fun A hA P _ hSP ↦ hSP A hA)
      · intro A hA
        exact hA _ (localizing_large _) (ObjectProperty.le_localizingClosure _)
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
      (Y ↘ Spec (.of k))
    obtain ⟨d, hd'⟩ := exists_fibre_dimension_bound p
    have hd (y : Y) : topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
      let t := CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))
      calc
        _ = topologicalKrullDim (pullback (pullback.snd p (Y.fromSpecResidueField y))
            (Spec.map t) : Scheme.{u}) :=
          (IsHomeomorph.topologicalKrullDim_eq _
            ((pullbackLeftPullbackSndIso p (Y.fromSpecResidueField y)
              (Spec.map t)).hom.homeomorph.isHomeomorph)).symm
        _ ≤ topologicalKrullDim (p.fiber y) := topologicalKrullDim_pullback_le_of_field _ _
        _ ≤ _ := hd' y
    have hs := AlgebraicGeometry.ProEtale.integralProperDirectSums ℓ E k (ringChar k)
      (Fact.out : (ringChar k).Prime).pos Fact.out X Y p d hd
    have hpush : ∀ M, localizingBoundedConstructible Λ X M →
        localizingBoundedConstructible Λ Y ((lowerStar Λ p).rightDerivedFunctor.obj M) := by
      intro M hM
      rw [heq X] at hM
      rw [heq Y]
      exact hs.2.2.2.2.1 M hM
    have hsum : (lowerStar Λ p).rightDerivedFunctor.PreservesCoproductsOn.{u + 1}
        (localizingBoundedConstructible Λ X) := by
      rw [heq X]
      exact canonical_sums_preserved _ _ hs.2.2.2.2.2
    have hPF (A B) (hA : boundedConstructible (condensedRingObj Λ X) A)
        (hB : boundedConstructible (condensedRingObj Λ Y) B) :
        IsIso (((projectionMap Λ p).app A).app B) := by
      have h := hbounded A B ((congrFun (hbc X) A).mp hA)
        ((congrFun (hbc Y) B).mp hB)
      exact (canonical_projection_isIso Λ p A B).mp h
    apply (canonical_projection_isIso Λ p K L).mpr
    exact isIso_projectionMap_of_localizingBoundedConstructible Λ p hpush hsum
      (fun A hA ↦ ((integralTensorInverseImage ℓ E k p).1 A hA).1)
      (fun A B hA hB ↦ by
        simpa only [WeilConjectures.SixFunctors.integralModel_coefficientMonObj,
          derivedTensor, MonoidalCategory.curriedTensor_obj_obj] using
          (integralTensorInverseImage ℓ E k (𝟙 X)).2.1 A B hA hB)
      hPF ((congrFun (heq X) K).mpr hK) ((congrFun (heq Y) L).mpr hL)

end AlgebraicGeometry.ProEtale.CondensedRing
