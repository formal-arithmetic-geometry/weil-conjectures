/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralTensorPullbackData

import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralPullbackInternalRoosUnit
import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralPullbackConstantRoosUnit
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueCriterion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompletionTriangle.CompletionTriangleComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorShriek
public import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsStacksBlueprint
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelHeart
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacks
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange

/-! # Integral inverse image preserves constructibility and completed pullback

Source: blueprint det-lem-int-tensor-pullback.
(blueprint: det-lem-int-tensor-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.IntegralTensorPullback

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem detectIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z U : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (φ : M ⟶ N) (hi : IsIso ((upperStar Λ i).map φ))
    (hj : IsIso ((upperStar Λ j).map φ)) : IsIso φ := by
  have := hi
  have := hj
  have hker : ∀ {T : Scheme.{u}} (f : T ⟶ X)
      [IsIso ((upperStar Λ f).map φ)],
      IsZero ((upperStar Λ f).obj (kernel φ)) := fun f _ ↦
    (isZero_kernel_of_mono ((upperStar Λ f).map φ)).of_iso
      (PreservesKernel.iso _ φ)
  have hcoker : ∀ {T : Scheme.{u}} (f : T ⟶ X)
      [IsIso ((upperStar Λ f).map φ)],
      IsZero ((upperStar Λ f).obj (cokernel φ)) := fun f _ ↦
    (isZero_cokernel_of_epi ((upperStar Λ f).map φ)).of_iso
      (PreservesCokernel.iso _ φ)
  have hcompl : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [hU]
    exact isCompl_compl
  have : Mono φ := Preadditive.mono_of_isZero_kernel _
    (isZero_of_isZero_upperStar_of_isCompl Λ i j hcompl _ (hker i) (hker j))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _
    (isZero_of_isZero_upperStar_of_isCompl Λ i j hcompl _ (hcoker i) (hcoker j))
  exact isIso_of_mono_of_epi φ

private theorem closedCounit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z U : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ) :
    IsIso (upperStarLowerStarAdjunction Λ i).counit := by
  exact moduleCounitOfAbelian Λ i (abelian_closed_support i j hU).1

/-- Open and closed base change in the fixed condensed coefficient presentation.
This is the module transport of the open--closed base change in blueprint P2:
transpose the inverse-image square comparisons, then test each mate on the open
and closed pieces. The open units and closed counits are isomorphisms and the
cross restrictions vanish. -/
private theorem openClosedBaseChange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z U : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    {X' : Scheme.{u}} (g : X' ⟶ X) :
    Nonempty (openImmersionLowerShriek Λ j ⋙ upperStar Λ g ≅
      upperStar Λ (pullback.snd g j) ⋙ openImmersionLowerShriek Λ (pullback.fst g j)) ∧
    Nonempty (lowerStar Λ i ⋙ upperStar Λ g ≅
      upperStar Λ (pullback.snd g i) ⋙ lowerStar Λ (pullback.fst g i)) := by
  let delta := upperStarSquareComparison Λ (IsPullback.of_hasPullback g j).flip.toCommSq
  let gamma := upperStarSquareComparison Λ (IsPullback.of_hasPullback g i).flip.toCommSq
  have hU' : Set.range (pullback.fst g j) = (Set.range (pullback.fst g i))ᶜ := by
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, hU]
    rfl
  have hc := closedCounit Λ i j hU
  have hc' := closedCounit Λ (pullback.fst g i) (pullback.fst g j) hU'
  have hu := openUnitIsIso Λ j
  have hu' := openUnitIsIso Λ (pullback.fst g j)
  let a := openImmersionLowerShriekUpperStarAdjunction Λ j
  let a' := openImmersionLowerShriekUpperStarAdjunction Λ (pullback.fst g j)
  let b := upperStarLowerStarAdjunction Λ i
  let b' := upperStarLowerStarAdjunction Λ (pullback.fst g i)
  let qU := upperStar Λ (pullback.snd g j)
  let qZ := upperStar Λ (pullback.snd g i)
  have hv (G) : IsZero ((upperStar Λ j).obj ((lowerStar Λ i).obj G)) :=
    openRestrictionPushforwardZero Λ i j hU G
  have hv' (G) : IsZero ((upperStar Λ (pullback.fst g j)).obj
      ((lowerStar Λ (pullback.fst g i)).obj G)) :=
    openRestrictionPushforwardZero Λ (pullback.fst g i) (pullback.fst g j) hU' G
  have hzi (N) : IsZero ((upperStar Λ i).obj ((openImmersionLowerShriek Λ j).obj N)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (b.homEquiv _ _).injective
    apply (a.homEquiv _ _).injective
    exact (hv _).eq_of_tgt _ _
  have hzi' (N) : IsZero ((upperStar Λ (pullback.fst g i)).obj
      ((openImmersionLowerShriek Λ (pullback.fst g j)).obj N)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (b'.homEquiv _ _).injective
    apply (a'.homEquiv _ _).injective
    exact (hv' _).eq_of_tgt _ _
  let t : qU ⋙ openImmersionLowerShriek Λ (pullback.fst g j) ⟶
      openImmersionLowerShriek Λ j ⋙ upperStar Λ g :=
    { app N := (a'.homEquiv _ _).symm
        (qU.map (a.unit.app N) ≫ delta.inv.app ((openImmersionLowerShriek Λ j).obj N))
      naturality N P φ := by
        apply (a'.homEquiv _ _).injective
        change a'.homEquiv _ _
            ((openImmersionLowerShriek Λ (pullback.fst g j)).map (qU.map φ) ≫ _) =
          a'.homEquiv _ _ (_ ≫ (upperStar Λ g).map ((openImmersionLowerShriek Λ j).map φ))
        rw [a'.homEquiv_naturality_left, a'.homEquiv_naturality_right]
        simp only [Functor.comp_obj, Equiv.apply_symm_apply]
        have hn := delta.inv.naturality ((openImmersionLowerShriek Λ j).map φ)
        change qU.map ((upperStar Λ j).map
            ((openImmersionLowerShriek Λ j).map φ)) ≫ delta.inv.app _ =
          delta.inv.app _ ≫ _ at hn
        rw [Category.assoc]
        erw [← hn]
        simp only [← Category.assoc, ← qU.map_comp]
        congr 2
        exact a.unit.naturality φ }
  let v : lowerStar Λ i ⋙ upperStar Λ g ⟶
      qZ ⋙ lowerStar Λ (pullback.fst g i) :=
    { app G := b'.homEquiv _ _
        (gamma.hom.app ((lowerStar Λ i).obj G) ≫ qZ.map (b.counit.app G))
      naturality G H φ := by
        apply (b'.homEquiv _ _).symm.injective
        change (b'.homEquiv _ _).symm
            ((upperStar Λ g).map ((lowerStar Λ i).map φ) ≫ _) =
          (b'.homEquiv _ _).symm (_ ≫
            (lowerStar Λ (pullback.fst g i)).map (qZ.map φ))
        rw [b'.homEquiv_naturality_left_symm, b'.homEquiv_naturality_right_symm]
        simp only [Functor.comp_obj, Equiv.symm_apply_apply]
        have hn := gamma.hom.naturality ((lowerStar Λ i).map φ)
        change _ ≫ gamma.hom.app _ = gamma.hom.app _ ≫
          qZ.map ((upperStar Λ i).map ((lowerStar Λ i).map φ)) at hn
        rw [← Category.assoc]
        erw [hn]
        simp only [Category.assoc, ← qZ.map_comp]
        congr 2
        exact b.counit.naturality φ }
  have ht (N) : IsIso (t.app N) := by
    apply detectIso Λ (pullback.fst g i) (pullback.fst g j) hU'
    · have hs := hzi' (qU.obj N)
      have ht := (qZ.map_isZero (hzi N)).of_iso
        (gamma.app ((openImmersionLowerShriek Λ j).obj N))
      exact isIso_of_source_target_iso_zero _ hs.isoZero ht.isoZero
    · have he : a'.unit.app (qU.obj N) ≫
          (upperStar Λ (pullback.fst g j)).map (t.app N) =
          qU.map (a.unit.app N) ≫ delta.inv.app ((openImmersionLowerShriek Λ j).obj N) := by
        exact (a'.homEquiv _ _).apply_symm_apply _
      have : IsIso (a.unit.app N) := inferInstance
      have : IsIso (a'.unit.app (qU.obj N)) := inferInstance
      have : IsIso (a'.unit.app (qU.obj N) ≫
          (upperStar Λ (pullback.fst g j)).map (t.app N)) := by
        rw [he]
        infer_instance
      exact IsIso.of_isIso_comp_left (a'.unit.app (qU.obj N)) _
  have hvIso (G) : IsIso (v.app G) := by
    apply detectIso Λ (pullback.fst g i) (pullback.fst g j) hU'
    · have he : (upperStar Λ (pullback.fst g i)).map (v.app G) ≫
          b'.counit.app (qZ.obj G) =
          gamma.hom.app ((lowerStar Λ i).obj G) ≫ qZ.map (b.counit.app G) := by
        exact (b'.homEquiv _ _).symm_apply_apply _
      have : IsIso (b.counit.app G) := inferInstance
      have : IsIso (b'.counit.app (qZ.obj G)) := inferInstance
      have : IsIso ((upperStar Λ (pullback.fst g i)).map (v.app G) ≫
          b'.counit.app (qZ.obj G)) := by
        rw [he]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (b'.counit.app (qZ.obj G))
    · have hs := (qU.map_isZero (hv G)).of_iso
        (delta.app ((lowerStar Λ i).obj G))
      have ht := hv' (qZ.obj G)
      exact isIso_of_source_target_iso_zero _ hs.isoZero ht.isoZero
  have : IsIso t := (NatTrans.isIso_iff_isIso_app _).2 ht
  have : IsIso v := (NatTrans.isIso_iff_isIso_app _).2 hvIso
  exact ⟨⟨(asIso t).symm⟩, ⟨asIso v⟩⟩

private theorem closedBaseChangeDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y Z X : Scheme.{u}} [IsNoetherian Y]
    (i : Z ⟶ Y) [IsClosedImmersion i] (g : X ⟶ Y) :
    Nonempty ((lowerStar Λ i).rightDerivedFunctor ⋙ (upperStar Λ g).mapDerivedCategory ≅
      (upperStar Λ (pullback.snd g i)).mapDerivedCategory ⋙
        (lowerStar Λ (pullback.fst g i)).rightDerivedFunctor) := by
  let U : Y.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : Set.range U.ι = (Set.range i)ᶜ := U.range_ι
  obtain ⟨hi, _⟩ := condensed_open_closed_recollement Λ i U.ι hU
  let := hi
  have hU' : Set.range (pullback.fst g U.ι) = (Set.range (pullback.fst g i))ᶜ := by
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, hU]
    rfl
  obtain ⟨hi', _⟩ := condensed_open_closed_recollement Λ
    (pullback.fst g i) (pullback.fst g U.ι) hU'
  let := hi'
  obtain ⟨e⟩ := (openClosedBaseChange Λ i U.ι hU g).2
  let Ri := lowerStar Λ i
  let Ri' := lowerStar Λ (pullback.fst g i)
  let G := upperStar Λ g
  let Gz := upperStar Λ (pullback.snd g i)
  exact ⟨Functor.isoWhiskerRight Ri.rightDerivedFunctorIsoMapDerivedCategory G.mapDerivedCategory ≪≫
    (Functor.mapDerivedCategoryCompIso Ri G).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso Gz Ri' ≪≫
    Functor.isoWhiskerLeft Gz.mapDerivedCategory Ri'.rightDerivedFunctorIsoMapDerivedCategory.symm⟩

private theorem openBaseChangeDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y S X : Scheme.{u}}
    (v : S ⟶ Y) [IsOpenImmersion v] [QuasiCompact v] (g : X ⟶ Y) :
    Nonempty ((openImmersionLowerShriek Λ v).mapDerivedCategory ⋙ (upperStar Λ
        g).mapDerivedCategory ≅
      (upperStar Λ (pullback.snd g v)).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ (pullback.fst g v)).mapDerivedCategory) := by
  have hU : Set.range v = (Set.range v.closedComplement)ᶜ := by
    rw [v.range_closedComplement, compl_compl]
  obtain ⟨e⟩ := (openClosedBaseChange Λ v.closedComplement v hU g).1
  exact ⟨(Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso _ _⟩

/-- The natural completion comparison is invertible on bounded constructible inputs,
and its scalar restriction is the Stacks completed inverse image with the same unit.
All K-flat representatives are allowed; they merely compute the fixed derived objects.
Source: blueprint det-lem-int-tensor-pullback, clauses (1),(2); Stacks 099I, 09C4
(blueprint: det-lem-int-tensor-pullback).

Proof (the four paragraphs of the current blueprint):
1. Cartesian coefficients identify inverse image of the integral and finite rings with
   their pullbacks. Inverse image is exact and commutes with the reduction cones.
   The quotient augmentation defines c_K, the completion map of g^*K, so it is
   invertible exactly when g^*K is derived complete. Both functors and c are exact.
2. For a stratum a = i u and a local model M with bounded finite free scalar
   complexes on a pro-etale cover, base change for u_! and i_* identifies g^*a_!M
   with a'_!g_S^*M. The base-changed cover has the same finite free scalar models.
   The integral criterion gives bounded constructibility on S', and extension by
   zero gives it on X. The criterion also gives completeness, hence invertibility
   of c on these generators.
3. Every bounded constructible K is obtained by finitely many localization
   extensions from those generators. Exactness and triangulated closure propagate
   bounded constructibility; the five lemma propagates invertibility of c.
4. Restriction to constant integral scalars commutes with inverse image, reduction
   and products, hence with the Roos limit. Its target is the constant-coefficient
   completed inverse image of Stacks 09C4, with the same quotient augmentation.
   The final equation expresses this compatibility including the canonical unit.
The zero complex, empty schemes and identity morphism require no exclusions. -/
theorem preserves_and_completed
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] (g : X ⟶ Y) [g.IsOver (Spec (.of k))]
    (K : DerivedCategory (AdicCompletion.Modules l E Y))
    (_hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) Y K) :
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X
      (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapDerivedCategory).obj K) ∧
    ∀ (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ)
      (_hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E Y) (.up ℤ)).kFlat P)
      (_eP : DerivedCategory.Q.obj P ≅ K),
      IsIso (DerivedCategory.Q.map (comparison l E g P)) ∧
      ∃ e : DerivedCategory.Q.obj
          (((restriction l E X).mapHomologicalComplex (.up ℤ)).obj
            (WeilConjectures.integralOperationsRoos (pulledTower l E g P))) ≅
          DerivedCategory.Q.obj (WeilConjectures.integralOperationsRoos
            (constantPulledTower l E g
              (((restriction l E Y).mapHomologicalComplex (.up ℤ)).obj P))),
        DerivedCategory.Q.map
            (((restriction l E X).mapHomologicalComplex (.up ℤ)).map (comparison l E g P)) ≫
            e.hom =
          DerivedCategory.Q.map (restrictionPullbackComplex l E g P).hom ≫
            DerivedCategory.Q.map (constantComparison l E g
              (((restriction l E Y).mapHomologicalComplex (.up ℤ)).obj P)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace X :=
    (quasiSeparated_iff_quasiSeparatedSpace (X ↘ Spec (.of k))).mp inferInstance
  have : QuasiSeparatedSpace Y :=
    (quasiSeparated_iff_quasiSeparatedSpace (Y ↘ Spec (.of k))).mp inferInstance
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  let F := CondensedRing.upperStar (DerivedNakayama.integerRing l E) g
  obtain ⟨hbc, hc⟩ := pullbackDevissage l E k p _hp _hpl g K _hK
  let φ := (IntegralConstantModel.pointComparison l E).inv.hom
  let H := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap φ X)
  have hB := (cbcComapIff φ X (F.mapDerivedCategory.obj K)).mpr hbc
  have hStacks := stacksConstructibleInterpretation l E X _ hB
  have hModels := ((IntegralModelsStacks.integral_models_stacks l E X).1
    (H.mapDerivedCategory.obj (F.mapDerivedCategory.obj K))).mpr hStacks
  refine ⟨(cbcComapIff φ X _).mp hModels, ?_⟩
  intro P hP eP
  have hQ := CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj
    (DerivedNakayama.integerRing l E) g hP
  let eQ := (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso eP
  have hu := (AdicCompletion.isDerivedComplete_iff l E X _ _ hQ eQ).mp hc
  constructor
  · obtain ⟨e, he⟩ := ordinary_roos_unit l E g P
    change IsIso (eQ.inv ≫ DerivedCategory.Q.map
      (AdicCompletion.augmentation l E X
        ((F.mapHomologicalComplex (.up ℤ)).obj P))) at hu
    have := hu
    have : IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X
        ((F.mapHomologicalComplex (.up ℤ)).obj P))) :=
      IsIso.of_isIso_comp_left eQ.inv _
    have : IsIso (DerivedCategory.Q.map (comparison l E g P) ≫
        DerivedCategory.Q.map e.hom) := by
      rw [← Functor.map_comp, he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (DerivedCategory.Q.map e.hom)
  · obtain ⟨e, he⟩ := constant_roos_unit l E g P
    refine ⟨DerivedCategory.Q.mapIso e, ?_⟩
    simpa only [Functor.map_comp, Functor.mapIso_hom] using congrArg DerivedCategory.Q.map he

/-- The integral-models equivalence interprets the pulled object in the Stacks
constructible category. Its comparison with scalar restriction identifies its image;
the criterion reflects that image back to the internal presentation. This records the
category identification of P4 before the explicit normalized unit equation. -/
private theorem stacksConstructibleInterpretation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (pulledBackModuleObjects (IntegralModelsStacks.integersObj l E) X))
    (hK : constantModelBoundedConstructible (IntegralModelsStacks.integersObj l E) X K) :
    IntegralModelsStacks.stacksConstructible l E X
      ((IntegralModelsStacks.restriction l E X).obj K) := by
  let B := constantModelBoundedConstructible (IntegralModelsStacks.integersObj l E) X
  let S := IntegralModelsStacks.stacksConstructible l E X
  obtain ⟨_, e, ⟨he⟩⟩ := IntegralModelsStacks.integral_models_stacks l E X
  have : S.IsClosedUnderIsomorphisms := ⟨fun i h ↦
    IntegralModelsStacks.bp_stacksConstructible_iso l E X i h⟩
  exact membershipOfInclusionComparison B S (IntegralModelsStacks.restriction l E X)
    e he K hK

/-- Transport an object's membership across the inclusion comparison of an equivalence
of full subcategories. Keeping this categorical step abstract avoids unfolding the
coefficient constructions while checking the comparison. -/
private theorem membershipOfInclusionComparison
    {C D : Type*} [Category C] [Category D]
    (B : ObjectProperty C) (S : ObjectProperty D) [S.IsClosedUnderIsomorphisms]
    (F : C ⥤ D) (e : B.FullSubcategory ≌ S.FullSubcategory)
    (he : e.functor ⋙ S.ι ≅ B.ι ⋙ F) (K : C) (hK : B K) : S (F.obj K) := by
  let A : B.FullSubcategory := ⟨K, hK⟩
  exact S.prop_of_iso (he.app A) (e.functor.obj A).property

private theorem pullbackDevissage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ l)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] (g : X ⟶ Y)
    (K : DerivedCategory (AdicCompletion.Modules l E Y))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) Y K) :
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X
        ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapDerivedCategory.obj K) ∧
      IsDerivedComplete l E X
        ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapDerivedCategory.obj K) :=
            by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
  let Λ := DerivedNakayama.integerRing l E
  let F := CondensedRing.upperStar Λ g
  let B := constantModelBoundedConstructible Λ X
  let C : ObjectProperty (DerivedCategory (AdicCompletion.Modules l E X)) := IsDerivedComplete l E X
  have : B.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
  have : B.IsTriangulated := integerHeart l E X
  have : C.IsClosedUnderIsomorphisms := ⟨by
    intro K L e hK
    obtain ⟨M, hM, ⟨eM⟩, h⟩ := hK
    exact ⟨M, hM, ⟨eM ≪≫ e⟩, h⟩⟩
  have : C.IsTriangulated := completeTriangulated l E X
  let P := (B ⊓ C).inverseImage F.mapDerivedCategory
  have : P.IsTriangulated := inferInstance
  have : P.IsClosedUnderIsomorphisms := inferInstance
  have hcmp (T : Scheme.{u}) [IsNoetherian T]
      (L : DerivedCategory (AdicCompletion.Modules l E T)) :
      boundedConstructible (AdicCompletion.ring l E T) L ↔
        constantModelBoundedConstructible Λ T L :=
    and_congr Iff.rfl (forall_congr' fun n ↦ integerConstructibleComparison l E T _)
  apply integerShriekGenerated l E k p hp hpl Y K ((hcmp Y K).mpr hK) P
  intro T a Z v i hv hi hvi M hM hmodels
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  let : IsNoetherian Z := ⟨⟩
  let Z' := pullback g i
  let i' : Z' ⟶ X := pullback.fst g i
  let gz : Z' ⟶ Z := pullback.snd g i
  let S' := pullback gz v
  let v' : S' ⟶ Z' := pullback.fst gz v
  let gs : S' ⟶ T.domain a := pullback.snd gz v
  have : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian i'
  have : CompactSpace Z' := QuasiCompact.compactSpace_of_compactSpace i'
  have : IsNoetherian Z' := ⟨⟩
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian v'
  have : TopologicalSpace.NoetherianSpace S' :=
    v'.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : IsNoetherian S' := ⟨⟩
  let M' := (CondensedRing.upperStar Λ gs).mapDerivedCategory.obj M
  have hm' : constantModelBoundedConstructible Λ S' M' := pullbackFreeModels l E gs M hmodels
  have hext : B (((CondensedRing.openImmersionLowerShriek Λ v').mapDerivedCategory ⋙
      (CondensedRing.lowerStar Λ i').rightDerivedFunctor).obj M') :=
    (hcmp X _).mp ((integerShriekPreserves l E k p hp hpl X).2.2 S' Z' v' i' M'
      ((hcmp S' M').mpr hm'))
  obtain ⟨ec⟩ := CondensedRing.closedBaseChangeDerived Λ i g
  obtain ⟨eo⟩ := CondensedRing.openBaseChangeDerived Λ v gz
  let e := ec.app ((CondensedRing.openImmersionLowerShriek Λ v).mapDerivedCategory.obj M) ≪≫
    (CondensedRing.lowerStar Λ i').rightDerivedFunctor.mapIso (eo.app M)
  have hbc : B (F.mapDerivedCategory.obj
      (((CondensedRing.openImmersionLowerShriek Λ v).mapDerivedCategory ⋙
        (CondensedRing.lowerStar Λ i).rightDerivedFunctor).obj M)) :=
    B.prop_of_iso e.symm hext
  have hc := ((condensed_integral_criterion l E X (F.mapDerivedCategory.obj
    (((CondensedRing.openImmersionLowerShriek Λ v).mapDerivedCategory ⋙
      (CondensedRing.lowerStar Λ i).rightDerivedFunctor).obj M))).out 0 1).mp hbc
  exact ⟨hbc, hc.1⟩

private theorem integerConstructibleComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (M : AdicCompletion.Modules l E X) :
    IsConstructibleModuleObject (AdicCompletion.ring l E X) M ↔
      IsConstantModelConstructible (DerivedNakayama.integerRing l E) X M := by
  obtain ⟨F, nf, na, fd, ⟨e⟩⟩ := coefficientSmallIso l E
  let := nf
  let := na
  let := fd
  let e₀ : Mon.mk (DerivedNakayama.integerRing l E) ≅
      Mon.mk (integralModelCondensedCoefficients l E).X :=
    eqToIso (IntegralConstantModel.pointEquality l E)
  have transport (B C : Subring F) (h : B = C) :
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} B) ≅
        Mon.mk (Profinite.continuousMapRingObj.{u} C)) := by
    subst C
    exact ⟨Iso.refl _⟩
  obtain ⟨e₂⟩ := transport _ _ (CondensedRing.continuousIntegers_eq l F)
  obtain ⟨e₁⟩ := smallIntegralCoefficientIso l F
  let e' := e₁ ≪≫ e₂.symm ≪≫ (e₀ ≪≫ e).symm
  exact (comparisonThroughIso l F (DerivedNakayama.integerRing l E) e'.hom.hom X M).symm

private theorem completeTriangulated
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ObjectProperty.IsTriangulated (IsDerivedComplete l E X) := by
  let P : ObjectProperty (DerivedCategory (AdicCompletion.Modules l E X)) :=
    IsDerivedComplete l E X
  let : P.IsClosedUnderIsomorphisms := ⟨by
    intro K L e hK
    obtain ⟨M, hM, ⟨eM⟩, h⟩ := hK
    exact ⟨M, hM, ⟨eM ≪≫ e⟩, h⟩⟩
  obtain ⟨data, hdata, a, F, c, κ, sF, hF, ha, hc, hψ, hcomplete, hshift, htri⟩ :=
    CompletionTriangle.completion_triangle_comparison l E X
  let : F.Additive := hF
  let : P.ContainsZero := ⟨⟨0, isZero_zero _,
    (hcomplete 0).mpr
      ((isZero_zero _).isIso (F.map_isZero (isZero_zero _)) (c.app 0))⟩⟩
  let : P.IsTriangulatedClosed₁ := .mk' (by
    intro T hT h₂ h₃
    obtain ⟨hd, γ, h₁', h₂', h₃'⟩ := htri T hT
    apply (hcomplete _).mpr
    rw [← h₁']
    exact isIso₁_of_isIso₂₃ γ hT hd
      (h₂' ▸ (hcomplete _).mp h₂) (h₃' ▸ (hcomplete _).mp h₃))
  let : P.IsTriangulatedClosed₂ := .mk' (by
    intro T hT h₁ h₃
    obtain ⟨hd, γ, h₁', h₂', h₃'⟩ := htri T hT
    apply (hcomplete _).mpr
    rw [← h₂']
    exact isIso₂_of_isIso₁₃ γ hT hd
      (h₁' ▸ (hcomplete _).mp h₁) (h₃' ▸ (hcomplete _).mp h₃))
  let : P.IsTriangulatedClosed₃ := .mk' (by
    intro T hT h₁ h₂
    obtain ⟨hd, γ, h₁', h₂', h₃'⟩ := htri T hT
    apply (hcomplete _).mpr
    rw [← h₃']
    exact isIso₃_of_isIso₁₂ γ hT hd
      (h₁' ▸ (hcomplete _).mp h₁) (h₂' ▸ (hcomplete _).mp h₂))
  exact triangulatedOfThree P

private theorem pullbackFreeModels
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {S S' : Scheme.{u}} [IsNoetherian S'] (g : S' ⟶ S)
    (M : DerivedCategory (AdicCompletion.Modules l E S))
    (hM : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ b : C.I₀,
      ∃ Q : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          (DerivedNakayama.integerRing l E)) ℤ,
        (∃ r s : ℤ, ∀ n : ℤ, n < r ∨ s < n → IsZero (Q.X n)) ∧
        (∀ n : ℤ, Mod.IsFree (DerivedNakayama.integerRing l E) (Q.X n)) ∧
        Nonempty ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
          (C.f b)).mapDerivedCategory.obj M ≅ DerivedCategory.Q.obj
            ((((upperStarFromPoint (C.X b)).mapMod (DerivedNakayama.integerRing l
                E)).mapHomologicalComplex (.up ℤ)).obj Q))) :
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) S'
      ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapDerivedCategory.obj M) := by
  let Λ := DerivedNakayama.integerRing l E
  let G := CondensedRing.upperStar Λ g
  apply ((condensed_integral_criterion l E S' (G.mapDerivedCategory.obj M)).out 2 0).mp
  obtain ⟨C, hC⟩ := hM
  let V : Scheme.Cover.{u} Scheme.proetalePrecoverage S' := C.pullback₂ g
  refine ⟨Scheme.Stratification.trivial S', fun a ↦ ?_⟩
  fin_cases a
  refine ⟨V, fun b ↦ ?_⟩
  obtain ⟨Q, ⟨r, s, hbd⟩, hf, ⟨eQ⟩⟩ := hC b
  have hr : Q.IsStrictlyGE r := (Q.isStrictlyGE_iff r).mpr (fun n hn ↦ hbd n (Or.inl hn))
  have hs : Q.IsStrictlyLE s := (Q.isStrictlyLE_iff s).mpr (fun n hn ↦ hbd n (Or.inr hn))
  refine ⟨Q, r, s, hr, hs, hf, ⟨?_⟩⟩
  let q : V.X b ⟶ C.X b := pullback.fst (C.f b) g
  let Fv := CondensedRing.upperStar Λ (V.f b)
  let Fq := CondensedRing.upperStar Λ q
  let Fc := CondensedRing.upperStar Λ (C.f b)
  let evg : CondensedRing.upperStar Λ (V.f b ≫ g) ≅ G ⋙ Fv :=
    CondensedRing.upperStarComp Λ (V.f b) g
  let eqc : CondensedRing.upperStar Λ (q ≫ C.f b) ≅ Fc ⋙ Fq :=
    CondensedRing.upperStarComp Λ q (C.f b)
  have comm : V.f b ≫ g = q ≫ C.f b := pullback.condition.symm
  let epull : G.mapDerivedCategory ⋙ Fv.mapDerivedCategory ≅
      Fc.mapDerivedCategory ⋙ Fq.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso G Fv).symm ≪≫
      Functor.mapDerivedCategoryNatIso evg.symm ≪≫
      Functor.mapDerivedCategoryNatIso (eqToIso (congrArg (CondensedRing.upperStar Λ) comm)) ≪≫
      Functor.mapDerivedCategoryNatIso eqc ≪≫ Functor.mapDerivedCategoryCompIso Fc Fq
  have exactPoint (T : Scheme.{u}) : PreservesFiniteLimits (upperStarFromPoint T) := by
    have : PreservesFiniteLimits pointUpperStar.{u} := by
      have : AB5OfSize.{u, u + 1} Ab.{u + 1} := AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
      dsimp [pointUpperStar, Functor.sheafPullbackConstruction.sheafPullback]
      infer_instance
    unfold upperStarFromPoint
    infer_instance
  have := exactPoint (C.X b)
  have := exactPoint (V.X b)
  have : ((upperStarFromPoint (C.X b)).mapMod Λ).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : ((upperStarFromPoint (V.X b)).mapMod Λ).Additive :=
    Functor.additive_of_preserves_binary_products _
  let epoint := pointPullbackIso Λ q
  let Qreal := ((upperStarFromPoint (C.X b)).mapMod Λ).mapHomologicalComplex (.up ℤ)
  let ep := Fq.mapDerivedCategoryFactors.app (Qreal.obj Q)
  let ec : (Fq.mapHomologicalComplex (.up ℤ)).obj (Qreal.obj Q) ≅
      (((upperStarFromPoint (V.X b)).mapMod Λ).mapHomologicalComplex (.up ℤ)).obj Q :=
    (Functor.mapHomologicalComplexCompIso epoint (.up ℤ)).app Q
  simpa only [Scheme.Stratification.trivial, Category.comp_id,
    condensedIntegralCriterionRealization, DerivedNakayama.pullback, Functor.comp_obj] using
    (epull.app M ≪≫ Fq.mapDerivedCategory.mapIso eQ ≪≫ ep ≪≫ DerivedCategory.Q.mapIso ec)

private noncomputable def pointPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarFromPoint Y).mapMod Λ ⋙ CondensedRing.upperStar Λ f ≅
      (upperStarFromPoint X).mapMod Λ := by
  let Fy : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤
      Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1} := upperStarFromPoint Y
  let G : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1} ⥤
      Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} := ProEtale.upperStar Ab.{u + 1} f
  let Fx : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤
      Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} := upperStarFromPoint X
  let φ := condensedPullbackHom Λ f
  let ecomp : Fy.mapMod Λ ⋙ G.mapMod (Fy.obj Λ) ≅ Fx.mapMod Λ ⋙ Mod.comap φ :=
    Functor.mapModCompIso Fy G (H := Fx) (upperStarFromPointComp f).hom Λ
  have : MonoidalClosed (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) := inferInstance
  have hleft (M : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) :=
    (ihom.adjunction M).leftAdjoint_preservesColimits
  have hright (M : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    GrothendieckTopology.hasSheafify_proEtTopology Ab.{u + 1} X
  have : HasWeakSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    HasSheafify.isRightAdjoint
  have : HasColimitsOfShape WalkingParallelPair Ab.{u + 1} := inferInstance
  have : HasCoequalizers (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    Sheaf.instHasColimitsOfShape.{u + 2, u + 1, u, u + 1, 0, 0}
      (J := Scheme.ProEt.topology X)
      (D := Ab.{u + 1}) (K := WalkingParallelPair)
  let esc : Mod.extendScalars.{u + 1, u + 2} φ ≅ Mod.comap (asIso φ).inv :=
    Mod.extendScalarsIsoComapInv.{u + 1, u + 2}
      (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
  let eunit : 𝟭 _ ≅ Mod.comap φ ⋙ Mod.comap (asIso φ).inv :=
    (Mod.comapEquivalenceOfIsIso (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ).unitIso
  unfold CondensedRing.upperStar
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ecomp _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ esc ≪≫ eunit.symm) ≪≫ Functor.rightUnitor _

private theorem integerShriekGenerated
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsNoetherian X]
    (K : DerivedCategory (pulledBackModuleObjects (DerivedNakayama.integerRing l E) X))
    (hK : boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) X) K)
    (P : ObjectProperty (DerivedCategory (pulledBackModuleObjects
      (DerivedNakayama.integerRing l E) X)))
    [P.IsClosedUnderIsomorphisms]
    [P.IsTriangulatedClosed₁] [P.IsTriangulatedClosed₂] [P.IsTriangulatedClosed₃]
    (hgen : ∀ (T : X.FiniteLocallyClosedStratification) (a : Fin T.n)
      (Z : Scheme.{u}) (v : T.domain a ⟶ Z) (i : Z ⟶ X)
      [IsOpenImmersion v] [IsClosedImmersion i],
      v ≫ i = T.immersion a →
      ∀ M : DerivedCategory (pulledBackModuleObjects (DerivedNakayama.integerRing l E)
        (T.domain a)),
        boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E)
          (T.domain a)) M →
        (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (T.domain a), ∀ b : C.I₀,
          ∃ Q : CochainComplex
            (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
              (DerivedNakayama.integerRing l E)) ℤ,
            (∃ r s : ℤ, ∀ n : ℤ, n < r ∨ s < n → IsZero (Q.X n)) ∧
            (∀ n : ℤ, Mod.IsFree (DerivedNakayama.integerRing l E) (Q.X n)) ∧
            Nonempty
              ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) (C.f
                b)).mapDerivedCategory.obj M ≅
                DerivedCategory.Q.obj
                  ((((upperStarFromPoint (C.X b)).mapMod (DerivedNakayama.integerRing l
                      E)).mapHomologicalComplex (.up ℤ)).obj Q))) →
        P (((CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E)
          v).mapDerivedCategory ⋙
          (CondensedRing.lowerStar (DerivedNakayama.integerRing l E)
            i).rightDerivedFunctor).obj M)) :
    P K := by
  let R : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
    ⟨(integralModelCondensedCoefficients l E).X⟩
  let S : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
    ⟨DerivedNakayama.integerRing l E⟩
  have heq : R = S := commMon_eq_of_toMon_eq (IntegralConstantModel.pointEquality l E).symm
  have h : generatedProperty R X := by
    simpa only [generatedProperty, integralTensorShriek_pointComplex] using
      integralTensorShriek_generated l E k p _hp _hpl X
  have h' : generatedProperty S X := heq ▸ h
  exact h' K hK P hgen

private theorem integerShriekPreserves
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsNoetherian X]
    : (∀ (U : Scheme.{u}) (j : U ⟶ X) [IsOpenImmersion j]
        (M : DerivedCategory (pulledBackModuleObjects (DerivedNakayama.integerRing l E)
          U)),
        boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) U) M →
          boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) X)
            ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E)
              j).mapDerivedCategory.obj M)) ∧
      (∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
        (M : DerivedCategory (pulledBackModuleObjects (DerivedNakayama.integerRing l E)
          Z)),
        boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) Z) M →
          boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) X)
            ((CondensedRing.lowerStar (DerivedNakayama.integerRing l E)
              i).rightDerivedFunctor.obj M)) ∧
      (∀ (S Z : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X)
        [IsOpenImmersion v] [IsClosedImmersion i]
        (M : DerivedCategory (pulledBackModuleObjects (DerivedNakayama.integerRing l E)
          S)),
        boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) S) M →
          boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) X)
            (((CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E)
              v).mapDerivedCategory ⋙
              (CondensedRing.lowerStar (DerivedNakayama.integerRing l E)
                i).rightDerivedFunctor).obj M)) := by
  let R : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
    ⟨(integralModelCondensedCoefficients l E).X⟩
  let S : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
    ⟨DerivedNakayama.integerRing l E⟩
  have heq : R = S := commMon_eq_of_toMon_eq (IntegralConstantModel.pointEquality l E).symm
  have h : preservesProperty R X := integralTensorShriek_preserves l E k p _hp _hpl X
  have h' : preservesProperty S X := heq ▸ h
  exact h'

private def generatedProperty (R : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (X : Scheme.{u}) : Prop :=
  ∀ (K : DerivedCategory (pulledBackModuleObjects R.X X))
    (_hK : boundedConstructible (condensedRingObj R.X X) K)
    (P : ObjectProperty (DerivedCategory (pulledBackModuleObjects
      R.X X)))
    [P.IsClosedUnderIsomorphisms]
    [P.IsTriangulatedClosed₁] [P.IsTriangulatedClosed₂] [P.IsTriangulatedClosed₃]
    (_hgen : ∀ (T : X.FiniteLocallyClosedStratification) (a : Fin T.n)
      (Z : Scheme.{u}) (v : T.domain a ⟶ Z) (i : Z ⟶ X)
      [IsOpenImmersion v] [IsClosedImmersion i],
      v ≫ i = T.immersion a →
      ∀ M : DerivedCategory (pulledBackModuleObjects R.X
        (T.domain a)),
        boundedConstructible (condensedRingObj R.X
          (T.domain a)) M →
        (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (T.domain a), ∀ b : C.I₀,
          ∃ Q : CochainComplex
            (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
              R.X) ℤ,
            (∃ r s : ℤ, ∀ n : ℤ, n < r ∨ s < n → IsZero (Q.X n)) ∧
            (∀ n : ℤ, Mod.IsFree R.X (Q.X n)) ∧
            Nonempty
              ((CondensedRing.upperStar R.X (C.f
                b)).mapDerivedCategory.obj M ≅
                DerivedCategory.Q.obj
                  ((((upperStarFromPoint (C.X b)).mapMod R.X).mapHomologicalComplex (.up ℤ)).obj
                      Q))) →
        P (((CondensedRing.openImmersionLowerShriek R.X
          v).mapDerivedCategory ⋙
          (CondensedRing.lowerStar R.X
            i).rightDerivedFunctor).obj M)), P K

private def preservesProperty (R : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (X : Scheme.{u}) : Prop :=
  (∀ (U : Scheme.{u}) (j : U ⟶ X) [IsOpenImmersion j]
        (M : DerivedCategory (pulledBackModuleObjects R.X
          U)),
        boundedConstructible (condensedRingObj R.X U) M →
          boundedConstructible (condensedRingObj R.X X)
            ((CondensedRing.openImmersionLowerShriek R.X
              j).mapDerivedCategory.obj M)) ∧
      (∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
        (M : DerivedCategory (pulledBackModuleObjects R.X
          Z)),
        boundedConstructible (condensedRingObj R.X Z) M →
          boundedConstructible (condensedRingObj R.X X)
            ((CondensedRing.lowerStar R.X
              i).rightDerivedFunctor.obj M)) ∧
      (∀ (S Z : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X)
        [IsOpenImmersion v] [IsClosedImmersion i]
        (M : DerivedCategory (pulledBackModuleObjects R.X
          S)),
        boundedConstructible (condensedRingObj R.X S) M →
          boundedConstructible (condensedRingObj R.X X)
            (((CondensedRing.openImmersionLowerShriek R.X
              v).mapDerivedCategory ⋙
              (CondensedRing.lowerStar R.X
                i).rightDerivedFunctor).obj M))

private theorem commMon_eq_of_toMon_eq
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {R S : CommMon C} (h : R.toMon = S.toMon) : R = S := by
  cases R
  cases S
  cases h
  rfl

private theorem integerHeart
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X).IsTriangulated := by
  obtain ⟨F, nf, na, fd, ⟨e⟩⟩ := coefficientSmallIso l E
  let := nf
  let := na
  let := fd
  let e₀ : Mon.mk (DerivedNakayama.integerRing l E) ≅
      Mon.mk (integralModelCondensedCoefficients l E).X := eqToIso
          (IntegralConstantModel.pointEquality l E)
  let e' := e₀ ≪≫ e
  let φ := e'.inv.hom
  have : IsMonHom φ := inferInstance
  have : IsIso φ := inferInstance
  let G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj
      (DerivedNakayama.integerRing l E) X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj
          (CondensedRing.integralCoeff l F) X) :=
    Mod.comap (coefficientMap φ X)
  have hT := (smallFieldHeart l F X).2.1
  have transport (B C : Subring F) (h : B = C) :
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} B) X).IsTriangulated →
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} C) X).IsTriangulated
          := by
    subst C
    exact id
  have hsmall : (constantModelBoundedConstructible
      (CondensedRing.integralCoeff l F) X).IsTriangulated :=
    transport _ _ (CondensedRing.continuousIntegers_eq l F).symm hT
  let : G.IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (coefficientMap φ X)).isEquivalence_functor
  have : (constantModelBoundedConstructible
      (CondensedRing.integralCoeff l F) X).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined (CondensedRing.integralCoeff l F) X).2.1
  have heq : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X =
      (constantModelBoundedConstructible (CondensedRing.integralCoeff l F) X).inverseImage
        G.mapDerivedCategory := by
    funext K
    exact propext (cbcComapIff φ X K).symm
  rw [heq]
  infer_instance

private theorem cbcComapIff
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ' ⟶ Λ) [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (K : DerivedCategory (pulledBackModuleObjects Λ X)) :
    constantModelBoundedConstructible Λ' X
        ((Mod.comap (coefficientMap φ X)).mapDerivedCategory.obj K) ↔
      constantModelBoundedConstructible Λ X K := by
  let F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤ Mod (Sheaf
      (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) :=
    Mod.comap (coefficientMap φ X)
  let : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso (coefficientMap φ X)).isEquivalence_functor
  let P' : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)) := IsConstantModelConstructible Λ' X
  have : P'.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ' X).1
  constructor
  · intro h
    refine ⟨F.bounded_of_bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
    apply (constantModel_comap_iff φ X _).mp
    exact P'.prop_of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K).symm (h.2 n)
  · intro h
    refine ⟨F.bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
    exact P'.prop_of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
      ((constantModel_comap_iff φ X _).mpr (h.2 n))

end AlgebraicGeometry.ProEtale.CondensedRing
