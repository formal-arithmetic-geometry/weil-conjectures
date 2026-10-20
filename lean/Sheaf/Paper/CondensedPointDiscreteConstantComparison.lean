/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.ProfinitePointPullback
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import Sheaf.Paper.FiniteDiscreteSchemeRing

/-!
# Discrete constant coefficients on the geometric point

Source: main-20261015, coefficient lemma, second paragraph.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance] Sheaf.monoidalCategory

private theorem constantRingMonObj {C : Type*} [Category C] (B : Type*) [Ring B] :
    (Functor.const C).monObjObj (AddCommGrpCat.of B) =
      Functor.monObjCompForget₂ ((Functor.const C).obj (RingCat.of B)) := by
  apply MonObj.ext
  ext U
  rfl

private theorem constantSheafRingMonObj {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal] (B : Type (u + 1)) [Ring B] :
    (constantSheaf J Ab.{u + 1}).monObjObj (AddCommGrpCat.of B) =
      Sheaf.monObj_presheafToSheaf_obj J
        (((Functor.const Cᵒᵖ).obj (RingCat.of B)) ⋙ forget₂ RingCat Ab) := by
  have h := Functor.monObjObj_comp (Functor.const Cᵒᵖ) (presheafToSheaf J Ab.{u + 1})
    (AddCommGrpCat.of B)
  refine h.trans ?_
  let transfer (m : MonObj ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B))) :
      MonObj ((constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of B)) :=
    @Functor.monObjObj _ _ _ _ _ _ (presheafToSheaf J Ab.{u + 1}) _ _ m
  exact congrArg transfer (constantRingMonObj (C := Cᵒᵖ) B)

private theorem constantRingIso {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J RingCat.{u + 1}]
    [HasWeakSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    [J.HasSheafCompose (forget₂ RingCat.{u + 1} Ab.{u + 1})]
    [J.PreservesSheafification (forget₂ RingCat.{u + 1} Ab.{u + 1})]
    (B : Type (u + 1)) [Ring B] :
    Nonempty ((constantSheaf J Ab.{u + 1}).mapMon.obj (Mon.mk (AddCommGrpCat.of B)) ≅
      Mon.mk ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of B)))) := by
  let P := (Functor.const Cᵒᵖ).obj (RingCat.of B)
  let S := (constantSheaf J RingCat.{u + 1}).obj (RingCat.of B)
  let φ := Functor.whiskerRight (toSheafify J P) (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have hφ : J.W (A := Ab.{u + 1}) φ :=
    J.W_of_preservesSheafification (forget₂ RingCat.{u + 1} Ab.{u + 1}) _
      (J.W_toSheafify P)
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map φ) := (J.W_iff φ).mp hφ
  let e := asIso ((presheafToSheaf J Ab.{u + 1}).map φ) ≪≫
    Sheaf.sheafifyRingPresheafIso J S
  have he : IsMonHom e.hom := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    infer_instance
  have h := constantSheafRingMonObj J B
  have he' : @IsMonHom _ _ _ _ _
      ((constantSheaf J Ab.{u + 1}).monObjObj (AddCommGrpCat.of B)) _ e.hom := by
    rw [h]
    exact he
  exact ⟨Mon.mkIso e he'.one_hom he'.mul_hom⟩

private noncomputable def constantToContinuous (A : Type u) [Ring A]
    [TopologicalSpace A] [DiscreteTopology A] :
    (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)) ⟶
      Profinite.continuousCoefficientRingPresheaf A where
  app S := RingCat.ofHom
    { toFun a := ULift.up (ContinuousMap.const S.unop a.down)
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

private noncomputable abbrev constantToContinuousAb (A : Type u) [Ring A]
    [TopologicalSpace A] [DiscreteTopology A] :=
  Functor.whiskerRight (constantToContinuous A) (forget₂ RingCat.{u + 1} Ab.{u + 1})

private instance locallySurjective_constantToContinuous (A : Type u) [Ring A]
    [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u})
      (constantToContinuousAb A) where
  imageSieve_mem {S} s := by
    let f : C(S, A) := s.down
    let : Fintype (Set.range f) :=
      ((IsLocallyConstant.iff_continuous f).2 f.continuous).range_finite.fintype
    let I := Fin (Fintype.card (Set.range f))
    let e : I ≃ Set.range f := (Fintype.equivFin (Set.range f)).symm
    have hclosed (i : I) : IsClosed {x : S | f x = (e i).val} :=
      isClosed_singleton.preimage f.continuous
    let (i : I) : CompactSpace {x : S // f x = (e i).val} :=
      isCompact_iff_compactSpace.mp (hclosed i).isCompact
    let U (i : I) : Profinite.{u} := Profinite.of {x : S // f x = (e i).val}
    let incl (i : I) : U i ⟶ S :=
      CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩
    have hι : EffectiveEpiFamily U incl := by
      apply Profinite.effectiveEpiFamily_of_jointly_surjective U incl
      intro x
      refine ⟨e.symm ⟨f x, ⟨x, rfl⟩⟩, ⟨x, ?_⟩, rfl⟩
      simp
    refine coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
      ⟨I, inferInstance, U, incl, hι, ?_⟩
    intro i
    refine ⟨ULift.up (e i).val, ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact x.property.symm

private instance locallyInjective_constantToContinuous (A : Type u) [Ring A]
    [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u})
      (constantToContinuousAb A) where
  equalizerSieve_mem {S} a b h := by
    by_cases hab : a = b
    · subst b
      exact (coherentTopology Profinite).superset_covering
        (fun _ _ _ ↦ rfl) ((coherentTopology Profinite).top_mem _)
    · have : IsEmpty S.unop := ⟨fun x ↦ hab (ULift.ext a b (congrArg
        (fun t : ULift.{u + 1} C(S.unop, A) ↦ t.down x) h))⟩
      let U : PEmpty → Profinite.{u} := PEmpty.elim
      let incl : ∀ i, U i ⟶ S.unop := fun i ↦ i.elim
      have hι : EffectiveEpiFamily U incl :=
        Profinite.effectiveEpiFamily_of_jointly_surjective U incl (fun x ↦ isEmptyElim x)
      exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
        ⟨PEmpty, inferInstance, U, incl, hι, fun i ↦ i.elim⟩

private theorem discreteCondensedRing_constant (A : Type u) [Ring A]
    [TopologicalSpace A] [DiscreteTopology A] :
    Nonempty ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMon.obj
        (Mon.mk (AddCommGrpCat.of (ULift.{u + 1} A))) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj A)) := by
  let J : GrothendieckTopology Profinite.{u} := coherentTopology Profinite.{u}
  let φ := constantToContinuousAb A
  have hφ : J.W (A := Ab.{u + 1}) φ := J.W_of_isLocallyBijective φ
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map φ) := (J.W_iff φ).mp hφ
  let e := asIso ((presheafToSheaf J Ab.{u + 1}).map φ) ≪≫
    Sheaf.sheafifyRingPresheafIso J (Profinite.continuousCoefficientRingSheaf A)
  have he : IsMonHom e.hom := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    infer_instance
  have h := constantSheafRingMonObj J (ULift.{u + 1} A)
  have he' : @IsMonHom _ _ _ _ _
      ((constantSheaf J Ab.{u + 1}).monObjObj (AddCommGrpCat.of (ULift.{u + 1} A))) _
      e.hom := by
    rw [h]
    exact he
  exact ⟨Mon.mkIso e he'.one_hom he'.mul_hom⟩

/-- The two constant-sheaf identifications for discrete ring coefficients.
Source: main-20261015 blueprint, coefficient lemma, second paragraph, Steps 5--6
(blueprint: lem-pe-condensed-point-discrete-constant-comparisons).

Proof: Map the constant ring presheaf to continuous functions by constant functions.
Every continuous function to the discrete ring has finite image. Its clopen fibres form
a finite jointly surjective profinite covering, on which it is constant, proving local
surjectivity. Equal constant functions have equal values on nonempty spaces; the empty
cover handles the empty space, proving local injectivity. Sheafification therefore turns
this map into an isomorphism. It preserves multiplication and unit, so the monoidal
sheafification comparison lifts the isomorphism to internal rings.

The canonical monoidal constantSchemeIso identifies the inverse image of the constant
abelian ring on the profinite site with the constant abelian ring on the scheme. Compose
it with the preceding isomorphism. For the etale comparison, apply the generic monoidal
constantPullbackMonoidalIso to the inclusion of the etale site into the pro-etale site;
the inclusion preserves the terminal object because it preserves finite limits. Finally
forgetting rings to abelian groups preserves sheafification, identifying both transported
constant internal rings with the underlying abelian sheaves of the specified constant
ring sheaves. All isomorphisms preserve multiplication and unit for arbitrary rings,
including noncommutative rings and the zero ring. -/
theorem condensed_point_discrete_constant_comparisons
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (A : Type u) [Ring A] [TopologicalSpace A] [DiscreteTopology A] :
    Nonempty (coefficientRing (Spec (.of Ω))
        (Mon.mk (Profinite.continuousCoefficientRingObj A)) ≅
          (comparisonUpperStar Ab.{u + 1} (Spec (.of Ω))).mapMon.obj
            ((Mon.mk ((sheafCompose (Spec (.of Ω)).smallEtaleTopology
              (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
                ((constantSheaf (Spec (.of Ω)).smallEtaleTopology RingCat.{u + 1}).obj
                  (RingCat.of (ULift.{u + 1} A))))))) ∧
      Nonempty (coefficientRing (Spec (.of Ω))
        (Mon.mk (Profinite.continuousCoefficientRingObj A)) ≅
          (Mon.mk ((sheafCompose (Scheme.ProEt.topology (Spec (.of Ω)))
              (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
                ((constantSheaf (Scheme.ProEt.topology (Spec (.of Ω))) RingCat.{u + 1}).obj
                  (RingCat.of (ULift.{u + 1} A)))))) := by
  let X := Spec (.of Ω)
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology X
  let E := X.smallEtaleTopology
  let M := Mon.mk (AddCommGrpCat.of (ULift.{u + 1} A))
  obtain ⟨d⟩ := discreteCondensedRing_constant A
  have : K.PreservesSheafification (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification K _
  have : E.PreservesSheafification (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification E _
  obtain ⟨cK⟩ := constantRingIso K (ULift.{u + 1} A)
  obtain ⟨cE⟩ := constantRingIso E (ULift.{u + 1} A)
  let s : (constantSheaf K Ab.{u + 1}).mapMon.obj M ≅
      (upperStarFromPoint X).mapMon.obj
        ((constantSheaf J Ab.{u + 1}).mapMon.obj M) :=
    (Functor.mapMonNatIso (constantSchemeIso X)).app M ≪≫
      Functor.mapMonCompIso.app M
  let e := (upperStarFromPoint X).mapMon.mapIso d.symm ≪≫ s.symm
  let t := constantPullbackMonoidalIso (A := Ab.{u + 1}) (Scheme.toProEt X) E K
    (Scheme.Etale.isTerminalMkId X)
    ((Scheme.Etale.isTerminalMkId X).isTerminalObj (Scheme.toProEt X))
  let v : (constantSheaf K Ab.{u + 1}).mapMon.obj M ≅
      (comparisonUpperStar Ab.{u + 1} X).mapMon.obj
        ((constantSheaf E Ab.{u + 1}).mapMon.obj M) :=
    (Functor.mapMonNatIso t).app M ≪≫ Functor.mapMonCompIso.app M
  exact ⟨⟨e ≪≫ v ≪≫ (comparisonUpperStar Ab.{u + 1} X).mapMon.mapIso cE⟩,
    ⟨e ≪≫ cK⟩⟩

end AlgebraicGeometry.ProEtale
