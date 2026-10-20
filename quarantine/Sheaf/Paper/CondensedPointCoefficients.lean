/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Paper.CondensedPointBasis
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import all Sheaf.Paper.GeometricFieldProfiniteDenseSubsite
import Sheaf.Paper.GeometricFieldProEtaleEvaluation
import Sheaf.Paper.CondensedPointDiscreteConstantComparison

/-!
# Coefficients on the pro-etale geometric point

Source: main-20261015 blueprint, sec-proetale-coefficients,
sk-prop-pe-condensed-point/sk-prop-pe-condensed-point-coefficients.md
(blueprint: det-pe-condensed-point-coefficients).

The test objects are the canonical `profiniteToProEtOf` objects. The natural identification
with `Spec LC(S,Ω)` is `condensed_point_basis`. Ring comparisons live in monoid objects of
abelian presheaves or sheaves, so they retain multiplication and unit as well as addition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Restriction of an internal ring sheaf to the canonical profinite test objects, retaining
its actual ring operations. Source: the coefficient lemma, first paragraph
(blueprint: det-pe-condensed-point-coefficients). -/
noncomputable def condensedPointRingRestriction (X : Scheme.{u}) :
    Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⥤
      Mon (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :=
  (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMon ⋙
    ((Functor.whiskeringLeft Profinite.{u}ᵒᵖ X.ProEtᵒᵖ Ab.{u + 1}).obj
      (profiniteToProEtOf X).op).mapMon

/-- The existing constant ring sheaf, regarded as an internal ring in abelian sheaves.
Source: the coefficient lemma, clause (2), and `def-weil-pbc-constant-sheaf`
(blueprint: det-pe-condensed-point-coefficients). -/
noncomputable def condensedPointConstantRing {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J RingCat.{u + 1}]
    [HasWeakSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    [J.HasSheafCompose (forget₂ RingCat.{u + 1} Ab.{u + 1})]
    (A : Type u) [Ring A] : Mon (Sheaf J Ab.{u + 1}) :=
  Mon.mk ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of (ULift.{u + 1} A))))

/-- The finite-quotient diagram `A^{S_i}`, with transition maps given by precomposition.
Source: the coefficient lemma, clause (2), finite-quotient formula
(blueprint: det-pe-condensed-point-coefficients). -/
noncomputable def condensedPointFiniteFunctionDiagram (A : Type u) [Ring A]
    (S : Profinite.{u}) : (DiscreteQuotient S)ᵒᵖ ⥤ RingCat.{u + 1} where
  obj q := RingCat.of (ULift.{u + 1} (q.unop → A))
  map {q r} f := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((RingHom.pi (fun x : r.unop ↦ Pi.evalRingHom (fun _ : q.unop ↦ A)
      (DiscreteQuotient.ofLE f.unop.le x))).comp ULift.ringEquiv.toRingHom))
  map_id q := by
    ext a x
    refine Quotient.inductionOn x ?_
    intro s
    rfl
  map_comp f g := by
    ext a x
    refine Quotient.inductionOn x ?_
    intro s
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical cocone from finite-quotient functions to locally constant functions:
its leg at a quotient q sends a to a composed with the quotient projection.
Source: the coefficient lemma, clause (2), finite-quotient formula
(blueprint: det-pe-condensed-point-coefficients). -/
noncomputable def condensedPointFiniteFunctionCocone (A : Type u) [Ring A]
    (S : Profinite.{u}) : Cocone (condensedPointFiniteFunctionDiagram A S) where
  pt := RingCat.of (ULift.{u + 1} (LocallyConstant S A))
  ι :=
    { app := fun q ↦ RingCat.ofHom
        { toFun := fun (a : ULift.{u + 1} (q.unop → A)) ↦ ULift.up
            ((⟨a.down, IsLocallyConstant.of_discrete a.down⟩ : LocallyConstant q.unop A).comap
              ⟨q.unop.proj, q.unop.proj_isLocallyConstant.continuous⟩)
          map_one' := rfl
          map_mul' _ _ := rfl
          map_zero' := rfl
          map_add' _ _ := rfl }
      naturality := by
        intro q r f
        ext a
        rfl }

private theorem condensedPointDense (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (profiniteToProEtOf (Spec (.of Ω))).IsDenseSubsite
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology (Spec (.of Ω))) := by
  have := (testFullyFaithful Ω).1
  have := (testFullyFaithful Ω).2
  have : (profiniteToProEtOf (Spec (.of Ω))).IsCoverDense
      (Scheme.ProEt.topology (Spec (.of Ω))) := by
    constructor
    intro U
    apply (Scheme.ProEt.topology (Spec (.of Ω))).superset_covering _
      ((Scheme.AffineProEt.toProEt (Spec (.of Ω))).is_cover_of_isCoverDense _ U)
    rintro V f ⟨⟨A, g, h, w⟩⟩
    obtain ⟨E, ⟨e⟩⟩ := (condensed_point_basis Ω).2.2.2.2.1
    have hs := (condensed_point_basis Ω).2.2.2.2.2
    obtain ⟨a⟩ := hs
    let Y : ObjectProperty.FullSubcategory
        (fun Y : Over (Spec (.of Ω)) ↦ IsAffine Y.left ∧ proAffineEtale Y.hom) :=
      ⟨(Scheme.ProEt.forget _).obj ((Scheme.AffineProEt.toProEt _).obj A),
        ⟨inferInstanceAs (IsAffine A.left), A.prop⟩⟩
    let S := E.inverse.obj Y
    let z : E.functor.obj S ≅ Y := E.counitIso.app Y
    let z' := (ObjectProperty.ι _).mapIso z
    let hi : (Scheme.ProEt.forget _).obj ((Scheme.AffineProEt.toProEt _).obj A) ≅
        (Scheme.ProEt.forget _).obj ((profiniteToProEtOf (Spec (.of Ω))).obj S) :=
      z'.symm ≪≫ e.app S ≪≫ a.app S
    let h' : (Scheme.AffineProEt.toProEt _).obj A ≅
        (profiniteToProEtOf (Spec (.of Ω))).obj S :=
      (Functor.FullyFaithful.ofFullyFaithful (Scheme.ProEt.forget _)).preimageIso hi
    exact ⟨⟨S, g ≫ h'.hom, h'.inv ≫ h, by simp [Category.assoc, w]⟩⟩
  exact { functorPushforward_mem_iff := fun {_ _} ↦
    ⟨testTopologyReflect Ω, (testCoverPreserving Ω).cover_preserve⟩ }

private theorem condensedPointRingEvaluation (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (F : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :
    Nonempty ((condensedPointRingRestriction (Spec (.of Ω))).obj
        (coefficientRing (Spec (.of Ω)) F) ≅
          (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMon.obj F) := by
  let X := Spec (.of Ω)
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology X
  have : (profiniteToProEt ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤
      (toSpecZ X)).IsContinuous J K := geometricFieldTest_isContinuous X
  let R := lowerStar Ab.{u + 1} (toSpecZ X) ⋙ pointLowerStar
  let adj : upperStarFromPoint X ⊣ R :=
    pointUpperStarLowerStarAdjunction.comp (upperStarLowerStarAdjunction _ (toSpecZ X))
  have := condensedPointDense Ω
  have : (geometricFieldRestriction X Ab.{u + 1}).IsEquivalence := inferInstance
  have : R.IsEquivalence := inferInstanceAs
    (geometricFieldRestriction X Ab.{u + 1}).IsEquivalence
  have : adj.IsMonoidal := by
    dsimp only [adj]
    have : pointUpperStarLowerStarAdjunction.{u}.IsMonoidal := by
      unfold pointUpperStarLowerStarAdjunction pointUpperStar pointLowerStar
      exact Functor.sheafPullbackConstruction.isMonoidal_sheafAdjunctionContinuous _ _ _ _
    have := isMonoidal_upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)
    exact Adjunction.isMonoidal_comp pointUpperStarLowerStarAdjunction
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : IsIso adj.unit := inferInstance
  have : NatTrans.IsMonoidal (asIso adj.unit).hom :=
    inferInstanceAs (NatTrans.IsMonoidal adj.unit)
  let e : F ≅ R.mapMon.obj
      (coefficientRing X F) :=
    (Functor.mapMonIdIso (C := Sheaf J Ab.{u + 1})).symm.app F ≪≫
      (Functor.mapMonNatIso (asIso adj.unit)).app F ≪≫
      Functor.mapMonCompIso.app F
  let t : R ≅ geometricFieldRestriction X Ab.{u + 1} :=
    Functor.sheafPushforwardContinuousComp' (eFG := Iso.refl _) _
      J (Scheme.ProEt.topology specZ) K
  have : NatTrans.IsMonoidal t.hom := by
    dsimp only [t]
    infer_instance
  have : NatTrans.IsMonoidal t.symm.hom := inferInstanceAs (NatTrans.IsMonoidal t.inv)
  let r : condensedPointRingRestriction X ≅
      R.mapMon ⋙
        (sheafToPresheaf J Ab.{u + 1}).mapMon :=
    Functor.mapMonCompIso.symm ≪≫
      Functor.mapMonNatIso
        (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
          (profiniteToProEtOf X) Ab.{u + 1} J K) ≪≫
      Functor.mapMonCompIso ≪≫
      Functor.isoWhiskerRight (Functor.mapMonNatIso t.symm) _
  exact ⟨r.app (coefficientRing X F) ≪≫
    (sheafToPresheaf J Ab.{u + 1}).mapMon.mapIso e.symm⟩

private theorem condensedPointFiniteColimit (A : Type u) [Ring A] (S : Profinite.{u}) :
    Nonempty (IsColimit (condensedPointFiniteFunctionCocone A S)) := by
  classical
  apply Nonempty.intro
  have : PreservesFilteredColimitsOfSize.{u, u} (forget RingCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  have : ReflectsColimit (condensedPointFiniteFunctionDiagram A S) (forget RingCat.{u + 1}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget RingCat.{u + 1})
  apply Types.FilteredColimit.isColimitOf'
  · intro f
    refine ⟨op f.down.discreteQuotient, ULift.up f.down.lift, ?_⟩
    rfl
  · intro q x y h
    refine ⟨q, 𝟙 q, ?_⟩
    suffices x = y by subst y; rfl
    apply ULift.ext
    funext a
    obtain ⟨s, rfl⟩ := q.unop.proj_surjective a
    exact congrArg (fun z : ULift.{u + 1} (LocallyConstant S A) ↦ z.down s) h

/-- On a separably closed geometric point, the inverse image of a condensed set or ring
has its original sections on every profinite test object. Continuous ring coefficients give
continuous functions; discrete coefficients give locally constant functions, their canonical
finite-quotient colimit, the comparison pullback of the etale constant ring, and the classical
pro-etale constant ring.

Source: main-20261015 blueprint, coefficient lemma, both paragraphs and clauses (1)--(2)
(blueprint: det-pe-condensed-point-coefficients).

Proof: The field-independent spectrum and covering calculations in
`GeometricFieldProfiniteDenseSubsite` give full faithfulness and identify the induced
topology with the coherent topology. The affine ind-etale equivalence of
`condensed_point_basis` and the affine pro-etale basis theorem give cover density.
Dense restriction is therefore an equivalence on sets and abelian groups. The specified
point adjunction has invertible unit, giving set evaluation. Its monoidal unit and the
monoidal pushforward-composition comparison give evaluation as internal rings.

Apply ring evaluation to continuous coefficients. The monoidal sheafification comparison
identifies their underlying presheaf with the specified continuous-function ring.
For discrete coefficients, continuity is local constancy. Every locally constant function
factors through its finite discrete quotient, and surjectivity of quotient projections
makes the cocone legs injective. The filtered-colimit criterion in types, reflected by
the ring forgetful functor, proves the finite-quotient formula, including the empty space.

Finally `condensed_point_discrete_constant_comparisons` identifies the discrete condensed
ring with the constant ring by locally bijective sheafification: the finite clopen fibres
of each function give local surjectivity, and the empty covering handles local injectivity
on the empty space. The canonical monoidal constant-sheaf pullback comparisons give both
the etale comparison inverse image and the classical pro-etale constant ring. -/
theorem condensed_point_coefficients (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (∀ F : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)),
      Nonempty ((profiniteToProEtOf (Spec (.of Ω))).op ⋙
        ((profinitePointSetSchemeInverseImage (Spec (.of Ω))).obj F).obj ≅ F.obj)) ∧
    (∀ F : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      Nonempty ((condensedPointRingRestriction (Spec (.of Ω))).obj
        (coefficientRing (Spec (.of Ω)) F) ≅
          (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMon.obj F)) ∧
    (∀ (T : Type u) [TopologicalSpace T] [Ring T] [IsTopologicalRing T],
      Nonempty ((condensedPointRingRestriction (Spec (.of Ω))).obj
        (coefficientRing (Spec (.of Ω)) (Mon.mk (Profinite.continuousCoefficientRingObj T))) ≅
          (Profinite.continuousCoefficientRingPresheaf T).toMonAb)) ∧
    (∀ (A : Type u) [Ring A] [TopologicalSpace A] [DiscreteTopology A],
      (∀ S : Profinite.{u},
        (∃ e : LocallyConstant S A ≃+* C(S, A), ∀ f : LocallyConstant S A,
          (e f : S → A) = f) ∧
        Nonempty (IsColimit (condensedPointFiniteFunctionCocone A S))) ∧
      Nonempty (coefficientRing (Spec (.of Ω))
        (Mon.mk (Profinite.continuousCoefficientRingObj A)) ≅
          (comparisonUpperStar Ab.{u + 1} (Spec (.of Ω))).mapMon.obj
            (condensedPointConstantRing (Spec (.of Ω)).smallEtaleTopology A)) ∧
      Nonempty (coefficientRing (Spec (.of Ω))
        (Mon.mk (Profinite.continuousCoefficientRingObj A)) ≅
          condensedPointConstantRing (Scheme.ProEt.topology (Spec (.of Ω))) A)) := by
  have hring := condensedPointRingEvaluation Ω
  refine ⟨?_, hring, ?_, ?_⟩
  · intro F
    have := condensedPointDense Ω
    have : (geometricFieldRestriction (Spec (.of Ω)) (Type (u + 1))).IsEquivalence :=
      inferInstance
    exact ⟨(sheafToPresheaf _ _).mapIso
      (asIso ((geometricFieldPointAdjunction (Spec (.of Ω))).unit.app F)).symm⟩
  · intro T _ _ _
    obtain ⟨e⟩ := hring (Mon.mk (Profinite.continuousCoefficientRingObj T))
    let J := coherentTopology Profinite.{u}
    let P := (Profinite.continuousCoefficientRingPresheaf T).toMonAb
    let S := Profinite.continuousCoefficientRingSheaf T
    let c : (presheafToSheaf J Ab.{u + 1}).mapMon.obj P ≅
        Mon.mk (Profinite.continuousCoefficientRingObj T) :=
      Mon.mkIso' (Sheaf.sheafifyRingPresheafIso J S)
    let adj := sheafificationAdjunction J Ab.{u + 1}
    have : adj.IsMonoidal := inferInstance
    have : IsIso (adj.unit.app P.X) := by
      change IsIso ((sheafificationAdjunction J Ab.{u + 1}).unit.app
        (Profinite.continuousCoefficientRingObj T).obj)
      exact isIso_toSheafify J (Profinite.continuousCoefficientRingObj T).property
    let a := ((Functor.mapMonIdIso (C := Profiniteᵒᵖ ⥤ Ab.{u + 1})).inv ≫
      Functor.mapMonNatTrans adj.unit).app P
    have : IsIso ((Mon.forget _).map a) := by
      change IsIso (adj.unit.app P.X)
      infer_instance
    have : IsIso a := isIso_of_reflects_iso a (Mon.forget _)
    exact ⟨e ≪≫ (sheafToPresheaf J Ab.{u + 1}).mapMon.mapIso c.symm ≪≫
      (Functor.mapMonCompIso.app P).symm ≪≫ (asIso a).symm⟩
  · intro A _ _ _
    refine ⟨?_, ?_⟩
    · intro S
      refine ⟨?_, condensedPointFiniteColimit A S⟩
      let e : LocallyConstant S A ≃+* C(S, A) :=
        { toFun := fun f ↦ f.toContinuousMap
          invFun := fun f ↦ ⟨f, (IsLocallyConstant.iff_continuous f).2 f.continuous⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_mul' := fun _ _ ↦ rfl
          map_add' := fun _ _ ↦ rfl }
      exact ⟨e, fun _ ↦ rfl⟩
    · exact condensed_point_discrete_constant_comparisons Ω A

end AlgebraicGeometry.ProEtale
