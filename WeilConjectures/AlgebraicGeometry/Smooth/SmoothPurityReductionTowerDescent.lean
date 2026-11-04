/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import all WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import all WeilConjectures.AlgebraicGeometry.StrictCoefficientTensor.StrictCoefficientTensorDescent
import all WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction
import all WeilConjectures.CategoryTheory.Constant.ConstantTowerNormalization


/-! # Strict reduction in the chosen coefficient-tower presentation

Source: blueprint latest, normalized-towers-reduction, construction paragraph;
Stacks Tags 00YV, 06YS, 06YY, 0G7D.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u c v w

attribute [local instance 21000]
  CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private def scalarIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{w} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
    {R S : Sheaf J CommRingCat.{w}} {φ : R ⟶ S}
    (A B : DerivedChangeOfRingsCochainModel φ) : A.E ≅ B.E :=
  NatIso.ofComponents (fun M ↦ eqToIso ((A.obj_eq M).trans (B.obj_eq M).symm)) (by
    intro M N f
    dsimp only [eqToIso, Functor.comp_map]
    rw [A.map_eq, B.map_eq]
    simp only [eqToHom_trans, Category.assoc, eqToHom_trans_assoc])

private theorem scalarIso_tmul
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{w} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
    {R S : Sheaf J CommRingCat.{w}} {φ : R ⟶ S}
    (A B : DerivedChangeOfRingsCochainModel φ)
    (M : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (c : S.obj.obj U) (x : M.val.obj U) :
    ((scalarIso A B).inv.app M).val.app U (systemModelTmul B M U c x) =
      systemModelTmul A M U c x := by
  dsimp only [systemModelTmul]
  rw [((scalarIso A B).inv.app M).val.app U |>.hom.map_smul]
  congr 1
  change (((eqToHom (B.obj_eq M).symm ≫ (scalarIso A B).inv.app M).val.app U) _) =
    (eqToHom (A.obj_eq M).symm).val.app U _
  have h : eqToHom (B.obj_eq M).symm ≫ (scalarIso A B).inv.app M =
      eqToHom (A.obj_eq M).symm := by
    simp [scalarIso]
  rw [h]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Left derivation from a resolving class on which the underived complex functor
inverts quasi-isomorphisms. Source: Stacks 06XN, 05SA. -/
private theorem derivedPair
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] (p : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (P : CochainComplex A ℤ) (s : P ⟶ K), p P ∧ QuasiIso s)
    (hinv : ∀ {P Q : CochainComplex A ℤ} (s : P ⟶ Q),
      p P → p Q → QuasiIso s → QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map s)) :
    ∃ (T : DerivedCategory A ⥤ DerivedCategory B)
      (β : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      T.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
        (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      (∃ (_ : T.CommShift ℤ), T.IsTriangulated) ∧
      ∀ K, p K → IsIso (β.app K) := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ, p K ∧ q.obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, s, hL, hs⟩ := res K
    exact ⟨q.obj L, q.map s, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hmap : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s → IsIso (F.map s) := by
    rintro X Y s ⟨K, hK, rfl⟩ ⟨N, hN, rfl⟩ hs
    obtain ⟨s, rfl⟩ := q.map_surjective s
    have hs := hinv s hK hN ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs)
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (.up ℤ)).map
        ((E.mapHomologicalComplex (.up ℤ)).map s)))
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hs)
  obtain ⟨hpw, T, ε, hu, ht, hc⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F P hres hmap
  let : F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) := hpw
  let : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) := hu
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh F T ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor T ε
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let β := Functor.whiskerRight i.inv T ≫ α ≫ j.hom
  have hβ := pointwise_change_iso T i j α hα
  refine ⟨T, β, ⟨hβ.isRightKanExtension⟩, ?_, ht, ?_⟩
  · intro X
    exact (Functor.hasPointwiseLeftDerivedFunctorAt_iff _ DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ)) X).2
        ((hβ _).hasPointwiseRightKanExtensionAt)
  · intro K hK
    have := hc (q.obj K) ⟨K, hK, rfl⟩
    dsimp [β, α]
    infer_instance

/-- Exact equivalences preserve quasi-isomorphisms of complexes. -/
private theorem equivalencePreserves
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (e : A ≌ B) [e.functor.Additive]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) (hf : QuasiIso f) :
    QuasiIso ((e.functor.mapHomologicalComplex (.up ℤ)).map f) := by
  let : QuasiIso f := hf
  let : e.functor.IsEquivalence := e.isEquivalence_functor
  infer_instance

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel checking the concrete sheaf and tower transports needs additional heartbeats.
/-- Transport strict tensor descent to the fixed section-ring and tower presentations.
For a supplied coefficient isomorphism, this constructs the functor and its universal
comparison only; it asserts
neither invertibility of reduction maps nor any constructibility or Tor bound.

Source: blueprint latest, sec-smooth-purity, normalized-towers-reduction, construction;
Stacks Tags 00YV, 06YS, 06YY, 0G7D
(blueprint: lem-sp-reduction-tower-presentation-descent).

Proof:
1. Compose the supplied coefficient isomorphism with the ell-power projections.
Naturality of the limit cone makes them compatible with all quotient transitions,
including equal indices.
2. Apply strictCoefficientTensorDescent to these maps. Its ordinary tensor systems have
levels M tensor R_n and quotient transitions on pure tensors.
3. Uncurry the ringed-sequence-site systems into StrictRingSystem, then apply the
inverse of D.equivalence. Both equivalences preserve the actual section modules and
semilinear maps. The resulting ordinary functor is additive. Uniqueness of the
sheafified scalar-extension left adjoint identifies its levels with D.scalar, carrying
their actual pure tensor generators to systemModelTmul. Hence transition has the
specified formula for every pair of indices.
4. Apply the exact equivalences to the descended derived functor and its comparison.
The universal property of localization and uniqueness of left derived functors give
the asserted counit and universal property. Evaluation compares it with D.scalar's
universal derived functor, giving the natural evaluation isomorphisms.
5. For a K-flat complex, scalar extension preserves quasi-isomorphisms between such
complexes, without requiring flat terms. Every evaluated comparison is therefore
invertible by the K-flat computation theorem. Exact evaluations jointly detect
quasi-isomorphisms of tower complexes, hence detect these derived isomorphisms.
This proves computes for all K-flat complexes, beyond the flat-term resolving class.
No qcqs assumption or boundedness is used; zero modules and empty schemes are included.
-/
theorem sp_reduction_tower_presentation_descent (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T) :
    ∃ (ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T)
        (_additive : ordinary.Additive)
        (level : spReductionOrdinaryLevels l E T D coefficient ordinary),
        IsSpReductionTransition l E T D coefficient ordinary level ∧
        ∃ (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
            spDerivedCoefficientTowers l E T D)
          (counit : DerivedCategory.Q ⋙ red ⟶
            ordinary.mapHomologicalComplex (.up ℤ) ⋙ spTowerLocalization l E T D),
          red.IsLeftDerivedFunctor counit
            (HomologicalComplex.quasiIso (spIntegralSectionModules l E T) (.up ℤ)) ∧
          (∀ P : CochainComplex (spIntegralSectionModules l E T) ℤ,
            CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T)
              P → IsIso (counit.app P)) ∧
          Nonempty (spReductionDerivedEvaluations l E T D coefficient red) := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt :=
    essentiallySmallSelf.{0, u, u + 1} _
  let R := spIntegralSectionRing l E T
  let B := spCoefficientCommRings l E T
  let α : (Functor.const ℕᵒᵖ).obj R ⟶ B :=
    { app := fun n ↦ spIntegralReductionScalar l E T coefficient n.unop
      naturality := by
        intro n m f
        change 𝟙 R ≫ _ = _
        rw [Category.id_comp]
        dsimp only [spIntegralReductionScalar]
        rw [Category.assoc]
        congr 1
        apply (sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
        simp only [Functor.map_comp, spIntegralEllProjection, Functor.map_preimage]
        have hb :
            (sheafCompose (Scheme.ProEt.topology T)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (B.map f) =
              (spCoefficientRings l E T).map f := by
          exact eq_of_heq (Functor.hcongr_hom (coefficientRings_eq l E T) f).symm
        rw [hb]
        exact ((Category.assoc _ _ _).trans
          (congrArg (fun g ↦ (sp_completed_coefficient_limit l E T).exists.choose.hom ≫ g)
            (limit.w (spCoefficientRings l E T) f))).symm }
  let G := SequenceProjection.extension.{u + 1, u, u + 1} R B α
  let := D.hasDerived
  let := D.equivalenceAdditive
  let : D.equivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  let : D.equivalence.symm.functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let F := G ⋙ D.equivalence.inverse
  let level : spReductionOrdinaryLevels l E T D coefficient F := fun n ↦
    Functor.associator G D.equivalence.inverse
        (D.equivalence.functor ⋙ systemEvaluation B n) ≪≫
      Functor.isoWhiskerLeft G
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight D.equivalence.counitIso (systemEvaluation B n) ≪≫
          Functor.leftUnitor _) ≪≫
      scalarIso (SequenceProjection.scalar.{u + 1, u, u + 1} R B α n).model
        (D.scalar (spIntegralReductionScalar l E T coefficient n)).model
  have transition : IsSpReductionTransition l E T D coefficient F level := by
    intro M m n h U c x
    have gen (k : ℕ) (b : (B.obj (op k)).obj.obj U) :
        spReductionGenerator l E T D coefficient F level M k U b x =
          ((D.equivalence.counitIso.inv.app (G.obj M)).app k).val.app U
            (systemModelTmul (SequenceProjection.scalar.{u + 1, u, u + 1}
              R B α k).model M U b x) := by
      change ((D.equivalence.counitIso.inv.app (G.obj M)).app k).val.app U
        (((scalarIso (C := T.ProEt) (J := Scheme.ProEt.topology T)
          (R := R) (S := B.obj (op k)) (φ := α.app (op k))
          (SequenceProjection.scalar.{u + 1, u, u + 1} R B α k).model
          (D.scalar (spIntegralReductionScalar l E T coefficient k)).model).inv.app M).val.app
          U _) = _
      rw [scalarIso_tmul (C := T.ProEt) (J := Scheme.ProEt.topology T)
        (R := R) (S := B.obj (op k)) (φ := α.app (op k))]
    rw [gen, gen]
    dsimp only [spStrictTransitionSection, F]
    have he := congrArg (fun f ↦ f.val.app U
      (systemModelTmul (SequenceProjection.scalar.{u + 1, u, u + 1}
        R B α n).model M U c x))
      ((D.equivalence.counitIso.inv.app (G.obj M)).comm h)
    change _ = _ at he
    refine he.trans ?_
    have ht := SequenceProjection.transition_tmul R B α M h U c x
    change _ = _
    exact congrArg (fun z ↦
      ((D.equivalence.counitIso.inv.app (G.obj M)).app m).val.app U z) ht
  have res (K : CochainComplex (spIntegralSectionModules l E T) ℤ) :
      ∃ (P : CochainComplex (spIntegralSectionModules l E T) ℤ) (s : P ⟶ K),
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧ QuasiIso s := by
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K
    exact ⟨P, s, hP, hs⟩
  have hinv {P Q : CochainComplex (spIntegralSectionModules l E T) ℤ} (s : P ⟶ Q)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q) (hs : QuasiIso s) :
      QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map s) := by
    have hg := SequenceProjection.extension_preserves R B α s hP hQ hs
    exact equivalencePreserves
      D.equivalence.symm ((G.mapHomologicalComplex (.up ℤ)).map s) hg
  obtain ⟨red, counit, universal, _, _, computes⟩ :=
    derivedPair F
      (CochainComplex.IsKFlatIndependentCoefficients (R := R)) res hinv
  refine ⟨F, inferInstance, level, transition, red, counit, universal, computes, ?_⟩
  refine ⟨fun n ↦ ?_⟩
  let := D.evaluationLimits n
  let := D.evaluationColimits n
  let : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  let V := spDerivedCoefficientEvaluation l E T D n
  let H := (D.scalar (spIntegralReductionScalar l E T coefficient n)).model.E.mapHomologicalComplex
    (.up ℤ) ⋙ DerivedCategory.Q
  let η : DerivedCategory.Q ⋙ (red ⋙ V) ⟶ H :=
    Functor.whiskerRight counit V ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
        (spCoefficientEvaluation l E T D.equivalence n).mapDerivedCategoryFactors.hom ≫
      (Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (level n) (.up ℤ)) DerivedCategory.Q).hom
  have hη P (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
      IsIso (η.app P) := by
    have := computes P hP
    dsimp only [η, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  exact (comparison_from_resolutions _ res (red ⋙ V)
    (D.scalar (spIntegralReductionScalar l E T coefficient n)).model.T H η
    (D.scalar (spIntegralReductionScalar l E T coefficient n)).model.ε hη
    (fun P hP ↦ (D.scalar _).model.computes P hP)).choose


end AlgebraicGeometry.ProEtale
