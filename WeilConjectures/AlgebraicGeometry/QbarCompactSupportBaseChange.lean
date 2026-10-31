/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteExtensionCompactSupportBaseChange
public import WeilConjectures.AlgebraicGeometry.PbcDescentFunctors
public import WeilConjectures.AlgebraicGeometry.PbcQbarCategory
public import WeilConjectures.AlgebraicGeometry.QbarCompactSupportExchangeModel
import WeilConjectures.AlgebraicGeometry.QbarCompactSupportExchangeModelExists
import WeilConjectures.AlgebraicGeometry.WeilTensorProduct

/-!
# Compact-support base change with algebraically closed l-adic coefficients

Source: Weil conjectures blueprint main-20261015, six-functors basics,
`sk-thm-sf-pf-field/thm-cbc-qbar`, order 1992 (blueprint: thm-cbc-qbar).

The finite-stage endpoints are fixed by their composites with integral localization,
and the exchange components by the specified completed compact-support exchange.
The conclusion includes both the overfield representative and independence relative
to an isomorphism from a representing pair to the fixed input object.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X' X Y' Y : Scheme.{u}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
  (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
  (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
  [QuasiCompact f]
  [IsNoetherian X] [IsNoetherian Y']
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]

attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.Limits.limit
  pbcIntegralDatum
  AdicCoefficientDatum.completedPull cbcDerivedOpenShriek completedCompactSupportExchange
  pbcFiniteField pbcScalarExtension pbcScalarAssociator
  ScalarLocalization.category ScalarLocalization.preadditive
  StageSystem.Morphism.descNatTrans

private theorem cbcIsIso_of_heq {C : Type*} [Category C] {A B A' B' : C}
    {a : A ⟶ B} {b : A' ⟶ B'} (hA : A = A') (hB : B = B')
    (h : HEq a b) [IsIso b] : IsIso a := by
  cases hA
  cases hB
  cases eq_of_heq h
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cbcModel_stage_isIso
    [IsSeparated f] [LocallyOfFiniteType f]
    (D : CbcQbarExchangeModel l Ω c c' gbar properSquare openSquare)
    (E : Padic.FiniteCoefficientFields l Ω) (K : pbcStageCategory l Ω X E) :
    IsIso ((D.exchange.τ E).app K) := by
  rcases K with ⟨K⟩
  let d := pbcStageDatum.{u} l Ω E
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  have hc : cbcCompleteProperty d X r a ha K.obj :=
    wfConstructible_complete X d r a ha K
  let e := completedCompactSupportExchange d c c' gbar properSquare openSquare
    r a ha ⟨K.obj, hc⟩
  have : IsIso e := (completeCompactSupportProetale_isIso d c c' gbar
    properSquare openSquare r a ha ⟨K.obj, hc⟩ K.property.2.2).1
  let b := ObjectProperty.homMk
    (X := (pbcConditionalIntegral d (cbcCompactSupportSource g c d) (D.presSource E)).obj K)
    (Y := (pbcConditionalIntegral d (cbcCompactSupportTarget g' c' d) (D.presTarget E)).obj K)
    e
  have hb : IsIso b.hom := by change IsIso e; infer_instance
  have : IsIso b := (ObjectProperty.isIso_hom_iff b).mp hb
  have : IsIso ((pbcStageLocalization l Ω Y' E).map b) := inferInstance
  have hs := congrArg (fun F ↦ F.obj K) (D.source E)
  have ht := congrArg (fun F ↦ F.obj K) (D.target E)
  exact cbcIsIso_of_heq hs ht (D.normalized E K r a ha hc)


private theorem cbcDescended_atStage
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    {S : StageSystem C} {T : StageSystem D} (F G : StageSystem.Morphism S T)
    (eta : StageSystem.Morphism.Hom F G) (K : S.PairCategory) (M : I)
    (h : K.stage ≤ M) :
    (StageSystem.Morphism.descNatTrans eta).app K =
      StageSystem.PairCategory.mkHom
        (X := F.functor.obj K) (Y := G.functor.obj K) M h h
        ((F.β h).hom.app K.obj ≫
          (eta.τ M).app ((S.T h).obj K.obj) ≫ (G.β h).inv.app K.obj) := by
  rw [StageSystem.Morphism.descNatTrans_app, StageSystem.ι_map_eq h]
  congr 1
  exact ((Iso.eq_comp_inv ((G.β h).app K.obj)).2
    (eta.comm h K.obj)).trans (Category.assoc _ _ _)


private theorem cbcConjugate_naturality
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (eta : F ⟶ G) {A K : C} (alpha : A ≅ K) :
    F.map alpha.inv ≫ eta.app A ≫ G.map alpha.hom = eta.app K := by
  rw [eta.naturality_assoc]
  rw [← G.map_comp, alpha.inv_hom_id, G.map_id, Category.comp_id]


private theorem cbcDescended_properties
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    {S : StageSystem C} {T : StageSystem D} (F G : StageSystem.Morphism S T)
    (eta : StageSystem.Morphism.Hom F G)
    (hi : ∀ i (K : C i), IsIso ((eta.τ i).app K)) :
    IsIso (StageSystem.Morphism.descNatTrans eta) ∧
    (∀ K, IsIso ((StageSystem.Morphism.descNatTrans eta).app K)) ∧
    (∀ (K : S.PairCategory) (M : I) (h : K.stage ≤ M),
      (StageSystem.Morphism.descNatTrans eta).app K =
        StageSystem.PairCategory.mkHom
          (X := F.functor.obj K) (Y := G.functor.obj K) M h h
          ((F.β h).hom.app K.obj ≫
            (eta.τ M).app ((S.T h).obj K.obj) ≫ (G.β h).inv.app K.obj)) ∧
    (∀ (K A B : S.PairCategory) (alpha : A ≅ K) (beta : B ≅ K),
      F.functor.map alpha.inv ≫ (StageSystem.Morphism.descNatTrans eta).app A ≫
          G.functor.map alpha.hom =
        F.functor.map beta.inv ≫ (StageSystem.Morphism.descNatTrans eta).app B ≫
          G.functor.map beta.hom) := by
  have hdesc (K : S.PairCategory) :
      IsIso ((StageSystem.Morphism.descNatTrans eta).app K) :=
    StageSystem.Morphism.isIso_descNatTrans_app eta K (hi K.stage K.obj)
  have : ∀ K, IsIso ((StageSystem.Morphism.descNatTrans eta).app K) := hdesc
  refine ⟨NatIso.isIso_of_isIso_app _, hdesc, cbcDescended_atStage F G eta, ?_⟩
  intro K A B alpha beta
  exact (cbcConjugate_naturality _ alpha).trans (cbcConjugate_naturality _ beta).symm


/-- The descended compact-support exchange is invertible, with its finite-overfield
representative and independence of the pair representing the fixed input.
There is no properness, smoothness or finite-type restriction on the base change.
Existence of descent data is a conclusion; every normalized presentation has the
stated properties. Thus coefficient compatibility is not an
additional hypothesis imposed on the geometric square.

Source: blueprint main-20261015, `thm-cbc-qbar`, order 1992
(blueprint: thm-cbc-qbar).

Proof:
1. Construct a normalized model using cbcQbarExchangeModel_exists. This is the
coefficient-coherence and descent part of the argument, separated from the assertions
about every normalized model.
2. For any such model, wfConstructible_complete makes each integral representative
complete. The completed compact-support base-change theorem makes its exchange
invertible. Full-subcategory inclusion and rational localization preserve this fact;
the model's normalization identifies it with the specified stage component.
3. Stage inclusion preserves these inverses. Pointwise invertibility gives invertibility
of the descended natural transformation. The compatibility equation Hom.comm and the
pair-category transport formula give its representative at any larger coefficient field.
4. Naturality conjugates the exchange along either representing isomorphism to its
component at the fixed object, proving independence of the chosen representing pair.
-/
theorem qbarCompactSupportBaseChange
    [IsSeparated f] [LocallyOfFiniteType f]
    [IsNoetherian Y] [IsNoetherian X']
    (_dimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (_dimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
    (_invY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (_invX' : ∀ x : X', IsUnit (l : X'.presheaf.stalk x)) :
    Nonempty (CbcQbarExchangeModel l Ω c c' gbar properSquare openSquare) ∧
      ∀ D : CbcQbarExchangeModel l Ω c c' gbar properSquare openSquare,
      (∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcStageCategory l Ω X E),
        IsIso ((D.exchange.τ E).app K)) ∧
      IsIso (StageSystem.Morphism.descNatTrans D.exchange) ∧
      (∀ K : pbcQbarCategory l Ω X,
        IsIso ((StageSystem.Morphism.descNatTrans D.exchange).app K)) ∧
      (∀ (K : pbcQbarCategory l Ω X) (M : Padic.FiniteCoefficientFields l Ω)
        (h : K.stage ≤ M),
        (StageSystem.Morphism.descNatTrans D.exchange).app K =
          StageSystem.PairCategory.mkHom
            (X := D.U.base.functor.obj K) (Y := D.V.base.functor.obj K) M h h
            ((D.U.base.β h).hom.app K.obj ≫
              (D.exchange.τ M).app
                (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj K.obj) ≫
              (D.V.base.β h).inv.app K.obj)) ∧
      (∀ (K A B : pbcQbarCategory l Ω X) (α : A ≅ K) (β : B ≅ K),
        D.U.base.functor.map α.inv ≫
            (StageSystem.Morphism.descNatTrans D.exchange).app A ≫
            D.V.base.functor.map α.hom =
          D.U.base.functor.map β.inv ≫
            (StageSystem.Morphism.descNatTrans D.exchange).app B ≫
            D.V.base.functor.map β.hom) := by
  refine ⟨cbcQbarExchangeModel_exists l Ω c c' gbar properSquare openSquare
    _dimY _dimX' _invY _invX', ?_⟩
  intro D
  have hi := cbcModel_stage_isIso l Ω c c' gbar properSquare openSquare D
  have hd := cbcDescended_properties
    (C := fun E ↦ pbcStageCategory l Ω X E)
    (D := fun E ↦ pbcStageCategory l Ω Y' E)
    (S := pbcScalarSystem l Ω X dX.out iX.out)
    (T := pbcScalarSystem l Ω Y' dY'.out iY'.out)
    D.U.base D.V.base D.exchange hi
  exact ⟨hi, hd⟩

end AlgebraicGeometry.Scheme
