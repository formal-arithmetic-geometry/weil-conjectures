/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.DerivedAutomorphismHomEvaluation
public import WeilConjectures.AlgebraicGeometry.CompactSupportFiniteAction
public import WeilConjectures.AlgebraicGeometry.DirectImagesConstructible
public import WeilConjectures.CategoryTheory.StageSystem.Functor
import WeilConjectures.AlgebraicGeometry.CommonStageEvaluationNaturality

/-! # Descent of exceptional adjunction maps and evaluation

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, exceptional-adjunction paragraph
(blueprint: lem-sf-package-qbar-adjunction-map-descent).

The stage-system morphisms retain the specified scalar comparisons. The finite
adjunction characterizes the exceptional functor as the right adjoint of the
actual compact-support functor. Hom is used only on its recorded permitted pairs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients

section StageAdjunction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u₁ v₁ u₂ v₂
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  {B : I → Type u₂} [∀ i, Category.{v₂} (B i)]
  {S : StageSystem C} {T : StageSystem B}
  (F : S.Morphism T) (G : T.Morphism S) (a : ∀ i, F.Φ i ⊣ G.Φ i)
  (hu : ∀ (i j : I) (h : i ≤ j) (K : C i),
    (S.T h).map ((a i).unit.app K) ≫ (G.β h).hom.app ((F.Φ i).obj K) ≫
      (G.Φ j).map ((F.β h).hom.app K) = (a j).unit.app ((S.T h).obj K))
  (he : ∀ (i j : I) (h : i ≤ j) (M : B i),
    (F.β h).hom.app ((G.Φ i).obj M) ≫ (F.Φ j).map ((G.β h).hom.app M) ≫
      (a j).counit.app ((T.T h).obj M) = (T.T h).map ((a i).counit.app M))

open StageSystem StageSystem.Morphism StageSystem.PairCategory in
private def descendedUnit : 𝟭 S.PairCategory ⟶ F.functor ⋙ G.functor :=
  (functorIdIso (S := S)).inv ≫
    descNatTrans (F := Morphism.id S) (G := F.comp G)
      { τ := fun i ↦ (a i).unit
        comm := fun {i j} h K ↦ by
          change (S.T h).map ((a i).unit.app K) ≫ ((F.comp G).β h).hom.app K =
            𝟙 _ ≫ (a j).unit.app ((S.T h).obj K)
          rw [comp_β_hom_app, Category.id_comp]
          exact hu i j h K } ≫
    (functorCompIso F G).hom

open StageSystem StageSystem.Morphism StageSystem.PairCategory in
private def descendedCounit : G.functor ⋙ F.functor ⟶ 𝟭 T.PairCategory :=
  (functorCompIso G F).inv ≫
    descNatTrans (F := G.comp F) (G := Morphism.id T)
      { τ := fun i ↦ (a i).counit
        comm := fun {i j} h M ↦ by
          change (T.T h).map ((a i).counit.app M) ≫ 𝟙 _ =
            ((G.comp F).β h).hom.app M ≫ (a j).counit.app ((T.T h).obj M)
          simp only [comp_β_hom_app, Category.comp_id]
          simpa only [Category.assoc] using (he i j h M).symm } ≫
    (functorIdIso (S := T)).hom

private lemma descendedUnit_app (K : S.PairCategory) :
    (descendedUnit F G a hu).app K = (S.ι K.stage).map ((a K.stage).unit.app K.obj) := by
  simp [descendedUnit, StageSystem.Morphism.descNatTrans_app]

private lemma descendedCounit_app (M : T.PairCategory) :
    (descendedCounit F G a he).app M = (T.ι M.stage).map ((a M.stage).counit.app M.obj) := by
  simp [descendedCounit, StageSystem.Morphism.descNatTrans_app]

private def descendedAdjunction : F.functor ⊣ G.functor :=
  Adjunction.mkOfUnitCounit
    { unit := descendedUnit F G a hu
      counit := descendedCounit F G a he
      left_triangle := by
        ext K
        simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_hom_app, Category.id_comp,
          descendedUnit_app, descendedCounit_app]
        rw [StageSystem.Morphism.functor_map_ι]
        change (T.ι K.stage).map ((F.Φ K.stage).map ((a K.stage).unit.app K.obj)) ≫
          (T.ι K.stage).map ((a K.stage).counit.app ((F.Φ K.stage).obj K.obj)) = 𝟙 _
        rw [← Functor.map_comp]
        simp
      right_triangle := by
        ext M
        simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_inv_app, Category.id_comp,
          descendedUnit_app, descendedCounit_app]
        rw [StageSystem.Morphism.functor_map_ι]
        change (S.ι M.stage).map ((a M.stage).unit.app ((G.Φ M.stage).obj M.obj)) ≫
          (S.ι M.stage).map ((G.Φ M.stage).map ((a M.stage).counit.app M.obj)) = 𝟙 _
        rw [← Functor.map_comp]
        simp }
end StageAdjunction

private lemma evaluation_transport {C : Type u} [Category.{v} C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H) (P : J.FullSubcategory) (B : C)
    (h : H.obj P = B) :
    HEq (S.evaluation P) ((S.transpose B P).symm (eqToHom h.symm)) := by
  subst B
  rfl

private lemma identity_transport {C : Type u} [Category.{v} C]
    {A B : C} (h : A = B) : HEq (eqToHom h.symm) (𝟙 A) := by
  subst B
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation normalization and its correctly variant naturality equation.
The normalization specializes inverse transpose to the identity, hence gives
[E,ev_E] at every common field, with the recorded tensor and Hom comparisons.
The residue inverse is derived from ell different from p, rather than assumed.
Source: current blueprint, exceptional-adjunction paragraph, evaluation clause
(blueprint: lem-sf-package-qbar-adjunction-map-descent). -/
def SfQbarEvaluationDescent (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (W : Scheme.{u}) [W.Over (Spec (.of D.k))] : Prop := by
  letI (x : W) : Invertible (l : W.residueField x) :=
    IsUnit.invertible (by
      let φ : D.k →+* W.residueField x :=
        (Scheme.Spec.preimage
          (W.fromSpecResidueField x ≫ (W ↘ Spec (.of D.k)))).unop.hom
      simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D l hl).map φ)
  exact (∀ (P : (commonStageHomPairs l Ω W).FullSubcategory) (L : Index l Ω)
      (hH : (commonStageHomObject l Ω W P).stage ≤ L)
      (hT : (commonStageTensorObject l Ω W
        (commonStageHomObject l Ω W P) P.obj.1.unop).stage ≤ L)
      (hQ : P.obj.2.stage ≤ L)
      (φ : (commonStageHomObject l Ω W P).toStage hH ⟶
        (commonStageHomObject l Ω W P).toStage hH),
      HEq (𝟙 ((commonStageDerivedInternalHom l Ω W).obj P))
        (GeneralAlgebraicallyClosedCoefficients.ofHom
          (commonStageHomObject l Ω W P) (commonStageHomObject l Ω W P) L hH hH φ) →
      HEq ((podCommonClosed l Ω W).evaluation P)
        (GeneralAlgebraicallyClosedCoefficients.ofHom
          (commonStageTensorObject l Ω W (commonStageHomObject l Ω W P) P.obj.1.unop)
          P.obj.2 L hT hQ
          ((commonStageTensorComparison l Ω W
            (commonStageHomObject l Ω W P) P.obj.1.unop L hT).hom ≫
            ((podRationalClosed l (Coefficient.{u} l Ω L) W).transpose
              ((commonStageHomObject l Ω W P).toStage hH)
              (commonStageHomPairAtStage l Ω W P L hH)).symm
                (φ ≫ (commonStageHomComparison l Ω W P L hH).hom)))) ∧
    ∀ (P Q : (commonStageHomPairs l Ω W).FullSubcategory) (g : P ⟶ Q),
      (commonStageDerivedTensor l Ω W).map
          (Prod.mkHom ((commonStageDerivedInternalHom l Ω W).map g) (𝟙 Q.obj.1.unop)) ≫
        (podCommonClosed l Ω W).evaluation Q =
      (commonStageDerivedTensor l Ω W).map
          (Prod.mkHom (𝟙 ((commonStageDerivedInternalHom l Ω W).obj P)) g.hom.1.unop) ≫
        (podCommonClosed l Ω W).evaluation P ≫ g.hom.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified rational adjunctions descend with their actual maps.
Source: current blueprint, prop-functor-package.proof.md, exceptional-adjunction
paragraph (blueprint: lem-sf-package-qbar-adjunction-map-descent).

Proof, following the six DAG steps:
1. Use def-weil-algebraically-closed-coefficients and the three operation
 definitions. A stage morphism maps [L,u] to [L,beta F_L(u) beta inverse].
 Naturality and the tower equation respect eventual equality; the two middle
 comparisons cancel in composites. The same argument applies contravariantly
 in the first internal-Hom argument.
2. At L apply u |-> G_L(u) eta_L, with inverse v |-> F_L(v) epsilon_L.
 The two comparison equations below say these maps commute with transitions.
 Apply lem-coef-qbar-adjunction-hom-descent (DirectLimit.congr and its two
 representative formulas) to obtain inverse bijections of the Hom colimits.
3. Represent arbitrary arrows and the tested Hom at a common finite field.
 Finite-stage naturality proves naturality of the resulting bijection. Its
 values and inverse values on identities are precisely the displayed units
 and counits. Enlarging the field or replacing object presentations uses
 the identity-represented transition isomorphisms, hence gives the same maps.
4. For evaluation use the specified tensor and internal-Hom comparisons and
 the inverse transpose of the identity. Preservation of evaluation makes
 the representative at L agree with its representative at any larger field;
 two choices agree over their compositum. Normalization is retained.
5. Finite-stage evaluation naturality in the second argument and dinaturality
 in the first give the displayed equation on every common-stage arrow.
6. Both triangles are finite-stage triangles, hence equalities of classes.
 Any finite diagram built from these maps, comparisons and operations can
 be put over one field. Induction on its expressions, using the operation
 representative formulas, composition and the normalization clauses below,
 identifies it with its finite-stage image, so every such equality descends.
 No finite-quotient reduction on the algebraically closed category is used.
-/
theorem sfPackageQbarAdjunctionMapDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    (F : (stageSystem l Ω X).Morphism (stageSystem l Ω Y))
    (G : (stageSystem l Ω Y).Morphism (stageSystem l Ω X))
    (hF : ∀ E, F.Φ E = sfCompactSupportFiniteFunctor l D.k
      (finiteFieldDatumPrimeUnit D l hl) c (Coefficient.{u} l Ω E))
    (a : ∀ E, F.Φ E ⊣ G.Φ E)
    (unit : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
      (stageTransition l Ω X E L h).map ((a E).unit.app K) ≫
        (G.β h).hom.app ((F.Φ E).obj K) ≫
        (G.Φ L).map ((F.β h).hom.app K) =
      (a L).unit.app ((stageTransition l Ω X E L h).obj K))
    (counit : ∀ (E L : Index l Ω) (h : E ≤ L) (M : Stage l Ω Y E),
      (F.β h).hom.app ((G.Φ E).obj M) ≫
        (F.Φ L).map ((G.β h).hom.app M) ≫
        (a L).counit.app ((stageTransition l Ω Y E L h).obj M) =
      (stageTransition l Ω Y E L h).map ((a E).counit.app M)) :
    (∃ A : F.functor ⊣ G.functor,
      (∀ (K : Pair l Ω X) (M : Pair l Ω Y) (L : Index l Ω)
        (hK : K.stage ≤ L) (hM : M.stage ≤ L)
        (b : (F.Φ L).obj (K.toStage hK) ⟶ M.toStage hM),
        A.homEquiv K M
            (StageSystem.PairCategory.mkHom
              (X := F.functor.obj K) (Y := M) L hK hM ((F.β hK).hom.app K.obj ≫ b)) =
          StageSystem.PairCategory.mkHom
              (X := K) (Y := G.functor.obj M) L hK hM
            ((a L).homEquiv (K.toStage hK) (M.toStage hM) b ≫
              (G.β hM).inv.app M.obj)) ∧
      (∀ (K : Pair l Ω X) (M : Pair l Ω Y) (L : Index l Ω)
        (hK : K.stage ≤ L) (hM : M.stage ≤ L)
        (b : K.toStage hK ⟶ (G.Φ L).obj (M.toStage hM)),
        (A.homEquiv K M).symm
            (StageSystem.PairCategory.mkHom
              (X := K) (Y := G.functor.obj M) L hK hM (b ≫ (G.β hM).inv.app M.obj)) =
          StageSystem.PairCategory.mkHom
              (X := F.functor.obj K) (Y := M) L hK hM
            ((F.β hK).hom.app K.obj ≫
              ((a L).homEquiv (K.toStage hK) (M.toStage hM)).symm b)) ∧
      (∀ K : Pair l Ω X,
        A.unit.app K =
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := X) K.stage).map ((a K.stage).unit.app K.obj)) ∧
      (∀ M : Pair l Ω Y,
        A.counit.app M =
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := Y) M.stage).map ((a M.stage).counit.app M.obj))) ∧
    SfQbarEvaluationDescent D l hl Ω X ∧ SfQbarEvaluationDescent D l hl Ω Y := by
  have _compactSupportIdentification := hF
  let A := descendedAdjunction F G a unit counit
  refine ⟨⟨A, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro K M L hK hM b
    rw [Adjunction.homEquiv_unit]
    change (descendedUnit F G a unit).app K ≫ G.functor.map _ = _
    rw [descendedUnit_app, StageSystem.ι_map_eq hK,
      StageSystem.Morphism.functor_map_mkHom, StageSystem.PairCategory.mkHom_comp_mkHom]
    apply congrArg (StageSystem.PairCategory.mkHom L hK hM)
    simp only [StageSystem.Morphism.mapAt, Functor.map_comp, Category.assoc,
      Adjunction.homEquiv_unit]
    have hu := unit K.stage L hK K.obj
    simpa only [Category.assoc, StageSystem.Morphism.functor_obj,
      StageSystem.PairCategory.toStage,
      GeneralAlgebraicallyClosedCoefficients.stageTransition] using
      congrArg (fun t ↦ t ≫ (G.Φ L).map b ≫ (G.β hM).inv.app M.obj) hu
  · intro K M L hK hM b
    rw [Adjunction.homEquiv_counit]
    change F.functor.map _ ≫ (descendedCounit F G a counit).app M = _
    rw [descendedCounit_app, StageSystem.ι_map_eq hM,
      StageSystem.Morphism.functor_map_mkHom, StageSystem.PairCategory.mkHom_comp_mkHom]
    apply congrArg (StageSystem.PairCategory.mkHom
      (X := F.functor.obj K) (Y := M) L hK hM)
    simp only [StageSystem.Morphism.mapAt, Functor.map_comp, Category.assoc,
      Adjunction.homEquiv_counit]
    rw [← counit M.stage L hM M.obj]
    change (F.β hK).hom.app K.obj ≫
      (F.Φ L).map b ≫ (F.Φ L).map ((G.β hM).inv.app M.obj) ≫
        (F.β hM).inv.app ((G.Φ M.stage).obj M.obj) ≫
          (F.β hM).hom.app ((G.Φ M.stage).obj M.obj) ≫
            (F.Φ L).map ((G.β hM).hom.app M.obj) ≫
              (a L).counit.app (M.toStage hM) = _
    simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app]
    change (F.β hK).hom.app K.obj ≫ (F.Φ L).map (b ≫ 𝟙 _) ≫
      (a L).counit.app (M.toStage hM) = _
    rw [Category.comp_id]
  · intro K
    exact descendedUnit_app F G a unit K
  · intro M
    exact descendedCounit_app F G a counit M
  · let (x : X) : Invertible (l : X.residueField x) :=
      IsUnit.invertible (by
        let φ : D.k →+* X.residueField x :=
          (Scheme.Spec.preimage
            (X.fromSpecResidueField x ≫ (X ↘ Spec (.of D.k)))).unop.hom
        simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D l hl).map φ)
    constructor
    · intro P L hH hT hQ φ hφ
      have ho : (commonStageDerivedInternalHom l Ω X).obj P =
          commonStageHomObject l Ω X P :=
        (commonStageDerivedInternalHom_existsUnique l Ω X).exists.choose_spec.1 P
      refine (evaluation_transport (podCommonClosed l Ω X) P _ ho).trans ?_
      exact (podCommonClosed_existsUnique l Ω X).exists.choose_spec
        (commonStageHomObject l Ω X P) P L hH hH hT hQ φ (eqToHom ho.symm)
        ((identity_transport ho).trans hφ)
    · exact commonStageEvaluation_naturality l Ω X
  · let (x : Y) : Invertible (l : Y.residueField x) :=
      IsUnit.invertible (by
        let φ : D.k →+* Y.residueField x :=
          (Scheme.Spec.preimage
            (Y.fromSpecResidueField x ≫ (Y ↘ Spec (.of D.k)))).unop.hom
        simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D l hl).map φ)
    constructor
    · intro P L hH hT hQ φ hφ
      have ho : (commonStageDerivedInternalHom l Ω Y).obj P =
          commonStageHomObject l Ω Y P :=
        (commonStageDerivedInternalHom_existsUnique l Ω Y).exists.choose_spec.1 P
      refine (evaluation_transport (podCommonClosed l Ω Y) P _ ho).trans ?_
      exact (podCommonClosed_existsUnique l Ω Y).exists.choose_spec
        (commonStageHomObject l Ω Y P) P L hH hH hT hQ φ (eqToHom ho.symm)
        ((identity_transport ho).trans hφ)
    · exact commonStageEvaluation_naturality l Ω Y

end WeilConjectures
