/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Full faithfulness on common-stage coefficient categories

Source: main-20261015, sec-smooth-purity/sk-prop-sf-closed-unit,
prop-sf-closed-unit-all-stages.proof.md, algebraically closed-stage paragraph
(blueprint: lem-sf-common-stage-full-faithfulness).

The existing stage morphism uses beta = theta inverse. Its functor is the literal
pair functor. Identity normalization is expressed using the published tensor units,
so no identity scalar extension is replaced by a different functor.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

section StageSystems

universe w u₁ u₂ v₁ v₂

variable {I : Type w} [Preorder I]
  {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
  {S : StageSystem C} {T : StageSystem D} (F : S.Morphism T)
  (hΦ : ∀ i, (F.Φ i).FullyFaithful)

open StageSystem.PairCategory

include hΦ in
private theorem sfMapAt_injective {i j n : I} {hi : i ≤ n} {hj : j ≤ n}
    {x : C i} {y : C j} :
    Function.Injective (F.mapAt (hi := hi) (hj := hj) (x := x) (y := y)) := by
  intro f g h
  apply (hΦ n).map_injective
  have e := congrArg
    (fun t ↦ (F.β hi).inv.app x ≫ t ≫ (F.β hj).hom.app y) h
  simpa [StageSystem.Morphism.mapAt] using e

private theorem sfMapAt_preimage {i j n : I} (hi : i ≤ n) (hj : j ≤ n)
    (x : C i) (y : C j)
    (v : (T.T hi).obj ((F.Φ i).obj x) ⟶ (T.T hj).obj ((F.Φ j).obj y)) :
    F.mapAt ((hΦ n).preimage ((F.β hi).inv.app x ≫ v ≫ (F.β hj).hom.app y)) = v := by
  simp [StageSystem.Morphism.mapAt]

variable [IsDirectedOrder I]

include hΦ in
private theorem sfPairFaithful : F.functor.Faithful where
  map_injective {X Y} f g h := by
    induction f using hom_induction with
    | h n hX hY u =>
      induction g using hom_induction with
      | h m hX' hY' v =>
        rw [F.functor_map_mkHom, F.functor_map_mkHom] at h
        obtain ⟨p, hp, hp', e⟩ := (mkHom_eq_mkHom_iff' _ _).1 h
        apply (mkHom_eq_mkHom_iff' _ _).2
        refine ⟨p, hp, hp', ?_⟩
        rw [F.tr_mapAt, F.tr_mapAt] at e
        exact sfMapAt_injective F hΦ e

include hΦ in
private theorem sfPairFull : F.functor.Full where
  map_surjective {X Y} f := by
    induction f using hom_induction with
    | h n hX hY v =>
      refine ⟨mkHom n hX hY
        ((hΦ n).preimage ((F.β hX).inv.app X.obj ≫ v ≫ (F.β hY).hom.app Y.obj)), ?_⟩
      rw [F.functor_map_mkHom, sfMapAt_preimage]

end StageSystems

/-- Fully faithful finite-stage functors descend, with their inverse on representatives.
Source: main-20261015, sec-smooth-purity/sk-prop-sf-closed-unit,
prop-sf-closed-unit-all-stages.proof.md, algebraically closed-stage paragraph
(blueprint: lem-sf-common-stage-full-faithfulness).

Proof: (1) At a common field L, full faithfulness of Phi_L and conjugation by
beta give a bijection b_L. Its inverse sends v to the finite fully faithful
preimage of beta_source inverse, followed by v, followed by beta_target.
(2) Substitute F.coh and its inverse at the endpoints into b_M of a transported
arrow; naturality of beta cancels the middle factors. Hence b commutes with
transport. (3) Eventual equality of representatives, supplied by
 def-weil-algebraically-closed-coefficients, proves independence of the forward
representative. (4) Normalization preserves identities. At one common stage,
adjacent beta inverses cancel, proving preservation of composition; this is
precisely the existing F.functor. (5) Apply b_M to the transport of b_L inverse
of v. Step 2 identifies the result with the transport of v; injectivity of b_M
therefore proves compatibility of the inverse with enlargement. Eventual equality
then proves independence of its representative. (6) The two finite inverse
identities descend to the two inverse identities on Hom classes. They supply
h, whose preimage equation below holds for every representative, including any
larger common field. No scalar transition need be faithful, and no essential
surjectivity or Karoubi completion is used. -/
theorem sfCommonStageFullFaithfulness
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (k : Type u) [Field k] (_hl : IsUnit (l : k))
    (Z X : Scheme.{u}) (z : Z ⟶ Spec (.of k)) (x : X ⟶ Spec (.of k))
    [IsSeparated z] [LocallyOfFiniteType z] [QuasiCompact z]
    [IsSeparated x] [LocallyOfFiniteType x] [QuasiCompact x]
    (F : StageSystem.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X))
    (hΦ : ∀ E : Padic.FiniteCoefficientFields l Ω, (F.Φ E).FullyFaithful)
    (_hunit : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (P : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Z E),
      HEq ((F.β (le_refl E)).hom.app P)
        ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω X E).hom.app
            ((F.Φ E).obj P) ≫
          (F.Φ E).map ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω Z E).inv.app P))) :
    ∃ h : F.functor.FullyFaithful,
      (∀ A : generalAlgebraicallyClosedConstructibleCategory l Ω Z,
        F.functor.obj A = ⟨A.stage, (F.Φ A.stage).obj A.obj⟩) ∧
      (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω Z)
        (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
        (u : A.toStage hA ⟶ B.toStage hB),
        F.functor.map (StageSystem.PairCategory.mkHom L hA hB u) =
          StageSystem.PairCategory.mkHom
            (X := F.functor.obj A) (Y := F.functor.obj B) L hA hB
            ((F.β hA).hom.app A.obj ≫ (F.Φ L).map u ≫ (F.β hB).inv.app B.obj)) ∧
      (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω Z)
        (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
        (v : (F.functor.obj A).toStage hA ⟶ (F.functor.obj B).toStage hB),
        h.preimage (StageSystem.PairCategory.mkHom L hA hB v) =
          StageSystem.PairCategory.mkHom L hA hB
            ((hΦ L).preimage
              ((F.β hA).inv.app A.obj ≫ v ≫ (F.β hB).hom.app B.obj))) := by
  have : F.functor.Faithful := sfPairFaithful F hΦ
  have : F.functor.Full := sfPairFull F hΦ
  let h : F.functor.FullyFaithful := .ofFullyFaithful F.functor
  refine ⟨h, F.functor_obj, ?_, ?_⟩
  · intro A B L hA hB u
    exact F.functor_map_mkHom hA hB u
  · intro A B L hA hB v
    apply h.map_injective
    rw [h.map_preimage, F.functor_map_mkHom, sfMapAt_preimage]

end WeilConjectures
