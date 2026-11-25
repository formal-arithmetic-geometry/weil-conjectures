/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.DeligneLaumon.CommonStagePullbackCompComponent

/-! # Naturality of the normalized common-stage compositor

The components of the normalized common-stage pullback compositor are natural.

## Implementation details

An arrow is represented at a common coefficient stage `L`. There one transports the integral
compositor to `L` using the scalar-extension tower coherence, applies the naturality square of
the integral pullback compositor and cancels the comparison isomorphisms. The recorded
object-equality transports cancel by proof irrelevance.

## References

* [Stacks Project, Tag 099N]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

private theorem pod_map_heq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx; cases hy; cases h; rfl

private theorem comp_ofHom_square
    (W : Scheme.{u})
    (P Q R S : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (hP : P.stage ≤ L) (hQ : Q.stage ≤ L) (hR : R.stage ≤ L) (hS : S.stage ≤ L)
    (u : P.toStage hP ⟶ Q.toStage hQ) (v : Q.toStage hQ ⟶ S.toStage hS)
    (u' : P.toStage hP ⟶ R.toStage hR) (v' : R.toStage hR ⟶ S.toStage hS)
    (e : u ≫ v = u' ≫ v') :
    GeneralAlgebraicallyClosedCoefficients.ofHom P Q L hP hQ u ≫
        GeneralAlgebraicallyClosedCoefficients.ofHom Q S L hQ hS v =
      GeneralAlgebraicallyClosedCoefficients.ofHom P R L hP hR u' ≫
        GeneralAlgebraicallyClosedCoefficients.ofHom R S L hR hS v' := by
  simpa only [GeneralAlgebraicallyClosedCoefficients.ofHom,
    StageSystem.PairCategory.mkHom_comp_mkHom] using
      congrArg (StageSystem.PairCategory.mkHom L hP hS) e

/-- Naturality of the common-stage compositor for a morphism given by an explicit
representative at a common coefficient stage. -/
theorem commonStagePullbackCompComponent_naturality_ofHom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    {P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Z}
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
    (r : P.toStage hP ⟶ Q.toStage hQ) :
    (commonStageDerivedPullback l Ω (f ≫ g)).map
        (GeneralAlgebraicallyClosedCoefficients.ofHom P Q L hP hQ r) ≫
        (commonStagePullbackCompComponent l Ω f g Q).hom =
      (commonStagePullbackCompComponent l Ω f g P).hom ≫
        (commonStageDerivedPullback l Ω f).map
          ((commonStageDerivedPullback l Ω g).map
            (GeneralAlgebraicallyClosedCoefficients.ofHom P Q L hP hQ r)) := by
  have compobj (M) :
      (commonStageDerivedPullback l Ω f).obj
        ((commonStageDerivedPullback l Ω g).obj M) =
      commonStagePullbackObject l Ω f (commonStagePullbackObject l Ω g M) := by
    rw [commonStageDerivedPullback_object_representation l Ω g M,
      commonStageDerivedPullback_object_representation l Ω f
        (commonStagePullbackObject l Ω g M)]
  have hleft := heq_comp
    (commonStageDerivedPullback_object_representation l Ω (f ≫ g) P)
    (commonStageDerivedPullback_object_representation l Ω (f ≫ g) Q)
    (compobj Q)
    (commonStageDerivedPullback_map_representation l Ω (f ≫ g) P Q L hP hQ r)
    (commonStagePullbackCompComponent_stage_representation l Ω f g Q L hQ)
  have hm := (pod_map_heq (commonStageDerivedPullback l Ω f)
      (commonStageDerivedPullback_object_representation l Ω g P)
      (commonStageDerivedPullback_object_representation l Ω g Q)
      (commonStageDerivedPullback_map_representation l Ω g P Q L hP hQ r)).trans
    (commonStageDerivedPullback_map_representation l Ω f
      (commonStagePullbackObject l Ω g P)
      (commonStagePullbackObject l Ω g Q) L hP hQ _)
  have hright := heq_comp
    (commonStageDerivedPullback_object_representation l Ω (f ≫ g) P)
    (compobj P) (compobj Q)
    (commonStagePullbackCompComponent_stage_representation l Ω f g P L hP) hm
  apply eq_of_heq
  refine hleft.trans (HEq.trans ?_ hright.symm)
  apply heq_of_eq
  refine comp_ofHom_square l Ω X
    (commonStagePullbackObject l Ω (f ≫ g) P)
    (commonStagePullbackObject l Ω (f ≫ g) Q)
    (commonStagePullbackObject l Ω f (commonStagePullbackObject l Ω g P))
    (commonStagePullbackObject l Ω f (commonStagePullbackObject l Ω g Q))
    L hP hQ hP hQ _ _ _ _ ?_
  exact
  commonStagePullbackCompComponent_stage_square l Ω f g L hP hQ r

/-- The normalized integral components descend naturally to common-stage morphisms. -/
theorem commonStagePullbackCompComponent_naturality {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    {P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Z} (a : P ⟶ Q) :
    (commonStageDerivedPullback l Ω (f ≫ g)).map a ≫
        (commonStagePullbackCompComponent l Ω f g Q).hom =
      (commonStagePullbackCompComponent l Ω f g P).hom ≫
        (commonStageDerivedPullback l Ω f).map ((commonStageDerivedPullback l Ω g).map a) := by
  induction a using StageSystem.PairCategory.hom_induction with
  | h L hP hQ r =>
    exact commonStagePullbackCompComponent_naturality_ofHom l Ω f g L hP hQ r

end WeilConjectures
