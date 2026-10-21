/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Paper.IntegralTwistScalarCoherence

/-! # Tate twists descend through common finite coefficient stages

Source: main-20261015 blueprint, sec-six-functors-basics/sk-prop-sf-existence,
`prop-weil-twist-preserves.proof.md`, final sentence
(blueprint: lem-weil-qbar-twist-common-stage).

The input finite-stage functors are fixed on integral objects and all rational pure
morphisms. Their comparisons are fixed by the published completed beta. The two
signs are indexed by Bool; true means m and false means -m. The comparison b is
beta: in Lean composition order its source is T_E followed by scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory AlgebraicGeometry TensorProduct
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
  (Stage Pair stageSystem integralTransition unitor)

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (S : Scheme.{u}) [∀ x : S, Invertible (l : S.residueField x)]

/-- The actual derived tensor map, restricted to the recorded intrinsic full subcategory.
Source: the integral representative in `prop-weil-twist-preserves.proof.md`, final sentence
(blueprint: lem-weil-qbar-twist-common-stage). -/
def qbarTwistIntegralMap (E : Index l Ω) (n : ℤ)
    {C D : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) S} (f : C ⟶ D) :
    integralTwistCoherenceObject l (Coefficient.{u} l Ω E) S n C ⟶
      integralTwistCoherenceObject l (Coefficient.{u} l Ω E) S n D :=
  ObjectProperty.homMk
    ((integralSheafTwist l (Coefficient.{u} l Ω E) S n).mapDerivedCategory.map f.hom)

/-- The canonical completed beta component in the full integral subcategory.
Its rationalization fixes the input beta, including identity extensions.
Source: `prop-weil-twist-preserves.proof.md`, final sentence, via
lem-weil-integral-twist-derived-scalar (blueprint: lem-weil-qbar-twist-common-stage). -/
def qbarTwistIntegralBeta {E F : Index l Ω} (h : E ≤ F) (n : ℤ)
    (C : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) S) :
    (integralTransition l Ω S E F h).obj
        (integralTwistCoherenceObject l (Coefficient.{u} l Ω E) S n C) ⟶
      integralTwistCoherenceObject l (Coefficient.{u} l Ω F) S n
        ((integralTransition l Ω S E F h).obj C) :=
  ObjectProperty.homMk
    ((integralTwistCompletedBeta l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω F)
      (coefficientInclusion l Ω E F h) S n).hom.app C)

/-- Twisting at finite coefficient stages descends, with the prescribed morphism
formula and both inverse evaluation isomorphisms.

Source: `prop-weil-twist-preserves.proof.md`, final sentence
(blueprint: lem-weil-qbar-twist-common-stage).

Proof:
1. At a common stage F conjugate T_F(f) by beta at the two endpoints. The integral
   object and pure-morphism normalizations identify T with the stated rational twist;
   the beta normalization uses lem-weil-integral-twist-derived-scalar.
2. The tower equation (lem-weil-integral-twist-scalar-coherence) moves both endpoint
   betas through the scalar associator of lem-weil-scalar-extension-composition.
3. Expand transport a_source.inv >> B(f) >> a_target.hom. Naturality of beta and
   cancellation give transport(twist(f)) = twist(transport(f)). Eventual equality
   of representatives in def-weil-algebraically-closed-coefficients therefore descends.
4. At a common stage beta and its inverse cancel for identities and at the middle
   endpoint of a composite. Functoriality of T proves both functor laws, for each sign.
5. Evaluation compatibility from lem-weil-integral-twist-base-change identifies the
   enlargement of each finite evaluation with evaluation after the two betas.
6. These evaluation classes are natural: expand the twice-twisted representative,
   use finite-stage evaluation naturality, and cancel comparisons. Their inverses
   are the classes of the inverse evaluations, giving both natural isomorphisms.
7. Apply the two evaluations to the coefficient unit. Since each T is tensor with
   the actual signed line, these identify both ordered tensor products of Qbar(m)
   and Qbar(-m) with the unit; this is invertibility in the common-stage category.
-/
theorem qbar_twist_common_stage (m : ℤ)
    (T : Bool → ∀ E : Index l Ω, Stage l Ω S E ⥤ Stage l Ω S E)
    (_hobj : ∀ (s : Bool) (E : Index l Ω) (C : Stage l Ω S E),
      (T s E).obj C =
        ⟨integralTwistCoherenceObject l (Coefficient.{u} l Ω E) S
          (if s then m else -m) C.obj⟩)
    (_hmap : ∀ (s : Bool) (E : Index l Ω)
      (C D : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) S)
      (f : C ⟶ D)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l
        (Coefficient.{u} l Ω E))),
      HEq ((T s E).map (a ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E)] f :
          (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) S).obj C ⟶
            (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) S).obj D))
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E)]
          qbarTwistIntegralMap l Ω S E (if s then m else -m) f))
    (b : ∀ (s : Bool) {E F : Index l Ω} (h : E ≤ F),
      T s E ⋙ (stageSystem l Ω S).T h ≅ (stageSystem l Ω S).T h ⋙ T s F)
    (_hbeta : ∀ (s : Bool) (E F : Index l Ω) (h : E ≤ F)
      (C : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) S),
      HEq ((b s h).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) S).obj C))
        ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l
          (Coefficient.{u} l Ω F))) ⊗ₜ[
            Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω F)]
              qbarTwistIntegralBeta l Ω S h (if s then m else -m) C))
    (_hunit : ∀ (s : Bool) (E : Index l Ω) (C : Stage l Ω S E),
      HEq ((b s (le_refl E)).hom.app C)
        ((unitor l Ω S E).hom.app ((T s E).obj C) ≫
          (T s E).map ((unitor l Ω S E).inv.app C)))
    (_htower : ∀ s : Bool,
      StageSystem.pairFunctorCoherent (stageSystem l Ω S) (stageSystem l Ω S) (T s) (b s))
    (e : ∀ (s : Bool) (E : Index l Ω), T s E ⋙ T (!s) E ≅ 𝟭 (Stage l Ω S E))
    (_heval : ∀ (s : Bool) (E F : Index l Ω) (h : E ≤ F) (C : Stage l Ω S E),
      (b (!s) h).hom.app ((T s E).obj C) ≫
        (T (!s) F).map ((b s h).hom.app C) ≫
        (e s F).hom.app (((stageSystem l Ω S).T h).obj C) =
          ((stageSystem l Ω S).T h).map ((e s E).hom.app C)) :
    ∃ U : Bool → (Pair l Ω S ⥤ Pair l Ω S),
      (∀ (s : Bool) (P : Pair l Ω S), (U s).obj P = ⟨P.stage, (T s P.stage).obj P.obj⟩) ∧
      (∀ (s : Bool) (P Q : Pair l Ω S) (F : Index l Ω)
        (hP : P.stage ≤ F) (hQ : Q.stage ≤ F) (f : P.toStage hP ⟶ Q.toStage hQ),
        HEq ((U s).map (StageSystem.PairCategory.mkHom F hP hQ f))
          (StageSystem.PairCategory.mkHom
            (X := (⟨P.stage, (T s P.stage).obj P.obj⟩ : Pair l Ω S))
            (Y := (⟨Q.stage, (T s Q.stage).obj Q.obj⟩ : Pair l Ω S)) F hP hQ
            ((b s hP).hom.app P.obj ≫ (T s F).map f ≫ (b s hQ).inv.app Q.obj))) ∧
      ∃ ε : ∀ s : Bool, U s ⋙ U (!s) ≅ 𝟭 (Pair l Ω S),
        ∀ (s : Bool) (P : Pair l Ω S),
          HEq ((ε s).hom.app P)
            (((stageSystem l Ω S).ι P.stage).map ((e s P.stage).hom.app P.obj)) := by
  -- The generic quotient descent uses exactly the supplied tower equation.
  let F : Bool → (stageSystem l Ω S).Morphism (stageSystem l Ω S) := fun s ↦
    { Φ := T s, β := b s, coh := _htower s }
  -- Evaluation compatibility is the transformation square for the composite family.
  let τ : ∀ s : Bool, (F s |>.comp (F (!s))).Hom
      (StageSystem.Morphism.id (stageSystem l Ω S)) := fun s ↦
    { τ := fun E ↦ (e s E).hom
      comm := fun h C ↦ by
        simpa [F, StageSystem.Morphism.comp, StageSystem.Morphism.id] using
          (_heval s _ _ h C).symm }
  have hτ (s : Bool) : IsIso (StageSystem.Morphism.descNatTrans (τ s)) :=
    StageSystem.Morphism.isIso_descNatTrans (τ s) (fun E ↦ by dsimp [τ]; infer_instance)
  -- Compare descent of composition and identity with the descended evaluation.
  let ε : ∀ s : Bool, (F s).functor ⋙ (F (!s)).functor ≅ 𝟭 (Pair l Ω S) := fun s ↦
    (StageSystem.Morphism.functorCompIso (F s) (F (!s))).symm ≪≫
      asIso (StageSystem.Morphism.descNatTrans (τ s)) ≪≫
        StageSystem.Morphism.functorIdIso
  refine ⟨fun s ↦ (F s).functor, ?_, ?_, ε, ?_⟩
  · intro s P
    rfl
  · intro s P Q E hP hQ f
    rfl
  · intro s P
    apply heq_of_eq
    simp [ε, StageSystem.Morphism.descNatTrans_app, τ]

end WeilConjectures
