/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.CategoryTheory.SystemScalarModel
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.DiagramSiteTopology
import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback

/-!
# Compatible K-flat representatives of semilinear coefficient towers

Source: blueprint main-20261015, sec-smooth-purity, sk-lem-sp-tower.proof.md,
preliminary coherent-tower realization; Stacks 06YS, 0G7E, 06YY, 0940 and 0941;
Bhatt--Scholze, Definition 3.5.3
(blueprint: lem-sp-semilinear-kflat-tower-model).

The single complex P is a complex in the actual varying-coefficient tower category.
Its evaluations are the Q_n, and its horizontal arrows are the q_(n,m), including
identity arrows. Index n denotes positive exponent n+1. The predicate below merely
packages all conclusions of the theorem; its local instances are the dependency's
chosen localization and exact evaluations. No representative or morphism is chosen
from a mere existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local instance high] HasDerivedCategory.standard

universe t u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

set_option backward.isDefEq.respectTransparency false in
/-- The actual completed-coefficient quotient, retaining the commutative structures.
It is the unique completed coefficient-limit comparison followed by its nth projection.
Source: blueprint, coherent-tower realization and coefficient convention
(blueprint: lem-sp-semilinear-kflat-tower-model). -/
def spSemilinearCompletedProjection (n : ℕ) :
    WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T ⟶
      (spCoefficientCommRings l E T).obj (op n) :=
  (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).preimage
      ((sp_completed_coefficient_limit l E T).exists.choose.hom ≫
        limit.π (spCoefficientRings l E T) (op n))


attribute [local irreducible] spCoefficientCommRings spCoefficientRings
  spSemilinearCompletedProjection

/-- The chain transition of one complex of actual coefficient towers. This is evaluation
of its strict horizontal transition, for every ordered pair including identities.
Source: blueprint, coherent-tower realization, chain squares
(blueprint: lem-sp-semilinear-kflat-tower-model). -/
def spSemilinearChainTransition (D : SpCoefficientTowersAbelian l E T)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ) {m n : ℕ} (h : m ≤ n) :
    letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
      surjectiveTower_hasSheafify.{t, u} T
    letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
        AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
    letI := D.equivalenceAdditive
    ((spCoefficientEvaluation l E T D.equivalence n).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((systemRestriction (spCoefficientCommRings l E T) h).mapHomologicalComplex
        (.up ℤ)).obj
          (((spCoefficientEvaluation l E T D.equivalence m).mapHomologicalComplex
            (.up ℤ)).obj P) :=
  letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    surjectiveTower_hasSheafify.{t, u} T
  letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
  letI := D.equivalenceAdditive
  (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft D.equivalence.functor
      (strictSystemTransition (spCoefficientCommRings l E T) h)) (.up ℤ)).app P

attribute [local irreducible] spSemilinearChainTransition

/-- The specified derived evaluation isomorphisms of one tower representative.
They use the canonical exact-evaluation factorization and the same tower isomorphism.
Source: blueprint, coherent-tower realization, chain squares
(blueprint: lem-sp-semilinear-kflat-tower-model). -/
def spSemilinearEvaluationIso (D : SpCoefficientTowersAbelian l E T)
    (C : @DerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (a : (@DerivedCategory.Q (spCoefficientTowers l E T) _ _ D.hasDerived).obj P ≅ C) :=
  letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    surjectiveTower_hasSheafify.{t, u} T
  letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits
  letI := D.evaluationColimits
  letI : ∀ n : ℕ, (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    fun n ↦ Functor.additive_of_preserves_binary_products
      (spCoefficientEvaluation l E T D.equivalence n)
  letI : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
  fun n : ℕ ↦
    ((spCoefficientEvaluation l E T D.equivalence n).mapDerivedCategoryFactors.app P).symm ≪≫
      (spCoefficientEvaluation l E T D.equivalence n).mapDerivedCategory.mapIso a

attribute [local irreducible] spSemilinearEvaluationIso

/-- The completed-ring derived lift, its specified evaluations and all derived-limit
projection squares. This is the completed-ring clause of the simultaneous model.
Source: blueprint, sk-lem-sp-tower.proof.md, coherent-tower realization;
Stacks 0940--0941 (blueprint: lem-sp-semilinear-kflat-tower-model). -/
def HasSpSemilinearCompletedLift (D : SpCoefficientTowersAbelian l E T)
    (C : @DerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (a : (@DerivedCategory.Q (spCoefficientTowers l E T) _ _ D.hasDerived).obj P ≅ C) :
    Prop :=
  letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    surjectiveTower_hasSheafify.{t, u} T
  letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits
  letI := D.evaluationColimits
  letI : ∀ n : ℕ, (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    fun n ↦ Functor.additive_of_preserves_binary_products
      (spCoefficientEvaluation l E T D.equivalence n)
  letI : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
  let Ev := spCoefficientEvaluation l E T D.equivalence
  let R := WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T
  let RM := SheafOfModules.{max u (t + 1)}
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)
  letI : HasDerivedCategory.{max u (t + 1) + 1} RM :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{max u (t + 1) + 1} (ℕᵒᵖ ⥤ RM) :=
    HasDerivedCategory.standard _
  let rho := spSemilinearCompletedProjection l E T
  let Res := fun n : ℕ ↦ restrictScalars.{max u (t + 1)}
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map (rho n))
  let resAdd : ∀ n : ℕ, (Res n).Additive := fun _n ↦ inferInstance
  let resLimits : ∀ n : ℕ, PreservesFiniteLimits (Res n) := fun _n ↦ inferInstance
  let resColimits : ∀ n : ℕ, PreservesFiniteColimits (Res n) := fun _n ↦ inferInstance
  let e := spSemilinearEvaluationIso l E T D C P a
  ∃ (U : spCoefficientTowers l E T ⥤ (ℕᵒᵖ ⥤ RM))
    (hadd : U.Additive) (hlim : PreservesFiniteLimits U)
    (hcolim : PreservesFiniteColimits U),
    letI := hadd
    letI := hlim
    letI := hcolim
    ∃ hU : ∀ n : ℕ, U ⋙ (evaluation ℕᵒᵖ RM).obj (op n) = Ev n ⋙ Res n,
      (∀ (M : spCoefficientTowers l E T) {m n : ℕ} (h : m ≤ n)
        (V : T.ProEtᵒᵖ),
        HEq (fun x ↦ (((U.obj M).map (homOfLE h).op).val.app V) x)
          (fun x ↦ (((D.equivalence.functor.obj M).transition h).val.app V) x)) ∧
      let UP := (U.mapHomologicalComplex (.up ℤ)).obj P
      let b := (U.mapDerivedCategoryFactors.app P).symm ≪≫
        U.mapDerivedCategory.mapIso a
      let evR := fun n : ℕ ↦ (evaluation ℕᵒᵖ RM).obj (op n)
      let comparison := fun n : ℕ ↦
        letI := resAdd n
        letI := resLimits n
        letI := resColimits n
        letI := D.evaluationLimits n
        letI := D.evaluationColimits n
        letI : (Ev n).Additive := Functor.additive_of_preserves_binary_products _
        letI := comp_preservesFiniteLimits (Ev n) (Res n)
        letI := comp_preservesFiniteColimits (Ev n) (Res n)
        letI := comp_preservesFiniteLimits U (evR n)
        letI := comp_preservesFiniteColimits U (evR n)
        (Functor.mapDerivedCategoryCompIso U (evR n)).symm ≪≫
          Functor.mapDerivedCategoryNatIso (eqToIso (hU n)) ≪≫
            Functor.mapDerivedCategoryCompIso (Ev n) (Res n)
      (∀ n : ℕ,
        (evR n).mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app P) ≫
            (evR n).mapDerivedCategory.map b.hom ≫ (comparison n).hom.app C =
          (comparison n).hom.app (DerivedCategory.Q.obj P) ≫
            (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (Res n)
              (resAdd n) (resLimits n) (resColimits n)).map
                ((Ev n).mapDerivedCategoryFactors.hom.app P ≫ (e n).hom)) ∧
      (∀ (RF : DerivedCategory (ℕᵒᵖ ⥤ RM) ⥤ DerivedCategory RM)
        (eta : (lim : (ℕᵒᵖ ⥤ RM) ⥤ RM).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
        (_hRF : RF.IsRightDerivedFunctor eta
          (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ RM) (.up ℤ)))
        (V : DerivedCategory (ℕᵒᵖ ⥤ RM) ⥤ (ℕᵒᵖ ⥤ DerivedCategory RM))
        (_epsilon : DerivedCategory.Q ⋙ V ≅
          HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
            (Functor.whiskeringRight ℕᵒᵖ (CochainComplex RM ℤ)
              (DerivedCategory RM)).obj DerivedCategory.Q)
        (pi : ∀ n : ℕ, RF ⟶ V ⋙ (evaluation ℕᵒᵖ (DerivedCategory RM)).obj (op n)),
        ∀ n : ℕ,
          RF.map b.hom ≫ (pi n).app (U.mapDerivedCategory.obj C) =
            (pi n).app (DerivedCategory.Q.obj UP) ≫ (V.map b.hom).app (op n))


/-- All clauses of the simultaneous model statement, expressed using one strict
coefficient-tower complex and the original normalized reductions.

`e n` is the localization comparison followed by evaluation of `a`. The ordinary
reduction `beta h` is the scalar-adjunction transpose of the strict chain transition
`q h`, defined by `strictSystemTransition`; `ordinaryReduction_eq` fixes its local
formula b tensor x maps to b times q(x).
The functor U is required to be precisely scalar restriction on every level, arrow
and section, so it cannot be an arbitrary functor into completed-ring towers.
The lift b is the image of a under this exact functor, with its localization
comparison. Its evaluation formula specifies the same e_n. The final clause is
compatibility with each projection in any total-derived-limit Roos presentation.

Source: blueprint, sk-lem-sp-tower.proof.md, preliminary coherent realization;
Stacks 06YS, 0G7E, 06YY, 0940--0941
(blueprint: lem-sp-semilinear-kflat-tower-model). -/
def HasSpSemilinearKFlatTowerModel (D : SpCoefficientTowersAbelian l E T)
    (C : @DerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived) : Prop :=
  letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    surjectiveTower_hasSheafify.{t, u} T
  letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits
  letI := D.evaluationColimits
  letI : ∀ n : ℕ, (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    fun n ↦ Functor.additive_of_preserves_binary_products
      (spCoefficientEvaluation l E T D.equivalence n)
  letI : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
  let B := spCoefficientCommRings l E T
  let Ev := spCoefficientEvaluation l E T D.equivalence
  ∃ (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (a : DerivedCategory.Q.obj P ≅ C),
    let Qn := fun n : ℕ ↦ ((Ev n).mapHomologicalComplex (.up ℤ)).obj P
    let e := spSemilinearEvaluationIso l E T D C P a
    let beta := fun {m n : ℕ} (h : m ≤ n) ↦
      (NatTrans.mapHomologicalComplex (D.ordinaryReduction h) (.up ℤ)).app P
    let q := fun {m n : ℕ} (h : m ≤ n) ↦ spSemilinearChainTransition l E T D P h
    (∀ n : ℕ, systemLevelKFlat.{t + 1, t, max u (t + 1)} B n (Qn n)) ∧
    (∀ {m n : ℕ} (h : m ≤ n),
      DerivedCategory.Q.map (q h) ≫
          (systemRestriction B h).mapDerivedCategoryFactors.inv.app (Qn m) ≫
          (systemRestriction B h).mapDerivedCategory.map (e m).hom =
        (e n).hom ≫ ((systemDerivedTensorAdj D.scalar B h).homEquiv _ _)
          ((D.reduction h).app C)) ∧
    (∀ {m n : ℕ} (h : m ≤ n) (i : ℤ) (V : T.ProEtᵒᵖ)
      (c : (B.obj (op m)).obj.obj V) (x : ((Qn n).X i).val.obj V),
      ((beta h).f i).val.app V
          (systemModelTmul (D.scalar (B.map (homOfLE h).op)).model
            ((Qn n).X i) V c x) =
        (ModuleCat.smul (((Qn m).X i).val.obj V) c).hom
          (@id (((Qn m).X i).val.obj V) (((q h).f i).val.app V x))) ∧
    (∀ {m n : ℕ} (h : m ≤ n),
      IsIso ((D.scalar (B.map (homOfLE h).op)).model.ε.app (Qn n)) ∧
      (systemDerivedTensor D.scalar B h).map (e n).hom ≫ (D.reduction h).app C =
        (D.scalar (B.map (homOfLE h).op)).model.ε.app (Qn n) ≫
          DerivedCategory.Q.map (beta h) ≫ (e m).hom) ∧
    HasSpSemilinearCompletedLift l E T D C P a


/-- Every derived semilinear coefficient tower has compatible flat-term K-flat
representatives, a strict completed-ring derived lift with the specified evaluations
and limit projections, and the original reduction maps on its tensor representatives.
No boundedness, normalization or flatness of the quotient maps is assumed.

Source: blueprint main-20261015, sk-lem-sp-tower.proof.md, preliminary realization;
Bhatt--Scholze, Definition 3.5.3; Stacks 06YS, 0G7E, 06YY and 0940--0941
(blueprint: lem-sp-semilinear-kflat-tower-model).

Proof:
1. Give N times T_proet the vertical topology of lem-weil-pbc-diagram-site-topology.
A module presheaf is a sheaf exactly when each vertical slice is a sheaf: glue on
the covering slice at n, and use separatedness on that same cover after every
horizontal restriction. Conversely extend matching families by horizontal maps.
Thus the ring sheaf with values B_n has precisely the given semilinear towers as
its modules, by det-sp-coefficient-towers-abelian.
2. Evaluation is the inverse image of a geometric morphism. Its right adjoint
places F at j >= n and the terminal sheaf below n. Maps into it are determined
by the map at n. Evaluation preserves finite limits and takes the ring to B_n.
Its module pullback is evaluation by the tensor unitor.
3. Represent C by a complex M of towers. Apply lem-pc-kflat-resolution once on
the diagram site, obtaining a flat-term K-flat P and a quasi-isomorphism P -> M.
4. Apply lem-weil-pbc-ringed-topos-kflat-pullback to the evaluation morphisms.
The evaluated Q_n are flat-term K-flat. Evaluation is exact, so P -> M remains
a quasi-isomorphism at every level.
5. Compose the localized resolution with Q(M) isomorphic to C to obtain a.
Its evaluations give e_n. The strict horizontal squares give the localized
transition equations. All longer maps are composites, with identities at equal
levels, by the strict-system identity and composition laws.
6. Restrict scalars through the completed coefficient projections. The cone
identities make horizontal maps R-linear. This gives U, exactly as normalized
above on every section and morphism. Kernels and sheafified cokernels are
unchanged, so U is exact. Apply D(U) to a and use the localization comparison
to obtain b. Exact evaluation and its compositors give the displayed evaluation
formula. Apply the total derived inverse limit of
lem-weil-pbc-ringed-strict-tower-homotopy-limit to b. The product-triangle first
arrow followed by its nth projection is a natural transformation pi_n;
naturality at b gives the last equation for each evaluation projection.
7. Transpose each horizontal chain transition by the normalized ordinary scalar
adjunction of lem-pur-system-scalar-model. On pure tensors beta sends b tensor x
to b times q(x). Its normalized derived transpose and
lem-pur-derived-change-of-rings identify its localization under the invertible
K-flat counit. Apply naturality of the original canonical reduction to a to
obtain the displayed reduction square. Equal levels give the tensor unitor.
This also retains all composite transitions, including nonflat coefficient maps. -/
theorem sp_semilinear_kflat_tower_model (D : SpCoefficientTowersAbelian l E T)
    (C : @DerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived) :
    HasSpSemilinearKFlatTowerModel l E T D C := by
  sorry

end AlgebraicGeometry.ProEtale
