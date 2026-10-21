/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.CompletedPullbackReduction
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.Paper.FlatCommonQuotientReductionTower
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization

/-! # All-quotient coherence of derived tower pullback

Source: main-20261015, sk-prop-sf-cbc, completed extension-by-zero comparison proof,
finite-reduction compatibility (blueprint: lem-cbc-derived-finite-quotient-coherence).

The index n denotes the positive exponent n+1. The finite comparison, the strict
tower transition and the finite target transition are the published canonical maps.
The extra ordinary map below is their scalar-extension adjunct, with real data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- The ordinary finite target, before localization; this is the existing composite.
Source: CBC finite-reduction compatibility, Step 4
(blueprint: lem-cbc-derived-finite-quotient-coherence). -/
abbrev cbcFiniteOrdinaryTarget (n : ℕ) :=
  reductionChange Y (completedReductionProjection Y d n) ⋙
    completedReductionFiniteModules g d n

/-- The ordinary finite normalization is the adjunct of the actual quotient map.
Source: CBC finite-reduction compatibility, Step 9; Stacks 06YY
(blueprint: lem-cbc-derived-finite-quotient-coherence). -/
def cbcFiniteOrdinaryNormalization (a b : ℕ) (h : a ≤ b) :
    cbcFiniteOrdinaryTarget g d b ⋙ reductionChange X (reductionCoefficientMap X d b a h) ⟶
      cbcFiniteOrdinaryTarget g d a :=
  Functor.whiskerRight (completedReductionOrdinaryTransition g d a b h)
      (reductionChange X (reductionCoefficientMap X d b a h)) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (cbcFiniteOrdinaryTarget g d a)
      (pbcScalarAdjunction (reductionCoefficientMap X d b a h)).counit ≫
    (cbcFiniteOrdinaryTarget g d a).rightUnitor.hom

/-- The canonical finite evaluation commutes with every strict quotient transition.
Its finite target normalizations have the prescribed balanced tensor formula, descend
through the canonical computation maps, and satisfy the unit and quotient cocycle.
Source: main-20261015, sk-prop-sf-cbc, completed extension-by-zero comparison proof,
finite-reduction compatibility (blueprint: lem-cbc-derived-finite-quotient-coherence).

Proof:
1. Put R=constant A, B=the completed coefficient sheaf, and S_n=the finite sheaf.
The constant-completion theorem gives flat R→B and the normalized common quotients.
Choose a flat-term K-flat B-model P of K and one objectwise flat-term K-flat strict
R-tower resolution V_n→S_n, using diagram K-flat replacements, not unrelated levels.
2. Form H_n=Tot(P tensor_R V_n). Balancing identifies this with tensor over B of P
and B tensor_R V_n. Change of rings and total tensor make H a resolving B-tower.
3. Flat scalar restriction makes P K-flat over R. Thus 1 tensor v_n is a
quasi-isomorphism. Common-quotient balancing gives a strict quasi-isomorphism
r:H→(P tensor_B S_n)_n, representing the canonical reduction tower.
4. The ordinary finite comparison beta_n identifies the pullback of P tensor_B S_n
with finite inverse image D_n. On sections its scalar is pi_n(b')c_n(s).
Finite constant-map naturality makes beta commute with every quotient.
5. Pullback/tensor coherence identifies beta_n G(r_n) with 1 tensor g_R^*v_n on
Tot(G(P) tensor_R' g_R^*V_n). The inverse balancing inserts the scalar 1.
6. Ringed pullback preserves K-flatness and flat terms. Flat scalar restriction
makes G(P) K-flat over R'. Exact constant inverse image preserves the acyclic
cone of v_n; tensoring it with G(P) is acyclic. Hence these maps are quasi-isomorphisms
and form one morphism of strict towers. No quotient is assumed K-flat over B.
7. The universal tower counit and inverse of L(r) give chi:L R(K)→Q'G(H).
Compose with Q'(beta G(r)). Evaluation normalization identifies its components with
the prescribed constant-completion comparisons, independently of both resolutions.
8. Since this is a map of derived strict towers, its evaluations commute with every
transition, giving the first equality with the canonical restriction composition.
9. Finite change of rings and exact finite inverse image preserve K-flat models.
Successive quotient extension is ordinary balancing: (x tensor r) tensor s maps to
x tensor q(r)s, with inverse inserting 1. The formula below uses scalar-first tensors.
The universal scalar counits give precisely its derived representative equation.
At equal indices it is the scalar unitor. For c≥b≥a both reassociations send a pure
triple tensor to x tensor q_ca(r_c)q_ba(r_b)r_a, giving the quotient cocycle. -/
theorem derived_finite_quotient_coherence :
    (∀ (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
      (a b : ℕ) (h : a ≤ b),
      (completedReductionFiniteEvaluation g d b).hom.app K ≫
          (pbcDerivedRestrict (completedReductionProjection X d b)).map
            ((completedReductionTargetTransition g d a b h).app K) ≫
          (pbcDerivedRestrictComp (completedReductionProjection X d b)
            (reductionCoefficientMap X d b a h) (completedReductionProjection X d a)
            (completedReductionProjection_comp X d b a h)).hom.app
              ((completedReductionFiniteTarget g d a).obj K) =
        (pbcTowerTransition X (pbcAdicCompletion X d) b a h).app
            ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) ≫
          (completedReductionFiniteEvaluation g d a).hom.app K) ∧
    (∀ (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
      (a b : ℕ) (h : a ≤ b), IsIso (completedReductionTargetNormalization g d K a b h)) ∧
    (∀ (a b : ℕ) (h : a ≤ b)
      (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt) (U : X.ProEt)
      (f : U ⟶ (proEtaleBaseChange g).obj V)
      (s : (reductionCoefficient X d a).obj.obj (op U))
      (r : (reductionCoefficient X d b).obj.obj (op U))
      (z : (reductionCoefficient Y d b).obj.obj (op V)) (x : M.val.obj (op V)),
      ((cbcFiniteOrdinaryNormalization g d a b h).app M).val.app (op U)
          (pbcTensorSection (reductionCoefficientMap X d b a h)
            ((cbcFiniteOrdinaryTarget g d b).obj M) (op U) s
            (completedReductionFiniteGenerator g d b M V U f r z x)) =
        completedReductionFiniteGenerator g d a M V U f
          (((reductionCoefficientMap X d b a h).hom.app (op U) r) * s)
          ((reductionCoefficientMap Y d b a h).hom.app (op V) z) x) ∧
    (∀ (a b : ℕ) (h : a ≤ b)
      (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P →
      (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map
          (completedReductionFiniteModelMap g d b P) ≫
        pbcComplexCounit (reductionCoefficientMap X d b a h)
          (((cbcFiniteOrdinaryTarget g d b).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (cbcFiniteOrdinaryNormalization g d a b h) (.up ℤ)).app P) =
      completedReductionTargetNormalization g d (DerivedCategory.Q.obj P) a b h ≫
        completedReductionFiniteModelMap g d a P) ∧
    (∀ (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
      (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
      (reductionDerivedChange X (reductionCoefficientMap X d b a hab)).map
          (completedReductionTargetNormalization g d K b c hbc) ≫
        completedReductionTargetNormalization g d K a b hab =
      (completedReductionQuotientAssoc d X a b c hab hbc
          ((completedReductionFiniteTarget g d c).obj K)).hom ≫
        completedReductionTargetNormalization g d K a c (hab.trans hbc)) ∧
    ∀ (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) (a : ℕ),
      completedReductionTargetNormalization g d K a a (le_refl a) =
        completedReductionUnit d X a ((completedReductionFiniteTarget g d a).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
