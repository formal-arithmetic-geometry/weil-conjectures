/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.Paper.IntegralQuotientDirectImageComparison
public import Sheaf.Paper.InternalScalarTensorComparison
public import Sheaf.Paper.ModuleObjectProjectionMap
import Sheaf.Paper.SectionDerivedTensorNormalization
import Sheaf.Paper.SectionDerivedPushpullNormalization
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality

/-! # Reduction of the actual integral projection morphism

Source: blueprint main-20261015, integral proper-base-change proof, paragraph (3);
Stacks Project, Tags 0B56, 07A4, 07A6 and 0D6D
(blueprint: lem-sfb-integral-quotient-projection-comparison).

The scalar tensor comparison is specified by its computation counits and the signed
ordinary balancing map. Unlike the exact-scalar interface, this applies to reduction
modulo a uniformizer. Positive levels are indexed by n + 1, as in the dependency.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.all false
set_option linter.unusedVariables false
set_option maxHeartbeats 200000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.ProEtale.QuotientChange
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The signed total of the canonical ordinary scalar tensor balancing map. Its
scalar-unit normalization sends (u tensor v) tensor s to
(u tensor 1) tensor (v tensor s), equivalently moving s to the first factor.
Source: Stacks 07A4, change-of-rings specialization
(blueprint: lem-sfb-integral-quotient-projection-comparison). -/
def scalarTensorTotal (n : ℕ) (T : Scheme.{u})
    (P Q : CochainComplex (Modules (integral l E) T) ℤ) :
    ((extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ⟶
      ((extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj Q :=
  letI := CondensedRing.internalScalarMonoidal (reduction l E n) T
  ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (extension (reduction l E n) T)).app P).app Q

/-- The type of the scalar tensor balancing isomorphism, natural in both inputs.
Source: Stacks 07A4, identity-topos scalar extension
(blueprint: lem-sfb-integral-quotient-projection-comparison). -/
abbrev ScalarTensorIso (n : ℕ) (T : Scheme.{u}) :=
  (Functor.postcompose₂.obj (D (reduction l E n) T)).obj
      (CondensedRing.derivedTensor (integral l E) T) ≅
    (((Functor.whiskeringLeft₂ _).obj (D (reduction l E n) T)).obj
      (D (reduction l E n) T)).obj (CondensedRing.derivedTensor (finite l E n) T)

/-- Universal computation-counit normalization of the scalar tensor comparison.
On flat-term K-flat representatives all computation maps are invertible, and this
is exactly the specified pure-tensor balancing formula. It also fixes the comparison
on every derived object by the K-flat localization property.
Source: Stacks 07A4 and 0D6D
(blueprint: lem-sfb-integral-quotient-projection-comparison). -/
def ScalarTensorNormalized (n : ℕ) (T : Scheme.{u})
    (b : ScalarTensorIso l E n T) : Prop :=
  ∀ P Q : CochainComplex (Modules (integral l E) T) ℤ,
    (b.hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
        (compute (reduction l E n) T P ⊗ₘ compute (reduction l E n) T Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          (((extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj P)
          (((extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj Q) =
      (D (reduction l E n) T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        compute (reduction l E n) T (P ⊗ Q) ≫
        DerivedCategory.Q.map (scalarTensorTotal l E n T P Q)

/-- The canonical scalar tensor isomorphism exists and is uniquely determined by
its balancing normalization, without flatness of the quotient ring over the integers.
Source: Stacks 07A4 and the coefficient square in blueprint paragraph (3)
(blueprint: lem-sfb-integral-quotient-projection-comparison).

Proof: use the internal/section exact tensor equivalence, which preserves flat and
K-flat complexes and the local pure tensors. Apply the canonical ringed derived
pullback tensor comparison to the identity topos and the actual quotient ring map.
Transport it back. On flat-term K-flat pairs its comparison is the signed total of
scalarTensorTotal, and its universal computation counits give the displayed equation
on all complexes. K-flat localization in both inputs gives uniqueness. The inverse
multiplies the two quotient scalar factors; this uses balancing, not flatness of the
quotient. The pure-tensor formula agrees with the one in the statement because a
quotient scalar may move between the two factors of the tensor over S. -/
theorem scalarTensorIso_existsUnique (n : ℕ) (T : Scheme.{u}) :
    ∃! b : ScalarTensorIso l E n T, ScalarTensorNormalized l E n T b := by
  sorry

/-- The uniquely normalized scalar tensor balancing isomorphism. The existence
statement determines the whole natural isomorphism, rather than an arbitrary map.
Source: Stacks 07A4, blueprint paragraph (3)
(blueprint: lem-sfb-integral-quotient-projection-comparison). -/
@[irreducible] def scalarTensorIso (n : ℕ) (T : Scheme.{u}) :
    ScalarTensorIso l E n T :=
  (scalarTensorIso_existsUnique l E n T).exists.choose

/-- The existing pullback tensor comparison with its named pullback functor.
Source: Stacks 07A4 (blueprint: lem-sfb-integral-quotient-projection-comparison). -/
@[irreducible] def actualTensorPull
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.postcompose₂.obj (L Λ f)).obj (CondensedRing.derivedTensor Λ Y) ⟶
      (((Functor.whiskeringLeft₂ _).obj (L Λ f)).obj (L Λ f)).obj
        (CondensedRing.derivedTensor Λ X) := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarTensor Λ f

/-- The actual projection bifunctor transformation, using the existing adjunction
and its actual tensor comparison. This is the recorded moduleObjectProjectionMap
before evaluating its two components, with only its functor names made explicit.
Source: Stacks 0B56 (blueprint: lem-sfb-integral-quotient-projection-comparison). -/
@[irreducible] def actualProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    F Λ f ⋙ CondensedRing.derivedTensor Λ Y ⟶
      (Functor.postcompose₂.obj (F Λ f)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 (DerivedCategory (Modules Λ X)))).obj
          (L Λ f)).obj (CondensedRing.derivedTensor Λ X)) :=
  (adj Λ f).rightAdjointProjectionMap (actualTensorPull Λ f)

/-- The displayed projection comparison equation, with the coefficient parameters
shared explicitly. This is an equality of actual arrows in the quotient module
category; it neither forgets the scalar action nor asserts only cohomological equality.
Source: blueprint integral proper-base-change proof (3), Stacks 0B56 and 07A6
(blueprint: lem-sfb-integral-quotient-projection-comparison). -/
@[irreducible] def ProjectionComparisonEquation
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : D a Y ⋙ L S f ≅ L R f ⋙ D a X)
    (bX : (Functor.postcompose₂.obj (D a X)).obj (CondensedRing.derivedTensor R X) ≅
      (((Functor.whiskeringLeft₂ _).obj (D a X)).obj (D a X)).obj
        (CondensedRing.derivedTensor S X))
    (bY : (Functor.postcompose₂.obj (D a Y)).obj (CondensedRing.derivedTensor R Y) ≅
      (((Functor.whiskeringLeft₂ _).obj (D a Y)).obj (D a Y)).obj
        (CondensedRing.derivedTensor S Y))
    (K : DerivedCategory (Modules R X)) (M : DerivedCategory (Modules R Y)) : Prop :=
  (bY.hom.app ((F R f).obj K)).app M ≫
      ((CondensedRing.derivedTensor S Y).map ((rho a f c).app K)).app ((D a Y).obj M) ≫
      ((actualProjection S f).app ((D a X).obj K)).app ((D a Y).obj M) =
    (D a Y).map (((actualProjection R f).app K).app M) ≫
      (rho a f c).app (((CondensedRing.derivedTensor R X).obj K).obj ((L R f).obj M)) ≫
      (F S f).map
        ((bX.hom.app K).app ((L R f).obj M) ≫
          ((CondensedRing.derivedTensor S X).obj ((D a X).obj K)).map (c.inv.app M))

/-- Reduction of the actual integral projection morphism is the actual quotient
projection morphism under the specified scalar tensor, pullback and direct-image
comparisons. The pullback comparison is fixed by exactly the normalization in the
direct-image dependency; that dependency supplies its existence. Both sides are
natural in K and M and are arrows in the quotient-coefficient derived category.

Source: blueprint main-20261015 integral proper-base-change proof, paragraph (3);
Stacks 0B56, 07A4, 07A6, 0D6D
(blueprint: lem-sfb-integral-quotient-projection-comparison).

Proof:
1. Use internal/section tensor comparison and section-derived pushpull and tensor
normalization to carry the specified tensors, adjunctions and counits to ringed modules.
2. The geometric coefficient maps are natural in the condensed ring. Consequently
both structural ring maps in the quotient square agree. Ringed derived monoidal
comparison identifies lambda with the composition comparison for this square.
3. Its monoidality says b_X D_X(t_R) lambda =
(lambda tensor lambda) t_S L_S(b_Y); the normalized scalar maps on both sides agree
on pure tensors. No interchange of homogeneous factors occurs.
4. Put C=F_R K, W=C tensor M, H=K tensor L_R M, and
q=b_X followed by identity tensor lambda_M inverse. The defining adjunction mate
rho satisfies epsilon_S L_S(rho_J)=D_X(epsilon_R,J) lambda_(F_R J).
5. Transpose the left side. Expand the actual quotient projection as the adjunct
of t_S followed by counit tensor identity. Naturality of t_S and the mate identity
rewrite this as (D_X(epsilon_R,K) tensor identity) (lambda_C tensor identity)
t_S L_S(b_Y).
6. Substitute step 3 and cancel lambda_M. Naturality of b_X gives exactly
q D_X((epsilon_R,K tensor identity) t_R) lambda_W.
7. Transpose the right side. Counit naturality, the mate identity at H and lambda
naturality give q D_X(epsilon_R,H L_R(pi_R)) lambda_W. The defining adjunct of
the actual integral projection identifies this with the expression in step 6.
8. Injectivity of the adjunction Hom bijection proves the displayed equality.
All constructions are natural in both inputs. No inverse of a projection morphism,
boundedness, properness, completeness or constructibility is used. -/
theorem integral_quotient_projection_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (c : D (reduction l E n) Y ⋙ L (finite l E n) f ≅
      L (integral l E) f ⋙ D (reduction l E n) X)
    (_hc : PullNormalized (reduction l E n) f c)
    (K : DerivedCategory (Modules (integral l E) X))
    (M : DerivedCategory (Modules (integral l E) Y)) :
    ProjectionComparisonEquation (reduction l E n) f c
      (scalarTensorIso l E n X) (scalarTensorIso l E n Y) K M := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralQuotient
