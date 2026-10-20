/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Sheaf.Paper.BoundaryExceptionalComparisonData
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
import Sheaf.Paper.ProjectionCompactification
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons

/-!
# The boundary comparison of exceptional counits and projection transformations

Source: Stacks Project, Tags 0B56, 0E48, 0B65 and 0DV0; blueprint boundary-duality
proof, ordinary-to-pro-etale realization
(blueprint: lem-weil-boundary-proetale-projection-comparison).

All maps below use the actual comparison adjunction, its pullback square, and the ordinary
counit-defined projection transformations. The exceptional Hom transport is specified before
its bijectivity is asserted. Its counit is characterized by its image in that Hom transport.

## Main definitions and statement

- `homTransport`, `CounitComparison`: the specified exceptional Hom chain and counit formula.
- `ProjectionComparison`: the canonical projection square and its conditional inverse square.
- `boundary_proetale_projection_comparison`: the two comparison assertions.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.BoundaryComparison

section ProjectionData

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [Etale.UpperStarPreservesFlat C] [ProEtale.UpperStarPreservesFlat C]
  [∀ W : Scheme.{u}, (comparisonUpperStar C W).PreservesFlat]

/-- The existing etale tensor target Q = B tensor Li_e^* M.
Source: Stacks 0B56; (blueprint: lem-weil-boundary-proetale-projection-comparison). -/
abbrev tensorObject {Z T : Scheme.{u}} (i : Z ⟶ T)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (M : DerivedCategory (Sheaf T.smallEtaleTopology C)) :=
  ((Etale.derivedTensor C Z).obj B).obj
    ((Etale.upperStar C i).leftDerivedFunctor.obj M)

/-- The actual monoidal comparison of the exact derived comparison pullback.
Source: Stacks 07A4 and 0E48;
(blueprint: lem-weil-boundary-proetale-projection-comparison). -/
abbrev tensorComparison (T : Scheme.{u})
    (K L : DerivedCategory (Sheaf T.smallEtaleTopology C)) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    C K).app L

/-- The specified isomorphism h : C_Z Q -> C_Z B tensor Li_p^* C_T M.
Source: Stacks 0E48, tensor and pullback-square arrows;
(blueprint: lem-weil-boundary-proetale-projection-comparison). -/
def tensorTargetIso {Z T : Scheme.{u}} (i : Z ⟶ T)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (M : DerivedCategory (Sheaf T.smallEtaleTopology C)) :
    (comparison C Z).obj (tensorObject C i B M) ≅
      ((ProEtale.derivedTensor C Z).obj
        ((comparison C Z).obj B)).obj
          ((upperStar C i).leftDerivedFunctor.obj
            ((comparison C T).obj M)) :=
  tensorComparison C Z B
      ((Etale.upperStar C i).leftDerivedFunctor.obj M) ≪≫
    ((ProEtale.derivedTensor C Z).obj
      ((comparison C Z).obj B)).mapIso ((pullbackSquare C i).symm.app M)

/-- The etale projection component is the named ordinary-counit-defined transformation.
Source: Stacks 0B56; (blueprint: lem-weil-boundary-proetale-projection-comparison). -/
abbrev etaleProjection {Z T : Scheme.{u}} (i : Z ⟶ T)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (M : DerivedCategory (Sheaf T.smallEtaleTopology C)) :=
  ((Etale.rightDerivedLowerStarProjectionMap
    C i).app B).app M

/-- The pro-etale projection component uses the same counit-defined construction.
Source: Stacks 0B56; (blueprint: lem-weil-boundary-proetale-projection-comparison). -/
abbrev proetaleProjection {Z T : Scheme.{u}} (i : Z ⟶ T)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (M : DerivedCategory (Sheaf T.smallEtaleTopology C)) :=
  ((ProEtale.rightDerivedLowerStarProjectionMap
    C i).app
      ((comparison C Z).obj B)).app ((comparison C T).obj M)

/-- The source identification t_C followed by b_B tensor the identity. The supplied
isomorphism is required below to have hom exactly the canonical b_B.
Source: Stacks 0E48; (blueprint: lem-weil-boundary-proetale-projection-comparison). -/
def projectionSourceIso {Z T : Scheme.{u}} (i : Z ⟶ T)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (M : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (b : (comparison C T).obj ((etaleImage C i).obj B) ≅
      (proetaleImage C i).obj ((comparison C Z).obj B)) :
    (comparison C T).obj
        (((Etale.derivedTensor C T).obj
          ((etaleImage C i).obj B)).obj M) ≅
      ((ProEtale.derivedTensor C T).obj
        ((proetaleImage C i).obj ((comparison C Z).obj B))).obj ((comparison C T).obj M) :=
  tensorComparison C T ((etaleImage C i).obj B) M ≪≫
    ((ProEtale.derivedTensor C T).mapIso b).app
      ((comparison C T).obj M)

/-- The target identification b_Q followed by Rp_* h.
Source: Stacks 0E48; (blueprint: lem-weil-boundary-proetale-projection-comparison). -/
def projectionTargetIso {Z T : Scheme.{u}} (i : Z ⟶ T)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (M : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (b : (comparison C T).obj ((etaleImage C i).obj (tensorObject C i B M)) ≅
      (proetaleImage C i).obj ((comparison C Z).obj (tensorObject C i B M))) :
    (comparison C T).obj ((etaleImage C i).obj (tensorObject C i B M)) ≅
      (proetaleImage C i).obj
        (((ProEtale.derivedTensor C Z).obj
          ((comparison C Z).obj B)).obj
            ((upperStar C i).leftDerivedFunctor.obj
              ((comparison C T).obj M))) :=
  b ≪≫ (proetaleImage C i).mapIso (tensorTargetIso C i B M)

/-- The precise eta projection identity, with both monoidal identifications displayed.
The final clause inverts that very identity whenever the etale projection is invertible;
it fixes the pro-etale inverse by its hom, rather than introducing an arbitrary comparison.
Source: Stacks 0E48; blueprint final displayed equality and its inverse
(blueprint: lem-weil-boundary-proetale-projection-comparison). -/
def ProjectionComparison {Z T : Scheme.{u}} (i : Z ⟶ T)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (M : DerivedCategory (Sheaf T.smallEtaleTopology C)) : Prop :=
  DerivedCategory.TStructure.t.plus (tensorObject C i B M) ∧
  ∃ bB : (comparison C T).obj ((etaleImage C i).obj B) ≅
      (proetaleImage C i).obj ((comparison C Z).obj B),
    bB.hom = (directImageMate C i).app B ∧
    ∃ bQ : (comparison C T).obj ((etaleImage C i).obj (tensorObject C i B M)) ≅
        (proetaleImage C i).obj ((comparison C Z).obj (tensorObject C i B M)),
      bQ.hom = (directImageMate C i).app (tensorObject C i B M) ∧
      proetaleProjection C i B M ≫ (projectionTargetIso C i B M bQ).inv =
        (projectionSourceIso C i B M bB).inv ≫
          (comparison C T).map (etaleProjection C i B M) ∧
      ∀ e :
          ((Etale.derivedTensor C T).obj
            ((etaleImage C i).obj B)).obj M ≅
              (etaleImage C i).obj (tensorObject C i B M),
        e.hom = etaleProjection C i B M →
        ∃ ep :
            ((ProEtale.derivedTensor C T).obj
              ((proetaleImage C i).obj ((comparison C Z).obj B))).obj ((comparison C T).obj M) ≅
            (proetaleImage C i).obj
              (((ProEtale.derivedTensor C Z).obj
                ((comparison C Z).obj B)).obj
                  ((upperStar C i).leftDerivedFunctor.obj
                    ((comparison C T).obj M))),
          ep.hom = proetaleProjection C i B M ∧
          (projectionTargetIso C i B M bQ).hom ≫ ep.inv =
            (comparison C T).map e.inv ≫ (projectionSourceIso C i B M bB).hom

end ProjectionData

/-- Proper compact support, exceptional counits, and projection transformations agree
under the finite-coefficient etale/pro-etale comparison.
Source: blueprint boundary-duality discharge, second proof paragraph and its explicit
ordinary-to-pro-etale comparison; Stacks 0B56, 0E48, 0B65, 0DV0
(blueprint: lem-weil-boundary-proetale-projection-comparison).

Proof:
1. A closed immersion is proper and qcqs. Normalize its compactification to (id_Z,i).
Finite type over the field makes both schemes Noetherian. The ordinary exceptional
adjunction exists by thm-amb-etale-exceptional-adjoint. The specified canonical direct-image
mate is invertible by lem-weil-pbc-comparison-direct-image-canonical-mate, with its counit
normalization; the exact/left-derived identifications used in pullbackSquare preserve it.
2. Compose precomposition with b_H, comparison adjunction, ordinary exceptional adjunction,
and the fully faithful C_Z. The site-comparison unit is invertible on D+ by
thm-weil-pbc-site-comparison, and the finite exceptional value is bounded below by
 def-weil-exceptional-inverse-image. Thus the displayed homTransport is a bijection.
3. For N as stated, the comparison unit identifies C_Z G_e N with G_p C_T N.
Under the Hom chain, b_(G_e N)^(-1) followed by C_T of the etale exceptional counit
maps to this identification, by the two adjunction triangle identities. Bijectivity
characterizes this arrow as the transported counit, giving CounitComparison.
4. The pullback comparison square is monoidal: all four constant-coefficient inverse
images preserve the same scalar actions, and the canonical K-flat tensor comparisons
are compatible with composition (lem-sfb-ringed-derived-monoidal-comparisons).
5. A bounded flat model of M exists by lem-sf-flat-model. Pullback preserves K-flat
flat-term models by lem-weil-pbc-ringed-topoi-derived-tensor-pullback. Tensoring a bounded
representative of B with this finite model shows Q is bounded below, so b_Q is invertible.
6. Transpose the two projection routes under ordinary pro-etale pullback/direct image.
The counit-mate normalization changes the left route to C_Z of the etale projection
transpose, followed by h. This uses lem-weil-pbc-adjunct-counit-identity.
7. For the right route, use naturality of the tensor comparison and the same counit-mate
normalization. Monoidality from step 4 identifies this transpose with the one in step 6.
The named maps here are precisely def-kun-projection-formula-map and its pro-etale analogue,
not unspecified isomorphisms (lem-weil-pbc-ringed-projection-mate-exact).
8. Injectivity of transposition gives the projection square. Compose with b_Q^(-1),
h^(-1), t_C^(-1), and b_B^(-1) to obtain the displayed eta identity. Inverting this
same equality gives the final conditional inverse identity in ProjectionComparison.
-/
theorem boundary_proetale_projection_comparison
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {Z T : Scheme.{u}} (i : Z ⟶ T)
    [Z.Over (Spec (.of D.k))] [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))]
    [i.IsOver (Spec (.of D.k))] [IsClosedImmersion i] :
    (∀ H : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology
      (coefficients (Padic.coefficientExtensionRing l E (n + 1)))),
      IsIso ((directImageMate
        (coefficients (Padic.coefficientExtensionRing l E (n + 1))) i).app H.obj)) ∧
    (∀ (H : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology
        (coefficients (Padic.coefficientExtensionRing l E (n + 1)))))
      (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T)
        (coefficients (Padic.coefficientExtensionRing l E (n + 1))))),
      Function.Bijective (homTransport (Padic.coefficientExtensionRing l E (n + 1)) i H L)) ∧
    (∀ N : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
        (coefficients (Padic.coefficientExtensionRing l E (n + 1)))),
      Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) T N.obj →
      Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) Z
        ((etaleExceptional (Padic.coefficientExtensionRing l E (n + 1)) i).obj N.obj) →
      @CounitComparison _ _ _ _ _ i _
        (QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of D.k))) N) ∧
    (∀ (B : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology
        (coefficients (Padic.coefficientExtensionRing l E (n + 1)))))
      (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
        (coefficients (Padic.coefficientExtensionRing l E (n + 1))))),
      Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) Z B.obj →
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) T M.obj →
      ProjectionComparison
        (coefficients (Padic.coefficientExtensionRing l E (n + 1))) i B.obj M.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.BoundaryComparison
