/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfConstructibleHeart
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
public import Sheaf.Paper.GlobalGeometricFrobenius
public import Sheaf.Paper.ProperSectionsSemilinearGerms
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import Sheaf.CategoryTheory.NaturalTransportPowers
import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import Sheaf.Paper.ProperCoincidenceFrobenius
public import Sheaf.SixFunctors.FrobeniusCohomologyTransportIso
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.BasicOperationsCoefficientReduction

/-! # Iterated global Weil operators and moving-point germs

Source: Deligne, Weil II (1.1.3), (1.1.7), (1.1.10)--(1.1.14), pp. 150--153
(blueprint: lem-a1-proper-weil-iterate-germ-formula).
All positive-power indices n denote exponent n+1. The existing counit germ,
compact transport, pullback compositors and point transports are retained.
Algebraically closed coefficients are expressed in finite-stage coordinates,
with canonical comparisons to the actual global operator on every Weil pair.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures
namespace ProperWeilIterateGerms

variable (D : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom]
  (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The specified compact global operator, with an arbitrary finite coefficient field.
Source: Deligne (1.1.14) (blueprint: lem-a1-proper-weil-iterate-germ-formula). -/
def global (K : sfWeilComplex D l Fact.out Y₀ E) :
    End ((ProperSemilinearGerms.rationalSections D Y₀ l E).obj K.carrier) :=
  (frobeniusCohomologyTransportRational D l Fact.out E Y₀
      (Compactification.ofIsProper Y₀.hom) K.carrier).2 ≫
    (ProperSemilinearGerms.rationalSections D Y₀ l E).map K.str.hom

/-- The right side of F^(n+1)=C(theta^[n+1]) tau^[n+1], in composition order.
Source: Deligne (1.1.14) (blueprint: lem-a1-proper-weil-iterate-germ-formula). -/
def contractedGlobal (K : sfWeilComplex D l Fact.out Y₀ E) (n : ℕ) :=
  ProperSemilinearGerms.rationalTransport D Y₀ l E K.carrier n ≫
    (ProperSemilinearGerms.rationalSections D Y₀ l E).map
      (localWeilIterate l E D Fact.out Y₀ K n).hom

/-- B_(n+1,z) is iterated point transport, Fib(b), then Fib(z*theta^[n+1]).
It goes from the moving-point fibre to the original fibre, without a return assumption.
Source: Deligne (1.1.7), (1.1.10)--(1.1.14)
(blueprint: lem-a1-proper-weil-iterate-germ-formula). -/
def block (K : sfWeilComplex D l Fact.out Y₀ E)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ) :=
  letI := sfWeilPrimeInvertible D l Fact.out Y₀
  letI := frobeniusPointPrimeInvertible D l Fact.out
  localPointTransportIterate l E D Fact.out
      ((rationalDerivedPullback l E (ProperSemilinearGerms.movingPoint D Y₀ z n)).obj
        K.carrier) n ≫
    (pointRationalFibre D l Fact.out E).map
      (ProperSemilinearGerms.rationalSquare D Y₀ l E z hz n K.carrier).hom ≫
    (ProperSemilinearGerms.rationalFibre D Y₀ l E z).map
      (localWeilIterate l E D Fact.out Y₀ K n).hom

/-- The specified finite-field global/germ formulas, invertibility and return clauses.
Naturality includes every morphism of Weil complexes, with no invertibility condition.
Source: Deligne, Weil II (1.1.3), (1.1.7), (1.1.10)--(1.1.14), pp. 150--153
(blueprint: lem-a1-proper-weil-iterate-germ-formula).
Proof:
1. Apply lem-trf-global-frobenius-iterate-formula to the natural compact transport.
The ordered Weil composite contracts to localWeilIterate by the associative
scalar-localized compositors of lem-pod-integral-pullback-composition; its inverse
compositor contracts the repeated transport to rationalTransport.
2. The whole-system counit and the proper compact/ordinary comparison are natural
on every rational constructible arrow (fix-prop-adjunctions and
lem-pod-proper-coincidence-frobenius). Thus the canonical germ is natural also
on theta^[n+1].
3. Substitute properSectionsSemilinearGermsRational at the underlying carrier and
postcompose its two sides with the stalk map of theta^[n+1]. Step 1 gives the germ
identity, with no return assumed.
4. The Weil map and b are isomorphisms. The point transport is invertible by
lem-weil-frobenius-cohomology-transport-iso, so its iterates and their composite B
are invertible.
5. Induct on the Weil-morphism equation to obtain equivariance of the ordered
Weil iterates, then contract by naturality of the compositors. Naturality of each
point transport (lem-weil-frobenius-point-transport-natural) gives naturality of B,
including for noninvertible arrows.
6. Upon a return, transport the moving source along the return equality. The three
factors are exactly localFrobeniusOperator; at the residue degree and closed-point
lift they are exactly localClosedFrobenius. These are derived-arrow equalities.
7. Rationalization preserves each factor and equation, by lem-fix-operation-reduction;
no invariant integral lattice, weights or semisimplicity enters the argument. -/
theorem rational (K : sfWeilComplex D l Fact.out Y₀ E)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ) :
    global D Y₀ l E K ^ (n + 1) = contractedGlobal D Y₀ l E K n ∧
    (global D Y₀ l E K ^ (n + 1)) ≫
        ProperSemilinearGerms.rationalGerm D Y₀ l E z hz K.carrier =
      ProperSemilinearGerms.rationalGerm D Y₀ l E
          (ProperSemilinearGerms.movingPoint D Y₀ z n)
          (ProperSemilinearGerms.movingPoint_properties D Y₀ z hz n).1 K.carrier ≫
        block D Y₀ l E K z hz n ∧
    IsIso (block D Y₀ l E K z hz n) ∧
    (∀ (L : sfWeilComplex D l Fact.out Y₀ E) (f : K ⟶ L),
      block D Y₀ l E K z hz n ≫
          (ProperSemilinearGerms.rationalFibre D Y₀ l E z).map f.hom.f =
        (ProperSemilinearGerms.rationalFibre D Y₀ l E
          (ProperSemilinearGerms.movingPoint D Y₀ z n)).map f.hom.f ≫
            block D Y₀ l E L z hz n) ∧
    (∀ (hfix : ProperSemilinearGerms.movingPoint D Y₀ z n = z),
      z ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
        localPositivePower (frobeniusPointIso D).hom n ≫ z ∧
      ∀ (hreturn : z ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
        localPositivePower (frobeniusPointIso D).hom n ≫ z),
      eqToHom (congrArg (fun w ↦
        (ProperSemilinearGerms.rationalFibre D Y₀ l E w).obj K.carrier) hfix).symm ≫
          block D Y₀ l E K z hz n =
        localFrobeniusOperator l E D Fact.out Y₀ K z n hreturn) ∧
    (∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
      (ι : Y₀.left.residueField y.val →+* D.k)
      (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
      (_heq : z = localClosedPoint D Y₀ y ι hι)
      (hfix : ProperSemilinearGerms.movingPoint D Y₀ z
        (localClosedPointDegree D Y₀ y - 1) = z),
      HEq (eqToHom (congrArg (fun w ↦
        (ProperSemilinearGerms.rationalFibre D Y₀ l E w).obj K.carrier) hfix).symm ≫
          block D Y₀ l E K z hz (localClosedPointDegree D Y₀ y - 1))
        (localClosedFrobenius l E D Fact.out Y₀ K y ι hι)) := by
  sorry

/-- Agreement with the recorded finite-subfield global geometric Frobenius.
Source: Deligne (1.1.14) (blueprint: lem-a1-proper-weil-iterate-germ-formula).
Proof: expand globalGeometricFrobenius and global; both use the same transport
and the same identity-compactification cohomology functor. -/
theorem global_eq (c : D.CoefficientDatum)
    (F : Padic.FiniteCoefficientFields c.l c.Qbar)
    (K : sfWeilComplex D c.l c.different Y₀ F.val) :
    @global D Y₀ _ c.l _ ⟨c.different⟩ F.val _ _ _ K =
      (globalGeometricFrobenius D c F Y₀ (Compactification.ofIsProper Y₀.hom) K).2 := by
  sorry

section CommonStage
variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Canonical cohomology comparison from a finite Weil model to a common-stage pair.
It is the literal stage object equality followed by C of the underlying model isomorphism.
Source: Deligne (1.1.3), (1.1.14)
(blueprint: lem-a1-proper-weil-iterate-germ-formula). -/
def modelSectionsComparison (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (A : sfWeilComplex D l Fact.out Y₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
    (K : sfCommonStageWeilComplex D l Fact.out Y₀ Ω)
    (e : sfWeilStageObject D l Fact.out Y₀ Ω F A ≅ K) :=
  (eqToIso (frobeniusCohomologyQbarSourceEq D l Fact.out Y₀ Ω
      (Compactification.ofIsProper Y₀.hom) true
      (sfWeilStageObject D l Fact.out Y₀ Ω F A).carrier)).symm ≪≫
    (frobeniusCohomologyQbarFunctor D l Fact.out Y₀ Ω
      (Compactification.ofIsProper Y₀.hom) true).mapIso
        ((sfCommonStageWeilForget D l Fact.out Y₀ Ω).mapIso e)

/-- Derived equations at a finite field, extended by the recorded faithful realization.
This retains the three specified factors of B, every noninvertible Weil arrow, and
both return clauses, rather than replacing them by an arbitrary isomorphism.
Source: Deligne (1.1.3), (1.1.7), (1.1.10)--(1.1.14)
(blueprint: lem-a1-proper-weil-iterate-germ-formula). -/
def realizedFormulas (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (A : sfWeilComplex D l Fact.out Y₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ) : Prop :=
  End.of ((ProperSemilinearGerms.stageRealization l Ω F).map
    (global D Y₀ l _ A)) ^ (n + 1) =
    (ProperSemilinearGerms.stageRealization l Ω F).map
      (contractedGlobal D Y₀ l _ A n) ∧
  (End.of ((ProperSemilinearGerms.stageRealization l Ω F).map
    (global D Y₀ l _ A)) ^ (n + 1)) ≫
      (ProperSemilinearGerms.stageRealization l Ω F).map
        (ProperSemilinearGerms.rationalGerm D Y₀ l _ z hz A.carrier) =
    (ProperSemilinearGerms.stageRealization l Ω F).map
      (ProperSemilinearGerms.rationalGerm D Y₀ l _
        (ProperSemilinearGerms.movingPoint D Y₀ z n)
        (ProperSemilinearGerms.movingPoint_properties D Y₀ z hz n).1 A.carrier) ≫
      (ProperSemilinearGerms.stageRealization l Ω F).map (block D Y₀ l _ A z hz n) ∧
  IsIso ((ProperSemilinearGerms.stageRealization l Ω F).map
    (block D Y₀ l _ A z hz n)) ∧
  (∀ (B : sfWeilComplex D l Fact.out Y₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)) (f : A ⟶ B),
    (ProperSemilinearGerms.stageRealization l Ω F).map (block D Y₀ l _ A z hz n) ≫
        (ProperSemilinearGerms.stageRealization l Ω F).map
          ((ProperSemilinearGerms.rationalFibre D Y₀ l _ z).map f.hom.f) =
      (ProperSemilinearGerms.stageRealization l Ω F).map
        ((ProperSemilinearGerms.rationalFibre D Y₀ l _
          (ProperSemilinearGerms.movingPoint D Y₀ z n)).map f.hom.f) ≫
        (ProperSemilinearGerms.stageRealization l Ω F).map (block D Y₀ l _ B z hz n)) ∧
  (∀ (hfix : ProperSemilinearGerms.movingPoint D Y₀ z n = z),
    z ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z ∧
    ∀ (hreturn : z ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z),
    (ProperSemilinearGerms.stageRealization l Ω F).map
      (eqToHom (congrArg (fun w ↦
        (ProperSemilinearGerms.rationalFibre D Y₀ l _ w).obj A.carrier) hfix).symm ≫
        block D Y₀ l _ A z hz n) =
      (ProperSemilinearGerms.stageRealization l Ω F).map
        (localFrobeniusOperator l _ D Fact.out Y₀ A z n hreturn)) ∧
  (∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (_heq : z = localClosedPoint D Y₀ y ι hι)
    (hfix : ProperSemilinearGerms.movingPoint D Y₀ z
      (localClosedPointDegree D Y₀ y - 1) = z),
    HEq ((ProperSemilinearGerms.stageRealization l Ω F).map
      (eqToHom (congrArg (fun w ↦
        (ProperSemilinearGerms.rationalFibre D Y₀ l _ w).obj A.carrier) hfix).symm ≫
        block D Y₀ l _ A z hz (localClosedPointDegree D Y₀ y - 1)))
      ((ProperSemilinearGerms.stageRealization l Ω F).map
        (localClosedFrobenius l _ D Fact.out Y₀ A y ι hι)))

/-- Every common-stage Weil complex and arrow admits finite-model coordinates, and
in those coordinates the asserted equations are precisely scalar extensions of rational ones.
The canonical comparison intertwines the actual global operator, for every finite model.
Source: Deligne, Weil II (1.1.3), (1.1.7), (1.1.10)--(1.1.14), pp. 150--153
(blueprint: lem-a1-proper-weil-iterate-germ-formula).
Proof:
1. Represent theta and its inverse at one common finite extension. The common-stage
Hom equality criterion allows enlarging it until the two inverse equations hold.
The resulting rational isomorphism defines a finite Weil pair A; the normalized
stage comparisons give an isomorphism of Weil pairs from its inclusion to K.
For a given arrow include both pairs, the arrow and its Weil equation in this
finite list, obtaining one finite model of the whole arrow.
2. Apply rational at that field and then stageRealization to its identities.
Functoriality preserves powers and compositions, and functors preserve inverses.
Thus realizedFormulas includes exactly the global power, moving germ, invertibility,
naturality and return assertions in the faithful derived coefficient realization.
3. Scalar compatibility of every operation, unit, counit and compositor is
lem-fix-operation-reduction. Point transport compatibility is
lem-weil-frobenius-point-transport-natural. Hence the normalized model comparison
intertwines the actual published global operator with the scalar-extended rational
operator, for every finite model and every exponent. The same prescribed comparisons
identify its germs and three block factors. There is no integral Weil lattice.
4. At a further field, apply the balanced tensor tower and the specified scalar
comparisons. The rational equations are the same equations there; eventual equality
of representatives proves independence and naturality for every common-stage arrow,
including identity extensions and different initial fields of definition. -/
theorem commonStage
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ) :
    (∀ (F : AlgebraicallyClosedCoefficients.Index l Ω)
      (A : sfWeilComplex D l Fact.out Y₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)),
      realizedFormulas D Y₀ l Ω F A z hz n) ∧
    (∀ K : sfCommonStageWeilComplex D l Fact.out Y₀ Ω,
      ∃ (F : AlgebraicallyClosedCoefficients.Index l Ω)
        (A : sfWeilComplex D l Fact.out Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)),
        Nonempty (sfWeilStageObject D l Fact.out Y₀ Ω F A ≅ K)) ∧
    (∀ (K L : sfCommonStageWeilComplex D l Fact.out Y₀ Ω) (f : K ⟶ L),
      ∃ (F : AlgebraicallyClosedCoefficients.Index l Ω)
        (A B : sfWeilComplex D l Fact.out Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
        (eA : sfWeilStageObject D l Fact.out Y₀ Ω F A ≅ K)
        (eB : sfWeilStageObject D l Fact.out Y₀ Ω F B ≅ L) (a : A ⟶ B),
        (GeneralAlgebraicallyClosedCoefficients.inclusion F).map a.hom.f ≫
          (sfCommonStageWeilForget D l Fact.out Y₀ Ω).map eB.hom =
        (sfCommonStageWeilForget D l Fact.out Y₀ Ω).map eA.hom ≫ f.hom.f) ∧
    (∀ (F : AlgebraicallyClosedCoefficients.Index l Ω)
      (A : sfWeilComplex D l Fact.out Y₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
      (K : sfCommonStageWeilComplex D l Fact.out Y₀ Ω)
      (e : sfWeilStageObject D l Fact.out Y₀ Ω F A ≅ K),
      (modelSectionsComparison D Y₀ l Ω F A K e).hom ≫
          (globalGeometricFrobeniusQbar D l Fact.out Y₀ Ω
            (Compactification.ofIsProper Y₀.hom) K true ^ (n + 1)) =
        (End.of ((ProperSemilinearGerms.stageRealization l Ω F).map
          (global D Y₀ l _ A)) ^ (n + 1)) ≫
          (modelSectionsComparison D Y₀ l Ω F A K e).hom) := by
  sorry

end CommonStage
end ProperWeilIterateGerms
end WeilConjectures
