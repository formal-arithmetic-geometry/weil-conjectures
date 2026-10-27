module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.FiniteCoefficientPoint
-- Data owner: def-fd-local-frobenius-coefficient-data (existing public definitions).
public import Sheaf.Paper.LocalFrobeniusCoefficientExtension
public import Sheaf.Paper.PointFdQbarCategory
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.PointSectionsScalarExtension
import Sheaf.Paper.LocalFrobeniusTransportNormalization

/-! # Common-stage point transport and semilinear return

Source: blueprint trace-transport, final common-stage transport paragraph, and
sec-purity-real-sheaves/sk-lem-wrp-l2-growth/lem-wf-l2-upper.proof.md, opening
punctual-Frobenius sentence (blueprint: lem-wf-common-stage-point-return).

The exponent is r+1, including every positive return period. The direct pullback
along the scheme power represents the iterated pullback via the specified compositors.
The finite-stage constructions are reused from LocalFrobeniusCoefficient; the
common-stage functor is the composite of the recorded pullback and point fibre.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures.AlgebraicallyClosedCoefficients (Coefficient)

namespace WeilConjectures
namespace CommonStagePointReturn

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The canonical identification of the composite point functor with its literal pair.
Both factors are the defining object identifications of the recorded functors.
Source: blueprint common-stage transport, object formula
(blueprint: lem-wf-common-stage-point-return). -/
def pointObjectIso (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (A : generalAlgebraicallyClosedConstructibleCategory c.l c.Qbar (D.geometricFiber Y₀).left) :=
  letI := frobeniusPointPrimeInvertible D c.l c.different
  letI := sfWeilPrimeInvertible D c.l c.different Y₀
  (pointQbarFibre D c.l c.different c.Qbar).mapIso
      (localQbarPullbackStageIso c.l c.Qbar z A) ≪≫
    eqToIso ((pointQbarFibre_existsUnique D c.l c.different c.Qbar).exists.choose_spec.1
      (commonStagePullbackObject c.l c.Qbar z A))

/-- J at a literal coefficient pair: take the specified finite-stage return map,
apply the canonical Shrink coefficient equivalence and stage inclusion, and insert
only the defining object identifications. No Weil structure is used.
Source: blueprint common-stage transport, Step 5
(blueprint: lem-wf-common-stage-point-return). -/
def component (C : IntegralComparisonSystem.{u} c.l) (r : ℕ)
    (x : D.extensionPoints Y₀ (r + 1) (Nat.succ_pos r))
    (A : generalAlgebraicallyClosedConstructibleCategory c.l c.Qbar (D.geometricFiber Y₀).left) :=
  letI := frobeniusPointPrimeInvertible D c.l c.different
  letI := sfWeilPrimeInvertible D c.l c.different Y₀
  (pointObjectIso D c Y₀ (localExtensionPoint D Y₀ (r + 1) (Nat.succ_pos r) x) A).hom ≫
    (DerivedCategory.pointFdQbarStage c.l c.Qbar A.stage).map
      ((DerivedCategory.pointFdScalarExtension
        (Shrink.algEquiv ℚ_[c.l] A.stage.val).toRingHom).map
          (LocalFrobeniusCoefficient.returnTransport D c.l c.different Y₀
            (Coefficient.{u} c.l c.Qbar A.stage) C r x A.obj)) ≫
    (pointObjectIso D c Y₀ (localExtensionPoint D Y₀ (r + 1) (Nat.succ_pos r) x)
      (commonStagePullbackObject c.l c.Qbar
        (localPositivePower (D.geometricFrobenius Y₀).hom r) A)).inv ≫
    (commonStageDerivedPullback c.l c.Qbar
        (localExtensionPoint D Y₀ (r + 1) (Nat.succ_pos r) x) ⋙
      pointQbarFibre D c.l c.different c.Qbar).map
        (localQbarPullbackStageIso c.l c.Qbar
          (localPositivePower (D.geometricFrobenius Y₀).hom r) A).inv

/-- Finite-stage naturality, for every underlying rational morphism, with the
specified successive transports and normalized semilinear return.
Source: blueprint common-stage transport, Step 2
(blueprint: lem-wf-common-stage-point-return). -/
def FiniteNaturality (C : IntegralComparisonSystem.{u} c.l) (r : ℕ)
    (x : D.extensionPoints Y₀ (r + 1) (Nat.succ_pos r)) : Prop :=
  ∀ (E : Type u) [Field E] [Algebra ℚ_[c.l] E] [FiniteDimensional ℚ_[c.l] E]
    (K L : sfRationalConstructibleCategory c.l E (D.geometricFiber Y₀).left) (v : K ⟶ L),
    (LocalFrobeniusCoefficient.fibre D c.l c.different Y₀ E
      (localExtensionPoint D Y₀ (r + 1) (Nat.succ_pos r) x)).map v ≫
        LocalFrobeniusCoefficient.returnTransport D c.l c.different Y₀ E C r x L =
      LocalFrobeniusCoefficient.returnTransport D c.l c.different Y₀ E C r x K ≫
        (LocalFrobeniusCoefficient.fibre D c.l c.different Y₀ E
          (localExtensionPoint D Y₀ (r + 1) (Nat.succ_pos r) x)).map
          ((LocalFrobeniusCoefficient.pullback D c.l c.different Y₀ E r).map v)

/-- The scalar equation uses b = inverse sections comparison followed by point
pullback comparison, and d = the specified pullback-power scalar comparison.
Source: blueprint common-stage transport, Steps 1 and 2
(blueprint: lem-wf-common-stage-point-return). -/
def ScalarEquation (C : IntegralComparisonSystem.{u} c.l) (r : ℕ)
    (x : D.extensionPoints Y₀ (r + 1) (Nat.succ_pos r)) : Prop :=
  ∀ (E M : Type u) [Field E] [Algebra ℚ_[c.l] E] [FiniteDimensional ℚ_[c.l] E]
    [Field M] [Algebra ℚ_[c.l] M] [FiniteDimensional ℚ_[c.l] M]
    (ι : E →ₐ[ℚ_[c.l]] M)
    (K : sfRationalConstructibleCategory c.l E (D.geometricFiber Y₀).left),
    (DerivedCategory.pointFdScalarExtension ι.toRingHom).map
        (LocalFrobeniusCoefficient.returnTransport D c.l c.different Y₀ E C r x K) ≫
      (LocalFrobeniusCoefficient.pointComparison D c.l c.different Y₀ E M ι C
        (localExtensionPoint D Y₀ (r + 1) (Nat.succ_pos r) x)
        ((LocalFrobeniusCoefficient.pullback D c.l c.different Y₀ E r).obj K)).hom ≫
      (LocalFrobeniusCoefficient.fibre D c.l c.different Y₀ M
        (localExtensionPoint D Y₀ (r + 1) (Nat.succ_pos r) x)).map
        ((LocalFrobeniusCoefficient.comparison D c.l c.different Y₀ E M ι C r).hom.app K) =
      (LocalFrobeniusCoefficient.pointComparison D c.l c.different Y₀ E M ι C
        (localExtensionPoint D Y₀ (r + 1) (Nat.succ_pos r) x) K).hom ≫
      LocalFrobeniusCoefficient.returnTransport D c.l c.different Y₀ M C r x
        ((LocalFrobeniusCoefficient.scalar D c.l Y₀ E M ι).obj K)

/-- Naturality of b on the full underlying category, with identity and tower
normalizations. Towers use the recorded completed scalar associator and the
ordinary derived field tensor associator, including equal coefficient fields.
Source: blueprint common-stage transport, Step 1
(blueprint: lem-wf-common-stage-point-return). -/
def ScalarCoherence (C : IntegralComparisonSystem.{u} c.l)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) : Prop :=
  (∀ (E M : Type u) [Field E] [Algebra ℚ_[c.l] E] [FiniteDimensional ℚ_[c.l] E]
    [Field M] [Algebra ℚ_[c.l] M] [FiniteDimensional ℚ_[c.l] M]
    (ι : E →ₐ[ℚ_[c.l]] M)
    (K L : sfRationalConstructibleCategory c.l E (D.geometricFiber Y₀).left) (v : K ⟶ L),
    (DerivedCategory.pointFdScalarExtension ι.toRingHom).map
        ((LocalFrobeniusCoefficient.fibre D c.l c.different Y₀ E z).map v) ≫
      (LocalFrobeniusCoefficient.pointComparison D c.l c.different Y₀ E M ι C z L).hom =
      (LocalFrobeniusCoefficient.pointComparison D c.l c.different Y₀ E M ι C z K).hom ≫
        (LocalFrobeniusCoefficient.fibre D c.l c.different Y₀ M z).map
          ((LocalFrobeniusCoefficient.scalar D c.l Y₀ E M ι).map v)) ∧
  (∀ (E : Type u) [Field E] [Algebra ℚ_[c.l] E] [FiniteDimensional ℚ_[c.l] E]
    (K : sfRationalConstructibleCategory c.l E (D.geometricFiber Y₀).left),
    ((LocalFrobeniusCoefficient.pointComparison D c.l c.different Y₀ E E
        (AlgHom.id ℚ_[c.l] E) C z K).hom).hom ≫
      ((LocalFrobeniusCoefficient.fibre D c.l c.different Y₀ E z).map
        ((sfRationalScalarUnit c.l E (D.geometricFiber Y₀).left 0
          (Nat.Prime.ne_zero (Fact.out : c.l.Prime))).hom.app K)).hom =
      (DerivedCategory.fieldScalarUnit E).hom.app
        ((LocalFrobeniusCoefficient.fibre D c.l c.different Y₀ E z).obj K).obj) ∧
  (∀ (E M N : Type u) [Field E] [Algebra ℚ_[c.l] E] [FiniteDimensional ℚ_[c.l] E]
    [Field M] [Algebra ℚ_[c.l] M] [FiniteDimensional ℚ_[c.l] M]
    [Field N] [Algebra ℚ_[c.l] N] [FiniteDimensional ℚ_[c.l] N]
    (ι : E →ₐ[ℚ_[c.l]] M) (j : M →ₐ[ℚ_[c.l]] N)
    (K : sfRationalConstructibleCategory c.l E (D.geometricFiber Y₀).left),
    (DerivedCategory.pointFdScalarExtension j.toRingHom).map
        (LocalFrobeniusCoefficient.pointComparison D c.l c.different Y₀ E M ι C z K).hom ≫
      (LocalFrobeniusCoefficient.pointComparison D c.l c.different Y₀ M N j C z
        ((LocalFrobeniusCoefficient.scalar D c.l Y₀ E M ι).obj K)).hom ≫
      (LocalFrobeniusCoefficient.fibre D c.l c.different Y₀ N z).map
        ((sfRationalScalarComp c.l E M ι (D.geometricFiber Y₀).left 0
          (Nat.Prime.ne_zero (Fact.out : c.l.Prime)) N j).hom.app K) =
      (pointFibreFdTensorTower ι.toRingHom j.toRingHom).hom.app
          ((LocalFrobeniusCoefficient.fibre D c.l c.different Y₀ E z).obj K) ≫
        (LocalFrobeniusCoefficient.pointComparison D c.l c.different Y₀ E N
          (j.comp ι) C z K).hom)

/-- Naturality on every common-stage underlying morphism, including the canonical
transition isomorphisms of literal coefficient pairs. The component construction
specifies the finite representative, rather than positing an arbitrary family.
Source: blueprint common-stage transport, Steps 3--5
(blueprint: lem-wf-common-stage-point-return). -/
def CommonNaturality (C : IntegralComparisonSystem.{u} c.l) (r : ℕ)
    (x : D.extensionPoints Y₀ (r + 1) (Nat.succ_pos r)) : Prop :=
  letI := frobeniusPointPrimeInvertible D c.l c.different
  letI := sfWeilPrimeInvertible D c.l c.different Y₀
  ∀ (K L : generalAlgebraicallyClosedConstructibleCategory c.l c.Qbar
    (D.geometricFiber Y₀).left) (v : K ⟶ L),
    (commonStageDerivedPullback c.l c.Qbar
        (localExtensionPoint D Y₀ (r + 1) (Nat.succ_pos r) x) ⋙
      pointQbarFibre D c.l c.different c.Qbar).map v ≫ component D c Y₀ C r x L =
      component D c Y₀ C r x K ≫
        (commonStageDerivedPullback c.l c.Qbar
            (localExtensionPoint D Y₀ (r + 1) (Nat.succ_pos r) x) ⋙
          pointQbarFibre D c.l c.different c.Qbar).map
          ((commonStageDerivedPullback c.l c.Qbar
            (localPositivePower (D.geometricFrobenius Y₀).hom r)).map v)

/-- The component is unchanged on passing to a later literal coefficient pair,
using the source category's canonical transition isomorphism and the recorded
functors on its two boundaries. This includes identity extensions and towers.
Source: blueprint common-stage transport, Step 5
(blueprint: lem-wf-common-stage-point-return). -/
def RepresentativeCompatibility (C : IntegralComparisonSystem.{u} c.l) (r : ℕ)
    (x : D.extensionPoints Y₀ (r + 1) (Nat.succ_pos r)) : Prop :=
  letI := frobeniusPointPrimeInvertible D c.l c.different
  letI := sfWeilPrimeInvertible D c.l c.different Y₀
  ∀ (A : generalAlgebraicallyClosedConstructibleCategory c.l c.Qbar
    (D.geometricFiber Y₀).left) (M : Padic.FiniteCoefficientFields c.l c.Qbar)
    (h : A.stage ≤ M),
    (commonStageDerivedPullback c.l c.Qbar
        (localExtensionPoint D Y₀ (r + 1) (Nat.succ_pos r) x) ⋙
      pointQbarFibre D c.l c.different c.Qbar).map
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem c.l c.Qbar
          (D.geometricFiber Y₀).left).isoToStage A h).hom ≫
      component D c Y₀ C r x
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem c.l c.Qbar
          (D.geometricFiber Y₀).left).ι M |>.obj (A.toStage h)) =
      component D c Y₀ C r x A ≫
        (commonStageDerivedPullback c.l c.Qbar
            (localExtensionPoint D Y₀ (r + 1) (Nat.succ_pos r) x) ⋙
          pointQbarFibre D c.l c.different c.Qbar).map
          ((commonStageDerivedPullback c.l c.Qbar
            (localPositivePower (D.geometricFrobenius Y₀).hom r)).map
            ((GeneralAlgebraicallyClosedCoefficients.stageSystem c.l c.Qbar
              (D.geometricFiber Y₀).left).isoToStage A h).hom)

end CommonStagePointReturn

/-- The specified return transport is natural at finite and common coefficient stages.
The finite exponent is r+1; no Weil structure, stable integral lattice, or integral
finite-Tor-amplitude condition is required.
Source: blueprint trace-transport, final transport paragraph, and the opening
punctual-Frobenius sentence of lem-wf-l2-upper.proof.md
(blueprint: lem-wf-common-stage-point-return).

Proof:
1. Compose the inverse rational point-sections comparison with the specified
   pullback scalar comparison. Both are natural on all underlying rational maps.
   Move the sections comparison past the pullback comparison by naturality to
   obtain the identity and tower equations (lem-weil-point-sections-scalar-extension,
   lem-trf-integral-pullback-comparison-realization).
2. Apply lem-trf-local-frobenius-transport-normalization with m=r+1 and y=x.
   Its successive transports and semilinear return give finite naturality and
   the scalar equation. Its no-finite-Tor clause applies to every object here.
3. At a common field M send u to b_target inverse, P_M(u), b_source, in composition
   order. The tower equation and naturality of b identify this with its further
   scalar extensions. Equivalent representatives therefore give equal maps.
   At a common stage the middle b and its inverse cancel, proving composition;
   the same cancellation proves identities. This is the recorded composite functor.
4. Put D_K=P_M(d_K)b_(T^n K). Its action on T^n(u) is conjugation by D.
   Substitute D_K R(J_K)=J_(K_M)b_K and finite naturality, then cancel D_L.
   This proves common-stage naturality for every underlying morphism.
5. Represent J_(E,K) by its specified J_E,K, inserting the unit identifications.
   The scalar equation identifies its image at M with D_K inverse, J_M, b_K.
   The tower equations identify every further extension, so the components are
   independent of representatives. The return is g_Y^n xbar=xbar g_s^n throughout;
   no equality g_Y^n xbar=xbar is used. -/
theorem commonStagePointReturn (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (C : IntegralComparisonSystem.{u} c.l)
    (_hC : ∀ (E M : Type u) [Field E] [Algebra ℚ_[c.l] E]
      [FiniteDimensional ℚ_[c.l] E] [Field M] [Algebra ℚ_[c.l] M]
      [FiniteDimensional ℚ_[c.l] M] (ι : E →ₐ[ℚ_[c.l]] M),
      IntegralComparisonRealizationCoherence c.l E M ι C)
    (r : ℕ) (x : D.extensionPoints Y₀ (r + 1) (Nat.succ_pos r)) :
    CommonStagePointReturn.FiniteNaturality D c Y₀ C r x ∧
    CommonStagePointReturn.ScalarEquation D c Y₀ C r x ∧
    CommonStagePointReturn.ScalarCoherence D c Y₀ C
      (localExtensionPoint D Y₀ (r + 1) (Nat.succ_pos r) x) ∧
    CommonStagePointReturn.CommonNaturality D c Y₀ C r x ∧
    CommonStagePointReturn.RepresentativeCompatibility D c Y₀ C r x := by
  sorry

end WeilConjectures
