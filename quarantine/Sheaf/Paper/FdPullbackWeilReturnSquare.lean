/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.LocalFrobeniusTransportNormalization
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.LocalFrobeniusCoefficientExtension
public import Sheaf.SixFunctors.FrobeniusSquareCartesian
import Sheaf.SixFunctors.FrobeniusPointTransportNatural

/-! # Pullback comparison for rational Weil return operators

Source: latest blueprint, sec-deligne-laumon-a1/sk-p-dl-a1-some-weight,
lem-fd-realified-kernel-real.proof.md, Step 2; Deligne, Weil II (1.1.7)--(1.1.10).
(blueprint: lem-fd-pullback-weil-return-square).

The helpers use the specified strict-system compositor and its rationalization.
Positive-power index r denotes exponent r+1. The direct scheme-power presentation
is the one in the recorded normalized transport and Weil-iterate definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures.FdPullbackWeilReturn

variable (D : FiniteFieldDatum.{u})
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The actual base change of the model morphism.
Source: blueprint Step 2, pullback along p₁
(blueprint: lem-fd-pullback-weil-return-square). -/
def map (f₀ : X₀ ⟶ Y₀) : (D.geometricFiber X₀).left ⟶ (D.geometricFiber Y₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

/-- Frobenius commutes with base change of a model morphism at every positive power.
Source: blueprint Step 2; affine geometric-Frobenius formula, Weil II (1.1.10)
(blueprint: lem-fd-pullback-weil-return-square).
Proof: at exponent one, both affine ring maps send a tensor b to f₀(a) tensor gamma(b),
as in def-weil-frobenius-detailed and lem-weil-frobenius-square-cartesian. For the
successor, expand localPositivePower, reassociate, apply the one-step equation,
then the induction hypothesis, and reassociate again. -/
theorem power_comm (f₀ : X₀ ⟶ Y₀) (r : ℕ) :
    localPositivePower (D.geometricFrobenius X₀).hom r ≫ map D f₀ =
      map D f₀ ≫ localPositivePower (D.geometricFrobenius Y₀).hom r := by
  have hcomm : (D.geometricFrobenius X₀).hom ≫ map D f₀ =
      map D f₀ ≫ (D.geometricFrobenius Y₀).hom :=
    (D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1
  induction r with
  | zero => exact hcomm
  | succ r ih =>
    simp only [localPositivePower, Category.assoc]
    rw [hcomm, ← Category.assoc, ih, Category.assoc]

variable (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (C : IntegralComparisonSystem.{u} l)

/-- Pullback along f, with prime invertibility supplied by the finite-field datum.
Source: blueprint Step 2, F=Lf* (blueprint: lem-fd-pullback-weil-return-square). -/
def pullback (f₀ : X₀ ⟶ Y₀) :=
  @rationalDerivedPullback l _ E _ _ _ _ _ (map D f₀)
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl Y₀)

/-- Beta_r is inverse c(g_X^r,f), the equality of scheme maps, then c(f,g_Y^r).
Source: blueprint Step 2, same-length pullback comparison
(blueprint: lem-fd-pullback-weil-return-square). -/
def beta (f₀ : X₀ ⟶ Y₀) (r : ℕ)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Y₀
  (LocalFrobeniusTransport.rationalComposition l E C
      (localPositivePower (D.geometricFrobenius X₀).hom r) (map D f₀) M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj M)
      (power_comm D f₀ r)) ≪≫
    LocalFrobeniusTransport.rationalComposition l E C (map D f₀)
      (localPositivePower (D.geometricFrobenius Y₀).hom r) M

/-- The canonical point comparison c_M is Fib_s of the inverse compositor for f z.
Source: blueprint Step 2, displayed c_M (blueprint: lem-fd-pullback-weil-return-square). -/
def pointComparison (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Y₀
  (pointRationalFibre D l hl E).mapIso
    (LocalFrobeniusTransport.rationalComposition l E C
      (hV := sfWeilPrimeInvertible D l hl Y₀)
      (hW := sfWeilPrimeInvertible D l hl X₀)
      (hZ := frobeniusPointPrimeInvertible D l hl) z (map D f₀) M).symm

/-- The pullback Weil pair has theta_X=F(theta_Y) beta_1.
Source: blueprint Step 2, pullback of the Weil structure
(blueprint: lem-fd-pullback-weil-return-square). -/
def weilPullback (f₀ : X₀ ⟶ Y₀) (K : sfWeilComplex D l hl Y₀ E) :
    sfWeilComplex D l hl X₀ E :=
  IsoAlgebra.mk ((pullback D l hl E f₀).obj K.carrier)
    (beta D l hl E C f₀ 0 K.carrier ≪≫ (pullback D l hl E f₀).mapIso K.str)

/-- R_n is normalized successive transport followed by the fibre of theta^[n].
The geometric point is arbitrary subject to its specified return equation.
Source: blueprint Step 2, displayed R^X_n and R^Y_n
(blueprint: lem-fd-pullback-weil-return-square). -/
def operator (K : sfWeilComplex D l hl X₀ E)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (n : ℕ)
    (hz : localPositivePower (frobeniusPointIso D).hom n ≫ z =
      z ≫ localPositivePower (D.geometricFrobenius X₀).hom n) :=
  LocalFrobeniusTransport.rationalTransport D l hl E X₀ C
      (hpoint := frobeniusPointPrimeInvertible D l hl)
      (hspace := sfWeilPrimeInvertible D l hl X₀) n z hz K.carrier ≫
    (LocalFrobeniusTransport.rationalFibre D l hl E X₀
      (hpoint := frobeniusPointPrimeInvertible D l hl)
      (hspace := sfWeilPrimeInvertible D l hl X₀) z).map
        (LocalFrobeniusCoefficient.iterate D l hl X₀ E C K n).hom

/-- The three equations, in direct positive scheme-power coordinates. In these
coordinates beta and the Weil iterates include all associative power comparisons.
Source: blueprint Step 2, pullback and the residue-degree Frobenius power
(blueprint: lem-fd-pullback-weil-return-square). -/
def Properties (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (n : ℕ)
    (hz : localPositivePower (frobeniusPointIso D).hom n ≫ z =
      z ≫ localPositivePower (D.geometricFrobenius X₀).hom n)
    (hx : localPositivePower (frobeniusPointIso D).hom n ≫ (z ≫ map D f₀) =
      (z ≫ map D f₀) ≫ localPositivePower (D.geometricFrobenius Y₀).hom n) : Prop :=
  (∀ M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left,
    LocalFrobeniusTransport.rationalTransport D l hl E X₀ C
        (hpoint := frobeniusPointPrimeInvertible D l hl)
        (hspace := sfWeilPrimeInvertible D l hl X₀) n z hz
        ((pullback D l hl E f₀).obj M) ≫
      (LocalFrobeniusTransport.rationalFibre D l hl E X₀
        (hpoint := frobeniusPointPrimeInvertible D l hl)
        (hspace := sfWeilPrimeInvertible D l hl X₀) z).map
          (beta D l hl E C f₀ n M).hom ≫
      (pointComparison D l hl E C f₀ z
        ((LocalFrobeniusCoefficient.pullback D l hl Y₀ E n).obj M)).hom =
    (pointComparison D l hl E C f₀ z M).hom ≫
      LocalFrobeniusTransport.rationalTransport D l hl E Y₀ C
        (hpoint := frobeniusPointPrimeInvertible D l hl)
        (hspace := sfWeilPrimeInvertible D l hl Y₀) n (z ≫ map D f₀) hx M) ∧
  (∀ (K : sfWeilComplex D l hl Y₀ E) (r : ℕ),
    (LocalFrobeniusCoefficient.iterate D l hl X₀ E C
      (weilPullback D l hl E C f₀ K) r).hom =
      (beta D l hl E C f₀ r K.carrier).hom ≫
        (pullback D l hl E f₀).map
          (LocalFrobeniusCoefficient.iterate D l hl Y₀ E C K r).hom) ∧
  (∀ K : sfWeilComplex D l hl Y₀ E,
    operator D l hl E C (weilPullback D l hl E C f₀ K) z n hz ≫
        (pointComparison D l hl E C f₀ z K.carrier).hom =
      (pointComparison D l hl E C f₀ z K.carrier).hom ≫
        operator D l hl E C K (z ≫ map D f₀) n hx)

end WeilConjectures.FdPullbackWeilReturn

namespace WeilConjectures

/-- Pullback intertwines same-length normalized point returns, all positive Weil
iterates, and their resulting rational derived return operators.
Source: latest blueprint, sec-deligne-laumon-a1/sk-p-dl-a1-some-weight,
lem-fd-realified-kernel-real.proof.md, Step 2; Weil II (1.1.7)--(1.1.10)
(blueprint: lem-fd-pullback-weil-return-square).

Proof:
1. Put F=Lf*, P_z=Lz*, P_x=Lx*, U=Lg_s* and B=Fib_s. Frobenius commutes
with f by the affine formula. Expand the inverse point compositor and beta_n.
Associativity of lem-trf-integral-pullback-comparison-realization identifies both
pastings along f g_X^n z = g_Y^n f z = f z g_s^n, including equal-map transports.
2. Naturality of the single point transport, from
lem-weil-frobenius-point-transport-natural, gives naturality of its n successive
iterates by induction. Apply this to the inverse point compositor. Apply B to
Step 1, then compose with the successive transport. This is the first equation,
using the recipe of lem-trf-local-frobenius-transport-normalization.
3. The same specified compositor associativity gives the beta successor equation;
its naturality gives beta_r G_X^r(F u) = F(G_Y^r u) beta_r at G_Y M.
4. Induct on positive r. The base is the definition of weilPullback. Expand the
Weil-iterate recursion of def-weil-local-frobenius-trace, apply the induction
hypothesis and Step 3 with u=theta_Y, then recombine the beta factors. This is
the second equation, with the specified family used by the recorded iterate.
5. Naturality of the inverse point compositor at theta_Y^[n], followed by B,
and the second equation rewrite c_M R_X as J_x(theta_Y^[n]) c_(G_Y^n M) beta_n t_X.
The first equation turns this into R_Y c_M. All maps are rational; no integral
Weil-stable lattice or finite Tor-amplitude condition is used. -/
theorem fdPullbackWeilReturnSquare (D : FiniteFieldDatum.{u})
    (c : D.CoefficientDatum) (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (C : IntegralComparisonSystem.{u} c.l) (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (n : ℕ)
    (hz : localPositivePower (frobeniusPointIso D).hom n ≫ z =
      z ≫ localPositivePower (D.geometricFrobenius X₀).hom n)
    (hx : localPositivePower (frobeniusPointIso D).hom n ≫
        (z ≫ FdPullbackWeilReturn.map D f₀) =
      (z ≫ FdPullbackWeilReturn.map D f₀) ≫
        localPositivePower (D.geometricFrobenius Y₀).hom n) :
    FdPullbackWeilReturn.Properties D c.l c.different E.val C f₀ z n hz hx := by
  sorry

end WeilConjectures
