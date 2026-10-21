/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.SixFunctors.FrobeniusPointTransportNatural
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.FieldDerivedScalarTower
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.Paper.LocalFrobeniusTransportNormalization

/-!
# Coefficient extension of local Frobenius

Source: main-20261015, sec-fourier-transform/sk-def-trace/def-fd-trace-function.md,
displayed local alternating trace and its coefficient-model independence
(blueprint: lem-fd-local-frobenius-coefficient-extension).

The helpers instantiate the published normalized comparison family. Positive-power index
`r` means exponent `r+1`. All maps are in the raw rationalized constructible categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures
namespace LocalFrobeniusCoefficient

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- G_(E,r+1), with invertibility supplied by the finite-field datum.
Source: displayed local trace (blueprint: lem-fd-local-frobenius-coefficient-extension). -/
def pullback (r : ℕ) :=
  @rationalDerivedPullback l _ E _ _ _ _ _
    (localPositivePower (D.geometricFrobenius X₀).hom r)
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀)

/-- D_E = Q_E P_E, on every constructible object and every rational morphism.
Source: displayed local trace (blueprint: lem-fd-local-frobenius-coefficient-extension). -/
def fibre (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :=
  @rationalDerivedPullback l _ E _ _ _ _ _ x
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀) ⋙
      pointRationalFibre D l hl E

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (C : IntegralComparisonSystem.{u} l)

/-- T_X is the published raw rational scalar extension, with its auxiliary parameter zero.
Source: scalar convention (blueprint: lem-fd-local-frobenius-coefficient-extension). -/
abbrev scalar :=
  sfRationalScalarExtension l E (D.geometricFiber X₀).left 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι

/-- The specified a_(r+1), obtained by rationalizing lambda followed by mu inverse.
Source: comparison normalization (blueprint: lem-fd-local-frobenius-coefficient-extension). -/
def comparison (r : ℕ) :=
  letI := sfWeilPrimeInvertible D l hl X₀
  LocalFrobeniusTransport.rationalScalar l E C L ι
    (localPositivePower (D.geometricFrobenius X₀).hom r)

/-- The specified b: inverse sections comparison, then Q_L of the point-pullback comparison.
Source: formula for b (blueprint: lem-fd-local-frobenius-coefficient-extension). -/
def pointComparison (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :
    (DerivedCategory.pointFdScalarExtension ι.toRingHom).obj
        ((fibre D l hl X₀ E x).obj M) ≅
      (fibre D l hl X₀ L x).obj ((scalar D l X₀ E L ι).obj M) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl X₀
  ((pointRationalFibreScalarIso D l hl E L ι).symm.app
      ((rationalDerivedPullback l E x).obj M)) ≪≫
    (pointRationalFibre D l hl L).mapIso
      ((LocalFrobeniusTransport.rationalScalar l E C L ι x).app M)

/-- The scalar-extended Weil pair, with theta_L = T(theta) a_1 inverse.
Source: theta_L formula (blueprint: lem-fd-local-frobenius-coefficient-extension). -/
def extend (K : sfWeilComplex D l hl X₀ E) : sfWeilComplex D l hl X₀ L :=
  IsoAlgebra.mk ((scalar D l X₀ E L ι).obj K.carrier)
    (((comparison D l hl X₀ E L ι C 0).app K.carrier).symm ≪≫
      (scalar D l X₀ E L ι).mapIso K.str)

/-- Iterate the Weil structure with exactly the stipulated strict-system compositors.
Source: theta iteration (blueprint: lem-fd-local-frobenius-coefficient-extension). -/
def iterate (K : sfWeilComplex D l hl X₀ E) :
    (r : ℕ) → (pullback D l hl X₀ E r).obj K.carrier ≅ K.carrier
  | 0 => K.str
  | r + 1 =>
    letI := sfWeilPrimeInvertible D l hl X₀
    LocalFrobeniusTransport.rationalComposition l E C
      (localPositivePower (D.geometricFrobenius X₀).hom r)
      (D.geometricFrobenius X₀).hom K.carrier ≪≫
        (pullback D l hl X₀ E r).mapIso K.str ≪≫ iterate K r

/-- R_E(M), the successive point transports followed by the semilinear return comparison.
Source: R_H formula (blueprint: lem-fd-local-frobenius-coefficient-extension). -/
def returnTransport (r : ℕ) (x : D.extensionPoints X₀ (r + 1) (Nat.succ_pos r))
    (M : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :=
  LocalFrobeniusTransport.rationalTransport D l hl E X₀ C
    (hpoint := frobeniusPointPrimeInvertible D l hl)
    (hspace := sfWeilPrimeInvertible D l hl X₀) r
    (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x)
    (localExtensionPoint_return D X₀ (r + 1) (Nat.succ_pos r) x).symm M

/-- The derived local operator D_E(theta^[r+1]) R_E, using the specified comparisons.
Source: local-operator formula (blueprint: lem-fd-local-frobenius-coefficient-extension). -/
def operator (r : ℕ) (x : D.extensionPoints X₀ (r + 1) (Nat.succ_pos r))
    (K : sfWeilComplex D l hl X₀ E) :=
  returnTransport D l hl X₀ E C r x K.carrier ≫
    (fibre D l hl X₀ E
      (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x)).map
        (iterate D l hl X₀ E C K r).hom

/-- All four comparison identities and the identity-extension normalization. Successor
indices include every positive n and r. No lattice or finite-Tor hypothesis occurs.
Source: coefficient-model independence of the displayed local alternating trace
(blueprint: lem-fd-local-frobenius-coefficient-extension). -/
def Properties (r : ℕ) (x : D.extensionPoints X₀ (r + 1) (Nat.succ_pos r)) : Prop :=
  (∀ (M N : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) (v : M ⟶ N),
    (DerivedCategory.pointFdScalarExtension ι.toRingHom).map
        ((fibre D l hl X₀ E
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x)).map v) ≫
        (pointComparison D l hl X₀ E L ι C
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x) N).hom =
      (pointComparison D l hl X₀ E L ι C
        (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x) M).hom ≫
        (fibre D l hl X₀ L
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x)).map
            ((scalar D l X₀ E L ι).map v)) ∧
  (∀ (K : sfWeilComplex D l hl X₀ E) (j : ℕ),
    (comparison D l hl X₀ E L ι C j).hom.app K.carrier ≫
        (iterate D l hl X₀ L C (extend D l hl X₀ E L ι C K) j).hom =
      (scalar D l X₀ E L ι).map (iterate D l hl X₀ E C K j).hom) ∧
  (∀ M : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left,
    (DerivedCategory.pointFdScalarExtension ι.toRingHom).map
        (returnTransport D l hl X₀ E C r x M) ≫
        (pointComparison D l hl X₀ E L ι C
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x)
          ((pullback D l hl X₀ E r).obj M)).hom ≫
        (fibre D l hl X₀ L
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x)).map
          ((comparison D l hl X₀ E L ι C r).hom.app M) =
      (pointComparison D l hl X₀ E L ι C
        (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x) M).hom ≫
        returnTransport D l hl X₀ L C r x ((scalar D l X₀ E L ι).obj M)) ∧
  (∀ K : sfWeilComplex D l hl X₀ E,
    (DerivedCategory.pointFdScalarExtension ι.toRingHom).map
        (operator D l hl X₀ E C r x K) ≫
        (pointComparison D l hl X₀ E L ι C
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x) K.carrier).hom =
      (pointComparison D l hl X₀ E L ι C
        (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x) K.carrier).hom ≫
        operator D l hl X₀ L C r x (extend D l hl X₀ E L ι C K)) ∧
  (∀ M : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left,
    ((pointComparison D l hl X₀ E E (AlgHom.id ℚ_[l] E) C
      (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x) M).hom).hom ≫
      ((fibre D l hl X₀ E
        (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x)).map
        ((sfRationalScalarUnit l E (D.geometricFiber X₀).left 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app M)).hom =
      (DerivedCategory.fieldScalarUnit E).hom.app
        ((fibre D l hl X₀ E
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) x)).obj M).obj)

end LocalFrobeniusCoefficient

/-- Coefficient extension intertwines the specified local Frobenius operators.
Source: main-20261015, sec-fourier-transform/sk-def-trace/def-fd-trace-function.md,
displayed local trace, coefficient-model independence
(blueprint: lem-fd-local-frobenius-coefficient-extension).

Proof:
1. Write b = Q_L(e) u, with u the inverse rationalized sections comparison and e
   the specified point pullback/scalar comparison. Naturality of u and e gives
   naturality of b on every raw rational morphism; both factors are isomorphisms.
2. Induct on the positive iterate. At one, cancel a_1 with its inverse. At the
   successor, expand theta_L, use the composition/scalar equation of
   lem-trf-integral-pullback-comparison-realization, then naturality of a_r at
   theta and the induction hypothesis. This gives theta_L^[r] a_r = T(theta^[r]).
3. Apply lem-trf-local-frobenius-transport-normalization to the extension point.
   Its rationalTransport and rationalFibreScalar are exactly R and b here.
   Finite-iteration coherence identifies its iterated scalar comparison with a_n,
   giving the return-transport equation, on the full constructible domain.
4. Apply naturality of b to theta^[n], substitute step 2 and step 3, and use the
   definition of the local operator. This gives the intertwining identity.
5. Rational naturality extends the integral equations from pure tensor morphisms
   to their sums. No integral Weil-stable lattice is used. For identity coefficients,
   the sections and pullback comparisons are the identity under the specified
   multiplication and completeness units, so b is the identity under those units. -/
theorem localFrobeniusCoefficientExtension (D : FiniteFieldDatum.{u})
    (c : D.CoefficientDatum) (F L : Padic.FiniteCoefficientFields c.l c.Qbar)
    (hFL : F ≤ L) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (C : IntegralComparisonSystem.{u} c.l)
    (_hC : IntegralComparisonRealizationCoherence c.l F.val L.val
      (IntermediateField.inclusion hFL) C)
    (r : ℕ) (x : D.extensionPoints X₀ (r + 1) (Nat.succ_pos r)) :
    LocalFrobeniusCoefficient.Properties D c.l c.different X₀ F.val L.val
      (IntermediateField.inclusion hFL) C r x := by
  sorry

end WeilConjectures
