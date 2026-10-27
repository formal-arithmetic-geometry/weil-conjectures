/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.FrobeniusGeometricExchange
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
import Sheaf.AlgebraicGeometry.FrobeniusOpenSquare
import Sheaf.SixFunctors.FrobeniusSquareCartesian
import Sheaf.Paper.IsomorphismDerivedPullback

/-! # Frobenius powers and the chosen-compactification exchange

Source: Stacks Project, Tag 03S6, lemma-shriek-base-change; blueprint
`sec-trace-formula/sk-d-weil/lem-trf-frobenius-operator-compact-description.proof.md`,
compact-support iterate paragraph (blueprint: lem-trf-frobenius-compact-power-exchange).

The proper-pasting equation is an explicit hypothesis. All maps below are the published
canonical maps, with the same retained compactification at every power. The conclusions
include the open-square geometry, bounded constructibility, and both pasting identities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.FrobeniusCompactPower
open FrobeniusExchange

variable (D : FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (c₀ : Compactification X₀.hom)

/-- The retained middle model W₀, using the published compactification convention.
Source: blueprint fixed-compactification paragraph
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
abbrev middle := zlCompactificationMiddle D (frobeniusCohomologyModelMap D X₀) c₀

/-- The existing geometric compactification X → W → Spec k, with this same k₀-model.
Source: blueprint fixed-compactification paragraph
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
abbrev model := frobeniusCohomologyCompactification D X₀ c₀

/-- The scheme map g^r, without a k-linearity condition.
Source: blueprint Frobenius-power convention
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
abbrev sourcePower (r : ℕ) := End.of (D.geometricGaloisFrobenius X₀) ^ r

/-- The scheme map b^r on the geometric middle scheme.
Source: blueprint Frobenius-power convention
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
abbrev middlePower (r : ℕ) := End.of (D.geometricGaloisFrobenius (middle D X₀ c₀)) ^ r

/-- h^r on Spec k, for h = Spec of inverse field Frobenius.
Source: blueprint Frobenius-power convention
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
abbrev basePower (r : ℕ) := End.of (frobeniusPointIso D).hom ^ r

/-- The canonical iterated-to-composite comparison, followed only by the equality
f^(m+1) = f^m f. In categorical End multiplication f^m f means f followed by f^m.
Source: Stacks Tag 0D6D; blueprint inverse composition comparisons c_m,d_m,t_m
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
def powerComposition (A : Type u) [CommRing A] {T : Scheme.{u}} (f : End T) (m : ℕ) :
    proEtaleConstantRingDerivedPullback A (f ^ m) ⋙
        proEtaleConstantRingDerivedPullback A f ≅
      proEtaleConstantRingDerivedPullback A (f ^ (m + 1)) :=
  proEtaleConstantRingPullbackComposition f (f ^ m) A ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) (pow_succ f m).symm)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)

/-- P_r = L(g^r)^* in the ordinary unbounded intrinsic derived category.
Source: blueprint P_r convention
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
abbrev sourcePullback (r : ℕ) :=
  proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n)
    (sourcePower D X₀ r)

/-- B_r = L(b^r)^* on the same constant finite coefficient ring.
Source: blueprint B_r convention
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
abbrev middlePullback (r : ℕ) :=
  proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n)
    (middlePower D X₀ c₀ r)

/-- Q_r = L(h^r)^* on Spec k.
Source: blueprint Q_r convention
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
abbrev basePullback (r : ℕ) :=
  proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) (basePower D r)

/-- J is the published exact termwise derived extension by zero.
Source: blueprint J convention; Stacks Tag 03S6
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
abbrev openExtension :=
  @sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E n) _
    (Padic.finite_coefficientExtensionRing l E n hn) _ _ (model D X₀ c₀).i _

/-- R is the published uncompleted unbounded proper derived direct image.
Source: blueprint R convention
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
abbrev properImage :=
  proEtaleConstantDerivedDirectImage (model D X₀ c₀).g (Padic.coefficientExtensionRing l E n)

/-- F = RJ for this same compactification, on all ambient derived objects.
Source: blueprint F convention
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
abbrev compactImage := openExtension D X₀ c₀ l E n hn ⋙ properImage D X₀ c₀ l E n

/-- The specified proper exchange u_r, using the semilinear projection identity.
Source: blueprint proper-square exchange, item (1)
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
def properExchange (r : ℕ) :
    properImage D X₀ c₀ l E n ⋙ basePullback D l E n r ⟶
      middlePullback D X₀ c₀ l E n r ⋙ properImage D X₀ c₀ l E n :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  finiteTensorExchange (Padic.coefficientExtensionRing l E n)
    (model D X₀ c₀).g (model D X₀ c₀).g
    (middlePower D X₀ c₀ r) (basePower D r)
    (D.frobenius_open_square X₀ (middle D X₀ c₀)
      (zlCompactificationOpen D (frobeniusCohomologyModelMap D X₀) c₀) r).2.2.2

/-- v_r is exactly the existing open-square exchange, normalized on the open.
Source: Stacks Tag 03S6; blueprint lem-trf-open-square-exchange
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
def openExchange (r : ℕ) :
    openExtension D X₀ c₀ l E n hn ⋙ middlePullback D X₀ c₀ l E n r ≅
      sourcePullback D X₀ l E n r ⋙ openExtension D X₀ c₀ l E n hn :=
  constantOpenSquareExchange l E n hn (sourcePower D X₀ r)
    (model D X₀ c₀).i (model D X₀ c₀).i (middlePower D X₀ c₀ r)
    (D.frobenius_open_square X₀ (middle D X₀ c₀)
      (zlCompactificationOpen D (frobeniusCohomologyModelMap D X₀) c₀) r).2.1

/-- The specified e_r = R(v_r) u_r J, using the same proper and open exchanges.
Source: blueprint compact-support exchange, item (2)
(blueprint: lem-trf-frobenius-compact-power-exchange). -/
def compactExchange (r : ℕ) :
    compactImage D X₀ c₀ l E n hn ⋙ basePullback D l E n r ⟶
      sourcePullback D X₀ l E n r ⋙ compactImage D X₀ c₀ l E n hn :=
  Functor.whiskerLeft (openExtension D X₀ c₀ l E n hn)
      (properExchange D X₀ c₀ l E n hn r) ≫
    Functor.whiskerRight (openExchange D X₀ c₀ l E n hn r).hom
      (properImage D X₀ c₀ l E n)

/-- Geometry, bounded constructibility, and open/compact pasting for the specified maps.
Source: Stacks Tag 03S6, lemma-shriek-base-change; blueprint compact-support iterate
paragraph (blueprint: lem-trf-frobenius-compact-power-exchange).

Proof:
1. Apply lem-trf-frobenius-open-square to j₀ and each positive r. Its Galois square
   is the displayed Cartesian square, and its lift has components (g^r,j).
   Lem-weil-frobenius-square-cartesian supplies the inverse Galois scheme map,
   and hence its powers are scheme isomorphisms; no k-linearity is used.
2. Bezout for l ≠ p makes l invertible on the characteristic-p geometric fibre.
   Apply lem-weil-isomorphism-derived-pullback to g^r to preserve D^b_c.
3. Paste the canonical open exchanges for powers m and 1, using
   lem-trf-open-square-exchange. The inverse canonical composition comparisons
   of lem-weil-pbc-proetale-derived-pullback-composition give the first equation.
4. Expand e_r = R(v_r)u_r J and use the assumed proper-pasting identity at JM.
   Apply R to step 3. Naturality of u_1 at v_m moves R(B_1(v_m)) past u_1.
   Functoriality of Q_1 then combines Q_1(R(v_m))Q_1(u_m) into Q_1(e_m),
   giving the second equation. Components of the specified natural transformations
   make both identities natural in M, in the ambient unbounded derived categories. -/
theorem frobenius_compact_power_exchange (_hl : l ≠ D.p) [IsSeparated X₀.hom]
    (proper_pasting : ∀ (m : ℕ), 1 ≤ m →
      ∀ K : proEtaleDerivedCategory (model D X₀ c₀).Z
          (Padic.coefficientExtensionRing l E n),
        (powerComposition (Padic.coefficientExtensionRing l E n) (basePower D 1) m).hom.app
            ((properImage D X₀ c₀ l E n).obj K) ≫
          (properExchange D X₀ c₀ l E n hn (m + 1)).app K =
        (basePullback D l E n 1).map ((properExchange D X₀ c₀ l E n hn m).app K) ≫
          (properExchange D X₀ c₀ l E n hn 1).app
            ((middlePullback D X₀ c₀ l E n m).obj K) ≫
          (properImage D X₀ c₀ l E n).map
            ((powerComposition (Padic.coefficientExtensionRing l E n)
              (middlePower D X₀ c₀ 1) m).hom.app K)) :
    (∀ (r : ℕ), 1 ≤ r →
      sourcePower D X₀ r ≫ (model D X₀ c₀).i =
        (model D X₀ c₀).i ≫ middlePower D X₀ c₀ r ∧
      IsPullback (sourcePower D X₀ r) (model D X₀ c₀).i
        (model D X₀ c₀).i (middlePower D X₀ c₀ r)) ∧
    (∀ (r : ℕ), 1 ≤ r → ∀ M : proEtaleDerivedCategory (D.geometricFiber X₀).left
        (Padic.coefficientExtensionRing l E n),
      intrinsicFiniteTorsionConstructible l E n hn (D.geometricFiber X₀).left M →
      intrinsicFiniteTorsionConstructible l E n hn (D.geometricFiber X₀).left
        ((sourcePullback D X₀ l E n r).obj M)) ∧
    ∀ (m : ℕ), 1 ≤ m →
      ∀ M : (intrinsicFiniteTorsionConstructible l E n hn
          (D.geometricFiber X₀).left).FullSubcategory,
        (powerComposition (Padic.coefficientExtensionRing l E n)
              (middlePower D X₀ c₀ 1) m).hom.app
            ((openExtension D X₀ c₀ l E n hn).obj M.obj) ≫
          (openExchange D X₀ c₀ l E n hn (m + 1)).hom.app M.obj =
        (middlePullback D X₀ c₀ l E n 1).map
            ((openExchange D X₀ c₀ l E n hn m).hom.app M.obj) ≫
          (openExchange D X₀ c₀ l E n hn 1).hom.app
            ((sourcePullback D X₀ l E n m).obj M.obj) ≫
          (openExtension D X₀ c₀ l E n hn).map
            ((powerComposition (Padic.coefficientExtensionRing l E n)
              (sourcePower D X₀ 1) m).hom.app M.obj) ∧
        (powerComposition (Padic.coefficientExtensionRing l E n) (basePower D 1) m).hom.app
            ((compactImage D X₀ c₀ l E n hn).obj M.obj) ≫
          (compactExchange D X₀ c₀ l E n hn (m + 1)).app M.obj =
        (basePullback D l E n 1).map
            ((compactExchange D X₀ c₀ l E n hn m).app M.obj) ≫
          (compactExchange D X₀ c₀ l E n hn 1).app
            ((sourcePullback D X₀ l E n m).obj M.obj) ≫
          (compactImage D X₀ c₀ l E n hn).map
            ((powerComposition (Padic.coefficientExtensionRing l E n)
              (sourcePower D X₀ 1) m).hom.app M.obj) := by
  sorry

end WeilConjectures.FrobeniusCompactPower
