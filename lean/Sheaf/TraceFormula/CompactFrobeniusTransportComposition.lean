/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.TraceFormula.PointTransportComposition
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.AlgebraicGeometry.FrobeniusOpenSquare
import Sheaf.SixFunctors.FrobeniusSquareCartesian
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.CondensedAmbientExchange
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import Sheaf.Paper.PullbackCoefficientIterateCoherence
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Composition of compact-support Frobenius transports

Source: Deligne, Weil II (1.1.10), (1.1.11), (1.1.14), printed pp. 151--153;
blueprint `lem-trf-frobenius-operator-compact-description`, iterate clause
(blueprint: lem-trf-compact-frobenius-transport-composition).

All powers use the same compactification over the finite field. The power transports
are direct exchange recipes, before inserting any Weil structure. The coefficient
exponent is n + 1, covering every positive finite level.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open FrobeniusExchange AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

/-- Pullback along the actual r-th power of geometric Galois Frobenius.
Source: Deligne, Weil II (1.1.10)--(1.1.11); Stacks 0D6D
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
abbrev compactPowerPullback (n r : ℕ) :=
  finiteDerivedPullback l E n ((End.of (galois D X₀)) ^ r)

/-- The chosen representative H = Fib_s Ra_X!, retaining the base change of c₀.
Source: Deligne, Weil II (1.1.14)
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
def compactPowerCohomology (c₀ : Compactification X₀.hom) (n : ℕ) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  sfIntrinsicCompactSupport (frobeniusCohomologyCompactification D X₀ c₀)
      (Padic.coefficientExtensionRing l E (n + 1)) ⋙
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory

/-- Direct power-r exchange, using the same model compactification for every r.
The recorded open-square theorem supplies both its Cartesian open square and the
semilinear projection equation for its proper square.
Source: Deligne, Weil II (1.1.10)--(1.1.14)
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
def compactPowerExchange (c₀ : Compactification X₀.hom) (n r : ℕ) :=
  finiteCompact l E (n + 1) (Nat.succ_pos n)
    (frobeniusCohomologyCompactification D X₀ c₀)
    ((End.of (galois D X₀)) ^ r)
    ((End.of (galois D
      (zlCompactificationMiddle D (frobeniusCohomologyModelMap D X₀) c₀))) ^ r)
    ((pointFrobeniusAut D) ^ r).hom
    ((D.frobenius_open_square X₀
      (zlCompactificationMiddle D (frobeniusCohomologyModelMap D X₀) c₀)
      (zlCompactificationOpen D (frobeniusCohomologyModelMap D X₀) c₀) r).2.2.2.trans
      (congrArg ((frobeniusCohomologyCompactification D X₀ c₀).g ≫ ·)
        (map_pow (Aut.toEnd _) (pointFrobeniusAut D) r).symm))
    (D.frobenius_open_square X₀
      (zlCompactificationMiddle D (frobeniusCohomologyModelMap D X₀) c₀)
      (zlCompactificationOpen D (frobeniusCohomologyModelMap D X₀) c₀) r).2.1

/-- The direct transport iota^(r) followed by Fib_s(e_r), in intrinsic coordinates.
The outside isomorphisms only identify the recorded tensor and intrinsic pullbacks.
Source: Deligne, Weil II (1.1.14), and the blueprint's finite-level iterate recipe
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
def compactPowerTransport (c₀ : Compactification X₀.hom) (n r : ℕ)
    (M : proEtaleDerivedCategory (D.geometricFiber X₀).left
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let F := sfIntrinsicCompactSupport (frobeniusCohomologyCompactification D X₀ c₀)
    (Padic.coefficientExtensionRing l E (n + 1))
  pointPowerTransportFinite D l hl E r n (F.obj M) ≫
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
      ((openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1))
        ((pointFrobeniusAut D) ^ r).hom).inv.app (F.obj M) ≫
        (compactPowerExchange D l E X₀ c₀ n r).app M ≫
        F.map ((openSquareDerivedPullbackModel
          (Padic.coefficientExtensionRing l E (n + 1))
          ((End.of (galois D X₀)) ^ r)).hom.app M))

/-- Canonical composite-to-iterated pullback identification, in intrinsic coordinates.
Its inverse is c_m in the statement; no comparison is chosen independently.
Source: Stacks 0D6D, normalized constant-coefficient specialization
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
def compactPowerPullbackStep (n m : ℕ) :
    compactPowerPullback D l E X₀ n (m + 1) ≅
      compactPowerPullback D l E X₀ n m ⋙ compactPowerPullback D l E X₀ n 1 :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  eqToIso (congrArg (finiteDerivedPullback l E n) (pow_succ (End.of (galois D X₀)) m)) ≪≫
    (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1))
      ((galois D X₀) ≫ ((End.of (galois D X₀)) ^ m))).symm ≪≫
    integralFiniteCanonicalPullbackComposition l E
      (galois D X₀) ((End.of (galois D X₀)) ^ m) n ≪≫
    Functor.isoWhiskerRight
      (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1))
        ((End.of (galois D X₀)) ^ m)) _ ≪≫
    Functor.isoWhiskerLeft _
      (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1))
        (galois D X₀)) ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (congrArg (finiteDerivedPullback l E n)
      (pow_one (End.of (galois D X₀))))).symm

/-- Direct compact-support transports compose under the inverse canonical pullback
comparison, with no Weil structure on M.
Source: Deligne, Weil II (1.1.10)--(1.1.14), printed pp. 151--153; blueprint
`lem-trf-frobenius-operator-compact-description`, m-th-iterate clause
(blueprint: lem-trf-compact-frobenius-transport-composition).

Proof:
1. Keep c₀ fixed and write F = Rp_* j_!, B_r = L(g-bar^r)^*. The Frobenius
   squares are Cartesian; their powers commute by induction. Horizontal powers
   are isomorphisms, so their squares are Cartesian too. Isomorphism pullback
   preserves bounded constructibility, so the degree-one transport at P_m M exists.
2. Specialize lem-trf-pullback-coefficient-iterate-coherence to p and the two
   geometric Frobenii. Invert its comparison equation to obtain the pasting law
   for the left square comparisons, with canonical base and middle compositors.
3. Apply lem-trf-point-transport-composition to N = F M. This gives composition
   of the explicit restriction-colimit-insertion point transports and naturality
   at every derived morphism, using the same coefficient ring and point Frobenius.
4. Apply lem-weil-pbc-mate-pasting to the proper square followed by itself.
   Use lem-weil-pbc-mate-whisker to insert the base and middle compositors.
   Taking mates gives the corresponding identity for the proper exchange u_r.
5. Use lem-trf-open-square-exchange pasting for v_r and substitute e_r = R(v_r)u_r.
   Naturality of u_1 at v_m moves the open factor across it. The result is
   e_(m+1)t_m = F(c_m)e_1 Q_1(e_m).
6. Naturality of point transport at e_m moves Fib(e_m) past iota_1. Substitute
   Step 5 and then point-transport composition from Step 3. Functoriality yields
   exactly tau_m followed by tau_1 at P_m M followed by H(c_m) = tau_(m+1).
7. For a different specified compact-support representative conjugate each e_r
   by its comparison with F. Point naturality conjugates tau_r by Fib of that
   comparison. Intermediate comparisons cancel; naturality at c_m identifies
   the final factors. Thus the same identity holds in that representative.
No map P_1 M to M is used. -/
theorem compact_frobenius_transport_composition (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom]
    (C : D.CoefficientDatum) (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (c₀ : Compactification X₀.hom) (n : ℕ)
    (M : (intrinsicFiniteTorsionConstructible C.l (Coefficient.{u} C.l C.Qbar F)
      (n + 1) (Nat.succ_pos n) (D.geometricFiber X₀).left).FullSubcategory)
    (m : ℕ) (hm : 1 ≤ m) :
    compactPowerTransport D C.l C.different (Coefficient.{u} C.l C.Qbar F)
        X₀ c₀ n (m + 1) M.obj =
      compactPowerTransport D C.l C.different (Coefficient.{u} C.l C.Qbar F)
          X₀ c₀ n m M.obj ≫
        compactPowerTransport D C.l C.different (Coefficient.{u} C.l C.Qbar F)
          X₀ c₀ n 1
          ((compactPowerPullback D C.l (Coefficient.{u} C.l C.Qbar F) X₀ n m).obj M.obj) ≫
        (compactPowerCohomology D C.l (Coefficient.{u} C.l C.Qbar F) X₀ c₀ n).map
          ((compactPowerPullbackStep D C.l (Coefficient.{u} C.l C.Qbar F)
            X₀ n m).inv.app M.obj) := by
  sorry

end WeilConjectures
