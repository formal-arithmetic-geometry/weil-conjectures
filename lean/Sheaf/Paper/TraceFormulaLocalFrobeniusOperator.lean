/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
public import Sheaf.Paper.FrobeniusPullbackComparisonCoherence
public import Sheaf.Paper.IteratedWeilMap
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.TraceFormulaStrictWeilComplex
public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.SchemeFrobenius
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
public import Sheaf.SixFunctors.SchemeGaloisComparison
public import Sheaf.TraceFormula.PointTransportComposition
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-!
# The finite-coefficient local Frobenius operator

Source: Weil conjectures blueprint, main-20261015, def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators).

This supplements the recorded etale cohomological operator with the local operator
on the intrinsic pro-etale ordinary-module complex, retaining rho, the specified kappa,
and the iterated Weil isomorphism separately. Point evaluation is exactly the ambient
functor whose constructible restriction is `pointFiniteFibre`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- Exact evaluation at the point, with precisely the localization universe of the
recorded point fibre. The sheaf category retains its standard larger localization.
Source: blueprint def-trf-frobenius-operators, clause 2, and def-weil-finite-coefficient-point
(blueprint: def-trf-frobenius-operators). -/
def finiteLocalSections (T : TraceFormulaCoefficientConventions.{u}) :
    proEtaleDerivedCategory (Spec (.of T.datum.k)) T.coefficientRing ⥤
      @DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _) :=
  @Functor.mapDerivedCategory
    (proEtaleRingModules (Spec (.of T.datum.k))
      (proEtaleConstantRing (Spec (.of T.datum.k)) T.coefficientRing)) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointFiniteSections T.datum.k T.coefficientRing)
    (pointFiniteSectionsAdditive T.datum.k T.coefficientRing)
    (pointFibreFiniteLimits T.datum T.coefficientRing)
    (pointFibreFiniteColimits T.datum T.coefficientRing)

/-- The stalk complex `Fib_s(Lz^*K)`, using exact sections at `s`.
Source: blueprint def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators). -/
def finiteLocalFibre (T : TraceFormulaCoefficientConventions.{u})
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange) :=
  proEtaleConstantRingDerivedPullback T.coefficientRing z ⋙
    T.finiteLocalSections

/-- The canonical fixed-point identification rho. Only equality of the scheme-Frobenius
translate is used; raw geometric Galois Frobenius need not fix z.
Source: blueprint def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators). -/
def finiteLocalRho (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ)
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange)
    (hz : z ≫ T.datum.schemeFrobeniusIterate T.X₀ m = z) :=
  T.finiteLocalSections.mapIso
    (eqToIso (congrArg
      (fun f ↦ (proEtaleConstantRingDerivedPullback T.coefficientRing f).obj K.obj.carrier)
      hz.symm) ≪≫
      (proEtaleConstantRingPullbackComposition z
        (T.datum.schemeFrobeniusIterate T.X₀ m) T.coefficientRing).symm.app K.obj.carrier)

/-- The local geometric Frobenius `Fib_s(Lz^* phi^[m])` after `Fib_s(Lz^* kappa)`
after rho, on the actual ordinary-module fibre complex. This formula applies to the
scalar-extended point of every rational point; no arbitrary transport is supplied.
Source: blueprint def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators). -/
def finiteLocalFrobenius (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ) (hm : 1 ≤ m)
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange)
    (hz : z ≫ T.datum.schemeFrobeniusIterate T.X₀ m = z) :
    (T.finiteLocalFibre z).obj K.obj.carrier ⟶ (T.finiteLocalFibre z).obj K.obj.carrier :=
  (T.finiteLocalRho K m z hz).hom ≫
    (T.finiteLocalFibre z).map (T.iteratedWeilSchemeFrobenius K m hm).hom

/-- The actual functor `H = Fib_s Ra_X!` on the ambient intrinsic derived category,
represented by the geometric base change of the retained compactification.
Source: blueprint def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def finiteGlobalCompactSections (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) :=
  sfIntrinsicCompactSupport (frobeniusCohomologyCompactification T.datum T.X₀ c₀)
    T.coefficientRing ⋙ T.finiteLocalSections

/-- Degree-one compact transport, in the canonical tensor-pullback coordinates.
Only the unit-normalized presentation comparison and `g^1 = g` are inserted.
Source: blueprint def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def finiteGlobalCompactStep (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) :
    (T.finiteGlobalCompactSections c₀).obj M ⟶
      (T.finiteGlobalCompactSections c₀).obj ((T.frobeniusPullbackPower 0).obj M) := by
  rcases T with ⟨D, C, E, n, hn, X, hft, hqc, hsep⟩
  cases n with
  | zero => omega
  | succ n =>
    let F := AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E
    exact frobeniusCompactTransportFinite D C.l C.different F X c₀ n M ≫
      (finiteGlobalCompactSections ⟨D, C, E, n + 1, hn, X⟩ c₀).map
        ((pointPowerPullbackModel C.l F n (D.geometricGaloisFrobenius X)).hom.app M ≫
          eqToHom (congrArg
            (fun f ↦ (proEtaleConstantRingDerivedPullback
              (Padic.coefficientExtensionRing C.l F (n + 1)) f).obj M)
            (pow_one (End.of (D.geometricGaloisFrobenius X))).symm))

/-- The repeated transport with exactly `r+1` factors; the index is the predecessor
of the positive exponent. No direct-power base-change map is used in this recursion.
Source: blueprint def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def finiteGlobalRepeatedTransport (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) :
    (r : ℕ) → (T.finiteGlobalCompactSections c₀).obj M ⟶
      (T.finiteGlobalCompactSections c₀).obj
        ((trfPositiveFunctorPower (T.frobeniusPullbackPower 0) r).obj M)
  | 0 => T.finiteGlobalCompactStep c₀ M
  | r + 1 => T.finiteGlobalRepeatedTransport c₀ M r ≫
      T.finiteGlobalCompactStep c₀
        ((trfPositiveFunctorPower (T.frobeniusPullbackPower 0) r).obj M)

/-- The first arrow `g_{gamma,c}^{m,*}` in the operator definition: repeated
transport followed by `H(d_m^{-1})`, where `m = r+1`.
Source: blueprint def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def finiteGlobalComparedTransport (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) (r : ℕ) :
    (T.finiteGlobalCompactSections c₀).obj M ⟶
      (T.finiteGlobalCompactSections c₀).obj ((T.frobeniusPullbackPower r).obj M) :=
  T.finiteGlobalRepeatedTransport c₀ M r ≫
    (T.finiteGlobalCompactSections c₀).map ((T.frobeniusPullbackPowerComparison r).inv.app M)

/-- The global operator `F_{c,K}^{m}` on the compact-support coefficient complex,
with `m = r+1`: the specified repeated transport followed by `H(phi^[m])`.
Source: blueprint def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def finiteGlobalFrobenius (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) (K : T.strictWeilComplex) (r : ℕ) :
    End ((T.finiteGlobalCompactSections c₀).obj K.obj.carrier) :=
  T.finiteGlobalComparedTransport c₀ K.obj.carrier r ≫
    (T.finiteGlobalCompactSections c₀).map
      (T.iteratedWeilIsomorphism K (r + 1) (Nat.succ_le_succ (Nat.zero_le r))).hom

/-- The induced endomorphism of compact-support cohomology in every integer degree.
Source: blueprint def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def finiteGlobalFrobeniusCohomology (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) (K : T.strictWeilComplex) (r : ℕ) (i : ℤ) :=
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  (DerivedCategory.homologyFunctor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) i).map
      (T.finiteGlobalFrobenius c₀ K r)

end WeilConjectures.TraceFormulaCoefficientConventions
