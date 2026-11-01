/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.TraceFormulaLocalFrobeniusOperator
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.FrobeniusRationalPointFixed
public import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections

/-! # Global and local finite-coefficient geometric Frobenius operators

Source: latest blueprint, sec-smooth-purity/sk-cor-sp-all-coefficients/
def-trf-frobenius-operators.md, clauses 1 and 2
(blueprint: def-trf-frobenius-operators).

The strict Weil category, its iterated isomorphism, the canonical comparison kappa,
and the local stalk construction are reused. Global transport is the direct
isomorphism along g^m, including restriction along Spec(gamma^m) on the base.
The retained model compactification represents the specified compact-support functor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- The specified first arrow g_(gamma,c)^(m,*), using the actual power square.
The helper constructs iota_(b_m) followed by Fib_s(e_!), with no implicit
identification of the semilinear base automorphism with the identity.
Source: latest blueprint, def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def globalCompactFrobeniusTransport (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) (K : T.strictWeilComplex)
    (m : ℕ) (_hm : 1 ≤ m) :
    (T.finiteGlobalCompactSections c₀).obj K.obj.carrier ≅
      (T.finiteGlobalCompactSections c₀).obj
        ((proEtaleConstantRingDerivedPullback T.coefficientRing
          ((End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ m)).obj K.obj.carrier) :=
  letI := T.finitePowerCompactTransport_isIso c₀ m K.obj.carrier
  asIso (T.finitePowerCompactTransport c₀ m K.obj.carrier)

/-- The global compact-support coefficient-complex endomorphism
F_(c,K)^m = RΓ_c(phi^[m]) after g_(gamma,c)^(m,*).
Source: latest blueprint, def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def globalCompactFrobenius (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) (K : T.strictWeilComplex)
    (m : ℕ) (hm : 1 ≤ m) :
    End ((T.finiteGlobalCompactSections c₀).obj K.obj.carrier) :=
  (T.globalCompactFrobeniusTransport c₀ K m hm).hom ≫
    (T.finiteGlobalCompactSections c₀).map (T.iteratedWeilIsomorphism K m hm).hom

/-- The induced operator on H_c^i, for every integer i, including negative degrees.
Source: latest blueprint, def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def globalCompactFrobeniusCohomology (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) (K : T.strictWeilComplex)
    (m : ℕ) (hm : 1 ≤ m) (i : ℤ) :=
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  (DerivedCategory.homologyFunctor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) i).map
      (T.globalCompactFrobenius c₀ K m hm)

/-- The canonical stalk transport tau_(x,m): rho from Phi^m xbar = xbar, followed
by Fib_s(Lxbar^* kappa^(m)). The fibre functor is exact terminal sections of the
pullback to Spec k, not the unevaluated sheaf-module complex on Spec k.
Source: latest blueprint, def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators). -/
def localFrobeniusTransport (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ) (hm : 1 ≤ m)
    (x : T.datum.extensionPoints T.X₀ m hm) :
    (T.finiteLocalFibre (localExtensionPoint T.datum T.X₀ m hm x)).obj K.obj.carrier ≅
      (T.finiteLocalFibre (localExtensionPoint T.datum T.X₀ m hm x)).obj
        ((proEtaleConstantRingDerivedPullback T.coefficientRing
          ((End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ m)).obj K.obj.carrier) :=
  T.finiteLocalRho K m (localExtensionPoint T.datum T.X₀ m hm x)
      (rationalPoint_schemeFrobenius_fixed T.datum T.X₀ m hm x) ≪≫
    (T.finiteLocalFibre (localExtensionPoint T.datum T.X₀ m hm x)).mapIso
      ((T.selectedSchemeGaloisComparison T.X₀ m hm).app K.obj.carrier)

/-- The local Frobenius operator at the canonical geometric lift of x. This
specializes the existing rho-kappa-phi composite, without a new arbitrary map or
an extra fixed-point hypothesis. Thus it is Fib_s(Lxbar^* phi^[m]) after tau_(x,m).
Source: latest blueprint, def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators). -/
def localFrobeniusAtRationalPoint (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ) (hm : 1 ≤ m)
    (x : T.datum.extensionPoints T.X₀ m hm) :
    End ((T.finiteLocalFibre (localExtensionPoint T.datum T.X₀ m hm x)).obj K.obj.carrier) :=
  T.finiteLocalFrobenius K m hm (localExtensionPoint T.datum T.X₀ m hm x)
    (rationalPoint_schemeFrobenius_fixed T.datum T.X₀ m hm x)

end WeilConjectures.TraceFormulaCoefficientConventions
