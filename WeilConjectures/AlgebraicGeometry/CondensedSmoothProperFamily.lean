/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedConstantGlobalFrobenius
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
import WeilConjectures.WeilSheaf.Finiteness
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientCompatibility

/-! # The smooth proper family with pulled-back condensed coefficients

Source: latest blueprint, def-weil-smooth-proper-cohomological-family
(blueprint: def-weil-smooth-proper-cohomological-family).

These are actual terminal-section cohomology modules, with transport followed by the unit
Weil structure. Q_l and Qbar_l use their published condensed rings. Finiteness needed to form
characteristic polynomials is separated into named proof obligations, never assumed as data.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedConstant

/-- A global constant scalar evaluated on the terminal profinite object.
Source: latest blueprint, Lambda(*)-linear coefficient cohomology
(blueprint: def-weil-smooth-proper-cohomological-family). -/
def scalarEvaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : CategoryTheory.MonObj.Γ Λ →+* condensedScalarRing Λ :=
  InternalAbelianSheafModule.sectionGlobalEval.{u + 1, u + 1, u}
    (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})

/-- The canonical Q_l scalar inclusion into condensed terminal sections.
Source: latest blueprint, Q_l coefficients
(blueprint: def-weil-smooth-proper-cohomological-family). -/
def qlScalars (ell : ℕ) [Fact ell.Prime] :
    Padic ell →+* condensedScalarRing (Profinite.continuousMapRingObj.{u} (Padic ell)) :=
  (scalarEvaluation _).comp (Profinite.continuousMapConstRingHom (Padic ell))

/-- The canonical Qbar_l scalar inclusion into bounded condensed terminal sections.
Source: latest blueprint, scalar-extended family
(blueprint: def-weil-smooth-proper-cohomological-family). -/
def qbarScalars (ell : ℕ) [Fact ell.Prime] :
    PadicAlgCl ell →+* condensedScalarRing (Profinite.padicAlgClRingObj.{u} ell) :=
  (scalarEvaluation _).comp (Profinite.PadicAlgCl.constRingHom ell)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {R : Type} [CommRing R] (rho : R →+* condensedScalarRing Λ)

/-- Terminal-section coefficient cohomology, with the specified constant scalar action.
This is H^i RΓ = H^i Fib_s Ra_* of the recorded cohomology convention.
Source: latest blueprint, V_i = H^i(X,Lambda)
(blueprint: def-weil-smooth-proper-cohomological-family). -/
def cohomology (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (i : ℤ) : ModuleCat.{u + 1} R :=
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (condensedScalarRing Λ)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _
  (ModuleCat.restrictScalars rho).obj
    ((DerivedCategory.homologyFunctor.{u + 1}
      (ModuleCat.{u + 1} (condensedScalarRing Λ)) i).obj
      ((CondensedRing.CohomologyTransport.Γ Λ (Spec (.of D.k))).obj
        ((CondensedRing.CohomologyTransport.R Λ (D.geometricFiber X₀).hom).obj
          (unit Λ _))))

/-- The global geometric Frobenius acting on actual coefficient cohomology.
Source: latest blueprint, F_i = F restricted to V_i
(blueprint: def-weil-smooth-proper-cohomological-family). -/
def frobenius (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (i : ℤ) : Module.End R (cohomology Λ rho D X₀ i) :=
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (condensedScalarRing Λ)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _
  ((ModuleCat.restrictScalars rho).map
    ((DerivedCategory.homologyFunctor.{u + 1}
      (ModuleCat.{u + 1} (condensedScalarRing Λ)) i).map (ordinary Λ D X₀))).hom

/-- Q_l ordinary cohomology of the condensed coefficient unit.
Source: latest blueprint, V_{i,ell} (blueprint: def-weil-smooth-proper-cohomological-family).
-/
abbrev qlCohomology (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (i : ℤ) :=
  cohomology (Profinite.continuousMapRingObj (Padic ell)) (qlScalars ell) D X₀ i

/-- Qbar_l ordinary cohomology of the pulled-back bounded condensed coefficient unit.
Source: latest blueprint, scalar extension (blueprint: def-weil-smooth-proper-cohomological-family).
-/
abbrev qbarCohomology (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (i : ℤ) :=
  cohomology (Profinite.padicAlgClRingObj ell) (qbarScalars ell) D X₀ i

/-- The Q_l finiteness proof required by the determinant definition.
Source: latest blueprint, family and prop-cohomological-finiteness
(blueprint: def-weil-smooth-proper-cohomological-family).
Proof: apply cohomological finiteness to the constant Q_l Weil sheaf on the proper
geometric fibre. The recorded point equivalence identifies terminal sections with its
coefficient module. The empty scheme gives the zero module. -/
theorem qlFinite (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (d : ℕ) (hSmooth : D.IsSmoothOfPureDimension X₀ d) (i : ℤ) :
    Module.Finite (Padic ell) (qlCohomology ell D X₀ i) := by
  sorry

/-- The actual Q_l Frobenius determinant polynomial in degree i.
Source: latest blueprint, P_{i,ell} (blueprint: def-weil-smooth-proper-cohomological-family).
-/
def qlPolynomial (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (d : ℕ) (hSmooth : D.IsSmoothOfPureDimension X₀ d) (i : ℤ) : Polynomial (Padic ell) :=
  letI := qlFinite ell D hEll X₀ d hSmooth i
  (frobenius (Profinite.continuousMapRingObj (Padic ell)) (qlScalars ell) D X₀ i).charpolyRev

end WeilConjectures.CondensedConstant
