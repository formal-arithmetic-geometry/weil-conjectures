/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.TraceFormulaFrobeniusOperators
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
public import WeilConjectures.ZetaSeries

/-! Derived transport and conjugacy block for local Frobenius conjugacy.
(blueprint: lem-trf-local-frobenius-conjugacy) -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace WeilConjectures.CondensedFrobeniusOperators
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
variable (F : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of F.k₀)))
  [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)

/-- Native perfectness, transport composition, and the orbit-local operator equation.
Source: proof steps 3--8 of the local Frobenius conjugacy blueprint.
(blueprint: lem-trf-local-frobenius-conjugacy-transport)

Proof: pull the bounded constructible finite-Tor carrier back to each geometric point
and apply scalar sections. Point perfectness gives finite-projective bounded complexes.
The derived pullback compositor and insertion satisfy their identity and associativity
laws because both are induced by the same pointed-neighbourhood section maps.
Naturality and the owning Weil-iterate cocycle give the displayed transport addition law.
At a divisible return the normalized absolute-Frobenius trivialization removes the
source field reparametrization, so the local operator is the circuit transport.
Expand the two equal lengths i+m and m+i by the cocycle, use periodicity of the
geometric point, and cancel the invertible i-segment to obtain the operator equation.
-/
theorem local_frobenius_conjugacy_transport (hEll : ell ≠ F.p)
    (K : FiniteStrictWeilComplex F Y₀ ell E n hn)
    (x : Y₀.left) (_hx : IsClosed ({x} : Set Y₀.left))
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (_hz : IsLocalFrobeniusLift F Y₀ x z)
    : letI : HasDerivedCategory.{u + 1}
        (ModuleCat.{u + 1} (condensedScalarRing (finiteCoefficient ell E n))) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    ∃ (hP : ∀ i : ℕ, DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
        ((localFrobeniusFibre F Y₀ ell E n (localFrobeniusOrbit F Y₀ z i)).obj K.carrier.obj))
      (hP₀ : DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
        ((localFrobeniusFibre F Y₀ ell E n z).obj K.carrier.obj)),
      HEq (localFrobeniusTransport F Y₀ ell E n hn K z 0).hom
        (𝟙 ((localFrobeniusFibre F Y₀ ell E n z).obj K.carrier.obj)) ∧
      (∀ i j : ℕ,
        HEq (localFrobeniusTransport F Y₀ ell E n hn K z (i + j)).hom
          ((localFrobeniusTransport F Y₀ ell E n hn K (localFrobeniusOrbit F Y₀ z i) j).hom ≫
            (localFrobeniusTransport F Y₀ ell E n hn K z i).hom)) ∧
      (∀ (m : ℕ) (hm : 1 ≤ m), Y₀.hom.degreeOver x ∣ m → ∀ i : ℕ,
        ∀ (y₀ yᵢ : F.extensionPoints Y₀ m hm)
          (hy₀ : extensionPointGeometry F Y₀ m hm y₀ = z)
          (hyᵢ : extensionPointGeometry F Y₀ m hm yᵢ = localFrobeniusOrbit F Y₀ z i),
        localFrobeniusAtLift F Y₀ ell E n hn hEll K m hm yᵢ _ hyᵢ =
          (localFrobeniusTransport F Y₀ ell E n hn K z i).hom ≫
            localFrobeniusAtLift F Y₀ ell E n hn hEll K m hm y₀ z hy₀ ≫
            (localFrobeniusTransport F Y₀ ell E n hn K z i).inv) := by
  sorry

end WeilConjectures.CondensedFrobeniusOperators
