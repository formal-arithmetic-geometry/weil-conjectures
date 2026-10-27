/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.NormalCrossingsDivisor
public import WeilConjectures.RingTheory.PthRootAlgebraLocal
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.SNCBoundaryParameterCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import WeilConjectures.RingTheory.StrictHenselizationRegular
import WeilConjectures.RingTheory.StrictHenselizationCotangentDimension
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Sheaf.RingTheory.HenselianLocalTargetEtaleMaps
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.Galois.Basic

/-! # Tame inertia as a quotient of a parameter-root group

Source: ILO, Travaux de Gabber, IX Proposition 2.1(i)--(iii), pp.133--134,
and VI 2.2--2.3, pp.72--73 (blueprint: lem-per-tame-inertia-snc-root-quotient).
The affine neighbourhood W is written directly as Spec S, where S is the invariant
subalgebra of the simultaneous-root algebra. The strict-local comparison extends this
same affine presentation. All diagonal actions are specified on coefficients and roots.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace AlgebraicGeometry

/-- A tame finite quotient of a normal Noetherian scheme over a regular normal-crossings
pair has an etale-local parameter-root invariant presentation. On strict localizations,
the quotient root group identifies with the actual geometric inertia action.
Source: ILO IX 2.1(i)--(iii), pp.133--134; VI 2.2--2.3, pp.72--73
(blueprint: lem-per-tame-inertia-snc-root-quotient).

Proof:
1. Use lem-trf-nc-subboundary-branch-atlas to choose boundary parameters and
   lem-per-finite-quotient-inertia-slice to replace the quotient locally by its H-slice.
   Invert only |H|. Etale preservation of parameters and
   lem-sfb-snc-boundary-parameter-criterion give the required boundary chart.
2. The finite normal slice is the normalization in its fraction field: an element
   integral over the base is integral over the normal slice ring. Apply
   lem-per-snc-parameter-root-quotient, preserving the chosen parameters, and compose
   the pointed etale neighbourhood maps (lem-weil-pbc-etale-composition-cancellation).
3. Pass to strict localizations using lem-trf-ind-etale-strict-local-invariance.
   Their base is regular by lem-sc-strict-henselization-regular; the parameter positions
   persist by lem-sc-strict-henselization-cotangent-dimension. Apply
   lem-per-snc-root-algebra-structure to the simultaneous root algebra over this base.
4. Monic division gives the monomial basis. Each rotation acts diagonally on it;
   the unit differences 1-zeta^a kill every coefficient with nontrivial K-character.
   The surviving monomials freely span the invariants, and this commutes with extension
   to the strict-local base.
5. The invariant ring C is a domain, and integrality of the root algebra over C,
   lying over, and maximality above maximal ideals make C local. Its residue field
   equals that of the strictly henselian root algebra. The finite henselian product
   theorem makes C henselian, hence strictly henselian. The henselian-local-target
   etale-map bijection identifies its own strict localization with C. Thus C is the
   actual strict-local ring of Z and the comparison extends the affine presentation.
6. Multiplying denominators over a finite group identifies fraction fields of
   invariants with fixed fields. The faithful H-action has fixed fraction field F;
   lem-wf-finite-field-action-fixed-degree and the finite Galois fixed-field theorem
   identify H with the full automorphism group of that fraction field over F.
7. The root group is abelian. Apply lem-per-finite-galois-normal-fixed-quotient:
   restriction identifies Gamma/K with the automorphisms of its fixed field.
   Compare with the actual H-action from step 6. Equality on fraction fields implies
   equality on the invariant subrings, giving the displayed equivariance. With no
   parameters the root group is trivial and the strict-local cover is the identity.
-/
theorem exists_tame_inertia_snc_root_quotient
    (Y Z : Scheme.{u}) [IsNoetherian Y] [IsNoetherian Z]
    (hY : IsRegularScheme Y)
    (D : Y.IdealSheafData) (hD : D.IsNormalCrossingsDivisor)
    (hred : ∀ U : Y.affineOpens, (D.ideal U).IsRadical)
    (G : Type v) [Group G] [Finite G] (a : G →* Aut Z)
    (q : Z ⟶ Y) [IsFinite q] [Surjective q]
    (hnormal : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
      IsIntegrallyClosed (Z.presheaf.stalk z))
    (hinvariant : ∀ g : G, (a g).hom ≫ q = q)
    (hsheaf : ∀ U : Y.Opens, Function.Injective (q.app U).hom ∧
      ∀ s : Γ(Z, q ⁻¹ᵁ U), s ∈ Set.range (q.app U).hom ↔
        ∀ (g : G) (V : Z.Opens) (hV : V ≤ q ⁻¹ᵁ U)
          (hVg : V ≤ (a g).hom ⁻¹ᵁ (q ⁻¹ᵁ U)),
          ((a g).hom.appLE (q ⁻¹ᵁ U) V hVg).hom s =
            (Z.presheaf.map (homOfLE hV).op).hom s)
    (horbits : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (z₁ z₂ : Spec (.of Ω) ⟶ Z), z₁ ≫ q = z₂ ≫ q →
        ∃ g : G, z₁ ≫ (a g).hom = z₂)
    (hfree : ∃ V : Z.Opens, Dense (V : Set Z) ∧
      (∀ (g : G) (z : Z), (a g).hom z ∈ V ↔ z ∈ V) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Z) (g : G),
        z (IsLocalRing.closedPoint Ω) ∈ V → z ≫ (a g).hom = z → g = 1)
    (hetale : Etale (q ∣_ D.support.compl))
    (htame : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Z),
      IsUnit (Nat.card {g : G // z ≫ (a g).hom = z} : Ω))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Z)
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ z ≫ (a g).hom = z) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A)
      (e : Spec (.of A) ⟶ Y) (yT : Spec (.of Ω) ⟶ Spec (.of A)),
      Etale e ∧ yT ≫ e = z ≫ q ∧
      ∃ (n r : ℕ) (t : Fin r → A) (ζ : Aˣ),
        0 < n ∧ IsUnit (n : A) ∧ (ζ : A) ^ n = 1 ∧
        (∀ b : ℕ, 0 < b → b < n → IsUnit (1 - (ζ : A) ^ b)) ∧
        (∃ s : List (Localization.AtPrime
            (yT (IsLocalRing.closedPoint Ω)).asIdeal),
          IsLocalRing.IsRegularSystemOfParameters s ∧
            (List.ofFn (fun i : Fin r ↦ algebraMap A
              (Localization.AtPrime (yT (IsLocalRing.closedPoint Ω)).asIdeal) (t i))).Sublist s) ∧
        e ⁻¹ᵁ D.support.compl = PrimeSpectrum.basicOpen (∏ i, t i) ∧
        ∃ (K : Subgroup (Multiplicative (Fin r → ZMod n)))
          (ρ : Multiplicative (Fin r → ZMod n) →*
            (Algebra.pthRootAlgebra n r A t ≃ₐ[A] Algebra.pthRootAlgebra n r A t))
          (S : Subalgebra A (Algebra.pthRootAlgebra n r A t)),
          (∀ (g : Multiplicative (Fin r → ZMod n)) (i : Fin r),
            ρ g (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
              algebraMap A _ ((ζ : A) ^ (Multiplicative.toAdd g i).val) *
                Ideal.Quotient.mk _ (MvPolynomial.X i)) ∧
          (∀ b : Algebra.pthRootAlgebra n r A t,
            b ∈ S ↔ ∀ k : K, ρ k.val b = b) ∧
          ∃ (w : Spec (.of S) ⟶ Z) (zW : Spec (.of Ω) ⟶ Spec (.of S)),
            Etale w ∧ zW ≫ w = z ∧
            Spec.map (CommRingCat.ofHom (algebraMap A S)) ≫ e = w ≫ q ∧
            zW ≫ Spec.map (CommRingCat.ofHom (algebraMap A S)) = yT ∧
            ∃ (c : A →+* Scheme.strictHenselizationRing (z ≫ q)),
              Spec.map (CommRingCat.ofHom c) ≫ e =
                Scheme.strictHenselizationStructuralMap (z ≫ q) ∧
              Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation (z ≫ q))) ≫
                Spec.map (CommRingCat.ofHom c) = yT ∧
              ∃ (ρR : Multiplicative (Fin r → ZMod n) →*
                  (Algebra.pthRootAlgebra n r (Scheme.strictHenselizationRing (z ≫ q))
                      (fun i ↦ c (t i)) ≃ₐ[
                    Scheme.strictHenselizationRing (z ≫ q)]
                    Algebra.pthRootAlgebra n r (Scheme.strictHenselizationRing (z ≫ q))
                    (fun i ↦ c (t i))))
                (C : Subalgebra (Scheme.strictHenselizationRing (z ≫ q))
                  (Algebra.pthRootAlgebra n r (Scheme.strictHenselizationRing (z ≫ q))
                    (fun i ↦ c (t i))))
                (j : Algebra.pthRootAlgebra n r A t →+*
                  Algebra.pthRootAlgebra n r (Scheme.strictHenselizationRing (z ≫ q))
                    (fun i ↦ c (t i)))
                (jS : S →+* C) (ι : C ≃+* Scheme.strictHenselizationRing z)
                (θ : (Multiplicative (Fin r → ZMod n) ⧸ K) ≃* H)
                (α : H → (Scheme.strictHenselizationRing z ≃+*
                  Scheme.strictHenselizationRing z)),
                (∀ (g : Multiplicative (Fin r → ZMod n)) (i : Fin r),
                  ρR g (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
                    algebraMap _ _ (c ((ζ : A) ^ (Multiplicative.toAdd g i).val)) *
                      Ideal.Quotient.mk _ (MvPolynomial.X i)) ∧
                (∀ b : Algebra.pthRootAlgebra n r (Scheme.strictHenselizationRing (z ≫ q))
                    (fun i ↦ c (t i)),
                  b ∈ C ↔ ∀ k : K, ρR k.val b = b) ∧
                (∀ b : A, j (algebraMap A _ b) = algebraMap _ _ (c b)) ∧
                (∀ i : Fin r, j (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
                  Ideal.Quotient.mk _ (MvPolynomial.X i)) ∧
                (∀ b : S,
                  (jS b : Algebra.pthRootAlgebra n r (Scheme.strictHenselizationRing (z ≫ q))
                    (fun i ↦ c (t i))) = j b) ∧
                Spec.map (CommRingCat.ofHom ι.toRingHom) ≫
                  Spec.map (CommRingCat.ofHom (algebraMap _ C)) =
                    Scheme.strictHenselizationMap q z ∧
                Spec.map (CommRingCat.ofHom ι.toRingHom) ≫
                  Spec.map (CommRingCat.ofHom jS) ≫ w =
                    Scheme.strictHenselizationStructuralMap z ∧
                Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation z)) ≫
                  Spec.map (CommRingCat.ofHom ι.toRingHom) ≫
                    Spec.map (CommRingCat.ofHom jS) = zW ∧
                (∀ h : H,
                  Spec.map (CommRingCat.ofHom (α h).toRingHom) ≫
                    Scheme.strictHenselizationStructuralMap z =
                      Scheme.strictHenselizationStructuralMap z ≫ (a h.val).hom) ∧
                (∀ h : H, (Scheme.strictHenselizationPointEvaluation z).comp
                  (α h).toRingHom = Scheme.strictHenselizationPointEvaluation z) ∧
                (∀ (g : Multiplicative (Fin r → ZMod n)) (b : C),
                  ρR g b = ((ι.symm (α (θ (QuotientGroup.mk g)) (ι b)) : C) :
                    Algebra.pthRootAlgebra n r (Scheme.strictHenselizationRing (z ≫ q))
                    (fun i ↦ c (t i)))) ∧
                (r = 0 → Subsingleton H ∧ IsIso (Scheme.strictHenselizationMap q z)) := by
  sorry

end AlgebraicGeometry
