/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.CategoryTheory.ContinuousScalarRing
public import Sheaf.Topology.LadicLattice
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Shared data for the homogeneous polynomial augmented resolution

The definitions from `HomogeneousPolynomialAugmentedResolution` are retained verbatim.
They specify the monomial coproducts, substitution maps, equivariant complex,
underlying contraction, and assertion, without choosing any unproved witness.
(blueprint: def-sfb-homogeneous-polynomial-resolution-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (continuousScalarRing)

namespace Profinite.CondensedAction.HomogeneousPolynomial

/-- Interpret a finite integer polynomial as a linear combination of coprojections.
Source: homogeneous polynomial reduction, finite monomial sums
(blueprint: lem-sfb-homogeneous-polynomial-augmented-resolution). -/
def polynomialArrow (A : CategoryTheory.CondensedBar.Ring.{u}) (r b : ℕ)
    (M : CategoryTheory.CondensedBar.Modules A)
    (ι : ((Fin b × Fin r) →₀ ℕ) → (Mod.regular A.X ⟶ M))
    (p : MvPolynomial (Fin b × Fin r) ℤ) : Mod.regular A.X ⟶ M :=
  ∑ m ∈ p.support, p.coeff m • ι m

/-- Alternately omit each of the n+2 blocks, in the displayed order.
Source: homogeneous polynomial reduction, displayed differential
(blueprint: lem-sfb-homogeneous-polynomial-augmented-resolution). -/
def deletion (r n : ℕ) (p : MvPolynomial (Fin (n + 1) × Fin r) ℤ) :
    MvPolynomial (Fin (n + 2) × Fin r) ℤ :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    MvPolynomial.rename (fun v ↦ (i.succAbove v.1, v.2)) p

/-- Insert the zero tuple before the remaining blocks.
Source: homogeneous polynomial reduction, displayed h in positive degrees
(blueprint: lem-sfb-homogeneous-polynomial-augmented-resolution). -/
def insertZero (r n : ℕ) (p : MvPolynomial (Fin (n + 2) × Fin r) ℤ) :
    MvPolynomial (Fin (n + 1) × Fin r) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v ↦ Fin.cases 0 (fun j ↦ MvPolynomial.X (j, v.2)) v.1) p

variable (ell : ℕ) [Fact ell.Prime] (F : Type u) [NormedField F]
  [NormedAlgebra ℚ_[ell] F] (r : ℕ)

/-- Diagonal substitution y_(a,i) maps to y_(a,i)-g_i for every continuous lattice section.
Source: homogeneous polynomial reduction, diagonal action
(blueprint: lem-sfb-homogeneous-polynomial-augmented-resolution). -/
def translatedMonomial (n : ℕ) (S : Profinite.{u})
    (g : C(S, Profinite.LadicLattice.Lattice.{u} ell r))
    (m : (Fin (n + 1) × Fin r) →₀ ℕ) :
    MvPolynomial (Fin (n + 1) × Fin r) C(S, F) :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v ↦ MvPolynomial.X v - MvPolynomial.C
      (⟨fun s ↦ algebraMap ℚ_[ell] F ((g s).toAdd.down v.2 : ℚ_[ell]),
        by fun_prop⟩ : C(S, F))) (MvPolynomial.monomial m 1)

/-- The equivariant polynomial complex, pinned by its coproducts, differential and
sectionwise action, with its constant augmentation. Negative degrees are zero objects.
The cochain complex and its morphism fields include d squared zero and equivariance.
Source: homogeneous polynomial reduction, construction and augmentation
(blueprint: lem-sfb-homogeneous-polynomial-augmented-resolution). -/
structure Model where
  /-- The ordinary equivariant cochain complex. -/
  cochain : CochainComplex (CategoryTheory.CondensedBar.Equivariant (continuousScalarRing F)
    (Profinite.LadicLattice.Lattice.{u} ell r)) ℤ
  /-- Extension by zero in negative degrees. -/
  negative : ∀ i : ℤ, i < 0 → IsZero (cochain.X i)
  /-- The specified monomial copies of the regular internal A-module. -/
  ι : ∀ n : ℕ, ((Fin (n + 1) × Fin r) →₀ ℕ) →
    (Mod.regular (continuousScalarRing F).X ⟶ (cochain.X (n : ℤ)).module)
  /-- Exactly the internal direct sum, in every nonnegative degree. -/
  isColimit : ∀ n : ℕ, IsColimit (Cofan.mk (cochain.X (n : ℤ)).module (ι n))
  /-- The full action formula, with parameter-dependent g and every coefficient c. -/
  translation : ∀ (n : ℕ) (S : Profinite.{u})
    (g : C(S, Profinite.LadicLattice.Lattice.{u} ell r))
    (m : (Fin (n + 1) × Fin r) →₀ ℕ) (c : ULift.{u + 1} C(S, F)),
    (cochain.X (n : ℤ)).act S g (((ι n m).hom.hom.app (op S)) c) =
      ∑ e ∈ (translatedMonomial ell F r n S g m).support,
        ((ι n e).hom.hom.app (op S))
          (ULift.up ((translatedMonomial ell F r n S g m).coeff e) * c)
  /-- Each individual block omission is an equivariant internal linear map. -/
  face : ∀ (n : ℕ), Fin (n + 2) →
    (cochain.X (n : ℤ) ⟶ cochain.X ((n + 1 : ℕ) : ℤ))
  /-- Coordinate omission, specified on the generating monomials. -/
  face_formula : ∀ (n : ℕ) (i : Fin (n + 2))
    (m : (Fin (n + 1) × Fin r) →₀ ℕ),
    ι n m ≫ (face n i).val =
      polynomialArrow (continuousScalarRing F) r (n + 2)
        (cochain.X ((n + 1 : ℕ) : ℤ)).module (ι (n + 1))
        (MvPolynomial.rename (fun v ↦ (i.succAbove v.1, v.2))
          (MvPolynomial.monomial m 1))
  /-- Alternating deletion on every monomial, determining the entire differential. -/
  differential : ∀ (n : ℕ) (m : (Fin (n + 1) × Fin r) →₀ ℕ),
    ι n m ≫ (cochain.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).val =
      polynomialArrow (continuousScalarRing F) r (n + 2)
        (cochain.X ((n + 1 : ℕ) : ℤ)).module (ι (n + 1))
        (deletion r n (MvPolynomial.monomial m 1))
  /-- The augmentation from the regular coefficient module with trivial action. -/
  augmentation :
    ((CochainComplex.singleFunctor _ 0).obj
      ((trivial (R := (continuousScalarRing F).toMon)
        (P := Profinite.LadicLattice.Lattice.{u} ell r)).obj
          (Mod.regular (continuousScalarRing F).X))) ⟶ cochain
  /-- In degree zero the augmentation includes the constant monomial. -/
  augmentation_zero :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      ((trivial (R := (continuousScalarRing F).toMon)
        (P := Profinite.LadicLattice.Lattice.{u} ell r)).obj
          (Mod.regular (continuousScalarRing F).X))).inv.val ≫
      (augmentation.f 0).val = ι 0 0

/-- The inserted-zero maps in the underlying internal-module category, with their
formulas and all augmented contraction identities. Internal maps commute with restriction.
No equivariance condition on these maps is imposed.
Source: homogeneous polynomial reduction, displayed h and contraction equations
(blueprint: lem-sfb-homogeneous-polynomial-augmented-resolution). -/
structure Contraction (P : Model ell F r) where
  /-- Evaluation of all r variables at zero in degree zero. -/
  h0 : (P.cochain.X 0).module ⟶ Mod.regular (continuousScalarRing F).X
  /-- Insertion of zero, from degree n+1 to degree n. -/
  h : ∀ n : ℕ, (P.cochain.X ((n + 1 : ℕ) : ℤ)).module ⟶
    (P.cochain.X (n : ℤ)).module
  /-- A monomial evaluates to one exactly when its exponent vector is zero. -/
  h0_formula : ∀ m : (Fin 1 × Fin r) →₀ ℕ,
    P.ι 0 m ≫ h0 = if m = 0 then 𝟙 _ else 0
  /-- Insertion of zero on the universal finite monomials. -/
  h_formula : ∀ (n : ℕ) (m : (Fin (n + 2) × Fin r) →₀ ℕ),
    P.ι (n + 1) m ≫ h n =
      polynomialArrow (continuousScalarRing F) r (n + 1)
        (P.cochain.X (n : ℤ)).module (P.ι n)
        (insertZero r n (MvPolynomial.monomial m 1))
  /-- h^0 a = 1 on coefficients. -/
  split : P.ι 0 0 ≫ h0 = 𝟙 _
  /-- a h^0 + h^1 delta^0 = 1 on degree zero. -/
  zero_identity : h0 ≫ P.ι 0 0 + (P.cochain.d 0 1).val ≫ h 0 = 𝟙 _
  /-- delta^(n-1) h^n + h^(n+1) delta^n = 1 in each positive degree. -/
  positive_identity : ∀ n : ℕ,
    h n ≫ (P.cochain.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).val +
      (P.cochain.d ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).val ≫ h (n + 1) = 𝟙 _

/-- The specified complex exists; every such presentation has the specified underlying
contraction, and its augmentation is a quasi-isomorphism and becomes an isomorphism in
its ordinary derived category. These are properties of pinned data, not arbitrary maps.
Source: homogeneous polynomial reduction, augmented resolution conclusion
(blueprint: lem-sfb-homogeneous-polynomial-augmented-resolution). -/
def Assertion : Prop :=
  Nonempty (Model ell F r) ∧ ∀ P : Model ell F r,
    Nonempty (Contraction ell F r P) ∧ QuasiIso P.augmentation ∧
      IsIso (DerivedCategory.Q.{u + 1}.map P.augmentation)

end Profinite.CondensedAction.HomogeneousPolynomial
