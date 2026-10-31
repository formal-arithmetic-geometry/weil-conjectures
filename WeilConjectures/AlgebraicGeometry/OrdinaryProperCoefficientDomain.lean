/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded
public import WeilConjectures.AlgebraicGeometry.InternalDerivedScalarComparisons
public import WeilConjectures.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude

/-! # Domains for ordinary proper coefficient exchange

Source: Bhatt--Scholze, sections 6.7--6.8; Stacks 095T and 0GL6.
(blueprint: def-pur-ordinary-proper-coefficient-domain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.OrdinaryProper
open CondensedRing QuotientChange WeilConjectures.SixFunctors

/-- Use the commutativity carried by the existing bundled coefficient ring.
Source: tensor ring objects (blueprint: def-pur-ordinary-proper-coefficient-domain). -/
instance coefficientComm (Λ : ScalarSixRing.{u}) : IsCommMonObj Λ.X := Λ.comm
/-- Commutativity is retained by the bundled forgetful functor to ring objects.
Source: tensor ring objects (blueprint: def-pur-ordinary-proper-coefficient-domain). -/
instance coefficientToMonComm (Λ : ScalarSixRing.{u}) : IsCommMonObj Λ.toMon.X := Λ.comm

/-- Finite coefficients have their actual continuous-function condensed ring.
Source: Bhatt--Scholze 6.8.2 (blueprint: def-pur-ordinary-proper-coefficient-domain). -/
abbrev residueRing (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E.1) (n : ℕ) : ScalarSixRing.{u} :=
  scalarSixTopologicalRing (completedResidue l E π n)

/-- The actual quotient of the integral condensed ring; index n means exponent n+1.
Source: Bhatt--Scholze 6.8.2 (blueprint: def-pur-ordinary-proper-coefficient-domain). -/
def reduction (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E.1) (n : ℕ) :
    latticeIntegralRing.{u} l E ⟶ residueRing l E π n :=
  scalarSixContinuousMap (Ideal.Quotient.mk _) continuous_quot_mk

/-- Bounded constructible finite-Tor inputs with bounded constructible etale origin.
The finite/discrete instances are existential propositions, not chosen scalar data.
Source: Stacks 095T, 0GL6 (blueprint: def-pur-ordinary-proper-coefficient-domain). -/
def finiteInput (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u})
    (K : DerivedCategory.{u + 1} (Modules (Profinite.continuousMapRingObj A) X)) : Prop := by
  letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  exact ∃ (_ : Finite A) (_ : DiscreteTopology A),
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj A) X) K ∧
    DerivedCategory.finiteTorAmplitude _ K ∧
    (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible.{u}
        (ULift.{u + 1, u} (ULift.{u, 0} A)) X) ⋙
      finiteCoefficientIntrinsicDerivedComparison.{u} X (ULift.{u, 0} A)).essImage
        ((integralModelIntrinsicRealization X A).rightDerivedFunctor.obj K)

/-- Integral inputs are complete in the ordinary category, bounded constructible with
finite relative Tor amplitude, with etale-origin reductions and two uniform intervals.
The reductions are the derived extensions along the actual quotient maps.
Source: Bhatt--Scholze 6.7.5, 6.8.14--15
(blueprint: def-pur-ordinary-proper-coefficient-domain). -/
def integralInput (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E.1) (X : Scheme.{u})
    (K : DerivedCategory.{u + 1} (Modules (latticeIntegralRing.{u} l E).X X)) : Prop :=
  IntegralModelsEmbedded.completedComplete l E π X K ∧
  boundedConstructible (condensedRingObj (latticeIntegralRing.{u} l E).X X) K ∧
  DerivedCategory.finiteTorAmplitude _ K ∧
  ∃ a b c d : ℤ, ∀ n : ℕ,
    finiteInput (completedResidue l E π n) X ((D (reduction l E π n).hom.hom X).obj K) ∧
    DerivedCategory.homologyConcentratedIn a b ((D (reduction l E π n).hom.hom X).obj K) ∧
    DerivedCategory.torAmplitudeIn _ c d ((D (reduction l E π n).hom.hom X).obj K)

/-- The four ordinary coefficient stages and their prescribed input domains.
Rational and closure inputs retain an actual integral antecedent, up to isomorphism.
The closure is the existing finite-subextension-valued condensed ring.
Source: Bhatt--Scholze 6.8.14--15
(blueprint: def-pur-ordinary-proper-coefficient-domain). -/
inductive Input (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (Λ : ScalarSixRing.{u}) → DerivedCategory.{u + 1} (Modules Λ.X X) → Prop
  | finite (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E.1)
      (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
      (n : ℕ) (K : DerivedCategory.{u + 1} (Modules (residueRing.{u} l E π n).X X))
      (hK : finiteInput (completedResidue l E π n) X K) :
        Input l X (residueRing l E π n) K
  | integral (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E.1)
      (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
      (K : DerivedCategory.{u + 1} (Modules (latticeIntegralRing.{u} l E).X X))
      (hK : integralInput l E π X K) : Input l X (latticeIntegralRing l E) K
  | rational (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E.1)
      (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
      (L₀ : DerivedCategory.{u + 1} (Modules (latticeIntegralRing.{u} l E).X X))
      (hL : integralInput l E π X L₀)
      (K : DerivedCategory.{u + 1} (Modules (scalarSixFieldRing.{u} l E).X X))
      (e : (D (scalarSixIntegralToField l E).hom.hom X).obj L₀ ≅ K) :
        Input l X (scalarSixFieldRing l E) K
  | closure (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E.1)
      (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
      (L₀ : DerivedCategory.{u + 1} (Modules (latticeIntegralRing.{u} l E).X X))
      (hL : integralInput l E π X L₀)
      (K : DerivedCategory.{u + 1} (Modules (latticeClosureRing.{u} l).X X))
      (e : (D (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X).obj
        ((D (scalarSixIntegralToField l E).hom.hom X).obj L₀) ≅ K) :
          Input l X (latticeClosureRing l) K

/-- The listed actual coefficient changes, restricted to quotient reductions and the
specified integral, rational and finite-subextension inclusions, with finite composition.
The finite quotient map is fixed on every profinite section, including b=a.
Source: Bhatt--Scholze 6.8.14; Stacks 0GL6
(blueprint: def-pur-ordinary-proper-coefficient-domain). -/
inductive Change (l : ℕ) [Fact l.Prime] :
    {Λ Λ' : ScalarSixRing.{u}} → (Λ ⟶ Λ') → Prop
  | reduction (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E.1)
      (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
      (n : ℕ) : Change l (OrdinaryProper.reduction l E π n)
  | quotient (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E.1)
      (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
      (a b : ℕ) (hab : a ≤ b)
      (φ : residueRing.{u} l E π b ⟶ residueRing l E π a)
      (hφ : ∀ (P : Profinite.{u})
        (s : ULift.{u + 1} C(P, completedResidue l E π b)) (x : P),
        ((φ.hom.hom.hom.app (op P)) s).down x =
          Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.add_le_add_right hab 1)
            (s.down x)) : Change l φ
  | integral {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) :
      Change l (latticeIntegralMap l h)
  | field {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) :
      Change l (⟨⟨Profinite.padicSubfieldRingObjMap l h⟩⟩ :
        scalarSixFieldRing l E ⟶ scalarSixFieldRing l F)
  | localization (E : PadicAlgCl.FiniteIntermediateField l) :
      Change l (scalarSixIntegralToField l E)
  | closure (E : PadicAlgCl.FiniteIntermediateField l) :
      Change l (⟨⟨Profinite.padicSubfieldRingObjToPadicAlgCl l E⟩⟩ :
        scalarSixFieldRing l E ⟶ latticeClosureRing l)
  | identity (Λ : ScalarSixRing.{u}) : Change l (𝟙 Λ)
  | comp {Λ Λ' Λ'' : ScalarSixRing.{u}} {a : Λ ⟶ Λ'} {b : Λ' ⟶ Λ''}
      (ha : Change l a) (hb : Change l b) : Change l (a ≫ b)

end AlgebraicGeometry.ProEtale.OrdinaryProper
