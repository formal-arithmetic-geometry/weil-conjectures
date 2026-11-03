/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnitConstructible
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided

/-! # Dualizing complexes with arbitrary finite primary coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/
def-trf-dualizing-complex.md,
Definition Dualizing complex and Verdier dual (blueprint: def-trf-dualizing-complex),
with the coefficient generality recorded in the node after Wei Yang #1412, answer 3.

The exceptional inverse image is the constructible restriction of the current Brown
adjunction. The coefficient is any finite commutative ell-primary ring, with discrete
topology. The target of the dual functor is the ordinary ambient derived category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.FiniteRingTrace

variable (A : Type) [CommRing A] [Finite A]

/-- The discrete condensed coefficient ring, pulled back by `condensedRingObj` on schemes.
Source: coefficient convention (blueprint: def-trf-dualizing-complex). -/
abbrev coefficient : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
  exact Profinite.continuousMapRingObj A

/-- The ordinary unbounded derived category of modules over the pulled-back coefficient.
Source: the displayed ambient category (blueprint: def-trf-dualizing-complex). -/
abbrev Ambient (Y : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (coefficient A) Y))

/-- The existing full subcategory of bounded constructible complexes of finite Tor amplitude.
Source: the domain of the dual functor (blueprint: def-trf-dualizing-complex). -/
abbrev Ctf (Y : Scheme.{u}) := ConstantModelConstructibleFiniteTor (coefficient A) Y

/-- The characteristic of the geometric field is supplied by the global datum itself.
Source: finite-field convention (blueprint: def-trf-dualizing-complex). -/
instance fieldChar (D : FiniteFieldDatum.{u}) : CharP D.k D.p := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  exact charP_of_injective_algebraMap' D.k₀ D.p

/-- The constructible exceptional inverse image of the structure morphism, from the
current finite-or-algebraically-closed-field Brown theorem. No ambient adjoint is assumed.
Its right-adjoint characterization determines the selected functor up to the unique
counit-compatible comparison.
Source: sk-thm-existence (3)--(4) (blueprint: def-trf-dualizing-complex). -/
def exceptional (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
    (Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    Ctf A (Spec (.of D.k)) ⥤ Ctf A Y.left := by
  letI := fieldChar D
  letI : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  letI : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
  letI : QuasiCompact (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
  letI : IsSeparated (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
  let hcoeff : IsLocalizingAdmissibleCoefficient ell (coefficient A) :=
    Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ⟨hA.choose, hA.choose_spec.2⟩, ⟨Iso.refl _⟩⟩
  exact (currentConstructibleExceptionalData (coefficient A) ell D.k
    (Or.inr (IsAlgClosure.isAlgClosed D.k₀)) (Over.mkIdTerminal.from Y) hcoeff).right

/-- The dualizing complex is precisely Ra_Y^! A_s, using the actual coefficient unit.
Source: the first displayed assignment (blueprint: def-trf-dualizing-complex). -/
def dualizingComplex (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
    (Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] : Ambient A Y.left :=
  ((exceptional A D ell hell hA Y).obj
    ⟨constantCoefficientObject (coefficient A) (Spec (.of D.k)),
      constantCoefficientObject_mem (coefficient A) (Spec (.of D.k))⟩).obj

/-- Verdier duality is RHom(-,omega) on the full finite-Tor constructible category.
Its action on a morphism u is RHom(u,id_omega).
Source: the second displayed assignment (blueprint: def-trf-dualizing-complex). -/
def verdierDual (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
    (Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    (Ctf A Y.left)ᵒᵖ ⥤ Ambient A Y.left :=
  (constantModelBoundedConstructible (coefficient A) Y.left ⊓
      DerivedCategory.finiteTorAmplitude _).ι.op ⋙
    (derivedHom (coefficient A) Y.left).flip.obj (dualizingComplex A D ell hell hA Y)

/-- The displayed tensor-Hom bijection, with the factors in the stated order.
The braiding first changes D(M) tensor M into M tensor D(M); then use the actual
relative derived tensor-Hom adjunction.
Source: the adjunction display (blueprint: def-trf-dualizing-complex). -/
def evaluationHomEquiv (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
    (Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (M : Ctf A Y.left) :
    (((derivedTensor (coefficient A) Y.left).obj
      ((verdierDual A D ell hell hA Y).obj (op M))).obj M.obj ⟶
        dualizingComplex A D ell hell hA Y) ≃
      ((verdierDual A D ell hell hA Y).obj (op M) ⟶
        ((derivedHom (coefficient A) Y.left).obj (op M.obj)).obj
          (dualizingComplex A D ell hell hA Y)) := by
  letI : BraidedCategory (Ambient A Y.left) := DerivedCategory.braidedCategory' _
  exact (Iso.homCongr (β_ _ _) (Iso.refl _)).trans
    ((derivedTensorHomAdjunction (coefficient A) M.obj).homEquiv _ _)

/-- Evaluation is exactly the inverse transpose of the identity of D_Y M.
Source: the evaluation display (blueprint: def-trf-dualizing-complex). -/
def evaluation (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
    (Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (M : Ctf A Y.left) :
    (((derivedTensor (coefficient A) Y.left).obj
      ((verdierDual A D ell hell hA Y).obj (op M))).obj M.obj ⟶
        dualizingComplex A D ell hell hA Y) :=
  (evaluationHomEquiv A D ell hell hA Y M).symm (𝟙 _)

end WeilConjectures.FiniteRingTrace
