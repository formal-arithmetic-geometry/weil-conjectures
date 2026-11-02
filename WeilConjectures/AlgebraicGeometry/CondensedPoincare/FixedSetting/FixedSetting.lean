/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedPoincare.CondensedPoincareSetting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeCondensedOperations
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import Mathlib.Algebra.CharP.CharAndCard

/-! # The fixed condensed setting for Poincare duality

Source: latest blueprint `sk-def-set`, order 3594.
The coefficient stages and the geometric datum are bundled without a properness
or exceptional-adjoint hypothesis; properness is introduced only by later trace
and Poincare-duality statements.
(blueprint: sk-def-set)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedPoincare

open PurityTransport

variable (ell : ℕ) [Fact ell.Prime]

/-- The ambient derived category attached to a condensed coefficient and a scheme.
Source: the ambient-category clause of `sk-def-set`, order 3594
(blueprint: sk-def-set). -/
abbrev ambientCategory
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :=
  DerivedCategory
    letI : MonObj (condensedRingObj Λ T) :=
      Functor.monObjObj (F := upperStarFromPoint T) Λ
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)

/-- The field scope and finite cohomological-dimension input used by the Brown
exceptional-adjoint construction.  The chosen closure `D.k` is algebraically closed.
Source: the standing field clause of `sk-thm-existence` (blueprint: sk-def-set).
Proof: the closure field `D.k` carries the existing `IsAlgClosed D.k` instance induced by
`D.isAlgClosure`; use the right branch of the displayed disjunction. -/
theorem FixedSetting.fieldScope
    (D : WeilConjectures.FiniteFieldDatum.{u}) :
    Finite D.k ∨ IsAlgClosed D.k := by
  exact Or.inr (IsAlgClosure.isAlgClosed D.k₀)

private theorem fixedSetting_ringChar
    (D : WeilConjectures.FiniteFieldDatum.{u}) : ringChar D.k = D.p := by
  let : Fintype D.k₀ := Fintype.ofFinite _
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact ringChar.eq D.k D.p

/-- The characteristic of the chosen algebraic closure is prime.
Source: the finite-field datum and its characteristic transport in
`sk-thm-existence` (blueprint: sk-def-set).
Proof: transport the prime characteristic equation from the finite-field datum to
its chosen algebraic closure and apply the existing prime-characteristic lemma. -/
theorem FixedSetting.fieldCharPrime
    (D : WeilConjectures.FiniteFieldDatum.{u}) : (ringChar D.k).Prime := by
  rw [fixedSetting_ringChar D]
  exact D.prime

/-- The coefficient prime is distinct from the characteristic of the chosen
algebraic closure. Source: `hEll` and characteristic transport in
`sk-thm-existence` (blueprint: sk-def-set).
Proof: rewrite the characteristic of `D.k` as `D.p`, then use `hEll` and the
same characteristic transport to obtain the stated inequality. -/
theorem FixedSetting.fieldCharNe
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p) :
    ringChar D.k ≠ ell := by
  rw [fixedSetting_ringChar D]
  exact hEll.symm

/-- The canonical finite `ell`-cohomological-dimension bound for the chosen
closure.
Source: the standing field clause of `sk-thm-existence` (blueprint: sk-def-set).
Proof: apply `BaseFieldFiniteCD.of_isAlgClosed` to the canonical
`IsAlgClosed D.k` instance. -/
theorem FixedSetting.baseFieldFiniteCD
    (D : WeilConjectures.FiniteFieldDatum.{u}) :
    AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell D.k := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  exact BaseFieldFiniteCD.of_isAlgClosed ell D.k

/-- The fixed finite-field, coefficient-stage and geometric setting used throughout
Poincare duality.  The function `coefficients` lists the finite, integral, rational,
and algebraic-closure stages, while `geometry` supplies a smooth separated
geometrically connected model and its geometric fibre.  The ambient and
constructible categories use the canonical `ambientCategory` and existing
`CondensedConstructibleFiniteTor` abbreviation. No properness or ambient-adjoint field is included.

Source: the complete fixed-setting definition, node `sk-def-set`, order 3594
(blueprint: sk-def-set). -/
structure FixedSetting (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ) where
  geometry : PoincareDualitySetting D.k₀ d


/-- Every coefficient stage is admissible for the localizing Brown construction.
Source: the four coefficient cases in `det-def-sf-operations` (blueprint:
sk-def-set). The proof checks the finite, integral, rational, and
closure coefficient presentations against the standing coefficient predicate.
Proof: split on `i`; unfold each coefficient constructor (the finite case is the
discrete ring `O_E/(π)^n`), provide its finite or standard padic presentation,
and transport the localizing admissibility equivalence along the coefficient
isomorphism. -/
theorem FixedSetting.coefficientAdmissible
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) (i : Stage) :
    IsLocalizingAdmissibleCoefficient ell ((coefficient ell E π hπ n hn i).obj ell) := by
  cases S
  cases i with
  | finite =>
      let A := PadicAlgCl.integers ell E ⧸ (Ideal.span ({π} : Set _)) ^ n
      let : TopologicalSpace A := ⊥
      let : DiscreteTopology A := discreteTopology_bot A
      refine Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
        residueFinite ell E π hπ n, ⟨n + 1, ?_⟩, ⟨Iso.refl _⟩⟩
      intro a
      rw [nsmul_eq_mul, Nat.cast_pow, residueAnnihilator ell E π hπ n, zero_mul]
  | integral =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  | rational =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))
  | closure =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))

/-- Forgetting the operation system and retaining one stage gives the older
`CondensedPoincare.Setting` declaration.  `FixedSetting` is its complete refinement:
it stores all four canonical stages and the exceptional adjunction on the native
finite-Tor category, whereas `Setting` stores one presentation index only.
Source: relation to the earlier `sk-def-set` declaration (blueprint: sk-def-set). -/
def FixedSetting.toSetting
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) (i : Stage) :
    Setting ell D hEll E π hπ n hn d :=
  { geometry := S.geometry
    stage := i }

/-- The geometric fibre `X = X₀ ×ₖ₀ k` of the fixed setting.
Source: the geometric-fibre clause of `sk-def-set`, order 3594
(blueprint: sk-def-set). -/
noncomputable def FixedSetting.X
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) : Scheme.{u} :=
  S.geometry.geometricFiber D.k

/-- The point `s = Spec k` of the fixed setting.
Source: the base-point clause of `sk-def-set`, order 3594
(blueprint: sk-def-set). -/
noncomputable def FixedSetting.s
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (_S : FixedSetting ell D hEll E π hπ n hn d) : Scheme.{u} :=
  Spec (CommRingCat.of D.k)

/-- The structure morphism `a_X : X ⟶ s` of the fixed setting.
Source: the structure-morphism clause of `sk-def-set`, order 3594
(blueprint: sk-def-set). -/
noncomputable def FixedSetting.aX
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    S.X ⟶ S.s :=
  S.geometry.structureMorphism D.k

/-- The geometric fibre has the finiteness and separatedness instances needed by
the canonical compactification. These are the base-change properties of the
smooth separated finite-type model. Source: the relative geometric hypotheses in
`sk-def-set` (blueprint: sk-def-set).
Proof: use smoothness, separatedness, finite type, and base change along the
finite-field extension to transport the six displayed properties. -/
theorem FixedSetting.compactificationFacts
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    LocallyOfFiniteType S.aX ∧
      QuasiCompact S.aX ∧
      IsSeparated S.aX ∧
      LocallyOfFiniteType (𝟙 S.s) ∧
      QuasiCompact (𝟙 S.s) ∧
      IsSeparated (𝟙 S.s) := by
  dsimp only [FixedSetting.aX, PoincareDualitySetting.structureMorphism]
  exact ⟨inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.X_over
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    S.X.Over (Spec (.of D.k)) :=
  ⟨S.aX⟩

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.s_over
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    S.s.Over (Spec (.of D.k)) :=
  ⟨𝟙 S.s⟩

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.X_rel_lft
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    LocallyOfFiniteType (S.X ↘ Spec (.of D.k)) := by
  change LocallyOfFiniteType S.aX
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.X_rel_qc
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    QuasiCompact (S.X ↘ Spec (.of D.k)) := by
  change QuasiCompact S.aX
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.X_rel_sep
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    IsSeparated (S.X ↘ Spec (.of D.k)) := by
  change IsSeparated S.aX
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.2.1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.s_rel_lft
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    LocallyOfFiniteType (S.s ↘ Spec (.of D.k)) := by
  change LocallyOfFiniteType (𝟙 S.s)
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.2.2.1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.s_rel_qc
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    QuasiCompact (S.s ↘ Spec (.of D.k)) := by
  change QuasiCompact (𝟙 S.s)
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.2.2.2.1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.s_rel_sep
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    IsSeparated (S.s ↘ Spec (.of D.k)) := by
  change IsSeparated (𝟙 S.s)
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.2.2.2.2

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.aX_isOver
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    S.aX.IsOver (Spec (.of D.k)) :=
  ⟨by rfl⟩

/-- The bundled source and target objects over `Spec D.k` used by the native
exceptional-operation interface. Source: the `a_X : X ⟶ s` clause of `sk-def-set`
(blueprint: sk-def-set). -/
noncomputable abbrev FixedSetting.XOver
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) : Over (Spec (.of D.k)) :=
  Over.mk S.aX

/-- The point object over `Spec D.k` used by the native exceptional-operation
interface. Source: the `s = Spec k` clause of `sk-def-set`
(blueprint: sk-def-set). -/
noncomputable abbrev FixedSetting.sOver
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) : Over (Spec (.of D.k)) :=
  Over.mk (𝟙 S.s)

/-- The bundled structure morphism over `Spec D.k`. Source: the `a_X` clause of
`sk-def-set` (blueprint: sk-def-set). -/
noncomputable def FixedSetting.aXOver
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    S.XOver ⟶ S.sOver :=
  Over.homMk S.aX (by simp)

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.XOver_lft
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    LocallyOfFiniteType S.XOver.hom := by
  change LocallyOfFiniteType S.aX
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.XOver_qc
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    QuasiCompact S.XOver.hom := by
  change QuasiCompact S.aX
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.XOver_sep
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    IsSeparated S.XOver.hom := by
  change IsSeparated S.aX
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.2.1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.sOver_lft
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    LocallyOfFiniteType S.sOver.hom := by
  change LocallyOfFiniteType (𝟙 S.s)
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.2.2.1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.sOver_qc
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    QuasiCompact S.sOver.hom := by
  change QuasiCompact (𝟙 S.s)
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.2.2.2.1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.sOver_sep
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    IsSeparated S.sOver.hom := by
  change IsSeparated (𝟙 S.s)
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.2.2.2.2

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.XOver_rel_lft
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    LocallyOfFiniteType (S.XOver.left ↘ Spec (.of D.k)) := by
  change LocallyOfFiniteType S.aX
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.XOver_rel_qc
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    QuasiCompact (S.XOver.left ↘ Spec (.of D.k)) := by
  change QuasiCompact S.aX
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.XOver_rel_sep
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    IsSeparated (S.XOver.left ↘ Spec (.of D.k)) := by
  change IsSeparated S.aX
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.2.1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.sOver_rel_lft
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    LocallyOfFiniteType (S.sOver.left ↘ Spec (.of D.k)) := by
  change LocallyOfFiniteType (𝟙 S.s)
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.2.2.1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.sOver_rel_qc
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    QuasiCompact (S.sOver.left ↘ Spec (.of D.k)) := by
  change QuasiCompact (𝟙 S.s)
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.2.2.2.1

/-- Source: geometric finiteness and separatedness in `sk-def-set` (blueprint: sk-def-set). -/
noncomputable instance FixedSetting.sOver_rel_sep
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) :
    IsSeparated (S.sOver.left ↘ Spec (.of D.k)) := by
  change IsSeparated (𝟙 S.s)
  exact (FixedSetting.compactificationFacts (ell := ell) (D := D) (hEll := hEll)
    (E := E) (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S).2.2.2.2.2

/-- The canonical native operation at a coefficient stage. Its lower component is
`rightDerivedLowerShriekOfCompactification` restricted to the existing native
finite-Tor category; its upper component is the Brown right adjoint.
Source: `det-def-sf-operations` (vi), `sk-thm-existence` (blueprint:
sk-def-set).
Proof: apply the adjunction supplied by the native Brown transport to the
bundled structure morphism `aXOver`; the preservation premise is
`nativeLowerShriek_mem`. -/
noncomputable def FixedSetting.operations
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (S : FixedSetting ell D hEll E π hπ n hn d) (i : Stage) :
    AlgebraicGeometry.ProEtale.CondensedRing.nativeLowerShriek
        ((coefficient ell E π hπ n hn i).obj ell) ell D.k
        (FixedSetting.fieldCharPrime D)
        (FixedSetting.fieldCharNe ell D hEll)
        (FixedSetting.fieldScope D)
        (FixedSetting.baseFieldFiniteCD ell D)
        (FixedSetting.aXOver (ell := ell) (D := D) (hEll := hEll) (E := E)
          (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S)
        (FixedSetting.coefficientAdmissible ell D hEll E π hπ n hn d S i) ⊣
      AlgebraicGeometry.ProEtale.CondensedRing.nativeExceptionalInverseImage
        ((coefficient ell E π hπ n hn i).obj ell) ell D.k
        (FixedSetting.fieldCharPrime D)
        (FixedSetting.fieldCharNe ell D hEll)
        (FixedSetting.fieldScope D)
        (FixedSetting.baseFieldFiniteCD ell D)
        (FixedSetting.aXOver (ell := ell) (D := D) (hEll := hEll) (E := E)
          (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S)
        (FixedSetting.coefficientAdmissible ell D hEll E π hπ n hn d S i) := by
  exact AlgebraicGeometry.ProEtale.CondensedRing.nativeExceptionalAdjunction
    ((coefficient ell E π hπ n hn i).obj ell) ell D.k
    (FixedSetting.fieldCharPrime D)
    (FixedSetting.fieldCharNe ell D hEll)
    (FixedSetting.fieldScope D)
    (FixedSetting.baseFieldFiniteCD ell D)
    (FixedSetting.aXOver (ell := ell) (D := D) (hEll := hEll) (E := E)
      (π := π) (hπ := hπ) (n := n) (hn := hn) (d := d) S)
    (FixedSetting.coefficientAdmissible ell D hEll E π hπ n hn d S i)

/-- The canonical coefficient list of a fixed setting.  Its finite stage is
`O_E/(π)^n`, and the other stages are `O_E`, `E`, and `Qbar` as condensed rings.
Source: coefficient list in `sk-def-set`, order 3594 (blueprint: sk-def-set). -/
def FixedSetting.coefficients
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal
      (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (_S : FixedSetting ell D hEll E π hπ n hn d) : Stage → Coefficient ell :=
  coefficient ell E π hπ n hn

end AlgebraicGeometry.ProEtale.CondensedPoincare
