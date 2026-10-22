/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.LocalizingClosure
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all Sheaf.Paper.BrownHypothesesGeneration
import Sheaf.SixFunctorsBasics.BrownHypothesesStructural
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Compact representatives in the geometric finite-field localizing category

Source: blueprint main-20261015, sk-lem-brown-hypotheses, proof paragraph 2.
The ambient canonical Hom-map assertion is transported to the actual full
localizing subcategory; its chosen coproducts need not be definitionally ambient sums.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- A small skeleton of constructible finite-Tor objects is compact inside its
localizing category over the algebraic closure in a finite-field datum.
The coefficient alternatives are exactly those supported by the compactness theorem,
including finite-subextension-valued algebraic-closure coefficients.

Source: blueprint main-20261015, sk-lem-brown-hypotheses-generation, proof paragraphs 1--3.
(blueprint: a4-brown-finite-field-internal-compactness).

Proof: apply the ambient canonical Hom-map compactness assertion to the representatives.
The structural localizing-closure theorem supplies small coproducts in the full subcategory.
Closure under ambient sums makes the inclusion create and preserve these coproducts.
Its fully faithful additive Hom maps, the induced direct-sum isomorphism, and the coproduct
comparison give a commutative square of canonical Hom maps. Commutativity is checked on
individual summands. Bijectivity of three sides gives compactness in the full subcategory. -/
theorem brownHypothesesFiniteFieldCompactness
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ r : ℕ, ∀ a : A, (ℓ ^ r) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (G : Type (u + 1)) (g : G → ConstantModelConstructibleFiniteTor Λ X)
    (hG : ∀ C : ConstantModelConstructibleFiniteTor Λ X,
      ∃ i : G, Nonempty (C.obj ≅ (g i).obj))
    (hG_skeletal : ∀ i j : G, Nonempty ((g i).obj ≅ (g j).obj) → i = j) :
    ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
      letI := hSums
      ∀ (hL : ∀ i, localizingClosureProEtale Λ X (g i).obj) (i : G),
        IsCompactObject (⟨(g i).obj, hL i⟩ :
          (localizingClosureProEtale Λ X).FullSubcategory) := by
  classical
  obtain ⟨_, htri, hiso, _, hcop, _⟩ := brownHypotheses_structural Λ X
  let L := localizingClosureProEtale Λ X
  let _ := htri
  let _ := hiso
  let _ := hcop
  have hclosed (I : Type (u + 2)) : L.IsClosedUnderColimitsOfShape (Discrete I) := by
    constructor
    rintro K ⟨c⟩ P hP hS
    let _ := hP.2.1
    let _ : HasColimit c.diag := ⟨_, c.isColimit⟩
    exact P.prop_of_iso ((colimit.isColimit c.diag).coconePointUniqueUpToIso c.isColimit)
      (hP.2.2 c.diag inferInstance (fun i ↦ c.prop_diag_obj (Discrete.mk i) P hP hS))
  have hgen := (WeilConjectures.brownHypothesesGeneration D ℓ hℓ X Λ hΛ G g
    hG hG_skeletal).1
  let _ := (localizingClosure_exists Λ X
    (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _)).1
  refine ⟨hcop, ?_⟩
  intro hL i I E
  have _ := hclosed (ULift.{u + 2} I)
  have _ : L.IsClosedUnderColimitsOfShape (Discrete I) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence Equiv.ulift)
  exact WeilConjectures.compactness_of_fullyFaithful L.ι ⟨(g i).obj, hL i⟩ I E
    (hgen i I (fun j ↦ (E j).obj) (fun j ↦ (E j).property))

end CategoryTheory
