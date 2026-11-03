/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteRingTrace.FiniteRingTraceDualizingComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProductComparisons.NativeSixFunctorKunnethMaps
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Constructible exceptional admissibility with finite primary coefficients

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-coefficients-constructible/
sec-n-brown/sk-thm-existence/def-trf-admissibility.md,
constructible adjunction, composition and base-change paragraphs
(blueprint: def-trf-admissibility).

The current Brown adjunction is used without imposing conditions on an ambient right
adjoint. Composition and exchange are computed by conjugating the normalized compact-support
comparisons. All finite commutative primary rings are allowed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.FiniteRingTrace.KVConstructible

variable (A : Type) [CommRing A] [Finite A]

/-- The actual constructible Brown adjunction for a separated finite-type morphism.
The same formula at the structure morphism is the datum defining `exceptional` and omega.
Source: constructible restriction in def-trf-admissibility
(blueprint: def-trf-admissibility). -/
def exceptionalDatum (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
    {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) : CurrentConstructibleExceptionalData (coefficient A) f := by
  letI := fieldChar D
  letI : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
  let hcoeff : IsLocalizingAdmissibleCoefficient ell (coefficient A) :=
    Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ⟨hA.choose, hA.choose_spec.2⟩, ⟨Iso.refl _⟩⟩
  exact currentConstructibleExceptionalData (coefficient A) ell D.k
    (Or.inr (IsAlgClosure.isAlgClosed D.k₀)) f hcoeff

/-- Exceptional admissibility at A means existence of the specified constructible
adjunction, with its natural unit and counit. The following constructions equip it with
the canonical composition and exchange, so they are not independently chosen arrows.
Source: def-trf-admissibility, at-A paragraph (blueprint: def-trf-admissibility). -/
def IsExceptionallyAdmissibleAtFiniteRing (D : FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (_hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
    {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) : Prop :=
  Nonempty (CurrentConstructibleExceptionalData (coefficient A) f)

/-- Exceptional admissibility means the same constructible datum for every finite
commutative ell-primary coefficient ring. There are no bounds uniform in the ring A.
Source: the all-finite-rings paragraph, with Wei Yang #1423
(blueprint: def-trf-admissibility). -/
def IsExceptionallyAdmissible (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p)
    {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) : Prop :=
  ∀ (B : Type) [CommRing B] [Finite B],
    ∀ hB : ∃ n : ℕ, 0 < n ∧ ∀ b : B, (ell ^ n) • b = 0,
      IsExceptionallyAdmissibleAtFiniteRing B D ell hell hB f

end WeilConjectures.FiniteRingTrace.KVConstructible

namespace AlgebraicGeometry.ProEtale.CondensedRing.CurrentTrace

variable {k : Type u} [Field k] (Λ : ScalarSixRing.{u})

/-- Identify the actual compactification functor with the lower functor of the given
constructible adjunction. Both object and morphism maps are fixed by `lower_eq`.
Source: compactification independence (blueprint: def-trf-admissibility). -/
def lowerComparison (H : RelativeKunneth.CanonicalCompositionData Λ.X k)
    {X Y : SepFinType k} (f : X ⟶ Y)
    (S : CurrentConstructibleExceptionalData Λ.X f.hom)
    (c : Compactification f.hom.left)
    (K : ConstantModelConstructibleFiniteTor Λ.X X.obj.left) :
    (CompactificationReindexing.F Λ.X c).obj K.obj ≅ (S.lower.obj K).obj :=
  (H.comparison f c (compactificationOverField f.hom)).app
      (RelativeKunneth.localizingObject Λ X.obj.left K) ≪≫
    (eqToIso S.lower_eq).symm.app K

end AlgebraicGeometry.ProEtale.CondensedRing.CurrentTrace
