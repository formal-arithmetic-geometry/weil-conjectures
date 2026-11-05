/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FieldDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TraceShiftUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.BraidedTrace
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.TraceShiftDecomposition
public import WeilConjectures.LinearAlgebra.TraceLongExactSequence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleShift
public import WeilConjectures.TraceFormula.Basic
public import WeilConjectures.TraceFormula.PointFiberFunctor

/-!
# Traces on the point category over a separably closed field

Let `k` be a separably closed field and `s = Spec k`. Evaluation at the geometric point identifies
the bounded constructible derived category `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` with the bounded derived category of
finite-dimensional `ℚ̄_ℓ`-vector spaces (blueprint `def-weil-finite-coefficient-point`,
`ProEtale.CondensedRing.exists_fiberFunctor_point`). Consequently every object of
`Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is a finite direct sum of shifts of the unit.

This file shows that the categorical trace on `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is the supertrace on the graded
spaces `Hⁿ(P) = Hom(𝟙⟦n⟧, P)`, and deduces that the trace is additive along every endomorphism of
a distinguished triangle (blueprint `prop-trf-trace-formal-laws`, items (2) and (4)): over a field
the filtered origin of the endomorphism is not needed.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

attribute [local instance] boundedConstructibleBraiding

example : MonoidalPreadditive (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  inferInstance

example (n : ℤ) :
    (shiftFunctor (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) n).Additive :=
  inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing

namespace DerivedCategory

variable {F : Type (u + 1)} [Field F]

/-- A retract of a bounded complex with finite-dimensional cohomology is again bounded with
finite-dimensional cohomology. -/
lemma boundedFiniteCohomology_of_retract {X Y : DerivedCategory (ModuleCat.{u + 1} F)}
    (i : X ⟶ Y) (p : Y ⟶ X) (h : i ≫ p = 𝟙 X) (hY : boundedFiniteCohomology F Y) :
    boundedFiniteCohomology F X := by
  have hz (n : ℤ) (hn : IsZero ((homologyFunctor _ n).obj Y)) :
      IsZero ((homologyFunctor _ n).obj X) := by
    rw [IsZero.iff_id_eq_zero, ← (homologyFunctor _ n).map_id, ← h, Functor.map_comp,
      hn.eq_of_tgt ((homologyFunctor _ n).map i) 0, zero_comp]
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hfin⟩ := hY
  refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun n ↦ ?_⟩
  · have ha' := (isGE_iff Y a).1 ha
    exact (isGE_iff X a).2 fun n hn ↦ hz n (ha' n hn)
  · have hb' := (isLE_iff Y b).1 hb
    exact (isLE_iff X b).2 fun n hn ↦ hz n (hb' n hn)
  · have := hfin n
    refine Module.Finite.of_surjective ((homologyFunctor _ n).map p).hom fun x ↦
      ⟨((homologyFunctor _ n).map i).hom x, ?_⟩
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, h, CategoryTheory.Functor.map_id]
    rfl

end DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

attribute [local instance] boundedConstructibleBraiding

/-- Over a separably closed field, every object of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is a finite direct sum of
shifts of the unit: transported along the fibre functor of `exists_fiberFunctor_point`, this is
the splitting of bounded complexes of vector spaces
(`DerivedCategory.prop_of_boundedFiniteCohomology_of_field`). -/
theorem nonempty_shiftDecomposition_point
    (P : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty (ShiftDecomposition (𝟙_ _) P) := by
  obtain ⟨G, _, hadd, ⟨hG⟩, hbfc, hess, ⟨e₀⟩⟩ := exists_fiberFunctor_point ℓ k
  have : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive G
  let F := ULift.{u + 1} (PadicAlgCl ℓ)
  let Q : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} F)) := fun Y ↦
    DerivedCategory.boundedFiniteCohomology F Y →
      ∀ P, (G.obj P ≅ Y) → Nonempty (ShiftDecomposition (𝟙_ _) P)
  have : Q.IsClosedUnderIsomorphisms := ⟨fun {Y Y'} e hY hY' P e' ↦
    hY ((DerivedCategory.boundedFiniteCohomology F).prop_of_iso e.symm hY') P (e' ≪≫ e.symm)⟩
  refine DerivedCategory.prop_of_boundedFiniteCohomology_of_field Q ?_ ?_ ?_ ?_ (hbfc P) (hbfc P)
    P (Iso.refl _)
  · intro Y hY _ P e
    refine ⟨ShiftDecomposition.ofIsZero ?_⟩
    rw [IsZero.iff_id_eq_zero]
    exact hG.map_injective (by rw [G.map_id, G.map_zero]; exact (hY.of_iso e).eq_of_src _ _)
  · intro X Y hX hY hXY P e
    have hX' := DerivedCategory.boundedFiniteCohomology_of_retract biprod.inl biprod.fst
      biprod.inl_fst hXY
    have hY' := DerivedCategory.boundedFiniteCohomology_of_retract biprod.inr biprod.snd
      biprod.inr_snd hXY
    obtain ⟨PX, ⟨eX⟩⟩ := hess X hX'
    obtain ⟨PY, ⟨eY⟩⟩ := hess Y hY'
    obtain ⟨DX⟩ := hX hX' PX eX
    obtain ⟨DY⟩ := hY hY' PY eY
    refine ⟨DX.sum DY (hG.preimage (eX.hom ≫ biprod.inl ≫ e.inv))
      (hG.preimage (eY.hom ≫ biprod.inr ≫ e.inv)) (hG.preimage (e.hom ≫ biprod.fst ≫ eX.inv))
      (hG.preimage (e.hom ≫ biprod.snd ≫ eY.inv)) ?_ ?_ ?_ ?_ ?_⟩
    · apply hG.map_injective
      simp only [G.map_add, G.map_comp, hG.map_preimage, Category.assoc, Iso.inv_hom_id_assoc,
        G.map_id]
      rw [← Preadditive.comp_add, ← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
      ← Preadditive.add_comp, biprod.total, Category.id_comp, Iso.hom_inv_id]
    all_goals
      apply hG.map_injective
      simp only [G.map_comp, hG.map_preimage, Category.assoc, Iso.inv_hom_id_assoc,
        G.map_id, G.map_zero, biprod.inl_fst_assoc, biprod.inr_snd_assoc, biprod.inl_snd_assoc,
        biprod.inr_fst_assoc, Iso.hom_inv_id, zero_comp, comp_zero]
  · intro X n hX hXn P e
    let P' := (shiftFunctor _ (-n)).obj P
    let e' : G.obj P' ≅ X := (G.commShiftIso (-n)).app P ≪≫ (shiftFunctor _ (-n)).mapIso e ≪≫
      (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).app X
    obtain ⟨D⟩ := hX ((DerivedCategory.boundedFiniteCohomology F).prop_of_iso e' (hbfc P')) P' e'
    exact ⟨(D.shift n).ofIso ((shiftFunctorCompIsoId _ (-n) n (neg_add_cancel n)).app P)⟩
  · intro _ P e
    exact ⟨(ShiftDecomposition.self _).ofIso (hG.preimageIso (e₀ ≪≫ e.symm))⟩

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Ambient

end Ambient

end AlgebraicGeometry.ProEtale.CondensedRing

namespace DerivedCategory

variable {F : Type (u + 1)} [Field F]

end DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

attribute [local instance] boundedConstructibleBraiding

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section GradedHom

end GradedHom

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section TraceFormula

attribute [local instance] DerivedCategory.braidedCategory'

end TraceFormula

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]

section Additivity

section Exact

variable {Y₁ Y₂ Y₃ : DerivedCategory (PointMod ℓ k)} {f : Y₁ ⟶ Y₂} {g : Y₂ ⟶ Y₃}
  {δ : Y₃ ⟶ (shiftFunctor (DerivedCategory (PointMod ℓ k)) (1 : ℤ)).obj Y₁}

end Exact

attribute [local instance] DerivedCategory.braidedCategory'

end Additivity

end AlgebraicGeometry.ProEtale.CondensedRing
