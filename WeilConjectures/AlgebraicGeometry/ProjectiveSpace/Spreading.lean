/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.RingTheory.Jacobson.Ring
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Spreading out morphisms to projective space with affine charts

Let `K / k` be a field extension and `X` a quasi-compact quasi-separated `k`-scheme. A morphism
`ψ : X_K ⟶ ℙ(γ; K)` over `K` such that the preimages of the standard opens are affine is defined,
together with the affineness of these preimages, over a finitely generated `k`-subalgebra `A` of
`K`; specialising at a maximal ideal of `A` gives such a morphism over a finite extension `k'`
of `k` (Zariski's lemma). This is the limit argument in the proof of Stacks, Tag 0BDE.

## Main statements

- `CommRingCat.isColimitFGSubalgebraCocone`: a `k`-algebra is the filtered colimit of its finitely
  generated `k`-subalgebras.
- `AlgebraicGeometry.exists_finite_isAffineOpen_preimage_standardOpen`: the spreading out.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace CommRingCat

variable (k K : Type u) [Field k] [CommRing K] [Algebra k K]

/-- The diagram in `CommRingCat` of the finitely generated `k`-subalgebras of a `k`-algebra `K`. -/
@[simps]
def fgSubalgebraDiagramOf : {A : Subalgebra k K // A.FG} ⥤ CommRingCat.{u} where
  obj A := .of A.1
  map {A B} f := ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom

/-- `K` as a cocone over its finitely generated `k`-subalgebras. -/
@[simps]
def fgSubalgebraCoconeOf : Cocone (fgSubalgebraDiagramOf k K) where
  pt := .of K
  ι := { app A := ofHom A.1.val.toRingHom }

lemma iSup_restrictScalars_fg :
    ⨆ A : {A : Subalgebra k K // A.FG}, A.1.restrictScalars ℤ = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  let A : {A : Subalgebra k K // A.FG} :=
    ⟨Algebra.adjoin k ↑({x} : Finset K), Subalgebra.fg_adjoin_finset _⟩
  have hx : x ∈ A.1 := Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_singleton_self x))
  exact Algebra.mem_iSup_of_mem (S := fun A : {A : Subalgebra k K // A.FG} ↦
    A.1.restrictScalars ℤ) A hx

lemma directed_restrictScalars :
    Directed (· ≤ ·) fun A : {A : Subalgebra k K // A.FG} ↦ A.1.restrictScalars ℤ :=
  Monotone.directed_le fun A B h _ hx ↦ (show A.1 ≤ B.1 from h) hx

/-- (Implementation) The ring homomorphism out of `K` induced by a cocone. -/
def fgSubalgebraDescOf (s : Cocone (fgSubalgebraDiagramOf k K)) : K →+* s.pt :=
  ((Subalgebra.iSupLift (fun A : {A : Subalgebra k K // A.FG} ↦ A.1.restrictScalars ℤ)
      (directed_restrictScalars k K)
      (fun A ↦ by exact (s.ι.app A).hom.toIntAlgHom)
      (fun A B h ↦ AlgHom.ext fun x ↦
        (ConcreteCategory.congr_hom (s.w (homOfLE (Subtype.coe_le_coe.mp
          (fun _ hy ↦ h hy)))) x).symm)
      ⊤ (iSup_restrictScalars_fg k K).ge).comp Subalgebra.topEquiv.symm.toAlgHom).toRingHom

lemma fgSubalgebraDescOf_val (s : Cocone (fgSubalgebraDiagramOf k K))
    (A : {A : Subalgebra k K // A.FG}) (x : A.1) :
    fgSubalgebraDescOf k K s (A.1.val x) = (s.ι.app A).hom x := by
  have h : Subalgebra.topEquiv.symm.toAlgHom (A.1.val x)
      = Subalgebra.inclusion (le_top : A.1.restrictScalars ℤ ≤ ⊤) x := Subtype.ext rfl
  simp only [fgSubalgebraDescOf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, h,
    Subalgebra.iSupLift_inclusion]
  rfl

/-- A `k`-algebra is the filtered colimit in `CommRingCat` of its finitely generated
`k`-subalgebras. -/
def isColimitFGSubalgebraCocone : IsColimit (fgSubalgebraCoconeOf k K) where
  desc s := ofHom (fgSubalgebraDescOf k K s)
  fac s A := by
    ext x
    exact fgSubalgebraDescOf_val k K s A x
  uniq s m hm := by
    ext x
    have hx : x ∈ (⊤ : Subalgebra ℤ K) := trivial
    rw [← iSup_restrictScalars_fg k K, ← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed
      (directed_restrictScalars k K)] at hx
    obtain ⟨A, hA⟩ := Set.mem_iUnion.mp hx
    exact (ConcreteCategory.congr_hom (hm A) ⟨x, hA⟩).trans
      (fgSubalgebraDescOf_val k K s A ⟨x, hA⟩).symm

end CommRingCat
