/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Colimit.Finiteness
public import WeilConjectures.Mathlib.RingTheory.Adjoin.FG

/-!
# A commutative ring is the filtered colimit of its finitely generated `ℤ`-subalgebras

If the `ℤ`-subalgebras of a commutative ring `R` satisfying a predicate `P` form a
nonempty directed poset with supremum `⊤`, then `R` is the colimit of the diagram they
form in `CommRingCat` (`CommRingCat.isColimitSubalgebraCocone`); this is the categorical
companion of `Subalgebra.iSupLift`. Applying it to `P = Subalgebra.FG` shows that `R` is
the filtered colimit of its finitely generated `ℤ`-subalgebras
(`CommRingCat.isColimitFGSubalgebraCocone`).

This is the algebra analogue of `Module.fgSystem`, the system of finitely generated
submodules of a module.

Only the base ring `ℤ` is treated. This is a deliberate specialization to what absolute
Noetherian approximation needs, not an intrinsic limitation: for a general base `R` and an
`R`-algebra `A`, the diagram of `R`-subalgebras of `A` still lands in `CommRingCat`, and a
cocone point acquires a canonical `R`-algebra structure from `s.ι.app A₀ ∘ algebraMap R A₀`
for any index `A₀`, independently of `A₀` by cocone compatibility and directedness.

## Main declarations

* `CommRingCat.subalgebraDiagram`, `CommRingCat.subalgebraCocone`: the diagram of the
  `ℤ`-subalgebras of `R` satisfying a predicate and the cocone on it with point `R`.
* `CommRingCat.isColimitSubalgebraCocone`: that cocone is colimiting if these subalgebras
  form a nonempty directed poset with supremum `⊤`.
* `CommRingCat.fgSubalgebraDiagram`, `CommRingCat.fgSubalgebraCocone`,
  `CommRingCat.isColimitFGSubalgebraCocone`: the special case of the family of all
  finitely generated `ℤ`-subalgebras of `R`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CommRingCat

variable (R : Type u) [CommRing R] (P : Subalgebra ℤ R → Prop)

/-- The diagram in `CommRingCat` of the `ℤ`-subalgebras of a commutative ring `R`
satisfying a predicate `P`, with the inclusions as transition maps. -/
@[simps]
def subalgebraDiagram : {A : Subalgebra ℤ R // P A} ⥤ CommRingCat.{u} where
  obj A := .of A.1
  map {A B} f := ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom

/-- The ring `R`, as a cocone on the diagram of the `ℤ`-subalgebras of `R` satisfying `P`.

```
  ↥A ⟶ ↥B
     ↘ ↙
      R
```
-/
@[simps]
def subalgebraCocone : Cocone (subalgebraDiagram R P) where
  pt := .of R
  ι := { app A := ofHom A.1.val.toRingHom }

variable [Nonempty {A : Subalgebra ℤ R // P A}] [IsDirectedOrder {A : Subalgebra ℤ R // P A}]

/-- Auxiliary definition for `CommRingCat.isColimitSubalgebraCocone`: the ring
homomorphism out of `R` induced by a cocone on `CommRingCat.subalgebraDiagram`. -/
noncomputable def subalgebraDesc (hP : ⨆ A : {A : Subalgebra ℤ R // P A}, A.1 = ⊤)
    (s : Cocone (subalgebraDiagram R P)) : R →+* s.pt :=
  ((Subalgebra.iSupLift (fun A : {A : Subalgebra ℤ R // P A} ↦ A.1)
      (Subtype.mono_coe _).directed_le
      -- `by exact` postpones elaboration until the `ℤ`-algebra structure on `↥A.1` has
      -- been unified with the one on `(subalgebraDiagram R P).obj A`
      (fun A ↦ by exact (s.ι.app A).hom.toIntAlgHom)
      (fun A B h ↦ AlgHom.ext fun x ↦
        (ConcreteCategory.congr_hom (s.w (homOfLE (Subtype.coe_le_coe.mp h))) x).symm)
      ⊤ hP.ge).comp Subalgebra.topEquiv.symm.toAlgHom).toRingHom

@[simp]
lemma subalgebraDesc_val (hP : ⨆ A : {A : Subalgebra ℤ R // P A}, A.1 = ⊤)
    (s : Cocone (subalgebraDiagram R P)) (A : {A : Subalgebra ℤ R // P A}) (x : A.1) :
    subalgebraDesc R P hP s (A.1.val x) = (s.ι.app A).hom x := by
  have h : Subalgebra.topEquiv.symm.toAlgHom (A.1.val x)
      = Subalgebra.inclusion (le_top : A.1 ≤ ⊤) x := Subtype.ext rfl
  -- a terminal `simp` rewrites the coercion of `Subalgebra.topEquiv.symm` past the shape
  -- `Subalgebra.iSupLift_inclusion` expects, so the rewrites are spelled out
  simp only [subalgebraDesc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, h,
    Subalgebra.iSupLift_inclusion]
  rfl

/-- If the `ℤ`-subalgebras of a commutative ring `R` satisfying `P` form a nonempty
directed poset with supremum `⊤`, then `R` is their colimit in `CommRingCat`. This is the
categorical companion of `Subalgebra.iSupLift`. -/
noncomputable def isColimitSubalgebraCocone
    (hP : ⨆ A : {A : Subalgebra ℤ R // P A}, A.1 = ⊤) : IsColimit (subalgebraCocone R P) where
  desc s := ofHom (subalgebraDesc R P hP s)
  fac s A := by
    ext x
    exact subalgebraDesc_val R P hP s A x
  uniq s m hm := by
    ext x
    have hx : x ∈ ⋃ A : {A : Subalgebra ℤ R // P A}, (A.1 : Set R) := by
      rw [← Subalgebra.coe_iSup_of_directed (Subtype.mono_coe _).directed_le, hP]
      trivial
    obtain ⟨A, hA⟩ := Set.mem_iUnion.mp hx
    exact (ConcreteCategory.congr_hom (hm A) ⟨x, hA⟩).trans
      (subalgebraDesc_val R P hP s A ⟨x, hA⟩).symm

/-- The diagram of finitely generated `ℤ`-subalgebras of a commutative ring `R`, with the
inclusions as transition maps. -/
abbrev fgSubalgebraDiagram : {A : Subalgebra ℤ R // A.FG} ⥤ CommRingCat.{u} :=
  subalgebraDiagram R Subalgebra.FG

/-- The ring `R`, as a cocone on the diagram of its finitely generated `ℤ`-subalgebras. -/
abbrev fgSubalgebraCocone : Cocone (fgSubalgebraDiagram R) :=
  subalgebraCocone R Subalgebra.FG

/-- A commutative ring is the filtered colimit of its finitely generated `ℤ`-subalgebras. -/
noncomputable def isColimitFGSubalgebraCocone : IsColimit (fgSubalgebraCocone R) :=
  isColimitSubalgebraCocone R Subalgebra.FG (Subalgebra.iSup_val_fg_eq_top ℤ R)

end CommRingCat
