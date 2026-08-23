/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.RingTheory.Adjoin.FG

/-!
# A commutative ring is the filtered colimit of its finitely generated `ℤ`-subalgebras

The finitely generated `ℤ`-subalgebras of a commutative ring `R` form a nonempty directed
poset `{A : Subalgebra ℤ R // A.FG}` (see `WeilConjectures/Mathlib/RingTheory/Adjoin/FG.lean`).
Here we show that the induced filtered diagram of rings has colimit `R`.

Only the base ring `ℤ` is treated, since the universal property is obtained from
`Subalgebra.iSupLift`, which produces an algebra homomorphism into the cocone point, and a
bare commutative ring carries a canonical algebra structure only over `ℤ`.

For the analogous statement about the finitely generated submodules of a module, see
`Module.fgSystem` in `Mathlib/Algebra/Colimit/Finiteness.lean`.

## Main declarations

* `CommRingCat.fgSubalgebraDiagram`: the diagram of finitely generated `ℤ`-subalgebras
  of a commutative ring `R`, with the inclusions as transition maps.
* `CommRingCat.fgSubalgebraCocone`: the cocone on it with point `R`.
* `CommRingCat.isColimitFgSubalgebraCocone`: that cocone is colimiting.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CommRingCat

variable (R : Type u) [CommRing R]

/-- The diagram of finitely generated `ℤ`-subalgebras of a commutative ring `R`, with the
inclusions as transition maps. -/
@[simps]
def fgSubalgebraDiagram : {A : Subalgebra ℤ R // A.FG} ⥤ CommRingCat.{u} where
  obj A := .of A.1
  map {A B} f := ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom

/-- The ring `R`, as a cocone on the diagram of its finitely generated `ℤ`-subalgebras.

```
  ↥A ⟶ ↥B
     ↘ ↙
      R
```
-/
@[simps]
def fgSubalgebraCocone : Cocone (fgSubalgebraDiagram R) where
  pt := .of R
  ι := { app A := ofHom A.1.val.toRingHom }

/-- Auxiliary definition for `CommRingCat.isColimitFgSubalgebraCocone`: the ring
homomorphism out of `R` induced by a cocone on the diagram of finitely generated
`ℤ`-subalgebras of `R`. -/
noncomputable def fgSubalgebraDesc (s : Cocone (fgSubalgebraDiagram R)) : R →+* s.pt :=
  ((Subalgebra.iSupLift (fun A : {A : Subalgebra ℤ R // A.FG} ↦ A.1)
      (Subtype.mono_coe _).directed_le
      -- `by exact` postpones elaboration until the `ℤ`-algebra structure on `↥A.1` has
      -- been unified with the one on `(fgSubalgebraDiagram R).obj A`
      (fun A ↦ by exact (s.ι.app A).hom.toIntAlgHom)
      (fun A B h ↦ AlgHom.ext fun x ↦
        (ConcreteCategory.congr_hom (s.w (homOfLE (Subtype.coe_le_coe.mp h))) x).symm)
      ⊤ (Subalgebra.iSup_val_fg_eq_top ℤ R).ge).comp
    Subalgebra.topEquiv.symm.toAlgHom).toRingHom

@[simp]
lemma fgSubalgebraDesc_val (s : Cocone (fgSubalgebraDiagram R))
    (A : {A : Subalgebra ℤ R // A.FG}) (x : A.1) :
    fgSubalgebraDesc R s (A.1.val x) = (s.ι.app A).hom x := by
  have h : Subalgebra.topEquiv.symm.toAlgHom (A.1.val x)
      = Subalgebra.inclusion (le_top : A.1 ≤ ⊤) x := Subtype.ext rfl
  -- a terminal `simp` unfolds the coercion of `Subalgebra.topEquiv.symm` past the shape
  -- `Subalgebra.iSupLift_inclusion` expects, so the rewrites are spelled out
  simp only [fgSubalgebraDesc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, h,
    Subalgebra.iSupLift_inclusion]
  rfl

/-- A commutative ring is the filtered colimit of its finitely generated `ℤ`-subalgebras. -/
noncomputable def isColimitFgSubalgebraCocone : IsColimit (fgSubalgebraCocone R) where
  desc s := ofHom (fgSubalgebraDesc R s)
  fac s A := by
    ext x
    exact fgSubalgebraDesc_val R s A x
  uniq s m hm := by
    ext x
    have hx := Subalgebra.self_mem_fgAdjoinSingleton ℤ R x
    exact (ConcreteCategory.congr_hom (hm (Subalgebra.fgAdjoinSingleton ℤ R x)) ⟨x, hx⟩).trans
      (fgSubalgebraDesc_val R s (Subalgebra.fgAdjoinSingleton ℤ R x) ⟨x, hx⟩).symm

end CommRingCat
