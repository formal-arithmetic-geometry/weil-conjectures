/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionLimit

/-!
# Torsion cohomological dimension through finitely generated subalgebras

An `L`-algebra `S` is the filtered union of its finitely generated `L`-subalgebras `A`, so that
`Spec S` is the limit of the affine schemes `Spec A`, with affine transition maps. A uniform bound
`cd_tor(Spec A) ≤ n` therefore passes to `Spec S`
(`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.spec_of_forall_fg`), by
`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.of_isLimit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

namespace SubalgebraLimit

variable {L : Type u} [CommRing L] (S : Type u) [CommRing S] [Algebra L S]

instance : IsDirected {A : Subalgebra L S // A.FG} (· ≤ ·) :=
  ⟨fun A B ↦ ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩,
    le_sup_left (a := A.1), le_sup_right (a := A.1)⟩⟩

instance : Nonempty {A : Subalgebra L S // A.FG} := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

/-- The diagram of the finitely generated `L`-subalgebras of `S`, as commutative rings. -/
noncomputable def ringDiagram : {A : Subalgebra L S // A.FG} ⥤ CommRingCat.{u} where
  obj A := .of A.1
  map f := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `S` as a cocone over its finitely generated `L`-subalgebras. -/
noncomputable def ringCocone : Cocone (ringDiagram (L := L) S) where
  pt := .of S
  ι := { app A := CommRingCat.ofHom A.1.val.toRingHom }

/-- `S` is the filtered colimit of its finitely generated `L`-subalgebras. -/
noncomputable def isColimitRingCocone : IsColimit (ringCocone (L := L) S) := by
  have : ReflectsFilteredColimits (CategoryTheory.forget CommRingCat.{u}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  refine isColimitOfReflects (CategoryTheory.forget _)
    (Types.FilteredColimit.isColimitOf _ _ ?_ ?_)
  · intro x
    exact ⟨⟨Algebra.adjoin L {x}, ⟨{x}, by rw [Finset.coe_singleton]⟩⟩,
      ⟨x, Algebra.subset_adjoin rfl⟩, rfl⟩
  · intro A B a b hab
    refine ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩, homOfLE (le_sup_left (b := B.1)),
      homOfLE (le_sup_right (a := A.1)), ?_⟩
    exact Subtype.ext hab

/-- The diagram of affine schemes `Spec A` over the finitely generated subalgebras `A`. -/
noncomputable abbrev schemeDiagram : {A : Subalgebra L S // A.FG}ᵒᵖ ⥤ Scheme.{u} :=
  (ringDiagram (L := L) S).op ⋙ Scheme.Spec

/-- The cone over `A ↦ Spec A` with point `Spec S`. -/
noncomputable def schemeCone : Cone (schemeDiagram (L := L) S) :=
  Scheme.Spec.mapCone (ringCocone (L := L) S).op

/-- `Spec S` is the limit of the `Spec A`. -/
noncomputable def isLimitSchemeCone : IsLimit (schemeCone (L := L) S) :=
  isLimitOfPreserves Scheme.Spec (isColimitRingCocone (L := L) S).op

end SubalgebraLimit

open SubalgebraLimit in
/-- If `cd_tor(Spec A) ≤ n` for every finitely generated `L`-subalgebra `A` of an `L`-algebra
`S`, then `cd_tor(Spec S) ≤ n`: `Spec S` is the limit of the `Spec A`. -/
theorem HasTorsionCohomologicalDimensionLE.spec_of_forall_fg {L : Type u} [CommRing L]
    (S : Type u) [CommRing S] [Algebra L S] {n : ℕ}
    (h : ∀ A : Subalgebra L S, A.FG → (Spec (.of A)).HasTorsionCohomologicalDimensionLE n) :
    (Spec (.of S)).HasTorsionCohomologicalDimensionLE n := by
  have : ∀ i, CompactSpace ((schemeDiagram (L := L) S).obj i) :=
    fun i ↦ inferInstanceAs (CompactSpace (Spec (.of i.unop.1)))
  have : ∀ i, QuasiSeparatedSpace ((schemeDiagram (L := L) S).obj i) :=
    fun i ↦ inferInstanceAs (QuasiSeparatedSpace (Spec (.of i.unop.1)))
  have : ∀ {i j} (g : i ⟶ j), IsAffineHom ((schemeDiagram (L := L) S).map g) :=
    fun g ↦ inferInstanceAs (IsAffineHom (Spec.map ((ringDiagram (L := L) S).map g.unop)))
  exact HasTorsionCohomologicalDimensionLE.of_isLimit (n := n) _ _
    (isLimitSchemeCone (L := L) S) fun i ↦ (h i.unop.1 i.unop.2 :)

end AlgebraicGeometry.Scheme
