/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Homology descent of the canonical localized chain-map comparison

Source: Stacks Project, Tag 0A8X, Hom complexes; Equation 0A8Y (degree zero)
(blueprint: lem-pur-localized-hom-complex-homology-aux).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

/-- The canonical cocycle equivalence descends to homology and homotopy classes.
The component formula is essential: an arbitrary equivalence of sets need not
respect boundaries.
Source: Stacks Project, Tag 0A8X (Hom complexes), Equation 0A8Y
(blueprint: lem-pur-localized-hom-complex-homology-aux).

Proof: identify every degree n section with a family of localized maps using
the sectionwise product cone of `homComplex_exists`. Under this identification,
the differential from degree -1 to degree 0 sends h to d_I h + h d_L.
The assumed component formula identifies e with the degree-zero chain-map
construction. Consequently, for cycles z and z', their images under e are
homotopic if and only if their difference is a boundary: a degree -1 section
yields a homotopy by its components, and the components of any homotopy assemble
into such a section by the same product universal property. The formula for e
also makes it additive, since all projections and the cycle inclusion are linear
and chain maps are determined by their components. The homology projection in
abelian groups is surjective, with kernel the boundaries. The quotient functor
to the homotopy category is full and identifies exactly homotopic chain maps.
Define a on a homology class represented by z to be q.map (e z). The established
boundary criterion makes this well defined and injective. Fullness of q and
surjectivity of e make it surjective. Take the equivalence associated to this
bijection; its defining formula is the asserted compatibility on representatives.
For zero complexes both quotients are singletons; with zero differential there
are no nonzero boundaries, as the same criterion requires. -/
theorem localizedHomComplex_homology_aux
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    (L I : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (hzero : Functor.PreservesZeroMorphisms
      (SheafOfModules.overFunctor.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U))
    (e : let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
      let H := homComplex (R := R) L I
      let S := ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
        forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj H
      letI := hzero
      let res := (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex
        (ComplexShape.up ℤ)
      S.cycles 0 ≃ (res.obj L ⟶ res.obj I)) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let H := homComplex (R := R) L I
    let π := Classical.choose (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
    let S := ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj H
    letI := hzero
    let res : CochainComplex (SheafOfModules.{max u v} R₀) ℤ ⥤
        CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ :=
      (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex (ComplexShape.up ℤ)
    let q := HomotopyCategory.quotient
      (SheafOfModules.{max u v} (R₀.over U)) (ComplexShape.up ℤ)
    (∀ (z : S.cycles 0) (p : ℤ) (W : (Over U)ᵒᵖ),
      ((e z).f p).val.app W =
        (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) →
    ∃ a : S.homology 0 ≃ (q.obj (res.obj L) ⟶ q.obj (res.obj I)),
      ∀ z : S.cycles 0, a (S.homologyπ 0 z) = q.map (e z) := by sorry

end CategoryTheory
