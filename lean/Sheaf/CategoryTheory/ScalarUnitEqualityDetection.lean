/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Equality detection by a scalar telescope of an adjunction unit

Source: the Weil conjectures blueprint, `main-20261015`, chapter `sec-proetale-coefficients`,
unit `sk-thm-sfb-rationalization-comparison`, proof of `thm-sfb-extend-scalars-localization`,
Full faithfulness (blueprint: lem-sfb-scalar-unit-equality-detection).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- If postcomposition with the legs of a scalar telescope with zeroth leg the adjunction
unit exhibits the corresponding Hom group as a colimit, equality under the left adjoint
is detected after multiplication by a finite scalar power.

Here `t` is the natural transformation of legs of the cocone with fixed vertex `U(F(B))`;
`Cocone.mk _ t` is that cocone. Its Hom image is taken in abelian groups, using the
preadditive coyoneda functor. The indexing category is the small ordered category `ℕ`.

Source: the Weil conjectures blueprint, `main-20261015`, proof of
`thm-sfb-extend-scalars-localization`, Full faithfulness
(blueprint: lem-sfb-scalar-unit-equality-detection).

Proof: (1) Naturality of the unit and `F.map f = F.map g` give
`f ≫ adj.unit.app B = g ≫ adj.unit.app B`, hence equality of the zeroth Hom-cocone images
by `hzero`. No additivity of either adjoint is used.
(2) Preadditivity makes postcomposition additive and identifies the successor maps of
this Hom diagram with multiplication by `a`. Its cocone is a colimit by `hcolimit`.
The ordered category `ℕ` is filtered (upper bounds are maxima and parallel arrows agree).
The forgetful functor from abelian groups preserves filtered colimits, by
`AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits`
(lem-weil-pbc-abelian-groups-forget-filtered-colimits); thus the same maps give a colimit
of sets. If necessary, replace `ℕ` by its small copy in the Hom universe.
(3) Apply `Types.FilteredColimit.isColimit_eq_iff'`
(lem-weil-pbc-filtered-colimit-sets-elementwise, clause (3)) to the two elements at index
zero. They agree after the map from zero to some `n`.
(4) Induction on `n` computes that transition as multiplication by `a ^ n`: at zero it is
the identity, and each successor multiplies by `a`. Substitution gives the conclusion.
This also covers `a = 0`, `a = 1`, and `n = 0`. -/
theorem scalar_unit_equality_detection
    {A : Type uA} [Category.{vA} A] [Preadditive A]
    {C : Type uB} [Category.{vB} C]
    {F : A ⥤ C} {U : C ⥤ A} (adj : F ⊣ U) (a : ℕ) (K B : A)
    (t : Functor.ofSequence (fun _ : ℕ ↦ a • 𝟙 B) ⟶
      (Functor.const ℕ).obj (U.obj (F.obj B)))
    (hzero : t.app 0 = adj.unit.app B)
    (hcolimit : IsColimit ((preadditiveCoyoneda.obj (op K)).mapCocone
      (Cocone.mk (U.obj (F.obj B)) t)))
    (f g : K ⟶ B) (hfg : F.map f = F.map g) :
    ∃ n : ℕ, a ^ n • f = a ^ n • g := by
  sorry

end CategoryTheory
