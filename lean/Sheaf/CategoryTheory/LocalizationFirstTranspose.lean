/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Counit normalization of the first localization-triangle component

Source: Weil conjectures blueprint, `sec-six-functors/sk-prop-sf-biduality-general/`
`lem-coef-finite-closed-shriek.md`, proof paragraph 2; Stacks Project, Tags 0145, 014A
and 0037 (blueprint: lem-coef-localization-first-transpose).
-/

@[expose] public section

universe uTA uTB uCA uCB vTA vTB vCA vCB

set_option autoImplicit false

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true in
/-- The first component of the comparison of localization triangles is invertible and
is the unique map normalized by the exceptional counit. It is the image of the prescribed
adjunction transpose.

Source: blueprint, `lem-coef-finite-closed-shriek.md`, proof paragraph 2; Stacks Project,
Tags 0145, 014A and 0037 (blueprint: lem-coef-localization-first-transpose).

Proof plan:
1. Exactness of `SX` makes its image of the first triangle distinguished, with the
connecting arrow transported by `SX.commShiftIso`. Rotate both triangles by TR2 and
apply TR3 to the identity on `SX.obj M` and `d.hom`, using `hd`. This gives a map
between the shifts of their first vertices. Full faithfulness of the shift gives its
unique unshifted map `a`. Additivity and faithfulness of shift give the first square,
so `(a, 1, d)` is a morphism of the original triangles. This uses
[def-weil-triangulated-category].
2. Its middle and third components are isomorphisms. By
[lem-sf-triangle-morphism-iso], so is its first component; no octahedral axiom is needed.
3. Write `P = SZ.obj (JA.obj M)`, `V = SX.obj M`, and `c0 = c.app (JA.obj M)`.
For any `t` with `t ≫ adjB.counit.app V = SX.map (adjA.counit.app M)`, fullness of
`IB` writes `c0.inv ≫ t = IB.map f`. Its counit composite is
`c0.inv ≫ SX.map (adjA.counit.app M)`. The adjunct-counit equivalence of
[lem-weil-pbc-adjunct-counit-identity] says that `f` is exactly the prescribed transpose.
Thus `t` equals `c0.hom` followed by the image of that transpose. This gives both the
formula for `a` and uniqueness among all counit-normalized maps. The first square
of any triangle morphism with identity middle component is the same counit equation,
so its first component is this same invertible map.
-/
theorem localization_first_transpose
    {TA : Type uTA} {TB : Type uTB} {CA : Type uCA} {CB : Type uCB}
    [Category.{vTA} TA] [Category.{vTB} TB] [Category.{vCA} CA] [Category.{vCB} CB]
    [Preadditive TA] [HasZeroObject TA] [HasShift TA ℤ]
    [∀ n : ℤ, (shiftFunctor TA n).Additive] [Pretriangulated TA]
    [Preadditive TB] [HasZeroObject TB] [HasShift TB ℤ]
    [∀ n : ℤ, (shiftFunctor TB n).Additive] [Pretriangulated TB]
    (IA : CA ⥤ TA) (JA : TA ⥤ CA) (adjA : IA ⊣ JA)
    (IB : CB ⥤ TB) (JB : TB ⥤ CB) (adjB : IB ⊣ JB) [IB.Full] [IB.Faithful]
    (SX : TA ⥤ TB) [SX.CommShift ℤ] [SX.IsTriangulated]
    (SZ : CA ⥤ CB) (c : IA ⋙ SX ≅ SZ ⋙ IB) (M LA : TA) (LB : TB)
    (ηA : M ⟶ LA) (δA : LA ⟶ (IA.obj (JA.obj M))⟦(1 : ℤ)⟧)
    (hA : Triangle.mk (adjA.counit.app M) ηA δA ∈ distTriang TA)
    (ηB : SX.obj M ⟶ LB) (δB : LB ⟶ (IB.obj (JB.obj (SX.obj M)))⟦(1 : ℤ)⟧)
    (hB : Triangle.mk (adjB.counit.app (SX.obj M)) ηB δB ∈ distTriang TB)
    (d : SX.obj LA ≅ LB) (hd : SX.map ηA ≫ d.hom = ηB) :
    ∃ φ : SX.mapTriangle.obj (Triangle.mk (adjA.counit.app M) ηA δA) ⟶
        Triangle.mk (adjB.counit.app (SX.obj M)) ηB δB,
      φ.hom₂ = 𝟙 (SX.obj M) ∧
      φ.hom₃ = d.hom ∧
      IsIso φ.hom₁ ∧
      φ.hom₁ ≫ adjB.counit.app (SX.obj M) = SX.map (adjA.counit.app M) ∧
      (∀ a : SX.obj (IA.obj (JA.obj M)) ⟶ IB.obj (JB.obj (SX.obj M)),
        a ≫ adjB.counit.app (SX.obj M) = SX.map (adjA.counit.app M) → a = φ.hom₁) ∧
      (c.app (JA.obj M)).inv ≫ φ.hom₁ =
        IB.map ((adjB.homEquiv (SZ.obj (JA.obj M)) (SX.obj M))
          ((c.app (JA.obj M)).inv ≫ SX.map (adjA.counit.app M))) := by
  let T := SX.mapTriangle.obj (Triangle.mk (adjA.counit.app M) ηA δA)
  let T' := Triangle.mk (adjB.counit.app (SX.obj M)) ηB δB
  have hT : T ∈ distTriang TB := SX.map_distinguished _ hA
  obtain ⟨a, ha₁, ha₃⟩ := complete_distinguished_triangle_morphism₁ T T' hT hB
    (𝟙 (SX.obj M)) d.hom (by simpa [T, T', Functor.mapTriangle] using hd)
  let φ : T ⟶ T' :=
    { hom₁ := a
      hom₂ := 𝟙 (SX.obj M)
      hom₃ := d.hom
      comm₁ := ha₁
      comm₂ := by simpa [T, T', Functor.mapTriangle] using hd
      comm₃ := ha₃ }
  have ha : a ≫ adjB.counit.app (SX.obj M) = SX.map (adjA.counit.app M) := by
    simpa [T, T', Functor.mapTriangle] using ha₁.symm
  have htranspose (t : SX.obj (IA.obj (JA.obj M)) ⟶ IB.obj (JB.obj (SX.obj M)))
      (ht : t ≫ adjB.counit.app (SX.obj M) = SX.map (adjA.counit.app M)) :
      (c.app (JA.obj M)).inv ≫ t =
        IB.map ((adjB.homEquiv (SZ.obj (JA.obj M)) (SX.obj M))
          ((c.app (JA.obj M)).inv ≫ SX.map (adjA.counit.app M))) := by
    have hf : IB.preimage ((c.app (JA.obj M)).inv ≫ t) =
        (adjB.homEquiv (SZ.obj (JA.obj M)) (SX.obj M))
          ((c.app (JA.obj M)).inv ≫ SX.map (adjA.counit.app M)) := by
      rw [Adjunction.homEquiv_unit]
      apply (adjB.eq_unit_comp_map_iff _ _).2
      rw [IB.map_preimage, Category.assoc, ht]
    rw [← hf, IB.map_preimage]
  refine ⟨φ, rfl, rfl, ?_, ha, ?_, htranspose a ha⟩
  · exact isIso₁_of_isIso₂₃ φ hT hB (by dsimp [φ, T, T', Functor.mapTriangle]; infer_instance)
      (by dsimp [φ, T, T', Functor.mapTriangle]; infer_instance)
  · intro t ht
    apply (cancel_epi (c.app (JA.obj M)).inv).1
    exact (htranspose t ht).trans (htranspose a ha).symm

end CategoryTheory
