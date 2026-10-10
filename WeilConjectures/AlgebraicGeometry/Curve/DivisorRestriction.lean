/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Restriction of divisors to an open subscheme

Let `i : C ⟶ Z` be an open immersion of Noetherian integral schemes, with `Z` a Jacobson space
(for instance `Z` of finite type over a field). Closed points of `C` are closed in `Z`, so a
divisor on `Z` restricts to a divisor on `C` by forgetting the points outside `C`. Restriction
is compatible with principal divisors, under the identification of the function fields, and a
divisor on `Z` whose restriction to `C` is principal is, up to a principal divisor, supported
on the closed points outside `C`. Hence `Cl(C)` is the quotient of `Cl(Z)` by the classes of
the closed points of `Z ∖ C`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.closedPointsMap`: the map on closed points.
- `AlgebraicGeometry.Scheme.Hom.functionFieldEquiv`: the isomorphism of function fields.
- `AlgebraicGeometry.Scheme.Divisor.restrict`: the restriction of divisors.

## Main statements

- `AlgebraicGeometry.Scheme.Divisor.restrict_div`: the restriction of `div g` is `div g`.
- `AlgebraicGeometry.Scheme.Divisor.mem_sup_closure_of_restrict_mem`: a divisor with principal
  restriction is a principal divisor plus a divisor supported outside `C`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {C Z : Scheme.{u}} (i : C ⟶ Z) [IsOpenImmersion i]

section ClosedPoints

variable [JacobsonSpace Z]

/-- An open immersion into a Jacobson scheme maps closed points to closed points. -/
lemma Hom.isClosed_singleton_apply {x : C} (hx : IsClosed ({x} : Set C)) :
    IsClosed ({i x} : Set Z) := by
  have h : x ∈ i ⁻¹' closedPoints Z := by
    rw [i.isOpenEmbedding.preimage_closedPoints]
    exact hx
  exact h

/-- The map on closed points induced by an open immersion into a Jacobson scheme. -/
def Hom.closedPointsMap (x : closedPoints C) : closedPoints Z :=
  ⟨i x, i.isClosed_singleton_apply x.2⟩

lemma Hom.closedPointsMap_injective : Function.Injective i.closedPointsMap :=
  fun _ _ h ↦ Subtype.ext (i.isOpenEmbedding.injective (congrArg Subtype.val h))

/-- The restriction `D|_C` of a divisor `D` on `Z` to an open subscheme `C`: it forgets the
closed points of `Z` outside `C`. -/
noncomputable def Divisor.restrict : Z.Divisor →+ C.Divisor :=
  Finsupp.comapDomain.addMonoidHom i.closedPointsMap_injective

@[simp]
lemma Divisor.restrict_apply (D : Z.Divisor) (x : closedPoints C) :
    Divisor.restrict i D x = D (i.closedPointsMap x) :=
  rfl

/-- The extension by zero of a divisor on `C` to `Z`. -/
noncomputable def Divisor.extend : C.Divisor →+ Z.Divisor :=
  Finsupp.mapDomain.addMonoidHom i.closedPointsMap

@[simp]
lemma Divisor.restrict_extend (D : C.Divisor) :
    Divisor.restrict i (Divisor.extend i D) = D :=
  Finsupp.comapDomain_mapDomain _ i.closedPointsMap_injective D

lemma Divisor.surjective_restrict : Function.Surjective (Divisor.restrict i) :=
  fun D ↦ ⟨Divisor.extend i D, Divisor.restrict_extend i D⟩

/-- A divisor whose restriction to `C` vanishes is supported on the closed points outside
`C`. -/
lemma Divisor.mem_closure_of_restrict_eq_zero (D : Z.Divisor) (hD : Divisor.restrict i D = 0) :
    D ∈ AddSubgroup.closure (Set.range fun P : {P : closedPoints Z // P.1 ∉ Set.range i} ↦
      Finsupp.single P.1 (1 : ℤ)) := by
  classical
  rw [← Finsupp.sum_single D]
  refine AddSubgroup.sum_mem _ fun P _ ↦ ?_
  by_cases hP : P.1 ∈ Set.range i
  · obtain ⟨x, hx⟩ := hP
    have h : D P = 0 := by
      have := congrArg (fun E : C.Divisor ↦ E ⟨x, by
        have h : x ∈ i ⁻¹' closedPoints Z := by
          change i x ∈ closedPoints Z
          rw [hx]
          exact P.2
        rwa [i.isOpenEmbedding.preimage_closedPoints] at h⟩) hD
      simp only [restrict_apply, Finsupp.coe_zero, Pi.zero_apply] at this
      rwa [show i.closedPointsMap _ = P from Subtype.ext (by exact hx)] at this
    rw [h, Finsupp.single_zero]
    exact zero_mem _
  · rw [← Finsupp.smul_single_one, ← zsmul_eq_smul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure
      (Set.mem_range_self (⟨P, hP⟩ : {P : closedPoints Z // P.1 ∉ Set.range i}))) _

end ClosedPoints

section FunctionField

variable [IsIntegral C] [IsIntegral Z]

lemma Hom.genericPoint_eq : genericPoint Z = i (genericPoint C) :=
  (genericPoint_eq_of_isOpenImmersion i).symm

/-- The isomorphism `k(Z) ≅ k(C)` of function fields induced by an open immersion `C ⟶ Z` of
integral schemes. -/
noncomputable def Hom.functionFieldEquiv : Z.functionField ≃+* C.functionField :=
  (Z.presheaf.stalkCongr (.of_eq i.genericPoint_eq) ≪≫
    asIso (i.stalkMap (genericPoint C))).commRingCatIsoToRingEquiv

lemma Hom.functionFieldEquiv_algebraMap (x : C) (s : Z.presheaf.stalk (i x)) :
    i.functionFieldEquiv (algebraMap (Z.presheaf.stalk (i x)) Z.functionField s) =
      algebraMap (C.presheaf.stalk x) C.functionField (i.stalkMap x s) := by
  change (Z.presheaf.stalkSpecializes ((genericPoint_spec Z).specializes trivial) ≫
    Z.presheaf.stalkSpecializes (Inseparable.of_eq i.genericPoint_eq).specializes' ≫
    i.stalkMap (genericPoint C)) s =
    (i.stalkMap x ≫ C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)) s
  rw [TopCat.Presheaf.stalkSpecializes_comp_assoc, ← Hom.stalkSpecializes_stalkMap]

variable [IsNoetherian C] [IsNoetherian Z] [JacobsonSpace Z]

/-- **Restriction of a principal divisor.** The restriction to `C` of the divisor of a rational
function `g` on `Z` is the divisor of `g` viewed as a rational function on `C`. -/
lemma Divisor.restrict_div (g : Additive Z.functionFieldˣ) :
    Divisor.restrict i (Z.div g) =
      C.div (.ofMul (Units.map (i.functionFieldEquiv : Z.functionField →* C.functionField)
        g.toMul)) := by
  ext x
  simp only [restrict_apply, div_apply, toMul_ofMul, Units.coe_map, MonoidHom.coe_coe]
  exact (ord_map_of_isOpenImmersion i x.1 (i.functionFieldEquiv : Z.functionField →+*
    C.functionField) (i.functionFieldEquiv_algebraMap x.1) _).symm

lemma Divisor.restrict_principalDivisors :
    Z.principalDivisors.map (Divisor.restrict i) ≤ C.principalDivisors := by
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  exact ⟨_, (Divisor.restrict_div i g).symm⟩

/-- **Divisors with principal restriction.** If the restriction of a divisor `D` on `Z` to `C`
is principal, then `D` is a principal divisor plus a divisor supported on the closed points of
`Z` outside `C`. -/
lemma Divisor.mem_sup_closure_of_restrict_mem (D : Z.Divisor)
    (hD : Divisor.restrict i D ∈ C.principalDivisors) :
    D ∈ Z.principalDivisors ⊔ AddSubgroup.closure
      (Set.range fun P : {P : closedPoints Z // P.1 ∉ Set.range i} ↦
        Finsupp.single P.1 (1 : ℤ)) := by
  obtain ⟨h, hh⟩ := hD
  let g : Additive Z.functionFieldˣ :=
    .ofMul (Units.map (i.functionFieldEquiv.symm : C.functionField →* Z.functionField) h.toMul)
  have hg : Divisor.restrict i (Z.div g) = Divisor.restrict i D := by
    rw [Divisor.restrict_div, ← hh]
    congr 1
    ext
    simp [g]
  have hrest : Divisor.restrict i (D - Z.div g) = 0 := by
    rw [map_sub, hg, sub_self]
  rw [show D = Z.div g + (D - Z.div g) by abel]
  exact AddSubgroup.add_mem_sup ⟨g, rfl⟩ (Divisor.mem_closure_of_restrict_eq_zero i _ hrest)

end FunctionField

end AlgebraicGeometry.Scheme
