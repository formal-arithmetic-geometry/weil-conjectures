/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso

/-!
# K-flatness is triangulated in the homotopy category

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, proof, first three
sentences, "the K-flat complexes form a left derivability structure"; supporting upstream
declarations `HomotopyCategory.kFlat_quotient_obj_iff` and the `ContainsZero`,
`IsStableUnderShift` and `IsTriangulated` instances of
`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`
(blueprint: lem-sfb-kflat-homotopy-triangulated).

This Q100 handoff preserves the already reviewed declaration and its canonical interfaces.

The statement has two clauses. First, two-sided total-tensor K-flatness is invariant under
cochain homotopy equivalence, so the property `𝒫(qL)` that `L` is K-flat is well defined on
the homotopy category. Second, the full subcategory of the homotopy category defined by
`𝒫`, written as the property of being isomorphic to `qL` for a K-flat `L`, is triangulated.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

/--
K-flatness is invariant under cochain homotopy equivalence, and K-flat complexes define a
triangulated property on the homotopy category.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, proof, first three
sentences; upstream `HomotopyCategory.kFlat_quotient_obj_iff` and the `ContainsZero`,
`IsStableUnderShift` and `IsTriangulated` instances in
`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`
(blueprint: lem-sfb-kflat-homotopy-triangulated).

The node records no proof steps. The intended proof is the following.
1. A homotopy equivalence `L ≃ L'` gives, after total tensoring with a fixed complex on
   either side, a homotopy equivalence; homotopy equivalences are quasi-isomorphisms, so by
   two out of three for quasi-isomorphisms `L` is K-flat iff `L'` is. This is the first
   clause, and it makes `𝒫(qL)` well defined and closed under isomorphisms in `K(A)`.
2. The zero complex is K-flat, since its total tensor with any complex is zero (additivity
   of the tensor in each variable).
3. Total tensoring commutes with shifts up to isomorphism, and shifts preserve
   quasi-isomorphisms, so `𝒫` is stable under every integer shift.
4. A complex `P` is K-flat iff `P ⊗ Z` and `Z ⊗ P` are acyclic for every acyclic
   complex `Z`. The forward implication applies the definition to `0 → Z`. Conversely,
   a map is a quasi-isomorphism iff its mapping cone is acyclic, and total tensoring
   commutes with mapping cones up to the signed canonical isomorphisms.
   For K-flat `L` and `L'` and a map `f : L ⟶ L'`, tensor its cone triangle with an
   acyclic `Z` on either side. The first two vertices are acyclic, so the third is
   acyclic by the cone homology sequence. The characterization gives K-flatness of
   `mappingCone f`.
5. Every distinguished triangle of `K(A)` is isomorphic to a mapping-cone triangle.
   Step 1 transports the property along these isomorphisms. Step 4 gives closure at
   the third vertex; rotating triangles and using step 3 gives closure at either
   other vertex. Together with step 2, this gives the asserted triangulated property.
-/
theorem kFlat_homotopy_isTriangulated
    {A : Type u} [Category.{v, u} A] [Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasColimits A]
    [∀ (X : A), PreservesColimits (tensorLeft X)]
    [∀ (X : A), PreservesColimits (tensorRight X)] :
    (∀ {L L' : CochainComplex A ℤ}, HomotopyEquiv L L' →
      L.IsKFlatForTotalTensor → L'.IsKFlatForTotalTensor) ∧
    ObjectProperty.IsTriangulated
      (fun K : HomotopyCategory A (.up ℤ) =>
        ∃ (L : CochainComplex A ℤ),
          Nonempty (K ≅ (HomotopyCategory.quotient A (.up ℤ)).obj L) ∧
            L.IsKFlatForTotalTensor) := by
  sorry

end CategoryTheory
