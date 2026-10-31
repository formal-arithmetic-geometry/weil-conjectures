/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Local finiteness of irreducible components of locally Noetherian schemes

Source: Stacks Project, Topology, Lemma 5.9.2, Tag 0052, applied on affine Noetherian
open neighbourhoods (blueprint: lem-sc-locnoeth-components-locally-finite).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Every point of a locally Noetherian scheme has an open neighbourhood meeting only
finitely many irreducible components.

Source: Stacks Project, Topology, Lemma 5.9.2, Tag 0052, applied on affine Noetherian
open neighbourhoods (blueprint: lem-sc-locnoeth-components-locally-finite).

Proof:
1. Fix a point `x`. Choose an affine open neighbourhood `U` whose ring of sections is
   Noetherian, using `pqf-def-locnoeth`.
2. The underlying space of `U` is Noetherian by
   `lem-sc-affine-noetherian-underlying-space`, so its irreducible components form a finite
   set by `lem-sc-noetherian-finite-irreducible-components` (Stacks Tag 0052).
3. By `lem-sc-components-open-injection`, each component of `X` meeting `U` restricts to a
   component of `U`, and distinct such components have distinct restrictions. Indeed, the
   nonempty open intersection with an irreducible component is dense in that component,
   so its closure in `X` recovers the original component. Hence the components meeting `U`
   inject into the finite set of components of `U`, and form a finite set.
4. This `U` is the required open neighbourhood. Since `x` was arbitrary, the components
   are locally finite. -/
theorem exists_open_finite_irreducibleComponents (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      {Z : Set X | Z ∈ irreducibleComponents X ∧ (Z ∩ (U : Set X)).Nonempty}.Finite := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x)
    (by trivial)
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : TopologicalSpace.NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
  let ι : U → X := Subtype.val
  refine ⟨U, hxU, Set.Finite.of_injOn (f := fun Z : Set X ↦ ι ⁻¹' Z) ?_ ?_
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := U))⟩
  · intro Z hZ
    apply preimage_mem_irreducibleComponents hZ.1 U.isOpen.isOpenEmbedding_subtypeVal
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hZ.2
  · intro Z hZ W hW hZW
    have hclosure (C : Set X)
        (hC : C ∈ irreducibleComponents X ∧ (C ∩ (U : Set X)).Nonempty) :
        closure (ι '' (ι ⁻¹' C)) = C := by
      apply closure_image_preimage_of_isPreirreducible _
        U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ _ hC.1.1.2
        (isClosed_of_mem_irreducibleComponents _ hC.1)
      obtain ⟨y, hyC, hyU⟩ := hC.2
      exact ⟨⟨y, hyU⟩, hyC⟩
    exact (hclosure Z hZ).symm.trans ((congrArg (fun C ↦ closure (ι '' C)) hZW).trans
      (hclosure W hW))

end AlgebraicGeometry
