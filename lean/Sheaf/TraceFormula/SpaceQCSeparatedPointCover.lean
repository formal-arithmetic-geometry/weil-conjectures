/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-!
# Quasi-compactness and separation for an actual jointly surjective etale family

Source: Stacks Project, Morphisms of Spaces, Tags 03KG and 03KM
(blueprint: lem-trf-space-qc-separated-etale-local).

The existing geometric predicates are retained. The family condition is surjectivity
on points, allowing a field extension, rather than objectwise surjectivity of sections.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Quasi-compactness and separatedness are local on the target for jointly surjective
etale scheme charts. Joint surjectivity is the existing point-class condition.
Source: Stacks, Morphisms of Spaces, Tags 03KG and 03KM
(blueprint: lem-trf-space-qc-separated-etale-local).

Proof:
1. If `f` has the two properties, transitivity of fibre products identifies every
   affine scheme test of its base change with a scheme test of `f`. The same
   quasi-compact atlas works, and base change preserves each closed diagonal test
   by lem-weil-pbc-closed-immersion-base-change.
2. Conversely, base change the diagonal along the target charts. Its local scheme
   tests are the closed diagonals of the local morphisms. The diagonal is
   representable, so lem-trf-space-closed-immersion-cover-descent descends these
   closed immersions, giving separatedness.
3. For an affine test `Z → Y`, lem-trf-space-fibre-products-etale-covers gives a
   jointly surjective etale scheme cover of `Z`. Apply
   lem-weil-pbc-etale-covering-affine-refinement to obtain finitely many affine
   opens of members that still cover `Z`. Quasi-compactness of each local morphism
   gives a quasi-compact scheme atlas after this affine test.
4. By lem-trf-space-finite-qc-atlas-assembly the finite coproduct of those atlases
   is a quasi-compact scheme with a surjective etale map to the original test
   fibre product. This proves quasi-compactness. Combine with step 2; step 1 gives
   the reverse implication. Empty targets and empty covers are included. -/
theorem quasiCompact_separated_etaleLocal_pointCover
    {S : Scheme.{u}} (X Y : AlgebraicSpace S) (f : X ⟶ Y) (I : Type v)
    (Yᵢ : I → Over S) (a : ∀ i : I, yoneda.obj (Yᵢ i) ⟶ Y.obj.obj)
    (he : ∀ i : I, IsEtale (a i)) (hs : IsJointlySurjective a) :
    (IsQuasiCompactPresheafMap f.hom.hom ∧ IsSeparatedPresheafMap f.hom.hom) ↔
      ∀ i : I, IsQuasiCompactPresheafMap (pullback.snd f.hom.hom (a i)) ∧
        IsSeparatedPresheafMap (pullback.snd f.hom.hom (a i)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
