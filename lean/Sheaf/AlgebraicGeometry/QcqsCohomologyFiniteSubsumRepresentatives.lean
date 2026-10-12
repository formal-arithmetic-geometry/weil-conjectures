/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Sheaf.AlgebraicGeometry.OpenModuleCohomologyDirectedColimit
import Mathlib.CategoryTheory.Limits.Constructions.Filtered

/-! # Finite-stage representatives for cohomology of a coproduct

Source: Stacks Project, Cohomology, Tags 01FF and 09J7
(blueprint: lem-weil-pbc-qcqs-cohomology-finite-subsum-representatives).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme

attribute [local instance] Abelian.hasFiniteBiproducts

open Classical in
/-- Every cohomology class of a coproduct is the image of a class in a finite partial
biproduct. This asserts only existence of a finite-stage representative; it does not
identify the cohomology of that finite stage with a direct sum of cohomology modules.

Source: Stacks Project, Cohomology, Lemma 01FF, applied to finite partial sums as in 09J7
(blueprint: lem-weil-pbc-qcqs-cohomology-finite-subsum-representatives).

Proof: The compact opens of a qcqs scheme form a basis stable under intersection, and
X itself is compact. The finite subsets of I form a nonempty directed preorder, including
the empty subset. For each finite J take the biproduct of the F j, with transition maps
induced by its inclusions. The coproduct S is the colimit of this diagram: compatible
maps from its finite stages are exactly families of maps from all F i. Apply the
surjectivity clause of Stacks 01FF at the whole space to this diagram. It yields a finite
J and a class y. Its structural map to S is the biproduct descent of the given inclusions,
by the coproduct universal property. This proves the displayed assertion. If I is empty,
the diagram has its single zero stage and both sides have zero cohomology; if X is empty,
the same assertion holds since global sections and their derived functors are zero.
At the top open, forgetting the global scalar action identifies module-valued
cohomology with open cohomology: both use the same injective module resolution,
and the exact forgetful functor preserves its homology. The identification is natural
in the sheaf, so it respects every structural map of the finite-subsum diagram.
For a larger index universe, first discard the zero summands. The remaining indices
form a u-small set: for each nonzero F i choose an open U and a nonzero section s.
Map i to (U, iota_i(s)) in the disjoint union of the section sets of S. This map is
injective, since the coproduct projection to F i is the identity on summand i and
zero on every other summand. That union is u-small. Reindex the nonzero summands
by a small equivalent type and apply the preceding argument. Transport its finite
subset back to I. Adding or removing zero summands preserves the coproduct and
finite partial biproducts, so the resulting representative has the required image. -/
theorem moduleCohomology_finiteSubsum_representative (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (I : Type v)
    (F : I → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (S : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ι : ∀ i : I, F i ⟶ S)
    (_hS : IsColimit (Cofan.mk S ι)) (p : ℕ)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj S) :
    ∃ (J : Finset I)
      (y : (RingedSpace.moduleCohomology X.toRingedSpace p).obj (⨁ (fun j : J ↦ F j))),
      ((RingedSpace.moduleCohomology X.toRingedSpace p).map
        (biproduct.desc (fun j : J ↦ ι j))).hom y = x := by
  sorry

end AlgebraicGeometry.Scheme
