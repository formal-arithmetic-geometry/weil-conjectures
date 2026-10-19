/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.Topology.Homeomorph.Defs
import Sheaf.AlgebraicGeometry.ProEtaleSheafDirectImageTopologicalInvariance
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Topological invariance of the small pro-etale topos

Source: Stacks Project, Tag 09AB, `proetale-lemma-thickening`; Tag 04DF identifies
universal homeomorphisms with integral, universally injective, surjective morphisms
(blueprint: lem-trf-proetale-topological-invariance).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Universal homeomorphisms induce equivalences of the small pro-etale topoi of sets.
Both equivalence assertions concern the recorded inverse and direct image, and the last
clauses assert invertibility of the components of their specified adjunction.
Source: Stacks Project, Tag 09AB, `proetale-lemma-thickening`, with Tag 04DF
(blueprint: lem-trf-proetale-topological-invariance).

Proof: The direct-image topological-invariance theorem follows the affine-basis
argument of Tag 09AB. Over an affine target, descend maps into the etale terms of
affine ind-etale presentations through the universal homeomorphism, and combine them
using the limit universal property. Descend an entire presentation with the inverse
etale equivalence to obtain essential surjectivity. Base change preserves and reflects
finite jointly surjective basis families, giving a dense-subsite comparison and hence
equivalence of the actual direct image in the affine case. Weakly etale base change
and the unit and counit mate identities identify the local adjunctions over an affine
open cover; restriction to the cover detects isomorphisms, giving the global result.
Finally, the general adjunction equivalence API gives equivalence of the inverse image
and invertibility of the specified unit and counit components. -/
theorem proEtaleSheaf_topological_invariance {X Y : Scheme.{u}} (r : X ⟶ Y)
    (hr : (topologically IsHomeomorph).universally r) :
    (proEtaleSheafInverseImage r (Type (u + 1))).IsEquivalence ∧
      (proEtaleSheafDirectImage r (Type (u + 1))).IsEquivalence ∧
      (∀ F : Sheaf (ProEt.topology Y) (Type (u + 1)),
        IsIso ((proEtaleSheafAdjunction r (Type (u + 1))).unit.app F)) ∧
      (∀ G : Sheaf (ProEt.topology X) (Type (u + 1)),
        IsIso ((proEtaleSheafAdjunction r (Type (u + 1))).counit.app G)) := by
  have hR := proEtaleSheafDirectImage_topological_invariance r hr
  let : (proEtaleSheafDirectImage r (Type (u + 1))).IsEquivalence := hR
  have hL : (proEtaleSheafInverseImage r (Type (u + 1))).IsEquivalence :=
    (proEtaleSheafAdjunction r (Type (u + 1))).isEquivalence_left_of_isEquivalence_right
  refine ⟨hL, hR, ?_, ?_⟩
  · intro F
    infer_instance
  · intro G
    infer_instance

end AlgebraicGeometry.Scheme
