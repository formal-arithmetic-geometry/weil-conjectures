/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.Ring.Colimits

/-!
# Dense opens and their section diagram

The colimit ring itself is `Scheme.rationalFunctionRing` in
`Sheaf.AlgebraicGeometry.RationalFunctionRing` (universe polymorphic).

Source: Stacks Project, Morphisms, Definitions 01RS, 01RT, 01RU and Lemma 01RV
(blueprint: def-sc-rational-functions).
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

/-- The dense open subsets of a scheme, ordered by inclusion (Stacks, Tag 01RS;
(blueprint: def-sc-rational-functions)). -/
def DenseOpens (X : Scheme) := {U : X.Opens // Dense (U : Set X)}

instance (X : Scheme) : PartialOrder (DenseOpens X) := inferInstanceAs
  (PartialOrder {U : X.Opens // Dense (U : Set X)})

/-- The intersection of two dense opens is dense (Stacks, Tag 01RS;
(blueprint: def-sc-rational-functions)). -/
def DenseOpens.inter {X : Scheme} (U V : DenseOpens X) : DenseOpens X :=
  ⟨U.val ⊓ V.val, by
    change Dense ((U.val : Set X) ∩ (V.val : Set X))
    exact U.property.inter_of_isOpen_left V.property U.val.isOpen⟩

/-- The inclusion of dense opens into all opens (Stacks, Tag 01RS;
(blueprint: def-sc-rational-functions)). -/
def denseOpensInclusion (X : Scheme) : DenseOpens X ⥤ X.Opens where
  obj U := U.val
  map f := homOfLE (leOfHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The section rings over dense opens with restriction maps (Stacks, Tag 01RV;
(blueprint: def-sc-rational-functions)). -/
def denseOpenSections (X : Scheme) : (DenseOpens X)ᵒᵖ ⥤ CommRingCat :=
  (denseOpensInclusion X).op ⋙ X.presheaf

end Scheme

end AlgebraicGeometry
