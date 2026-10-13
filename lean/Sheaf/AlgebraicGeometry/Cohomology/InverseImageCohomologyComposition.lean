/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.Cohomology.InverseImageCoefficientComposition
import Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison

/-! # Composition of exact inverse-image cohomology maps

Source: Stacks Project, Tag 01F7, cohomology-equation-functorial.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Inverse-image maps on cohomology compose under the canonical comparison.
Source: Stacks Project, Tag 01F7, cohomology-equation-functorial;
Mathlib's exact-functor action on Ext and uniqueness of left-adjoint comparisons.
(blueprint: lem-pbc-inverse-image-cohomology-composition)

Proof: The constant integer comparison for the composite is the comparison
for g followed by the inverse image under g of the comparison for f, then
invImageComp g f evaluated at the constant integer sheaf. This follows by
applying the composite adjunction: both comparisons are adjoint to the same
constant sections map, so uniqueness of adjuncts identifies them. Expand
H.mapFunctor as precomposition by the constant comparison followed by the
exact-functor action on Ext. The exact-functor action preserves composition
and degree-zero morphisms. Its action for a composite functor agrees with
the successive actions; naturality in the natural isomorphism invImageComp
identifies the composite action with the action of inverse image along g ≫ f.
Associativity of Ext composition and the constant comparison identity give
the displayed equality. No coefficient morphisms occur here. This works for
any abelian sheaf, including zero, every nonnegative degree, identities and
empty schemes.
-/
theorem inverseImageCohomology_comp {X Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (f : Y ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) (x : F.H n) :
    Sheaf.H.map ((invImageComp g f).hom.app F) n
        (Sheaf.H.mapFunctor (invImage g) (constIso g).symm ((invImage f).obj F) n
          (Sheaf.H.mapFunctor (invImage f) (constIso f).symm F n x)) =
      Sheaf.H.mapFunctor (invImage (g ≫ f)) (constIso (g ≫ f)).symm F n x := by sorry

end AlgebraicGeometry.Scheme.Modules
