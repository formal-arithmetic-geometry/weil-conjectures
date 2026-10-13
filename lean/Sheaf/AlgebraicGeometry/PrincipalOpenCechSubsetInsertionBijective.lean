/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion

/-! # Properties of explicit subset insertion

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

/-- The explicit finite sum of subset insertions is bijective.

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
(blueprint: lem-sc-principal-open-cech-subset-insertion-bijective).

Proof: In column p, the extension by zero identifies the nonnegative component with
sections on increasing (p+1)-tuples. Increasing enumeration bijects these tuples with
subsets of cardinality p+1. Section transport is an additive isomorphism on each
coordinate. Negative columns are zero, and columns p >= r have no tuples and are zero.
On each total diagonal the only nonzero summands are therefore the finitely many
columns 0 <= p < r. The universal coproduct is the finite direct sum of these groups,
which is their finite product. The map defined by summing the summand insertions is
this product-to-coproduct isomorphism. Its inverse reads each tuple coordinate after
projecting to its column and applies inverse section transport. These maps are inverse
on every summand and coordinate. For r=0 all families are empty and both groups are zero.
Repeated opens retain different indices, and all arguments apply to zero section groups. -/
theorem principalSubsetInsertion_bijective
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ) :
    Function.Bijective (principalSubsetInsertion A r f J n) := by sorry

/-- The inverse is determined uniquely by the bijective explicit insertion map. -/
noncomputable def principalSubsetInsertionIso
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ) :
    principalSubsetCoordinates A r f J n ≅ (principalSubsetTotal A r f J).X n :=
  (AddEquiv.ofBijective (principalSubsetInsertion A r f J n).hom
    (principalSubsetInsertion_bijective A r f J n)).toAddCommGrpIso

end AlgebraicGeometry
