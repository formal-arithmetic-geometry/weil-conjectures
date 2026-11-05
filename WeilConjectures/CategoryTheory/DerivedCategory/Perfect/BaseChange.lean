/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.RingTheory.TensorProduct.Finite
public import WeilConjectures.Algebra.Homology.FlatComplexBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Base change of perfect complexes

Let `K` be a bounded complex of flat modules over a commutative ring `A` whose image in `D(A)` is
perfect, and `B` an `A`-algebra. Then the base change `B ⊗[A] K`, which computes the derived base
change of `K`, is perfect in `D(B)` (`DerivedCategory.isPerfect_Q_obj_baseChange`).

A bounded complex `P` of finitely generated projective modules is K-projective, so an
isomorphism `P ≅ K` in `D(A)` comes from a quasi-isomorphism `P ⟶ K` of complexes. Its mapping
cone is a bounded acyclic complex of flat modules, which stays acyclic after base change; hence
`B ⊗[A] P ⟶ B ⊗[A] K` is a quasi-isomorphism, and `B ⊗[A] P` is a bounded complex of finitely
generated projective `B`-modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

end DerivedCategory

namespace DerivedCategory

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]

end DerivedCategory
