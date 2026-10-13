/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Algebra.Homology.LocalizedTensorComparisonProperty

/-! # Shift stability of localized tensor comparison

Source: Stacks Project, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-localized-tensor-comparison-shift).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- Localized tensor comparison in all degrees is preserved by integer shifts.
Source: Stacks Project, Tag 0DJA(1), reindexing the cohomological comparison.

Proof: given a K-flat representative U of X[n], shift U by -n. The localization
commutes with shift, and the inverse-shift equivalence gives a representative
of X. Shifts preserve K-flatness: tensoring an acyclic test complex with a
shifted complex is a shift of an acyclic total tensor complex. Apply hX to
this representative and all its base-derived models.
The first-variable total-tensor shift isomorphism identifies
(U[-n] tensor Q)[n] with U tensor Q. Termwise scalar extension commutes with
shift, and the corresponding tensor shift identifies
(F(U[-n]) tensor N)[n] with F(U) tensor N. The tensor-shift signs occur on
both sides of the comparison; naturality identifies the shifted chain map
mu.inv followed by F(U[-n]) tensor t with the map for U.
Transport a base-derived model of U tensor Q through these shift isomorphisms
and reindex its cohomology in degree i to degree i+n for the unshifted complex.
The left-derived functor commutes with shifts by uniqueness of its universal
counit. This uniqueness is compatible with multiplication by A and the B
module structure, so the cohomology transports are A tensor_R B-linear.
The comparison_eq and localized_eq equations identify the resulting square
with the shifted comparison square. Scalar extension to C preserves these
source isomorphisms and cohomology supplies target isomorphisms. Its unshifted
horizontal arrow is invertible by hX; hence the shifted arrow is invertible.
This proves the predicate for each U, model and degree. For n=0 these are the
identity transports. The argument needs neither flatness of C nor bounds on Q.
(blueprint: lem-pc-localized-tensor-comparison-shift). -/
theorem localizedTensorComparisonProperty_shift
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : localizedTensorComparisonProperty R A B C Q N t X) (n : ℤ) :
    localizedTensorComparisonProperty R A B C Q N t (X⟦n⟧) := by sorry

end ModuleCat
