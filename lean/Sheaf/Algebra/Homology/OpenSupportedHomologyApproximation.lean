/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.Algebra.Homology.OpenExtensionCounitStalk

/-! # A concentrated approximation on an open support

Source: Stacks Project, Cohomology, Tags 08BS and 08BT.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Exact extension by zero of the restriction of `K` gives a concentrated object
mapping to `K`. Maps from `S` to degree-`n` homology factor through this counit.
This is a statement about a local approximation, not an isomorphism with `K`.

Source: Stacks Project, Cohomology, Tags 08BS and 08BT (exact extension by zero
and its adjunction); Modules, Tag 01AG (stalkwise detection).
(blueprint: lem-sc-open-supported-homology-approximation)

Proof: Let j be the inclusion of U. Restriction R and extension by zero J
are exact and additive, with sheaf adjunction counit epsilon : R followed by J
-> identity. Their composite F is an exact additive endofunctor of modules on
X. Choose a complex P representing K and apply F termwise. Set L = Q(F(P));
apply Q to the chain map whose components are epsilon(P^m), then compose with
the representative isomorphism Q(P) -> K to obtain b : L -> K. Exactness gives
H^m(L) isomorphic to F(H^m(K)). The homology map of this chain map is epsilon
on homology: this follows from its commutation with cycles and the quotient
from cycles to homology. Thus the comparisons identify H^m(b) with the
sheaf counit. This construction uses only the given derived category on X.

For m != n the sheaf F(H^m(K)) has zero stalks everywhere. Off U this is the
extension-by-zero stalk formula. On U its counit stalk is an isomorphism to
the zero stalk specified by hlocal. Stalkwise detection makes this sheaf zero.
Similarly epsilon(S) : F(S) -> S is an isomorphism: on U its stalk is an
isomorphism and off U its source and target have zero stalks by hsource.
For a : S -> H^n(K), define c by epsilon(S)^{-1} followed by F(a), then the
inverse of the homology comparison H^n(L) -> F(H^n(K)). Counit naturality
and the homology comparison for b give c followed by H^n(b) equal to a.
For empty U, S and L are zero. For U = X the counit is an isomorphism.
No truncation or derived lift from a single object is asserted here. -/
theorem open_supported_homology_approximation (X : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    (U : Opens X) (S : SheafOfModules.{u} (moduleRings X))
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) (n : ℤ)
    (hsource : ∀ x : X, x ∉ U → IsZero ((RingedSpace.moduleStalkFunctor X x).obj S))
    (hlocal : ∀ m : ℤ, m ≠ n → ∀ x : X, x ∈ U →
      IsZero ((RingedSpace.moduleStalkFunctor X x).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X)) m).obj K))) :
    ∃ (L : DerivedCategory (SheafOfModules.{u} (moduleRings X))) (b : L ⟶ K),
      (∀ m : ℤ, m ≠ n → IsZero
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X)) m).obj L)) ∧
      ∀ a : S ⟶ (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X)) n).obj K,
        ∃ c : S ⟶ (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X)) n).obj L,
          c ≫ (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X)) n).map b = a := by sorry

end AlgebraicGeometry
