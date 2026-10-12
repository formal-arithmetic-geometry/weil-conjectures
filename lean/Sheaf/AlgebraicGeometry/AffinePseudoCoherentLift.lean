/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.AffinePseudoCoherentCriterion
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.PseudoCoherentQCoh
import Sheaf.AlgebraicGeometry.QcOpenDerivedLift
import Sheaf.RingTheory.ConePseudoCoherent
import Sheaf.RingTheory.FiniteHomologyOfMPseudoCoherent

/-! # Lifting pseudo-coherent objects from quasi-compact opens of affine schemes

Source: Stacks Project, Derived Categories of Schemes, Tag 08EE,
Lemma 36.13.6, lemma-lift-pseudo-coherent (blueprint: lem-sc-affine-pseudo-coherent-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- A pseudo-coherent derived object on a quasi-compact open of an affine scheme has a
bounded-above finite-free complex on the whole scheme representing it after restriction.
The ranks may vary with the degree, and the complex need not be bounded below.
Source: Stacks Project, Tag 08EE, lemma-lift-pseudo-coherent
(blueprint: lem-sc-affine-pseudo-coherent-lift).

Proof:
1. By lem-sc-pseudo-coherent-qcoh, E has quasi-coherent cohomology. Apply
   lem-sc-qc-open-derived-lift to lift it to E' in D_QCoh(O_X).
2. Write X = Spec(A). By lem-pc-affine-qcoh-derived-equivalence, represent E' by
   the associated complex of an A-module complex M. Choose a finite principal-open
   cover U = union D(f_j). By lem-pc-affine-pseudo-coherent-criterion, each localized
   complex M_{f_j} has a bounded-above finite-free representative.
3. Descend on n, constructing a finite-free complex F supported in degrees at least n
   and a map alpha : F → M inducing localized cohomology isomorphisms above n and
   surjections in degree n. Start with F = 0 above a common cohomology bound.
   The cone C of alpha has localized cohomology zero in degrees at least n.
   Apply lem-sc-cone-pseudo-coherent with m = n-1: the bounded finite-free F is
   m-pseudo-coherent, and M is m-pseudo-coherent by truncating its local model.
   Then lem-sc-finite-cohomology makes H^{n-1}(C_{f_j}) finite.
4. Choose generators of these finitely many finite modules and clear denominators
   to obtain representatives in C^{n-1}. Multiply by further powers of the f_j to
   kill their differentials. Their direct sum gives a finite-free F^{n-1} mapping
   to cocycles of C and surjecting on every localized H^{n-1}. The two components
   in C^{n-1} = M^{n-1} ⊕ F^n define alpha^{n-1} and minus the differential of F.
   The cone triangle gives the induction invariant at n-1. Degrees already fixed
   are never changed, so the resulting bounded-above F is a localized quasi-isomorphism.
5. Associate sheaves termwise (lem-pc-affine-qcoh-derived-equivalence). The map is a
   quasi-isomorphism on each D(f_j), hence on U. Its restriction represents E.
-/
theorem exists_boundedAbove_finiteFree_lift
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (E : schemeDerivedCategory U.toScheme) (hE : IsPseudoCoherent U.toScheme E) :
    ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
      (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
        (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin r)))) ∧
      Nonempty
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj (DerivedCategory.Q.obj P) ≅ E) :=
  sorry

end AlgebraicGeometry.Scheme
