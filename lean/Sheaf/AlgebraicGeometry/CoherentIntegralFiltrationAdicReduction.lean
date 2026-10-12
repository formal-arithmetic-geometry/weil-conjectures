/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Algebra.Homology.ModuleStalkFunctor

/-! # Reducing an integral-support filtration to generic residue-field modules

Source: Stacks Project, Cohomology of Schemes, Lemma 01YF, ideal-power paragraph.
(blueprint: lem-weil-pbc-coherent-integral-filtration-adic-reduction)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- For an irreducible closed support, it suffices to filter the coherent modules
supported there whose generic stalk is killed by the ambient maximal ideal.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YF, proof, third paragraph,
using Lemma 01Y9 and the reduced induced closed subscheme of Schemes Lemma 01J3.
(blueprint: lem-weil-pbc-coherent-integral-filtration-adic-reduction)

Proof: let J be the vanishing ideal of T with its reduced induced scheme structure.
Its zero locus is T and its stalk at ξ is the maximal ideal: a function vanishing at ξ
vanishes throughout T on its domain, since its zero locus is closed and ξ is generic.
By the support-power lemma some J^n kills F. Put A_t = J^t F for 0 <= t <= n, with
A_0 = F, and Q_t = A_t/A_{t+1}. Ideal products and powers are quasi-coherent on affine
opens, hence A_t and Q_t are coherent on the Noetherian scheme. Stalk exactness shows
Supp Q_t is contained in T. The equality of ideal-product stalks with products of
local modules shows J Q_t = 0, so the maximal ideal at ξ kills (Q_t)_ξ. Apply hgraded
to every Q_t. A_n is zero, so has the length-zero filtration. Descending induction
on t, using coherentIntegralFiltration_of_shortExact for A_{t+1} -> A_t -> Q_t,
gives a filtration of A_0 = F. If n = 0, F itself is zero and the same base case applies.
No assertion that all the Q_t have full support T is needed. -/
theorem coherentIntegralFiltration_of_generic_annihilated
    (X : Scheme.{u}) [IsNoetherian X]
    (T : TopologicalSpace.Closeds X) (ξ : X)
    (hξ : IsGenericPoint ξ (T : Set X))
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = (T : Set X))
    (hgraded : ∀ (G : X.Modules), RingedSpace.IsCoherent X.toRingedSpace G →
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} ⊆ (T : Set X) →
      (∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ),
        ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G, a • m = 0) →
      HasCoherentIntegralFiltration G) :
    HasCoherentIntegralFiltration F := by sorry

end AlgebraicGeometry.Scheme.Modules
