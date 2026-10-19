/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
import Sheaf.CategoryTheory.RingedSliceExtensionExactness
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Exact restriction and K-flat complexes on a localized ringed site

Source: Stacks Project, Cohomology on Sites, Tag 0E8K, lemma-restriction-K-flat;
Modules on Sites, Tags 03DJ and 0E8G
(blueprint: lem-sfb-ringed-site-restriction-kflat).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Restriction to an arbitrary object of a ringed site is exact and preserves
K-flatness of possibly unbounded complexes, without flatness of their terms.
Source: Stacks Project, Cohomology on Sites, Tag 0E8K, lemma-restriction-K-flat;
Modules on Sites, Tags 03DJ, 0E8G and 0E8I
(blueprint: lem-sfb-ringed-site-restriction-kflat).

Proof plan:
1. Use lem-pur-site-restriction-module-adjunction-exact for exact restriction
and the exact extension left adjoint L = j_!. The restriction here is literally
localizedSystemRestriction, hence overFunctor on J.over U with ring R.over U.
2. Given an acyclic complex G on the slice, apply the forward direction of
lem-weil-pbc-ringed-slice-extension-exactness to each consecutive triple. Thus
LG is acyclic. K-flatness of K makes Tot(LG tensor K) acyclic, using
 def-pc-acyclic-complex-modules and def-pc-kflat-complex.
3. The extension adjunction gives Hom(L(directSum G_i), H) =
product_i Hom(G_i, j^*H) = product_i Hom(LG_i, H), naturally in H.
The coproduct universal property therefore identifies L of a direct sum with
the direct sum of the extensions. The diagonal subsets of Z squared indexing
 def-pc-tensor-complex-sheaves are small in the coefficient universe.
4. Apply lem-weil-pbc-ringed-slice-extension-tensor in every bidegree and the
coproduct comparison of step 3. This gives L Tot(G tensor K|U) isomorphic to
Tot(LG tensor K). Naturality in G identifies the first differential components;
naturality in K identifies the second. Additivity of L preserves their sum and
the coefficient (-1)^p. Thus this is an isomorphism of the signed total complexes,
including when both complexes are unbounded.
5. Apply the reverse direction of
lem-weil-pbc-ringed-slice-extension-exactness to every consecutive triple of
Tot(G tensor K|U). Its extension is acyclic by steps 2 and 4, so it is itself
acyclic. Quantifying over all acyclic G is precisely K-flatness on the slice.
No enough-points, subterminal-object, boundedness or termwise-flatness hypothesis
is used. -/
theorem ringedSite_restriction_exact_kflat
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v w}) (U : C) :
    PreservesFiniteLimits (localizedSystemRestriction.{u, v, w} R U) ∧
    PreservesFiniteColimits (localizedSystemRestriction.{u, v, w} R U) ∧
    ∀ K : CochainComplex (SheafOfModules.{max u v w}
      ((sheafCompose J
        (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) K →
      CochainComplex.IsKFlatIndependentCoefficients (R := R.over U)
        (((localizedSystemRestriction.{u, v, w} R U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) := by
  sorry

end SheafOfModules
