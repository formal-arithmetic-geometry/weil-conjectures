/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Algebra.Homology.DerivedOpenShriekAdjunction
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
import Sheaf.AlgebraicGeometry.DerivedAmbientDirectSumsCofan
import Sheaf.AlgebraicGeometry.DerivedAmbientDirectSumsHomology

/-! # Scalar formality on the rank strata of a closed subscheme

Source: Stacks Project, Tag 0BQZ, single-degree truncation and reconstruction;
the rank-stratum assembly in lem-sc-koszul-regular-immersion-derived-hom, step 3
(blueprint: lem-sc-closed-immersion-rank-strata-scalar-formality).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

/-- A family of arbitrary module sheaves on disjoint rank strata is formal after
scalar direct image along a closed immersion. The family need not be finite.

Source: Stacks Project, Tag 0BQZ, single-degree truncation; parent reconstruction
step 3 (blueprint: lem-sc-closed-immersion-rank-strata-scalar-formality).

Proof:
1. Put Z_n = {z | r z = n}. Each Z_n is clopen in Z. Its image and the image of
   its complement are closed in Y, since i is a closed immersion. Put
   V_n = Y minus i(Z minus Z_n), and V_out = Y minus i(Z). These opens cover Y.
   For distinct m,n, V_m intersect V_n is contained in V_out. On V_n only T^n
   can be nonzero after direct image; on V_out every pushed-forward T^q is zero.
   In particular the family of closed supports i(Z_n) is locally finite in Y.
2. Exact restriction to V_n and hK show that K restricted to V_n has cohomology
   only in degree n, identified with the restricted direct image of E_n. Choose
   a representative and truncate above and below n. The truncation maps are
   quasi-isomorphisms, and identify this restriction with that sheaf in degree n.
   The restricted zero-differential complex has exactly the same single term.
3. Extend each local identification by zero from V_n to Y. Extension by zero
   for module sheaves is exact. The counit maps from the coproduct of these
   extended restrictions to K are isomorphisms on cohomology: at a point of i(Z)
   exactly one rank support contributes, and outside i(Z) all cohomology is zero.
   Coproducts of module sheaves are exact, so these counits are isomorphisms in
   the derived category. Apply the same construction to the zero-differential
   comparison complex. Direct sum of the extended single-degree isomorphisms,
   followed by the two counit isomorphisms, gives the claimed isomorphism.
There is no need to glue arbitrary derived isomorphisms. The rank supports are
closed in Y, not asserted to be open in Y. Empty Z gives zero; rank zero is the
ordinary degree-zero case. Unbounded rank is allowed by the coproduct argument.
Neither algebra-module structure on K nor a derived category on Z is needed. -/
theorem closedImmersion_rankStrata_scalar_formality
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (r : LocallyConstant Z ℕ)
    (E : ∀ n : ℕ, (Scheme.Modules.exteriorRankOpen r n).toScheme.Modules)
    (T : ℤ → Z.Modules)
    (hT : ∀ n : ℤ, T n = if 0 ≤ n then
      (Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r n.toNat).ι).obj
        (E n.toNat) else 0)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (hK : ∀ n : ℤ, Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj K ≅
        (Scheme.Modules.pushforward i).obj (T n))) :
    Nonempty (K ≅ DerivedCategory.Q.obj
      (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.of T (fun _ => 0) (fun _ => zero_comp)))) := by sorry

end AlgebraicGeometry
