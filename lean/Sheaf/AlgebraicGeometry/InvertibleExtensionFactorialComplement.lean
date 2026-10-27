/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import Sheaf.AlgebraicGeometry.CartierExtensionFactorialComplement
import Sheaf.CategoryTheory.SiteModuleSheafGluing

/-!
# Extending invertible modules across a factorial complement

Source: Stacks Project, Divisors, Tag 0BD9 (`lemma-extend-invertible-module`)
(blueprint: lem-sfb-invertible-extension-factorial-complement).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module on an open subscheme of a locally Noetherian scheme extends
if every local ring outside the open is a unique factorization domain. Restriction
is the canonical tensor pullback along the open immersion. Only existence of the
extension and of its restriction isomorphism is asserted.

Source: Stacks Project, Divisors, Tag 0BD9 (`lemma-extend-invertible-module`)
(blueprint: lem-sfb-invertible-extension-factorial-complement).

Proof (the accepted stage-1 split):
1. Suppose U is contained in an open V carrying an extension N, and let W be an
   affine open of Z. The intersection T = V ∩ W is locally Noetherian by
   pqf-def-locnoeth. It is quasi-compact by lem-sfb-noetherian-open-immersion-qc
   applied to V → Z over W. Thus T is Noetherian and quasi-affine, without
   requiring Z or V to be quasi-compact or separated.
2. By lem-sfb-quasiaffine-line-effective-divisor, write N restricted to T as O_T(D)
   for an effective Cartier divisor D. A point of W outside T is outside V,
   hence outside U, and has factorial local ring. Apply
   lem-sfb-cartier-extension-factorial-complement to extend D to a divisor E
   on W. Its line module P = O_W(E) is invertible by def-pc-divisor-line-bundle
   and def-sc-invertible-module. The equality of restricted ideal sheaves gives
   P restricted to T isomorphic to N restricted to T: locally dualize a
   nonzerodivisor generator of the same ideal, and these identifications agree
   on overlaps since they use the same ideal inclusions.
3. Well-order a set-indexed affine cover (W_alpha) of Z. Put
   V_alpha = U ∪ ⋃ (gamma < alpha), W_gamma. Starting with N_0 = M, construct
   invertible N_alpha on V_alpha and isomorphisms
   q_{beta,alpha} : N_alpha restricted to V_beta ≅ N_beta for beta ≤ alpha.
   Keep q_{alpha,alpha} = id and
   q_{delta,alpha} = q_{delta,beta} composed with the restriction of q_{beta,alpha}.
   All choices and the set of stages lie in a sufficiently large fixed universe.
4. At a successor, apply steps 1 and 2 to V_alpha and W_alpha. Glue N_alpha
   and P by the overlap isomorphism and its inverse, with identity transitions
   on equal indices, using lem-weil-pbc-site-module-sheaf-gluing on the Zariski
   site. The cocycle is inverse cancellation. Local trivializations make the
   glued module invertible and quasi-coherent (def-sc-invertible-module).
   Its comparison with N_alpha defines q_{alpha,alpha+1}; define earlier q's
   by composition. Associativity and the earlier invariant give compatibility.
5. At a nonzero limit lambda the opens V_beta for beta < lambda cover V_lambda.
   On an overlap with beta ≤ gamma use q_{beta,gamma}^{-1}, and for the reverse
   ordering its inverse. The invariant gives the cocycle for sorted triples;
   inverse cancellation gives every ordering. Apply
   lem-weil-pbc-site-module-sheaf-gluing. Its overlap equation is precisely the
   new q-compatibility equation. Local trivializations again give invertibility
   and quasi-coherence by def-sc-invertible-module. No density or uniqueness is used.
6. At the last stage V_kappa = Z, take N_kappa and q_{0,kappa}. If the affine
   cover is empty, Z and U are empty and take M itself. If U = Z, take M
   immediately. Empty U, empty overlaps, and disconnected schemes are allowed.
-/
theorem exists_invertible_extension_of_factorial_complement
    {Z : Scheme.{u}} [IsLocallyNoetherian Z] (U : Z.Opens)
    (hfactorial : ∀ z : Z, z ∉ U →
      IsDomain (Z.presheaf.stalk z) ∧ UniqueFactorizationMonoid (Z.presheaf.stalk z))
    (M : U.toScheme.Modules) [M.IsInvertible] :
    ∃ Mext : Z.Modules, Mext.IsInvertible ∧
      Nonempty ((tensorPullback U.ι).obj Mext ≅ M) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
