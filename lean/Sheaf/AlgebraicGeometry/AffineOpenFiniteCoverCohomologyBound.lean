module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.OpenRestrictionModuleCohomology
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.Topology.ModuleMayerVietoris

/-!
# A finite affine cover bounds cohomology on an open of an affine scheme

Source: Stacks Project, Cohomology of Schemes, Tag 01XI,
`lemma-vanishing-nr-affines`, first proof, specialized to an open of an affine scheme;
the empty-cover case follows from Cohomology, Tag 01DZ
(blueprint: lem-sfb-affine-open-finite-cover-cohomology-bound).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- A cover by `s` affine opens forces quasi-coherent module cohomology to vanish
in every degree `p ≥ s`, including `s = 0` and `p = 0` on the empty open.
Source: Stacks Project, Cohomology of Schemes, Tag 01XI, first proof;
Cohomology, Tags 01DZ, 01E1 and 01EB
(blueprint: lem-sfb-affine-open-finite-cover-cohomology-bound).

Proof:
1. If `s = 0`, the covering equality forces `U` to be empty. The sheaf axiom for
   the empty covering makes every module's sections a zero group. Applying global
   sections to an injective resolution therefore gives a zero complex, whose
   cohomology vanishes in every degree, including degree zero.
2. Present the affine scheme `Y` as `Spec A`. Its isomorphism to `Spec A` is separated,
   since its diagonal is an isomorphism and hence a closed immersion. By
   `lem-weil-pbc-separated-affine-open-intersection`, intersections of affine opens
   of `Y` are affine. The same holds for affine opens of its open subscheme `U`.
3. Restriction to an open is tensor pullback along its inclusion and preserves
   quasi-coherence by `lem-weil-pbc-module-pullback-quasi-coherent`.
   Use `lem-pc-open-restriction-module-cohomology` to identify cohomology of the
   restricted module with open module cohomology after forgetting scalar actions.
4. Induct strongly on the given cover size, simultaneously for all opens of affine
   schemes and all quasi-coherent modules. The case `s = 1` is
   `pqf-lem-affine-vanishing`. For `s ≥ 2`, let `V` be the union of the first `s - 1`
   members and `W` the last member. The intersection `V ∩ W` has an affine cover
   of size `s - 1`, formed by intersecting each earlier member with `W`. Induction
   gives vanishing of `H^p(V,F)` and `H^(p-1)(V ∩ W,F)` when `p ≥ s`.
   Affine vanishing gives `H^p(W,F) = 0`.
5. Apply `lem-sc-mayer-vietoris-ringed-space` to `V` and `W`. In its exact segment
   `H^(p-1)(V ∩ W,F) → H^p(U,F) → H^p(V,F) ⊕ H^p(W,F)`, both outer groups
   vanish, so every middle element is zero. No minimality or nonemptiness of
   cover members is used. -/
theorem subsingleton_moduleCohomology_of_affine_open_finite_cover
    (Y : Scheme.{u}) [IsAffine Y] (U : Y.Opens) (s : ℕ)
    (V : Fin s → U.toScheme.Opens) (hV : ∀ i : Fin s, IsAffineOpen (V i))
    (hcover : iSup V = ⊤) (F : U.toScheme.Modules) [F.IsQuasicoherent]
    (p : ℕ) (hp : s ≤ p) :
    Subsingleton ((RingedSpace.moduleCohomology U.toScheme.toRingedSpace p).obj F) := by
  sorry

end AlgebraicGeometry
