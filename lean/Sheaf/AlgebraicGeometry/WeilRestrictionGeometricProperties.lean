module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant
import Sheaf.AlgebraicGeometry.FiniteLocallyFreePrincipalBasisCover
import WeilConjectures.AlgebraicGeometry.Hilbert.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFlatLfpSource
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationFppfSource
import WeilConjectures.AlgebraicGeometry.FormallySmooth
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyTrivial
import WeilConjectures.AlgebraicGeometry.FpqcDescendQuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Geometric properties of representable Weil restrictions

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §7.6, Proposition 5(a),(b),(c),(h),
printed pp. 195–198 (blueprint: lem-sfb-weil-restriction-geometric-properties).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Representable Weil restriction preserves separatedness, local finite type, and smoothness;
it also preserves quasi-compactness when the base is locally Noetherian.
Source: BLR, Néron Models, §7.6, Proposition 5(a),(b),(c),(h), printed pp. 195–198
(blueprint: lem-sfb-weil-restriction-geometric-properties).

The natural isomorphism is precisely the natural family of representing bijections:
`Over.pullback p` sends `X/S` to `X ×[S] S' / S'`, and `yoneda.obj (Over.mk z)` takes
its morphisms over `S'` to `Z`. No affineness or positive-rank assumption is made.

Proof plan (the eleven steps of the node):
1. The representing bijections supply evaluation and commute with base change and fibre
products. Work on finite-free affine basis charts, using
lem-weil-pbc-finite-locally-free-degree-locally-constant and
lem-a1-finite-locally-free-principal-basis-cover.
2. For separatedness, pull back the closed diagonal of `Z` along the two evaluations over
`W ×[S] W`. On each constant-degree piece apply lem-pc-hilb-containment-locus to the entire
finite locally free family and this closed equalizer. Its closed containment locus represents
the diagonal of `W`, so that diagonal is a closed immersion.
3. On an affine basis chart, write the equations of an affine restriction in basis
coordinates (lem-sfb-finite-free-algebra-map-coordinates and
lem-sfb-affine-weil-restriction-charts). Finite generators give finite generators for its
coordinate ring; finite generators and relations give a finite presentation. The affine
identifications extend to schemes by lem-weil-pbc-scheme-morphism-gluing.
4. Take finite coproducts of an affine cover of `Z`. Their affine restrictions map étale to
`W` by lem-sfb-etale-sections-finite-locally-free. They cover `W`: apply
lem-sfb-finite-etale-cover-local-sections to lift the evaluation étale-locally to the cover,
and quasi-compactness of the finite preimage of an affine test makes the lift use finitely
many summands. Use the scheme-coproduct and finite-affine-coproduct-spectrum nodes.
5. If `Z/S'` is locally of finite type, these affine restrictions are locally of finite type
by step 3; descend along this étale atlas using lem-a1-lft-flat-lfp-source-descent.
6. The same argument for finite presentations uses
lem-weil-pbc-lfp-affine-opens-finite-presentation, lem-weil-pbc-finite-coproduct-lfp-qcqs,
and lem-trf-lfp-fppf-source-locality to give local finite presentation of `W/S`.
7. For smooth `Z/S'`, step 6 applies. Pull back an affine square-zero thickening along `p`.
It remains affine and square-zero. Formal smoothness lifts its map to `Z`; the representing
bijections and naturality give the required lift to `W`. Thus `W/S` is formally smooth and
locally finitely presented, hence smooth (def-sbc-smooth-morphisms).
8. For a finite locally free universal homeomorphism, restrictions of a finite affine cover
of a quasi-compact source are open and cover the restriction: each geometric fibre has
one point. Use lem-sfb-finite-locally-free-weil-restriction for space existence,
lem-sfb-finite-free-universal-containment-loci for the opens, and
lem-sfb-space-quasicompact-affine-tests for quasi-compactness, including arbitrary base change.
9. For finite étale `p`, split it étale-locally (lem-fet-locally-trivial). Restriction becomes
a finite product of quasi-compact schemes or spaces, hence is quasi-compact. A finite
subfamily over each affine base gives an fpqc cover; apply
lem-weil-pbc-fpqc-descend-quasi-compact. The empty product is the base.
10. Over an integral reduced closed subscheme of a Noetherian affine base, use
lem-sfb-generic-finite-free-etale-radicial-factorization on a nonempty open. First apply
step 8 to its radicial factor and then step 9 to its finite étale factor. Functorial
transitivity and step 1 identify the composite restriction with the given scheme `W`.
11. Noetherian induction finishes: choose nonempty affine opens in the finitely many
irreducible components where step 10 applies. The complement is a proper closed subset.
The induction hypothesis and the finite-union compactness argument cover the total
space. Passing to reduced closed subschemes does not alter underlying base-changed spaces.
Use lem-weil-pbc-qcqs-morphism-permanence and affine-test locality to conclude for `W/S`.
The empty base and rank-zero family are included throughout. -/
theorem weilRestriction_geometric_properties
    {S S' Z W : Scheme.{u}} (p : S' ⟶ S) [p.IsFiniteLocallyFree]
    (z : Z ⟶ S') (w : W ⟶ S)
    (hrep : Nonempty
      (yoneda.obj (Over.mk w) ≅ (Over.pullback p).op ⋙ yoneda.obj (Over.mk z))) :
    (IsSeparated z → IsSeparated w) ∧
    (LocallyOfFiniteType z → LocallyOfFiniteType w) ∧
    (Smooth z → Smooth w) ∧
    (IsLocallyNoetherian S → QuasiCompact z → QuasiCompact w) := by
  sorry

end AlgebraicGeometry
