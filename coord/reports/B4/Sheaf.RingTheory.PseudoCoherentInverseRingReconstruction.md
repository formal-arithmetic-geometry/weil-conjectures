## What changed

Preserved the complete statement of
`DerivedCategory.isPseudoCoherent_inverse_ring_reconstruction`. Its proof now constructs the
marked tower, constructs its finite-free termwise limit, identifies the prescribed Roos
limit respecting every projection, and proves the final comparison equations by the
ordinary and derived adjunctions.

The final base-change comparison uses K-projective Hom bijections directly. Private
helpers in the item prove the localization bijection, its compatibility with chain maps,
the localized ordinary unit's universal property, the coyoneda isomorphism criterion,
and the unit-normalized comparison. The ordinary extension of the limit model is
K-projective because its given reduction is isomorphic to the bounded-above free model
at that level. Thus the proof uses exactly the supplied derived adjunctions and proves
normalization for those adjunctions.

Added seven intermediate modules. `NilpotentFiniteFreeComplexTower` proves the dependent
recursion from a single-step marked lift. `FiniteFreeComplexTowerInverseLimit` constructs
the categorical termwise limit and its projections, proves the compatible-tuple universal
property and common upper bound, and constructs the reduction chain isomorphisms from
the degreewise module assertion. `ComplexTowerLimitProjectionComparison` proves the
restriction-composition diagram, transports the Roos triangle and uses TR3 and
isomorphism of triangle morphisms to preserve all projections. The two remaining
algebraic assertions are isolated in `NilpotentMarkedFreeComplexStep` and
`NilpotentFiniteFreeBasisLift`. `CompatibleFiniteFreeModuleBases` proves the dependent
basis recursion, and `FiniteFreeModuleTowerInverseLimit` proves the coordinate-limit
and scalar-extension calculations from those compatible bases. Each has a source, a complete
proof in words and a new node. Updated the existing node's proof route and pruned obsolete tool
approvals.

No existing definition or statement changed. The removed public import and local elaboration
options are recorded in `coord/changes/pseudocoherent-reconstruction-proof-context.md`.
The sole consumer, `Sheaf.RingTheory.RlimPerfectComplete` (held by R1), directly publicly
imports the removed dependency and needs no adaptation.

## Proved and sorry left

Closed the original hole in
`DerivedCategory.isPseudoCoherent_inverse_ring_reconstruction` (one of one original holes).
This is a decomposition, not a hole-free proof: the delivery adds two strictly smaller
algebraic obligations. The item itself contains zero `sorry`.

Also proved the new declarations
`DerivedCategory.exists_nilpotent_finiteFree_complexTower`,
`DerivedCategory.exists_finiteFree_complexTower_inverseLimit`,
`DerivedCategory.exists_complexTower_limit_projection_comparison`,
`ModuleCat.exists_compatible_finiteFree_module_coordinates`, and
`ModuleCat.finiteFree_moduleTower_inverseLimit`.

Every new hole left is listed here:

- `DerivedCategory.exists_nilpotent_marked_finiteFree_step`, node
  `lem-weil-pbc-nilpotent-marked-free-complex-step`. It still needs transport of the
  existing quotient-ring marked lift to an arbitrary surjective ring map, identification
  of the supplied left adjoint with derived extension, and its transition normalization.
  The statement is one lift across one ring map, with no inverse system or limit.
- `ModuleCat.exists_nilpotent_finiteFree_basis_lift`, node
  `lem-weil-pbc-nilpotent-finite-free-basis-lift`. It still needs the single-step basis
  lift across a surjective nilpotent ring map. The finite-coordinate inverse-limit
  calculation and the infinite compatible-basis recursion are proved. This remaining
  statement concerns two modules over one ring map, with no inverse system, limit,
  differential, upper bound, derived category, pseudo-coherence, or Roos limit.

All eight delivered modules compile without warnings. The unchanged sole consumer
`Sheaf.RingTheory.RlimPerfectComplete` also compiles against this delivery.

The net change in named holes of the delivered modules is one closed and two added.
The statements were checked on zero rings, zero modules and rank-zero terms: nilpotent
surjective quotients cannot introduce a nonzero module with zero reduction when the
terms are finite free; the compatible-basis argument includes the empty basis.
Neither new hole restates the reconstruction theorem. Existing holed lifting and
surjective-tower declarations remain dependencies as intended by stage 3.

## No longer needed

Removed these direct imports from the item:

- `Sheaf.Algebra.Homology.DerivedChangeOfRings`
- `Sheaf.Algebra.Homology.BoundedFlatKFlat`
- `Sheaf.RingTheory.PseudoCoherentNilpotentInvariance`
- `Mathlib.RingTheory.TensorProduct.Basic`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Mathlib.CategoryTheory.Triangulated.Triangulated`
- `Sheaf.Algebra.Homology.SurjectiveModuleComplexTowerLimit`
- `Sheaf.RingTheory.NilpotentMarkedFreeComplexLift`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`

The last comparison no longer uses the original route through
`lem-weil-pbc-projective-module-flat`, `lem-pc-module-bounded-flat-kflat`,
`lem-weil-pbc-singleton-site-module-comparison`,
`lem-pur-derived-change-of-rings`, or
`lem-pur-sheaf-ring-derived-coefficient-adjunction`. The K-projective Hom bijection
replaces that route; `lem-weil-pbc-free-module-projective` is supplied by Mathlib's module
projectivity instance. Removed the bounded-flat, derived-change-of-rings and sheaf-ring
coefficient-adjunction entries from this node's top-level `tool_uses`; retained triangle
isomorphisms and the K-projective representative tool. These are removals from this
node's direct proof route, not assertions that all those nodes are globally unreachable.
The existing nilpotent lifting declarations may still use some of them downstream.

Nilpotent invariance and marked free-complex lifting are used below the single-step
obligation; the surjective module-complex tower result and triangle comparison are used
below the projection-comparison module. Their direct imports moved to those modules. Redundant imports were also removed from
the new modules: derived-limit imports from the lifting statements, exact derived
functors from the purely complex-limit construction, and the marked-lift import from
the tower recursion. The pure module statements import Mathlib module and ideal APIs.
The direct import of `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit` was
redundant with the retained public Sheaf wrapper. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original node's final comparison route was longer than necessary for these free
models. Bounded-above projectivity and the ordinary adjunction give the normalized
comparison directly, including for the particular supplied derived adjunction.

The existing marked lifting declaration is for the literal quotient ring and a specified
universal derived counit; it does not directly accept the item's arbitrary surjective
map and derived adjunction. This missing interface transport is now a precise single-step
obligation. The single-step compatible-basis lift is substantial elementary algebra rather than
an existing ready-to-apply complex-limit theorem. The infinite basis induction and the
finite-coordinate limit calculation are now implemented. Neither issue changes the mathematical
statement. The source library's matrix-tower constructions were checked, but its ready
perfect-tower theorem assumes local rings and its tower-limit theorem fixes the module
universe to the ring universe; they do not directly specialize to the present statement.

## New nodes

`lem-weil-pbc-nilpotent-marked-free-complex-step` records the one-step nilpotent marked
lift with ordinary and derived transition normalization. Its one remaining hole and the
needed quotient/adjunction transports are described above.

`lem-weil-pbc-nilpotent-finite-free-complex-tower` records the proved dependent recursion
that iterates the single-step lift while retaining the cutoff and each chosen marking.

`lem-weil-pbc-finite-free-module-tower-inverse-limit` records the one-degree compatible
basis and scalar-extension calculation, now proved from compatible coordinates.

`lem-weil-pbc-finite-free-complex-tower-inverse-limit` records the proved construction of
the complex limit and its reduction chain isomorphisms from the degreewise assertion.

`lem-weil-pbc-complex-tower-limit-projection-comparison` records the proved comparison
with the specified Roos limit, including all projection equations. The ring cone,
compatible-tuple limit test, transition diagram and triangle morphism are implemented.

`lem-weil-pbc-nilpotent-finite-free-basis-lift` records the single-step prescribed
coordinate lift, the remaining elementary algebra hole.

`lem-weil-pbc-compatible-finite-free-module-bases` records the proved initial finite-basis
choice and dependent recursion from that single-step lift.

All seven nodes are below the existing proper-base-change reconstruction node. The unit's
statement and required route are preserved. The import-context change record is
`coord/changes/pseudocoherent-reconstruction-proof-context.md`; no definition or statement
was changed.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
