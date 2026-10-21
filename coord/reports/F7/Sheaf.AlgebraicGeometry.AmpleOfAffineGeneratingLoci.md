## What changed

Proved `AlgebraicGeometry.isAmple_of_affine_generatingLoci` in
`Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci`, preserving its exact signature,
definitions and public imports. The given affine generating loci satisfy absolute
ampleness using the proved nonvanishing/local-generation equivalence. The existing
affine-base theorem gives a projective-space immersion of a positive tensor power;
properness makes it closed. A proved private induction compares positive tensor
powers, and uniqueness of left adjoints compares the two pullback functors. These
data directly satisfy the existing `IsVeryAmple` and `IsAmple` definitions.

Updated `lem-pc-ample-affine-loci-criterion` to record this argument and its actual
dependencies. No unit statement or realized unit step is bypassed: the item is a
supporting node of `sk-thm-picard-rr`, whose realization is `sk-thm-picard-rr` itself.

The retained proof compiled using the required remote compiler (3.5 seconds), with
no warnings. `#print axioms AlgebraicGeometry.isAmple_of_affine_generatingLoci`
reports exactly `[propext, Classical.choice, Quot.sound]`. The temporary axiom
inspection command was removed from the delivered source.

On resumption, server preflight identified the added file-level monoidal namespace
opening as an environment change. Restored the original `open CategoryTheory` and
qualified the helper's three monoidal operations, preserving the original file-level
environment.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.isAmple_of_affine_generatingLoci`
(node `lem-pc-ample-affine-loci-criterion`).

Added zero holes; zero `sorry` remain in the delivered module. The private helper
`AlgebraicGeometry.positiveTensorPower_iso_tensorPow` is proved by induction.
No new modules, public declarations, definitions or axioms are added.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed`.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints`.
- `WeilConjectures.AlgebraicGeometry.Ample` (available through the used imports).
- `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple` (available through the
  unchanged public import `WeilConjectures.AlgebraicGeometry.Modules.Ample`).

The following former proof dependencies are unnecessary for this item:
`lem-pc-complete-linear-system-closed`,
`lem-weil-pbc-projective-space-functor-of-points`,
`lem-weil-pbc-closed-immersion-from-composite`, and
`lem-weil-pbc-closed-immersion-integral-separated-uc`.
The existing definition of `IsVeryAmple` directly accepts the constructed closed
immersion and pullback isomorphism, so no construction or enlargement of a linear
subsystem is needed. Removed the two obsolete top-level `tool_uses` approvals for
functor of points and closed-immersion cancellation. The remaining approvals keep
their original order.

These dependencies are pruned from this item's route only. No modules or adopted
source declarations are withdrawn; other consumers may still need them.

## Where the brief, the DAG or earlier work was wrong

The old proof plan and explanatory docstring take an unnecessary detour through a
finite subsystem and the complete linear system. The current unchanged
`AlgebraicGeometry.IsVeryAmple` definition already accepts any closed immersion
into finite projective space with the required pullback isomorphism.

The plan also omitted the existing bridge
`lem-sc-nonvanishing-iff-generates-at`, needed to identify `generatingLocus` with
the stalk predicate in absolute ampleness. The updated node explicitly cites it.
The affine-base theorem's positive tensor power and tensor pullback use different
constructions from the final definition; proved comparison isomorphisms resolve
these differences without changing any interface.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
