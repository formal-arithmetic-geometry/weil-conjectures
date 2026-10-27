## What changed

Replaced `AlgebraicGeometry.ringComplex_godement_cech` by an assembly from the existing
finite ordered flasque Čech comparison, explicit ordered Čech sections, and two
strictly smaller geometric/calculation obligations. The target theorem's signature
and the Godement definition are unchanged.

`Sheaf.Paper.RingComplexOrderedCechConstruction` constructs the restricted principal
cover, proves that a generating list covers the ideal complement, constructs the
ordered Čech restriction map, proves its first differential vanishes, and defines
its inverse-rotated mapping fibre and projection. No object is selected from an
unproved mere existence theorem.

The item proves exactness of the constant ring-site functor by faithful evaluation,
flasqueness of the specified Godement terms, passage from a commuting section square
to a quasi-isomorphism of mapping fibres, and inversion of a roof while retaining
the projection equation. It applies the existing finite flasque comparison, transports
its two maps through restriction of scalars and the constant functor, and combines
this augmented fibre isomorphism with the coordinate calculation.

## Proved and sorry left

Original holes: 1. Closed upper hole:
`AlgebraicGeometry.ringComplex_godement_cech`
(node `lem-weil-pbc-ring-complex-godement-cech`).

Added holes: 2, in separate new modules, each exactly `:= by sorry`:

- `AlgebraicGeometry.ringComplexGodement_affineSections`
  (`lem-weil-pbc-ring-complex-godement-affine-sections`): evaluation of the specified
  Godement augmentation on the affine principal intersections is a quasi-isomorphism.
- `AlgebraicGeometry.ringComplexOrderedCech_coordinates`
  (`lem-weil-pbc-ring-complex-ordered-cech-coordinates`): the fixed ordered Čech fibre
  has the stated localization coordinates and differentials. It asserts no derived
  comparison with Godement.

This is a decomposition, not a net proof gain: one upper hole is replaced by two
strictly smaller obligations. The item and the construction module have zero holes;
the delivery has two holes. The assembly uses the original augmentation and includes
empty lists, zero or repeated generators, and the zero ring.

## No longer needed

Removed from the item's direct proof imports:

- `WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`
- `Sheaf.Paper.ModuleCupFlasqueAcyclicity`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`
- `WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives`
- `Sheaf.Paper.RingComplexCechData` (already a public dependency of the construction).

The first four results remain in the argument of the new affine-section node; they
are not declared mathematically obsolete. The localization-open and tilde nodes are
needed by the two geometric obligations instead of by the upper assembly. No existing
module or DAG node is withdrawn, and no unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's three prose steps omit the actual ordered Čech restriction map and the
augmentation-compatible mapping-fibre roof assembly. Those constructions are now
explicit. The existing dependencies supply the general finite Čech comparison and
Godement exactness/flasqueness, but their signatures do not directly supply the
principal-intersection evaluation quasi-isomorphism or the localization-coordinate
calculation. These are isolated without repackaging the complete original conclusion.
No existing statement or definition was corrected.

## New nodes

`def-weil-pbc-ring-complex-ordered-cech-construction` records the actual ordered Čech
section complex and its augmented fibre. All its data and elementary cochain and
cover identities are constructed/proved in Lean.

`lem-weil-pbc-ring-complex-godement-affine-sections` is the affine-section step:
Godement exactness, affine coefficient acyclicity, flasque term acyclicity, and the
bounded-below acyclic-resolution comparison. The empty cover has no tuples, and
empty intersections have zero section modules.

`lem-weil-pbc-ring-complex-ordered-cech-coordinates` is the coordinate calculation
for the fixed fibre. Section localization isomorphisms and the signs
`(-1)^(q+1)` in degree `q+1` give precisely the required differential. It carries
no Godement isomorphism or existence of an arbitrary model.

The recorded Mathlib searches were run with msearch; local searches also read
the existing Cech and Godement modules. No exact specialization was already present.
The blueprint searches for Godement and ordered Cech supplied no duplicate node.

Proof-scope change record: `coord/changes/Y3-ringComplex-godement-cech-proof-scope.md`.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
