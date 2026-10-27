## What changed

Implemented `AlgebraicGeometry.Scheme.integral_fibre_monodromy_reconstruction`
with its original signature and definitions. The proof constructs the finite-level
representations from the existing linear fibre path family, checks continuity via
finite-set evaluation, constructs the coordinatewise inverse-limit representation,
and uses the declared adic-limit theorem for finite generation and the projection
kernels and topology. A direct uniformizer-cancellation argument proves that the
limit is torsion-free, and the Mathlib PID theorem gives freeness.

The rationalization component chooses a finite basis of the original integral
module and its scalar extension. Its tensor unit is injective, its image is an
actual invariant lattice, and finite matrix-coordinate formulas prove joint
continuity. Finite-level equivariant fibre isomorphisms lift by the specified
finite Galois correspondence; naturality of the entire diagram follows by fibre
faithfulness. Recovery compares the actual two abelian-sheaf limit cones, proves
constant scalar compatibility by their projection equations, and then proves
continuous scalar compatibility locally modulo each uniformizer power. It uses
actual extension of coefficients and the stipulated normalization of the same J.

These three independent components have their own modules and nodes. The two
existing private finite-stalk helpers in the unclaimed
`LatticeNormalizationRationalExact` are now public, with identical propositions
and proofs; both retained duplicate copies of faithfulness and the reconstruction
copy of equality detection are removed. No existing public signature, definition,
attribute, or public import was changed. All remaining new
helpers used only in proofs are private and fully proved. No source-library file
was changed. The fixed unit route is preserved: its `realized` arrays do not attach
this node, and the existing integral-monodromy step in the affine Hc0 argument
continues to use this statement.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.Scheme.integral_fibre_monodromy_reconstruction`
(`lem-a1-integral-fibre-monodromy-reconstruction`).

Added component theorems with complete proofs:

- `AlgebraicGeometry.Scheme.integral_representation_rationalization`
  (`lem-a1-integral-representation-rationalization`).
- `AlgebraicGeometry.Scheme.finite_fibre_linear_lifting`
  (`lem-a1-finite-fibre-linear-lifting`).
- `AlgebraicGeometry.Scheme.completed_normalization_recovery`
  (`lem-a1-completed-normalization-recovery`).

Source hole counts: the item had 1 `sorry` and now has 0; the three new modules
each have 0. Thus 1 original hole is closed and 0 holes are added or split off.
The repaired packet has five modules, including the previously proved lattice
exactness module with its visibility-only change. All five have zero holes.
The final `lcompile.py --all` completed with exit code 0 and no diagnostics.
Reported elapsed times: CompletedNormalizationRecovery 51.8 s,
IntegralRepresentationRationalization 31.6 s, LatticeNormalizationRationalExact
32.0 s, FiniteFibreLinearLifting 43.1 s, and the assigned module 70.9 s.
Both direct `import_prune_check.py` checks for the repaired consumers passed.
The delivery's server preflight is the final per-file timeout and axiom gate.
Imported declared dependencies can still rest on their existing holes; this packet
does not claim to close those dependencies.

## No longer needed

No module is withdrawn and no original import is removed. The three retained
private duplicate declarations are removed in favor of the existing shared proofs.
No original library declaration is removed. The proof does not invoke the
existence assertions
`etale_local_monodromy_realization`, `completed_system_comparison`, or
`integral_lisse_reduction_equivalence`: their relevant structures and normalized
data are already supplied as the parameters C and J. Their original public
imports remain verbatim, so no import-closure pruning of those modules is claimed.
The parent's proof dependency list now names only the actual argument and its
three component results. The old direct proof dependencies
`lem-sfb-etale-local-monodromy-realization` and
`lem-sfb-integral-lisse-reduction-equivalence` are used through the given normalized
data, rather than invoked as existence theorems.
`def-sfb-monodromy-realization-data` remains a statement dependency, and
`cor-galois-lisse-representations` is now a proof dependency of the finite lifting
component. None of these nodes is globally pruned. The DVR factorization and PID
freeness steps are retained.
The finite-level use of `cor-galois-lisse-representations` is retained through the
specified finite correspondence, its fundamental-group equivalence and faithfulness.

The existing `new-e5-linear-fibre-path-transport` is used as a generic, already
proved linearization tool, with its explicit evaluation formula. It does not
replace any step of the Rankin--Selberg unit. The maintainer may review that use;
this packet does not add or reorder `tool_uses` approvals.

## Where the brief, the DAG or earlier work was wrong

The return at c5abafba593 correctly identified duplicated private finite-stalk
faithfulness proofs. Both `finite_fiber_faithful` and `eq_of_finite_fiber` already
exist in `LatticeNormalizationRationalExact`; the first could not be imported
while private. This repair promotes the existing helpers and reuses them.
The original assigned statement remains unchanged and no mathematical defect was found.
The DAG's rational-continuity step uses an open-lattice cover in words; the proof
uses an equivalent, direct finite matrix-coordinate argument. The recovery step
needs continuous coefficient linearity, not merely constant scalar linearity;
that extra verification is explicit, using locally constant residues and the
sheaf axiom. Rank zero, level zero (positive exponent one), arbitrary ramification
and nonnormal base schemes are included in these arguments.

The launcher interrupted the work for a provider error and subsequently to shorten
the compile queue. The sandbox reference start changed from attempt 1792749534
to 1792773481 on resumption. No budget metadata was edited by this worker; work
continued on the same proof packet. No delivery was in flight when resuming.

## New nodes

`lem-a1-integral-representation-rationalization` gives scalar extension of a
continuous finite free integral representation and its actual stable tensor-unit
lattice. It is strictly the linear-algebra/topology component of the parent.

`lem-a1-finite-fibre-linear-lifting` gives the unique lift of an equivariant linear
stalk isomorphism between finite locally constant module sheaves. It is independent
of inverse limits and rational realization and uses the existing finite Galois
correspondence. The coefficient ring need not itself be finite.

`lem-a1-completed-normalization-recovery` recovers the specified rational module
from an isomorphism of normalized integral towers. It starts with a diagram
isomorphism and proves the coefficient-linear limit and scalar-extension comparison;
it does not construct the fibre representation, freeness, continuity or tower
isomorphism of the parent.

All three inherit the parent's chapter and unit, and point to its blueprint
ancestor `lem-a1-affine-hc0` through the parent. Searches found no exact Mathlib
or blueprint replacement for these explicit component statements.
The visibility-only repair is recorded in
`coord/changes/K7-shared-finite-fibre-faithfulness.md`. No new node or new
mathematical assertion is introduced by this repair: these are existing proved
helpers for the finite correspondence already cited by the nodes.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
