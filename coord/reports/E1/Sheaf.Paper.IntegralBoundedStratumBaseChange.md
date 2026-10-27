## What changed

Restored `lean/Sheaf/Paper/IntegralBoundedStratumBaseChange.lean` from its
quarantine archive and repaired its compilation performance. A proved generic
`bounded_open_closed_base_change` carries out the bounded argument over an
arbitrary commutative condensed ring; the public integral theorem specializes it.
A proved private `stratum_composite_cancel` establishes the final functor identity
abstractly, replacing `dsimp [e₀, β, γ, Λ]` on integral coefficient data.
The proved `mixed_open_zero` now derives exact termwise mixed vanishing
from the underived module support theorem and homology comparison, avoiding
construction of the total left derived pullback and its resolution data.

The optimized monolithic file still took 99.2 seconds, so the proof was then
split into two new modules as permitted after optimization:
`Sheaf.Paper.CondensedStratumBaseChangeCalculus` contains the original eight
public constructions (verbatim) and the proved unbounded support/mate calculus;
`Sheaf.Paper.CondensedBoundedStratumBaseChange` contains the proved generic
bounded theorem. The original module publicly imports the bounded theorem and
therefore publicly reexports all eight constructions under their original names.
Every original public import and both original public theorem signatures remain
verbatim. The original node retains its statement and primary Lean attachment;
the moved constructions are attached to the new calculus node and the proof
edges follow the new module organization. No other existing module changes.

## Proved and sorry left

This is a zero-hole performance repair. The archive and restored module both
have zero `sorry`s. Holes closed: 0 of 0. Holes added: 0. Split-off holes: 0.
The existing complete proofs retained are
`AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange.integral_bounded_open_closed_base_change`
and
`AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange.integral_bounded_locally_closed_base_change`.
Both belong to `lem-sfb-integral-bounded-stratum-base-change`.
Every new helper and every declaration in the two new modules is proved
completely; no proof hole was moved by the file split.

## No longer needed

Removed the private proof import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed` and replaced
it with `WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed`.
The proof uses underived support vanishing plus exact-functor homology directly,
so it no longer needs the total-derived vanishing wrapper or that module's
bounded-constructible dependency layer. All source-library declarations remain
unchanged. The new generic calculus module omits the integral-coefficient data import and
the broad ancillary public imports that its arbitrary-ring statements do not
use; the original module retains all its original public imports.
The remaining private proof imports (`ProfinitePointPullback`,
`CondensedOpenClosedRecollement`, `Derived.OpenImmersionEssImage`, and the
abelian open `BaseChange` module) now belong to the new unbounded calculus,
instead of being unused direct imports of the integral wrapper.
No module or DAG node is withdrawn. The original direct proof dependencies now
sit below the two new proved calculus nodes; none is globally declared
unnecessary. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined performance repair, not an unfinished theorem.
The current rework row records a 60.2-second compile. Profiling the archive
identified repeated typeclass synthesis and a 5.26-second final `dsimp` over
coefficient and derived-functor data. The optimized file still exceeded the limit (99.2 seconds), so it was split
into self-contained modules after eliminating the expensive total-derived
vanishing conversion and the final large-definition simplification. The repair
changes proof organization without changing mathematical data or the two
original theorem statements.

Consumer checks: the live direct-importer scan returns zero modules; a source
search in both Lean roots and the quarantine tree finds no outside textual
consumer of this module or its two public theorems. The node is restored, not
withdrawn. No consumer adaptation is necessary because the public interface is
unchanged. Change record:
`coord/changes/E1-integral-bounded-base-change-proof-context.md`.

Validation: all three split modules compiled successfully in import order through
`lcompile.py --all`. Final delivery validation compiles the documented final
version with the new calculus module's public imports trimmed to its actual
statement dependencies, checks every declaration's axioms, and runs preflight.

## New nodes

`lem-sfb-condensed-stratum-base-change-calculus` records the existing unbounded
support, actual adjunction mate, and exactness calculus, with the eight original
constructions moved verbatim to its new module. Its entire proof is complete.
The closed square conclusion uses locally Noetherian ambient schemes to obtain
quasi-compact complementary opens. The open result and mixed vanishing require
no constructibility or completeness assumption.

`lem-sfb-condensed-bounded-stratum-base-change` records the complete generic
bounded theorem for any commutative condensed ring, with complementary cartesian
open and closed squares and quasi-compact opens. It restricts the proved
unbounded mates, proves boundedness by exact homology, and supplies all actual
normalization and mixed-zero equations. No new `sorry`s are added.

Change record: `coord/changes/E1-integral-bounded-base-change-proof-context.md`.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
