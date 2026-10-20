## What changed

Restored Sheaf.AlgebraicGeometry.ZeroSupportFiniteScheme from its rework quarantine,
preserving its Lean attachment and exact theorem signature. Made the existing Coherent
import public to repair the reported unknown public declaration. Filled the proof of
AlgebraicGeometry.coherent_zero_support_finite_scheme completely.

The proof constructs the annihilator support, applies the stated zero-dimensional
closed-subscheme finiteness theorem, and uses its actual global-functions algebra.
The closed-immersion annihilation/unit theorem constructs G as tensor pullback and
identifies F with its pushforward. The projection formula and the singleton open-cover
argument on the finite discrete source identify F tensor N with F. This transports
coherence and support. Degree-zero cohomology is global sections with restricted
scalars; positive degrees vanish by affine cohomology and affine pushforward.
Two proved private helpers implement the finite-discrete tensor and affine-source
cohomology arguments. The DAG proof and proof dependencies now describe this route.

Validation: lcompile.py compiled the complete proof without warnings; after import
pruning, the axiom check compiled in 12.5 seconds and printed only propext,
Classical.choice, Quot.sound. No sorryAx is reachable. Empty support is covered by the
zero global-functions algebra and empty biproduct; no point/nonemptiness assumption
is used. For X = Spec k and F = O_X, the construction is the usual annihilator-zero
support and gives the expected finite algebra. The theorem statement is unchanged.

Import/interface change record:
coord/changes/zero-support-finite-scheme-public-coherence.md.
No definitions or upstream source files changed. No forced adaptations.

## Proved and sorry left

Closed 1 of 1 original holes:
AlgebraicGeometry.coherent_zero_support_finite_scheme
(node lem-pc-zero-support-finite-scheme).

Added 0 holes. There are 0 sorries left in the delivered module and no split-off lemmas.
Both private helper theorems are fully proved. The entire public theorem's axiom closure
is standard, as checked by #print axioms.

## No longer needed

Removed direct proof imports:
- WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence;
- Sheaf.AlgebraicGeometry.FiniteSchemeCohomologyTensor;
- Sheaf.Paper.SchemeTheoreticSupport (retired re-export; use its upstream source directly);
- WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed;
- Sheaf.AlgebraicGeometry.CoherentFiniteType (the new proof uses the actual coherence
  equivalence on locally Noetherian schemes).

The proof no longer directly needs lem-sc-dim0-finite or
lem-weil-pbc-finite-type-module-support-closed: it obtains the support image and its
scheme directly, then transports the dimension through the closed embedding.
It uses the annihilation/unit theorem instead of the full
lem-weil-pbc-closed-immersion-coherent-equivalence (including its formal-module clause).
It does not need lem-pc-finite-scheme-cohomology-tensor: this statement asks for
cohomology comparison, coherence, and support, rather than finranks or Euler
characteristics. The finite-discrete local tensor argument is proved directly.
Removed obsolete tool_uses entries for the full coherent equivalence and direct
support-closed theorem; retained the existing closed-immersion cohomology approvals.

These are removals from this proof's direct dependencies, not withdrawals of library
modules. SchemeTheoreticSupport still uses FiniteTypeModuleSupportClosed internally;
that upstream declaration and dependency remain intact. Other consumers may still
need all of the listed modules. No module is deleted, and no unit route is bypassed.
The unit's realized record is unchanged.

## Where the brief, the DAG or earlier work was wrong

The item source is quarantined, not withdrawn; the rework row correctly diagnosed the
private Coherent import. Its public theorem now explicitly imports that source publicly.
The old DAG's final finite-scheme cohomology/finrank step asserted results not present
in this theorem's conclusion and was unnecessary. The ordinary affine cohomology API
uses the source H model, so the new proof explicitly transports positive-degree
vanishing through the natural source comparison to the required module-derived model.
All scalar comparisons in degree zero remain module isomorphisms along i.appTop.
No mathematical statement was disputed or changed, and no new nodes were needed.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
