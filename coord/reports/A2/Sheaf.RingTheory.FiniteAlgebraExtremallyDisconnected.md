## What changed

Proved `extremallyDisconnected_spectrum_of_finite_finitePresentation` in
`Sheaf.RingTheory.FiniteAlgebraExtremallyDisconnected`, preserving its exact signature.
Added private, fully proved helpers for constructible/clopen sets, locality of extremal
disconnectedness, topological pullbacks covered by section charts, affine finite-presentation
cancellation, Hausdorffness of finite affine covers, and finiteness of residue-field maps
at maximal primes.
Added proof-only imports of `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` and
`Mathlib.RingTheory.Ideal.GoingUp`. Updated the theorem's proof documentation and the node's
proof and proof_origin to the actual argument.

The finite section images are clopen by finite presentation and Chevalley. Consequently their
preimages already give open charts, and locality on open covers replaces Boolean atom
partitioning. The topological pullback along the continuous section is extremally disconnected;
the previously proved scheme-pullback uniqueness calculation identifies it homeomorphically
with Spec S. The empty ring and empty charts require no extra nonemptiness assumptions.

Repair of return at 68674e8b6: removed the duplicate private
`finite_spec_residueFieldMap`. Imported
`Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres` privately and applied the
existing `AlgebraicGeometry.finite_spec_residueFieldMap` instead. That theorem was private;
its original module is unclaimed, so this delivery exports it in place. Its type and proof
are unchanged. The change record
`coord/changes/finite-spec-residueFieldMap-public.md` lists the consumer audit. The node describes this reuse;
the Dedekind theorem itself is not a mathematical dependency of this argument.

Validation: both changed modules compiled through lcompile.py, without diagnostics
(5.1 and 3.8 seconds). The unchanged direct importer
`Sheaf.RingTheory.SemilocalNormalizationDimOne` also compiled against the changed helper
(2.6 seconds, no diagnostics); its temporary sandbox copy was removed.
No existing public signature or definition changed. The only interface
addition is exporting the existing helper; consumers need no adaptation.

## Proved and sorry left

Closed the one original hole:
`extremallyDisconnected_spectrum_of_finite_finitePresentation`
(node `lem-ce-finite-algebra-extremally-disconnected`).

Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
All helpers introduced in the item are private and fully proved. The reused helper is now public
in its original module. That adapted module has zero holes before and after this repair.
The existing finite affine section-cover theorem remains a dependency; this delivery proves the assigned theorem from that interface,
the proved zero-dimensional spectrum theorem and the proved continuous-section theorem.

## No longer needed

All three planned dependencies remain used. Removed the duplicate private
`finite_spec_residueFieldMap` proof (theorem body and its local transparency setting).
Its single existing implementation is reused through a proof-only import. No dependency node
or module is pruned.
The old plan's Boolean partition, section equalizer loci, representative selection and finite
sigma-type decomposition are unnecessary. They were not separately attached dependency nodes.
The proof instead uses clopen section charts and locality of extremal disconnectedness.

## Where the brief, the DAG or earlier work was wrong

The old DAG marked the sizeable incidence/equality partition argument elementary. It is
unnecessary: each section immersion itself is finitely presented, because its composite with
the finite locally free projection is an isomorphism and the projection is of finite type.
Its image is therefore clopen by Chevalley. Overlapping open charts suffice; no equality-locus
calculation or disjoint refinement is needed. The assigned statement and the three dependency
interfaces are correct and usable unchanged. No new nodes or split-offs were needed.

The returned delivery duplicated an existing private theorem word for word. The repair removes
that copy and exports and uses the original theorem. The original public declarations retain
their signatures and proofs. The existing Dedekind node is not cited as proving the general
helper: the helper itself, already fully proved, is the reused declaration. No new statement,
node or `sorry` was added.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
