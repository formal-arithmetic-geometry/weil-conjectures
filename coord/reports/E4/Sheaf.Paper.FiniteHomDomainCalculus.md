## What changed

Proved `WeilConjectures.finiteHomDomain_transpose` in
`Sheaf.Paper.FiniteHomDomainCalculus` from the existing normalized closed records
and the actual evaluation-defined comparison. Nine proved private categorical
helpers establish the inverse-transpose formula, evaluation naturality, naturality
of base change, uniqueness, and the conjunction of these laws. The proof works
for arbitrary unbounded objects and uses no finite Tor-amplitude hypothesis.

Added the concrete public proposition `FiniteHomDomainTransposeLaws` in the same
module. It is the original four-clause conjunction, parameterized by the two
closed records, scalar functor and tensor comparison. The final theorem names this
predicate at the same finite-coefficient data. Its comparison is exactly
`coefficientBaseChangeHom`, which is the body of `etaleFiniteHomCanonical`.
There is no change in mathematical content or in any target signature. The
change record is `coord/changes/finite-hom-domain-transpose-predicate.md`.

This presentation avoids a kernel timeout caused by the definitionally equal
ring instances `ULift.commRing.toRing` and `ULift.ring` occurring through the
etale-category notation and the canonical comparison. The expanded specialization
timed out even with a fully proved generic lemma; keeping the category parameters
shared behind the predicate makes the isolated specialization compile in 6.6 s.
The proof uses explicit categorical identities rather than unrestricted simp.
Local reducibility hints expose only the small categorical operations needed by
the helpers; local irreducibility keeps the large scalar and closed constructions
folded. No debug profiling or raised heartbeat limit is retained.

The node records the direct closed-record proof of its transpose steps and the
additional predicate declaration. The blueprint unit route is unchanged. No import
was added or removed. Every pre-existing definition and completed proof is retained.

Validation: the complete item module compiled cleanly in 43.5 s, below the 60 s
limit. The unchanged direct importer was then compiled against the sandbox artifact
with `lcompile.py --all`; both files passed. That batch reported longer times
(104.0 s for the item and 83.7 s for the importer) than the standalone item run;
no timeout or compiler error was reported. The delivery tool's required compile
and preflight checks remain the acceptance check. The unchanged consumer copy
was removed from the packet after this check.
Source-only
`tools/downstream.py --uses finiteHomDomain_transpose` found 98 transitive module
importers and no use of this declaration outside its own module. Its sole direct
importer is `Sheaf.SixFunctors.FiniteCoefficientVerdier` (unclaimed); no adaptation
is needed. The change record lists all 98 module importers and their holders.

## Proved and sorry left

Closed 1 of the 3 original holes:
`WeilConjectures.finiteHomDomain_transpose`.

Two original holes remain, both under node
`lem-coef-finite-hom-domain-calculus`:

- `WeilConjectures.finiteHomDomain_monoidal`.
- `WeilConjectures.finiteHomDomain_scalarCoherence`.

Added holes: none. Split off: none. The nine private helpers and the new predicate
contain no holes. The flat-model, pullback, endpoints and quotient-identity proofs
are retained. The imported normalized closed data still depend on the existing
statement modules; this delivery closes the assigned transpose hole from those
existing declarations, as required by stage 3.

## No longer needed

No imports, nodes or modules are globally pruned by this partial delivery.
The transpose proof itself needs only the closed structure and tensor comparison
already exported by `EtaleFiniteCoefficientHomArrow`; it does not require a fresh
application of `lem-sf-ringed-derived-closed-symmetric-monoidal` or the monoidal
coherence theorem. The ringed closed theorem remains in the node's proof
dependencies because the untouched monoidality plan still uses it.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The existing closed record
already contains the adjunction needed in the transpose step, so its universal
property and the definition of `coefficientBaseChangeHom` suffice. Naturality is
purely categorical and does not assert invertibility. The old expanded Lean
presentation was expensive to specialize because of a ring-instance diamond;
the named predicate preserves that exact proposition while sharing its parameters.

For the two remaining holes, the stated general monoidal-comparison dependency is
formulated for ringed-site module categories with a chosen normalized lift.
Applying it to the existing ModuleCat-valued small-etale scalar functors still
requires identifying the derived lift, tensor comparison, unit and signed
symmetry with the published finite coefficient data. No claim that its abstract
witness already supplies these equalities has been made here.

The adopted source library also has `Functor.leftDerivedFunctorMonoidal` and its
braiding theorem in `LeftDerivedFunctor.MonoidalStructure`. These offer another
route for the remaining monoidality argument, but identifying their tensor and
unit maps after transport to the chosen scalar adjoint is still necessary.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
