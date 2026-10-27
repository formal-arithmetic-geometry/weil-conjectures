## What changed

Filled `RingHom.WeaklyEtale.isNormalRing` in
`Sheaf.RingTheory.WeaklyEtaleNormalRing` without changing its statement or public imports.
Two proved private helpers supply normality of an ind-etale algebra and the
same-universe refinement argument.

Repaired the return at delivery head `1c9a2037797`: removed the duplicate private
`RingHom.normal_equiv` entirely. Added the proof-only
`import all Sheaf.RingTheory.GeometricallyNormalTensorNormal` and used its existing
private `Algebra.normal_equiv` at all three transport sites. Lean's `import all`
provides access to that private theorem without exposing it publicly or changing
its owning module. No visibility, signature, or definition repair is needed.

The ind-etale presentation is mapped to commutative rings using
`commAlgCatEquivUnder` and preservation of connected colimits by `Under.forget`.
Every stage is normal by `RingHom.Etale.isNormalRing`; applying
`CommRingCat.isNormal_of_filtered_colimit` and the presentation isomorphism gives
normality of the refinement. `Algebra.normal_ring_of_faithfullyFlat` descends it.
Finally `Algebra.WeaklyEtale.ulift_iff` and the existing `Algebra.normal_equiv`
handle the independently quantified source and target universes.

The argument follows the existing four-step DAG plan, including its elementary
ring-equivalence transport, so no node changes are needed. All proof imports are
used. No other modules, definitions or interfaces were changed.
The repaired module compiled through `lcompile.py` without errors or warnings.

## Proved and sorry left

Closed 1 existing hole: `RingHom.WeaklyEtale.isNormalRing`
(node `lem-sfb-weakly-etale-normal-ring-ascent`).
Added 0 holes; split off 0 statements. There are 0 sorries left in the delivered module.
Both retained private helpers are fully proved. The imported declarations retain
their existing proofs and any transitive holes; no imported theorem is re-proved here.

## No longer needed

The previous delivery's duplicate private `RingHom.normal_equiv` is removed;
the existing `Algebra.normal_equiv` supplies exactly that result.
No imports are removed. The proof uses all declared proof dependencies.
No modules or DAG nodes are withdrawn. The blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The previous delivery overlooked the word-for-word private helper already present
in `Sheaf.RingTheory.GeometricallyNormalTensorNormal`. Importing that module with
`import all` permits direct reuse and repairs the landing refusal.
The stated mathematical dependencies suffice without extra intermediate results.
Zero rings cause no special case: normality is quantified over prime ideals,
and every transport and descent result applies without a nontriviality hypothesis.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
