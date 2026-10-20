## What changed

Proved `AlgebraicGeometry.etaleSheavesGsetsPoint` with its original statement and
universes. The equivalence is assembled from the existing Galois stalk functor,
full faithfulness, and essential surjectivity. The representable-stalk bijection
is proved explicitly from the stalk colimit, the separably closed lifting lemma,
and unramified injectivity. Its equivariance follows by extending Galois
automorphisms; naturality follows from the germ transition identity.

Generalized the coefficient universes of the supporting, already proved Galois
stalk and invariant-section lemmas from `max (u+1) v` to `max u v`. All their
proofs compile. Supplied sheafification at the smaller coefficient universe
through the essentially small affine etale site. Adapted the existing abelian
and field-sections consumers by explicitly specializing the generalized universe.
Every supporting module was unclaimed at the time of the holder check.

Change record: `coord/changes/D5-galois-stalk-coefficient-universes.md`.
The supporting nodes' explicit coefficient bounds and `lean.statement` fields
follow the generalized signatures, with statement-change records for every citer;
the item's proof steps and dependencies follow the actual Lean proof.

The resumed worker rechecked the retained packet against current sources: the
item signature is unchanged, all fifteen supporting/adapted modules remain
unclaimed, and the delivered Lean files contain zero holes. The existing
proof and universe repair are retained. Current preflight identified the newly landed
consumer `FieldModuleSectionsInvariants`; its explicit universe specialization is
adapted in the same delivery, preserving its signature.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.etaleSheavesGsetsPoint`
(node `lem-exc-etale-sheaves-gsets-point`).

Added 0 holes and split off 0 statements. There are no remaining `sorry`s in
any delivered Lean module. The supporting declarations were already proved;
their universe generalizations and consumer adaptations retain complete proofs.
This is a proof from existing declarations, not a decomposition into new holes.

The main module and supporting modules compile with lcompile.py. The unchanged
consumer `Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisImage` was compiled
against the delivered dependencies and passes. A separate axiom probe reports only `propext`, `Classical.choice`, and
`Quot.sound` for the item, stalk functor, full faithfulness, essential surjectivity,
etale lifting, unramified injectivity, and automorphism extension. The main
statement is unchanged, including its original `max u (v+1)` coefficient bound.
The resumed dry run found stale Sheaf imports after upstream migration; these
now use existing WeilConjectures modules for automorphism extension and orbit
coproducts. The finite-Galois representative universe repair stays in the existing
Sheaf module. No upstream statement changes.
A repeated compile timeout was diagnosed with Lean profiling. The local stalk
natural transformation now has an explicit defining equation and its local
value is cleared after that equation, avoiding repeated automatic unfolding in
the action construction; its statement and mathematical construction are unchanged.
Edge cases are inherited from the existing equivalence machinery (empty action,
separably closed K) and the representable colimit proof works for empty X.

## No longer needed

Removed direct proof imports from the item:
- `WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
  (`lem-weil-pbc-etale-fibre-discrete-separable-points`);
- `Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants`
  (`lem-exc-field-sections-stalk-invariants`);
- `WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`
  (`lem-weil-pbc-small-etale-representable-presheaf-sheaf`);
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`
  (`def-weil-pbc-geometric-stalks`).

The item now uses the existing stalk action, full-faithfulness and essential
surjectivity lemmas instead of redoing their arguments. Invariant sections,
finite residue fields and etale field G-sets remain needed transitively, so no
whole-library module withdrawal is claimed. The small-etale uliftYoneda sheaf
uses Mathlib's subcanonical instance directly, and the pointed stalk is the
Mathlib point's sheafFiber. The representable-stalk node is retained and realized
by the private colimit calculation. Removed obsolete top-level tool-use approvals
for the two generic nodes no longer used directly by this proof.

No new modules or nodes. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof-dependency interfaces used `Type (max (u+1) v)`, whereas this
item requires `Type (max u (v+1))`. Substituting v+1 does not bridge that gap when
u exceeds v+1. Generalizing the supporting proved lemmas to `Type (max u v)`
repairs the interface without strengthening the item's hypotheses or altering
its conclusion. The smaller-universe sheafification instances need the dense
affine etale subsite construction; plain large-site instance search fails.

The earlier retained attempt had no delivery report, several elaboration errors
in the item, and a missing small-universe sheafification instance in essential
surjectivity. These are repaired here. Its temporary probe is retained only in
scratchpad, outside the delivered Lean tree.

The retained report incorrectly said the supporting natural-language nodes had
no universe bound. Ten of them explicitly specified `max(u+1,v)`; these now say
`max(u,v)`, with the former statements and the validity of every DAG citer
recorded in `statement_change`. Their mathematical content is otherwise unchanged.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
