## What changed

Proved `genericFormalFiber_bot_geometricallyRegular_of_finite_subring` by obtaining the
finite-type and quasi-finite-at-prime structure from module finiteness and applying
`RingHom.isRegular_formalFiber_of_isQuasiFiniteAtPrime` to the inclusion `A₀ → A`, with
zero prime below `P`. Added the proof-only import
`Sheaf.RingTheory.FiniteRingMapQuasiFinite`. Updated the item's DAG proof and dependencies
to record both declarations used.

## Proved and sorry left

Closed the sorry in `genericFormalFiber_bot_geometricallyRegular_of_finite_subring`.
No sorries were added (one local hole closed, zero added; no decomposition).
The result still rests on the existing open declarations
`Algebra.finiteType_and_isQuasiFiniteAtPrime_of_finite` and
`RingHom.isRegular_formalFiber_of_isQuasiFiniteAtPrime`; it is not yet an
axiom-free proof of the target import closure.

## No longer needed

Removed the unused import `Mathlib.RingTheory.Localization.FractionRing`.
Changed `Sheaf.RingTheory.FormalFibreQuasiFiniteAscent` to a proof-only import,
and publicly imported `Sheaf.RingTheory.GRing` for the definitions in the signature.
No old proof-dependency node was pruned: the ascent theorem remains used.
The unit's realized route is unchanged.

Change record: `coord/changes/GenericFormalFiberFiniteSubringBase-imports.md`.

## Where the brief, the DAG or earlier work was wrong

The original one-step DAG proof omitted the finite-ring-map theorem needed to construct the
finite-type instance and quasi-finiteness hypothesis. The Lean proof uses that existing node
as an additional dependency.


## Second reading by D2

1. Compared the delivered module with the repository using diff. The existing
   declaration signature and docstring are byte-for-byte unchanged. No definitions
   or target statements changed. Import visibility repair is recorded above.
2. Compiled the original delivered proof without warnings. Scratch `#print axioms`
   returned only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, the last
   from the two existing open dependencies. No local sorry, axiom, unsafe, opaque,
   extern, implemented_by, hollow definition, or arbitrary chosen data occurs.
3. No new statements or nodes were split off, so there are no new holes to validate.
   The finite-type witness is a proof of a proposition, not chosen ring data.
4. Read both dependency statements, searched Sheaf and upstream RingTheory for
   formal-fibre ascent and generic-fibre results, and checked the Stacks quasi-finite
   ascent argument in the locally available more-algebra.tex. The reduction is
   appropriate; injectivity contracts zero to zero, including the cases P = zero
   and the identity subring. The existing DAG dependency remains used; no unit
   realized node is bypassed. Import experiments showed FractionRing unnecessary
   and GRing sufficient for the statement. The sole direct importer already
   imports the affected dependencies itself and was compiled unchanged against
   the repaired module.
5. Compared the node JSONs: only proof and proof_deps changed. The two steps name
   precisely the two existing theorems used, their union equals proof_deps, and
   proof_origin agrees with the Stacks argument. No new-node fields are required.

Changed only imports and reporting: removed FractionRing, made ascent proof-only,
publicly imported GRing, and added the import change record. Kept the correct proof.
