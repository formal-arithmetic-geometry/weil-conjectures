## What changed

Proved `CategoryTheory.ringedSite_resolution_roof` without changing its signature or public
imports. Added private, completely proved helpers for nonnegative injective replacements,
strict lifting along monic quasi-isomorphisms, homotopy uniqueness, and the abstract roof
comparison. All proof dependencies are private imports.

The proof extends nonnegative complexes by zero, applies the existing bounded-below
injective replacement theorem, and transports the result back through the fully faithful
extension functor. Strict lifting uses the existing Mathlib bounded-below lifting property.
It chooses a single reference roof. For any other resolution pair and roof, it lifts the
comparison to the reference replacement. Homotopy uniqueness identifies the source maps;
canonical resolution naturality identifies the target maps. Cancellation gives exactly
the all-resolution normalization equation. Evaluation preserves the replacement
quasi-isomorphism by direct-image injective acyclicity and Leray acyclicity.

Sources read: Stacks `sites-cohomology.tex`, `remark-before-Leray` (08J6), and
`derived.tex`, `lemma-morphisms-lift` (013P) and
`lemma-morphisms-equal-up-to-homotopy` (013S), together with the dependency declarations.
Compilation is exclusively through `lcompile.py` in the assigned sandbox.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.ringedSite_resolution_roof`
(`lem-weil-pbc-ringed-site-resolution-roof`).

All new private helpers are proved. The item contains zero remaining holes; this delivery
adds zero holes and zero nodes. Count: 1 of 1 original sorries proved; 0 split off.
The existing declared dependencies retain their own independent proof obligations.

## No longer needed

None. No original imports, declarations, nodes or modules were removed or withdrawn.
All seven original proof dependencies remain used, including the injective-resolution
comparison API. The proof follows the original three-step node plan and preserves the
unit route. No target-reachable module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The bounded-below dependency uses integer indices,
whereas the item uses natural indices; extension by zero and full faithfulness provide
the required transport. Mathlib does not automatically infer preservation of monomorphisms
for this extension functor, so the helper proves that fact degreewise.

Validation: the complete module compiled cleanly through `lcompile.py` in 22.6 seconds,
exit code 0. The theorem signature and all seven original public imports were compared
verbatim with the shared source. Every added project import passed `import_direction.py may`.
All lines are at most 100 characters. No `sorry`, axiom or admitted definition remains.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
