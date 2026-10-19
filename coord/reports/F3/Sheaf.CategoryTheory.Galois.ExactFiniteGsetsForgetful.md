## What changed

Proved `ContAction.nonempty_forget_iso_of_exact_finite` without changing its signature
or public imports. The proof uses the already proved
`CategoryTheory.PreGaloisCategory.nonempty_iso_of_fiberFunctor` in
`WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability`.

Private helpers establish finite limits and colimits of continuous finite actions,
continuity of invariant complements, and the Galois-category and forgetful-fibre-functor
structures. An exact set-valued functor preserves nonemptiness and reflects initial
objects. Its preservation of equalizers and complements gives faithfulness; balancedness
then gives reflection of isomorphisms. Lift the finite-valued functor to `FintypeCat`,
apply fibre-functor uniqueness, and whisker the isomorphism into types.

The item's node records this shorter route. A new node attaches the existing proved
fibre-functor uniqueness theorem; it adds no Lean declaration. All helper declarations
are private, so importers see the same public interface.

## Proved and sorry left

Hole closed: `ContAction.nonempty_forget_iso_of_exact_finite`
(`lem-wf-exact-finite-gsets-forgetful`), 1 of 1 original holes.
Holes added: zero. Holes left in delivered Lean files: zero. Split off: zero.
The new node attaches an existing proved theorem, rather than introducing a new hole.

The resumed standalone compile requests and a minimal connectivity probe initially
received no server answer (207, 186 and 189 seconds respectively). The required delivery
dry run subsequently passed its compilation stages and reached the server preflight;
the proof and axiom checks passed. Preflight then requested a change record for
added commands; `coord/changes/F3-exact-finite-gsets-proof-options.md` records the
options, private instances and sole unchanged downstream importer.

## No longer needed

Removed the direct proof import `Mathlib.CategoryTheory.CofilteredSystem`. The item no
longer directly constructs the small system of open normal finite-index subgroups,
compatible points on regular quotients, regular covers, or kernel-pair descent.
Their roles are supplied by the existing fibre-functor uniqueness proof.

The former direct dependency `lem-trf-cofiltered-finite-sets-section` remains needed
transitively by the newly attached uniqueness theorem, so it is not globally pruned.
`def-galois-exact-functor` remains a Mathlib dependency. No existing Sheaf module or
other DAG node becomes unnecessary. The unit `sk-d-geometry` has no realized statement
or proof steps for this item; the blueprint's stalk-transport route is retained.

## Where the brief, the DAG or earlier work was wrong

The existing source library already proves uniqueness of fibre functors. The original
nine-step quotient-system plan can therefore be replaced by verifying its hypotheses
for continuous finite actions. This works for an arbitrary topological group and
independent group and finite-set universes, as in the unchanged statement.

The import-direction checker confirms that the new source-library import creates no
cycle. No statement or definition repair or consumer adaptation is needed. The required
change record documents the scanner-reported addition of commands and private instances.

## New nodes

`lem-wf-fibre-functor-uniqueness` attaches the existing proved theorem
`CategoryTheory.PreGaloisCategory.nonempty_iso_of_fiberFunctor` and records its proof:
pro-representability identifies natural transformations with compatible fibre sections;
the finite cofiltered-system theorem supplies a section; equivariance on Galois objects
and descent from Galois covers make the transformation an isomorphism. The source
module is unchanged. Its Mathlib searches are recorded in `searches.jsonl`.

Change record: `coord/changes/F3-exact-finite-gsets-proof-options.md`.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
