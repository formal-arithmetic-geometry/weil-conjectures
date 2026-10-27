## What changed

Replaced the sole hole in `Sheaf.FieldTheory.DenseHenselianEtaleComparison` with a
compiling assembly proof, preserving the original theorem signature verbatim.
The proof uses the existing restriction-image theorem to obtain continuity and
surjectivity. For injectivity it extracts a simple polynomial root from the
approximation step, proves its separability by differentiating a minimal-polynomial
factorization, proves that it lies in the chosen separable closure, and performs
field-adjoin induction. Compactness of the Krull Galois group turns this into the
required topological group isomorphism with its literal restriction formula.

The actual inverse-image equivalence then implies bijectivity of the existing
`cohomologyMap` by `Sheaf.H.mapFunctor_bijective`. The final equation is the existing
`cohomologyMap_map`. Neither application requires the torsion hypotheses.
Two proved private helpers handle separability from a simple root and membership
in the image of a separably closed field; neither introduces any hole.

Added three statement modules for genuine remaining steps of the original argument,
with complete proofs in words, sources, and matching nodes. They isolate the
relative-separable-closedness argument (original step 1), coefficient perturbation
(original step 3), and the general Galois-to-sheaf equivalence (original step 6).
The assigned module imports them privately, along with
`Sheaf.FieldTheory.SeparableClosureRestrictionImage`. All original public imports
are preserved. No existing declaration, definition, instance, or shared module
interface is changed.

Validation: all four delivered Lean modules compiled with `lcompile.py`; the three
new modules took 2.8, 2.3, and 2.4 seconds, and the final assigned module took 8.4
seconds. The compiler reported no errors or warnings. Checked the original theorem
signature for literal equality, all new node dependencies for existence, and all
Lean lines for the 100-character limit. The delivery tool supplies the final axiom
and direct-hole probes.

## Proved and sorry left

Closed the original direct hole in
`AlgebraicGeometry.Etale.denseHenselianField_etaleComparison`
(node `lem-per-dense-henselian-field-etale-comparison`). No `sorry` remains in the
assigned module. The private helpers `separable_mem_closure_range` and
`isSeparable_of_simple_root` have complete Mathlib proofs.

This is a decomposition: one original hole closed, three strictly smaller holes
added, net minus two holes closed. The entire mathematical comparison is not yet
an unconditional proof. The three admitted declarations are:

- `FieldTheory.denseHenselian_isSeparable_mem_range`, node
  `lem-per-dense-henselian-relative-separable-closed`, in
  `Sheaf.FieldTheory.DenseHenselianRelativeSeparableClosed`.
- `FieldTheory.denseHenselian_exists_simple_root`, node
  `lem-per-dense-henselian-simple-root-approximation`, in
  `Sheaf.FieldTheory.DenseHenselianSimpleRootApproximation`.
- `AlgebraicGeometry.Etale.upperStar_isEquivalence_of_galoisRestriction`, node
  `lem-per-galois-restriction-etale-equivalence`, in
  `Sheaf.AlgebraicGeometry.GaloisRestrictionEtaleEquivalence`.

Each is a public theorem with exactly `:= by sorry`, a complete sourced argument
in its docstring, and its own new module and DAG node. The existing imported
`IntermediateField.separableClosure_restriction_image` remains admitted in its
existing module; this delivery neither changes it nor adds its hole.

## No longer needed

Removed the private proof imports:

- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`;
- `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`;
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`;
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`.

The first two are no longer direct proof dependencies of the assigned module;
their mathematics remains below the new general Galois/sheaf equivalence node.
They are not claimed as globally pruned. Likewise finite Galois envelopes,
`Sheaf.FieldTheory.HenselianFiniteExtensionTopology`,
`Sheaf.FieldTheory.HenselianKrasnerNeighbourhood`, and
`Sheaf.FieldTheory.HenselianSimpleRootStability` remain needed below the two
new valuation steps; these have been transferred, not discarded.

The route genuinely no longer requires
`prop-weil-pbc-kinjective-resolutions-exist` or
`def-weil-pbc-kinjective-resolutions`, and their two original top-level `tool_uses`
approvals are removed. Their modules above are absent from the new proof imports.
The exact Ext API proves the needed cohomology assertion directly from an exact
equivalence, with the canonical constant-sheaf comparison; no bridge to a chosen
K-injective resolution is needed.

`lem-galois-closed-subgroup-product-finite-groups` is removed from the direct node
route: the already proved Mathlib compactness instance for a Galois group supplies
compactness from the Krull inverse-limit theorem. No source-library declaration
or module is removed, and no withdrawal is proposed. All original public imports
are retained as part of the public interface.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original seven-step argument is mathematically
usable, but its categorical ending requests unnecessary K-injective comparison
work: the library's actual cohomology map is already the Ext comparison of an exact
functor and has a proved bijectivity theorem for fully faithful functors preserving
injectives, plus the exact required naturality equation.

The valued-field inputs use different presentations: multiplicative `Valued`
topologies, additive ball-generated topologies for Krasner, and a neighbourhood
basis hypothesis for simple-root stability. Translating these presentations and
carrying out finite coefficient approximation are retained explicitly in the two
new valuation nodes, rather than hidden inside an anonymous hole. Their hypotheses
are strictly less than the whole comparison: relative closedness needs only K
henselian, and root approximation needs only L henselian and chooses no Ks.

The new sheaf-equivalence statement has no valuation or cohomology hypotheses or
conclusions. It isolates a general categorical argument from the restriction
isomorphism. Its proof in words includes replacing arbitrarily large separable
closures by compatible closures in the ground-field universe before applying the
same-universe stalk-action interfaces.

The assigned node does not realize a unit statement or proof step in
`dag/units/sk-p-dl-a1-perverse.json`; this delivery preserves that unit's route.
The newest blueprint and the local ILO PDF (printed page 374, PDF page 380) were read.
The existing rank-one complete-field result
`lem-trf-dense-subfield-separable-descent` does not cover arbitrary-rank henselian
valuations and cannot replace either valuation step.

## New nodes

`lem-per-dense-henselian-relative-separable-closed` is the original first Krasner
step: a dense henselian subfield contains each element separable over it. It has
no Galois-closure choices or cohomology assertion and does not require L henselian.
The case of an element already in K is immediate, covering the empty-conjugate case.

`lem-per-dense-henselian-simple-root-approximation` is the original coefficient
perturbation step: a in Ls belongs to L(b) for a simple root b of a monic K-polynomial.
The proof assembles finite Galois envelopes, valuation prolongation, simple-root
stability, finite product density, and Krasner. It does not assert separability
over K, membership in Ks, or injectivity of restriction: those are proved in the
assigned module. If a lies in L, g=X and b=0 supply the assertion directly.

`lem-per-galois-restriction-etale-equivalence` is the general field-theoretic
criterion that a restriction-compatible topological Galois isomorphism makes the
existing abelian inverse image an equivalence. Its proof uses the existing
normalized abelian stalk equivalences and field-pullback/action comparison, and
restriction along the inverse topological group isomorphism. It contains no
cohomology conclusion, and applies to all abelian sheaves.

All three nodes inherit the chapter and unit and the blueprint ancestry of the
assigned node. Semantic search, Loogle, and Mathlib grep were run and recorded for
each, as was LeanSearch. Blueprint searches found no matching blueprint statement.
No change record is needed: existing statements, definitions, attributes, and
public imports are unchanged, and all additional statements live in new modules.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
