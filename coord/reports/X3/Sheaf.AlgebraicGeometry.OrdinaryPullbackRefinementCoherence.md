## What changed

Proved `AlgebraicGeometry.Scheme.Modules.ordinary_pullback_refinement_coherence`
in `Sheaf.AlgebraicGeometry.OrdinaryPullbackRefinementCoherence`, preserving its
entire signature, visibility, docstring, and existing public import. Added two
proved private helpers: `refinement_comp_assoc` evaluates Mathlib's
`pseudofunctor_associativity` after identifying composite maps;
`refinement_comp_square` combines two such identities by cancellation. The main
proof substitutes all five specified isomorphisms, normalizes the refinement to
A, and then compares the two paths to X by two further associativity identities.
Updated the existing node's proof and proof_origin to record these calculations.
The unit statement and its proof route are unchanged.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.Modules.ordinary_pullback_refinement_coherence`
(node `lem-pc-ordinary-pullback-refinement-coherence`).
Both private helpers are proved. No holes were added or split off; no `sorry`
remains in the delivered module. Single-file lcompile compilation passed cleanly.
The delivery dry run checks the axioms of every declaration as well.

## No longer needed

None. No imports were added or removed, and no DAG node or module was bypassed.
The sole import remains `Mathlib.AlgebraicGeometry.Modules.Sheaf`, needed by both
the statement and proof. In particular no tensor-pullback module or adjunction
comparison is needed for this ordinary-pullback calculation, as the original
node's plan already specifies. The recorded definition dependencies remain as
the source concepts used by the statement and proof; the Lean construction is
Mathlib's ordinary pullback.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was necessary. The existing coherence
plan can be completed from the already-proved Mathlib associativity identity.
The private helpers retain arbitrary schemes and modules, with no nonemptiness,
open immersion, nonzero-module, or invertibility assumption on scheme maps.
Equality substitution in the associativity helper handles proof transports;
identity refinements and zero modules require no separate cases.

## Second reading by X3

1. Compared the delivered Lean module with the repository version. The theorem
   signature, visibility, docstring, and public import are byte-for-byte
   unchanged; only the proof and two private helpers were added.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or
   warnings. The file contains no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern`, or `debug.skipKernelTC`.
3. Checked the two private helper identities and the main calculation against
   the existing Mathlib `pseudofunctor_associativity` and `pullbackCongr`
   declarations. No split-off statements or new nodes were added, and the
   existing node records exactly the proof steps and dependencies used.
4. The proof follows the unit route: it expands the five supplied canonical
   isomorphisms, proves the refinement square, then applies the two
   associativity identities. No shorter unused import or dependency was found;
   no imports or nodes can be pruned.
5. The unit statement and realized route are preserved, and the theorem proves
   the node statement without extra hypotheses or weakened conclusions.

Changed only the proof record and proof origin in the existing node to describe
these calculations, and added the two private helpers and the complete main
proof to the module. No holes were added.
