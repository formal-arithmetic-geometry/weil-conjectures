## What changed
Completed `AlgebraicGeometry.integralClosure_finite_fibre_choose_g` directly in
`Sheaf.AlgebraicGeometry.IntegralClosureFiniteFibreChooseG`, with the existing signature
and public imports unchanged. Added the proof-only import
`Mathlib.AlgebraicGeometry.Morphisms.IsIso`, which also exposes the affine basic-open
comparison used in the proof. No definitions or other existing declarations changed.

The principal-open choice uses the surjective quotient/product map q and K = ker(fst ∘ q).
The closed complement of U has vanishing ideal J. The prime correspondence shows V(K) ⊆ U,
so J ⊔ K = ⊤. Write j + k = 1 and choose q(g₀) = (1,0); then g = g₀j has the required image
and D(g) ⊆ U. Restrict the given isomorphism further to D(g), use
`SpecMapRestrictBasicOpenIso`, and conclude with `isIso_SpecMap_iff`.

## Proved and sorry left
Proved `AlgebraicGeometry.integralClosure_finite_fibre_choose_g`, the sole theorem of the
original module. No sorry remains, and no new theorem or split-off statement is delivered.
The axiom audit and local/server compilation results are recorded in the second reading.

## No longer needed
Removed the first worker's proposed modules and imports
`Sheaf.AlgebraicGeometry.IntegralClosureFiniteFibreChooseGExists` and
`Sheaf.AlgebraicGeometry.IntegralClosureFiniteFibreChooseGBijective`, and their two new nodes:
`lem-weil-pbc-integral-closure-finite-fibre-choose-g-exists` and
`lem-weil-pbc-integral-closure-finite-fibre-choose-g-bijective`.
Neither had been landed; both arguments are now proved inline. Removed the redundant
proof import `Mathlib.AlgebraicGeometry.AffineScheme` added during the second reading;
`Morphisms.IsIso` supplies it transitively.

Pruned these old proof-dependency edges, whose ingredients are supplied directly by Mathlib:
- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`: use `zeroLocus_sup` and
  `zeroLocus_empty_iff_eq_top` for the unit-ideal step.
- `lem-weil-pbc-morphism-into-affine-scheme`: use the restriction Arrow isomorphisms.
- `lem-weil-pbc-affine-ideals-closed-subscheme`: use `SpecMapRestrictBasicOpenIso` and
  `isIso_SpecMap_iff` for the localization conclusion.
These are removed edges of this node, not claims that the nodes are globally unreachable.
The spectrum and away-localization definition nodes remain in `proof_deps`.

## Where the brief, the DAG or earlier work was wrong
The first worker's split was mathematically valid, but its new nodes had placeholder
statements and proof steps, empty search records, non-verbatim Lean statements, and
incorrect blueprint tags in the theorem docstrings. The docstrings also lacked complete
natural-language proofs. The target node was not updated to the proposed reduction, and
the target proof had two long-line warnings. These deficiencies are resolved by proving
both arguments inline, deleting the proposed split, and updating the existing node.

The full proof needs no new open geometric or localization statement: Mathlib's
`morphismRestrictRestrict`, `SpecMapRestrictBasicOpenIso`, and `isIso_SpecMap_iff` supply
the final comparison. The prescribed quotient lift is a short ideal-comaximality argument.

## Second reading by T2
1. Compared the delivered module with the repository using diff and an exact signature
   comparison. Verdict: the existing theorem signature is byte-for-byte identical; its
   docstring and all existing public imports are unchanged. No definitions changed, no
   additional declaration is delivered, and no change record is needed.
2. Read the proof and compiled the final module through lcompile.py. Verdict: it compiles
   without warnings or errors and contains no sorry, axiom, unsafe, opaque, implemented_by,
   extern, or skipped kernel checking. A scratch copy with `#print axioms` was used to
   verify the theorem's axioms; the result is recorded below.
3. Checked the proposed split statements as mathematical consequences: the first is the
   lift/open construction and the second the localization consequence. Both are strict
   parts, rather than restatements. Tested the degenerate cases conceptually: C₁′ = 0
   makes the first component empty (g = 0 is available); C₂′ = 0 gives the whole closed
   fibre; U = ⊤ allows any prescribed lift; U = ∅ forces that first component empty and
   D(g) empty, making both away localizations zero rings. No nontriviality assumptions
   entered the proof. Searched with fresh LeanFinder queries for the two arguments, Loogle
   for restriction/isomorphism results, and rg across Mathlib and both library roots.
   Verdict: the ingredients are already in Mathlib and both proposed statements can be
   closed inline; no split-off statement or new node remains to audit.
4. Read the proof top downward and verified the source argument in the local Stacks copy
   `/home/ubuntu/c1-stacks-review/more-algebra.tex`, proof of `lemma-helper-finite-type`
   (Tag 09XH). The algebraic construction follows the existing node's route; the final
   restriction/localization comparison is packaged by Mathlib. Reviewed the imported
   modules and removed the redundant added AffineScheme import. Verdict: the existing
   `sk-thm-p1` unit route and its `realized` entries are unchanged; this auxiliary node
   is not itself one of those realized entries. All old unused proof-dependency edges
   are listed above. Existing public imports still provide signature vocabulary.
5. Compared the node with the Lean proof. Verdict: its statement and Lean statement
   remain unchanged; proof, proof_deps, and proof_origin describe the actual completed
   proof, including the quotient-kernel construction and Mathlib Arrow comparison.
   No new nodes remain.

Second reading changes: proved both split arguments and inlined them into the original
theorem; removed both proposed split modules/nodes; repaired proof metadata and the report;
added one proof-only Mathlib import; eliminated all compilation warnings.

Axiom audit: `#print axioms AlgebraicGeometry.integralClosure_finite_fibre_choose_g`
reports exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
Final local compilation passed without warnings or errors (4.9 seconds).
The deliver3.py dry run passed local compilation, the automated axiom probe, server
compilation, and preflight. It printed `OK (dry run)` with review class
`CODEX: changes a node file`; the existing node's proof metadata is the only DAG change.
