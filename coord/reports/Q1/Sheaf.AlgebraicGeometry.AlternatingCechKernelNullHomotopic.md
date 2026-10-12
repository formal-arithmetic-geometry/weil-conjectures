## What changed

Replaced the sorry of `AlgebraicGeometry.Scheme.alternatingCechKernelNullHomotopic`
with a compiling proof, preserving its signature and its existing public imports.
Added two proof-only imports for the separate sorting identities. The proof adds
canonical null homotopies of two explicit degree-lowering families, cancels their
stable-sorting terms, proves directly that the increasing-coordinate hypothesis
annihilates the signed projection, and precomposes the combined homotopy with f.

Added `AlternatingCechSortingOperators`, containing real finite-sum constructions
of stable sorting, alternating projection, and both contraction families. There is
no data chosen from a sorry'd theorem and no sorry in any definition. Stable sorting
and partial sorting use finite permutation filters; the repeat operator uses the
first adjacent equality. The definitions' additivity and zero laws are proved.

Added `AlternatingCechFirstSortingIdentity` and
`AlternatingCechSecondSortingIdentity`, each stating one of the two separate
identities of Stacks 01FM with a complete proof in words. The first contracts
identity minus stable sorting; the second contracts stable sorting minus increasing
projection. Neither mentions f or its vanishing hypothesis. Both concern concrete
operators, not existentially selected witnesses.

Validation: all four modules compile locally through lcompile.py. The two formal
tuple-coefficient identities were checked exhaustively over a three-element ordered
alphabet through degree 4, including repeated tuples. Degree zero has no incoming
component and the second operator is zero; empty I has no tuples and zero cochain
groups. The definitions and identities require no covering hypothesis. These finite
checks verify signs and boundary cases, not the general combinatorial proofs.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.alternatingCechKernelNullHomotopic`
(node `lem-pc-alternating-cech-kernel-null-homotopic`). Its proof has no sorry.

Added and left as whole-proof sorries:

- `AlgebraicGeometry.Scheme.cechFirstSortingIdentity`
  (`lem-pc-alternating-cech-first-sorting-identity`).
- `AlgebraicGeometry.Scheme.cechSecondSortingIdentity`
  (`lem-pc-alternating-cech-second-sorting-identity`).

This is a decomposition: one upper hole closed, two lower holes added, net -1.
All operator data and the combination of the two identities are implemented in Lean.
The general cancellation proofs for the two explicit operators remain.

## No longer needed

None of the item's existing imports, nodes, or modules is pruned. Its sole previous
proof dependency, `def-weil-pbc-site-cech-complex`, remains necessary. No section or
restriction-homotopy theorem is imported, so the proof avoids an import cycle.
The new operator module needs no Homotopy import; the identity modules import it
publicly because their statements mention nullHomotopicMap'.

## Where the brief, the DAG or earlier work was wrong

The original node placed both long combinatorial cancellations in a single step
using only the Čech-complex definition. Those identities had no separate Lean
statements. They are now separate items, with explicit operators and no change to
the mathematics or the unit's route. Searches found only generic homotopy and
simplicial normalization tools, not these ordered Čech identities. LeanSearch returned
Internal Server Error; the attempted searches are recorded in searches.jsonl and in
the new nodes. No statement was disputed or changed, and no adaptation is required.

## New nodes

`def-pc-alternating-cech-sorting-operators`: the concrete finite-sum operators and
adjacent-degree families, in `Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators`.
This module has no sorry.

`lem-pc-alternating-cech-first-sorting-identity`: the first contraction identity,
in `Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingIdentity`, equation the project server.

`lem-pc-alternating-cech-second-sorting-identity`: the repeated-tuple identity pulled
back by stable sorting, in `Sheaf.AlgebraicGeometry.AlternatingCechSecondSortingIdentity`,
equation the project server. Its proof plan uses the first identity to show κ commutes with d.

All new nodes inherit `sec-picard-framework` and `sk-thm-picard-pn`; the existing node's
proof, proof_deps, and proof_origin now describe the Lean argument. No change record
is needed: all existing signatures, definitions, and public visibility are preserved.

## Second reading by Q1

1. Compared the existing item module with the repository version using diff.
   Its sole existing theorem signature, hypotheses, conclusion, docstring, and
   three public imports are byte for byte unchanged. Only its proof and two
   proof-only imports differ. All three additional modules are new; there are
   no forced adaptations or statement changes. Verdict: pass.
2. Compiled all four modules in dependency order through lcompile.py, with no
   errors or warnings. Text inspection finds exactly the two reported whole-proof
   theorem sorries, no prohibited declaration forms, and no sorry in data.
   A scratch-copy #print axioms check of the target, both identities, all four
   homomorphisms, and both families found only propext, Classical.choice and
   Quot.sound, with sorryAx additionally on the two identities and the target.
   The concrete operators and families have no sorryAx. Verdict: valid reduction,
   with the two explicitly reported remaining holes; not an axiom-free proof.
3. Read both identity statements and their complete cancellation arguments,
   and compared the operators with Stacks 01FM equations the project server and the project server
   (https://stacks.math.columbia.edu/tag/01FM). Enumerated the permutation
   filters literally in an independent coefficient checker: 988 identities pass
   for alphabet sizes 0 through 4 and degrees 0 through 3. This covers degree
   zero, empty indexing, equal entries, and noninjective unsorted tuples.
   Universal properties identify the restriction transports in paired terms.
   Neither identity assumes f or its increasing-coordinate vanishing condition;
   each is a separate, strictly smaller operator identity used by the actual
   addition-and-precomposition proof. Repeated searches with LeanFinder
   (degenerate subcomplex/least adjacent duplicate/permutation prism), Loogle
   (Homotopy.nullHomotopicMap), and rg (prism/stable sort/semi-ordered/duplicate
   homotopy) found generic homotopy and simplicial tools, not these identities.
   The imported SiteCechComplex and upstream ordered Cech code likewise contain
   no ready proof. Neither cancellation identity can be closed in a few minutes.
   Verdict: true sourced decomposition, with no tautological restatement.
4. Read the target proof from its use of the two identities down to the explicit
   operators. Mathlib already supplies construction, addition and precomposition
   of null homotopies; the proof uses these directly. All imports serve signatures
   or the proof. The original proof dependency def-weil-pbc-site-cech-complex
   remains needed, so No longer needed is complete and pruning is none.
   sk-thm-picard-pn's statement, step and realized record remain unchanged (the
   existing realized lists are empty); the ordered-Cech reduction inside that
   step is preserved. Verdict: pass, no departure from the unit route.
5. Checked all four node records against their Lean statements and the proof.
   The target's dependencies are precisely the two identities, their concrete
   operators and SiteCechComplex. The second identity's documented proof uses
   the first identity for compatibility of stable sorting with d. The new nodes
   have source, searches, creation, blueprint, chapter, unit and Lean records.
   The operator node records the signature beginning with def, matching the
   delivery checker's convention of omitting the noncomputable modifier.
   Verdict: pass.

Changes made in this reading: removed the private cech_ite_add theorem and used
Mathlib's ite_add_zero in the four additivity proofs instead. This repairs the
rule forbidding private helpers in public definition bodies without changing
any operator data, statement or definition signature. Added this review. No holes were closed
or added by the second reading: the delivery remains one hole closed and two
split off, a decomposition with net -1, and no pruning.
