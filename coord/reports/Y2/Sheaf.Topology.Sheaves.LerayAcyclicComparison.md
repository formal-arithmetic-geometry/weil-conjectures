## What changed

Proved `TopCat.Sheaf.exists_lerayEdge_isIso_of_acyclic` in
`lean/Sheaf/Topology/Sheaves/LerayAcyclicComparison.lean`, with its signature unchanged.
Added the proof-only import `Sheaf.Topology.TopologicalLeraySpectralSequence`.
Six proved private helpers implement the existing DAG's row-zero argument: preservation
of the cycles kernel and homology cokernel, propagation of zero terms through pages,
invertibility of bottom transitions, and invertibility of the filtration inclusion.
The existing node's two proof steps now describe the actual Lean proof; its proof
dependencies and proof origin remain unchanged.

The proof extracts the canonical map and natural edge from the existing spectral-sequence
theorem, transports the cohomology-functor equalities, and reuses its cocycle formula.
At each acyclic sheaf, evaluation preserves kernels and cokernels. The proof propagates
positive-row vanishing through all pages, proves every bottom transition and iterate
invertible, proves all lower graded pieces vanish, and inductively proves the final
filtration inclusion invertible. The displayed factorization then proves the same edge
invertible. This is a complete Lean proof of degeneration, not an additional assumed
comparison theorem.

Source read: Stacks Project Tags 01F2 and 01F4(1), online at
https://stacks.math.columbia.edu/tag/01F2 and
https://stacks.math.columbia.edu/tag/01F4. The local literature checkout contains only
citation lists, so the source pages were read online. Searches: LeanFinder for the Leray
acyclic comparison, Loogle for `Functor.rightDerived`, the logged Mathlib grep for
spectral-sequence collapse and cycles/homology isomorphisms, and direct repository searches.
LeanFinder returned general injective-resolution lemmas rather than the desired comparison;
Loogle reported `Functor.rightDerived` as an unknown identifier; the Mathlib grep found
cycles and homology projection isomorphisms used in the proof.
No shorter existing comparison with the required naturality and cocycle formula was found.

## Proved and sorry left

Proved `TopCat.Sheaf.exists_lerayEdge_isIso_of_acyclic`
(node `lem-sc-leray-closed-pushforward-cohomology`): one original sorry removed.
No sorry remains in the item's module, and none is added elsewhere.
All six private helpers are proved. The existing dependency
`CategoryTheory.exists_topological_leray_spectralSequence`
(node `lem-sc-topological-leray-spectral-sequence`) remains an assumed, named stage-3
statement in its own module; its construction is the next work below this item.

Validation: local single-file compilation succeeded. The delivery dry run checks local
and server compilation and preflight. The zero-degree case uses the identity bottom
iterate and the top filtration step; the range of lower graded pieces is empty. Empty
spaces and the zero sheaf introduce no additional hypotheses. No target, definition,
or existing statement was changed.

## No longer needed

None. All three original public imports are needed by the unchanged statement. The only
added import is the proof dependency named by the original plan. No node or module of
that plan was bypassed. The unit `sk-thm-curveestimate` has no realized proof step inside
this comparison; its statement and route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The spectral-sequence theorem was not originally
imported by the item; adding its proof-only import made the planned data available.
The cohomology-presheaf functor evaluated at the terminal open has no directly inferred
`PreservesZeroMorphisms` instance. Its object is definitionally an `extFunctorObj`, whose
additivity supplies the required zero-object preservation; the proof uses that existing
functor explicitly. The recorded stable-page isomorphism is unnecessary because
`pageInfinity` is definitionally the page at p+q+2.

## Second reading by Y2

1. **Visible declarations — pass.** Compared the sole delivered Lean module with the
   repository using `diff`, and independently compared the exact text between the existing
   theorem's name and `:= by`. The signature and existing docstring are byte-for-byte
   unchanged. There are no changed definitions, additional hypotheses, weakened conclusions,
   or change records. The six added helpers are private, and the added spectral-sequence
   import is plain `import`, used only by the proof.
2. **Proof and trust — pass.** Independently compiled the module through `lcompile.py`:
   exit code zero, no warnings. Read all six helpers and the full final proof; no `sorry`,
   axiom, unsafe code, opaque declaration, external implementation, or hollow definition is
   introduced. A scratch copy prints the axioms of every helper and the final theorem;
   the helpers use only standard axioms, while the final theorem additionally uses `sorryAx`
   through the existing, still-open topological spectral-sequence dependency. This is a
   completed reduction to that dependency, not an unconditional axiom-free closure.
3. **Split statements — pass, none added.** There are no new public statements, split
   theorems, nodes, or new sorries to audit. The private mapped-kernel and mapped-cokernel
   lemmas prove precisely the evaluated versions required: vanishing before evaluation is
   not assumed. Checked the edge cases p=0 (identity bottom iterate, top filtration arrow,
   no lower graded pieces), r=2 (induction base), p<r (no incoming differential), and zero
   sheaves or empty spaces (no excluded cases or extra hypotheses).
4. **Route and pruning — pass.** Read Stacks Tags 01F2 (cohomology-lemma-Leray) and 01F4(1)
   (cohomology-lemma-apply-Leray), at https://stacks.math.columbia.edu/tag/01F2 and
   https://stacks.math.columbia.edu/tag/01F4. The abelian-sheaf specialization and row-zero
   collapse agree with these sources. Read the imported spectral-sequence theorem's actual
   witnesses and equations, `pageInfinity` (page p+q+2), and the cokernel definition of
   `gradedPiece`. The proof uses these statements, not an unstated construction from their
   proofs. Independently searched LeanFinder for exact evaluation of a bottom-row spectral
   sequence (eight general exactness/homology hits, no comparison theorem), and searched
   Mathlib, upstream, and both library roots for Leray and cycles/homology isomorphisms.
   Mathlib's `HomologicalComplex.isIso_iCycles` and `isIso_homologyπ` assume the original
   differential vanishes; they do not replace these evaluated helpers directly. The upstream
   pushforward comparison requires a dimension-shifting class and does not supply the
   required all-sheaf natural edge and cocycle formula; `siteLeray_degenerate` is still sorry
   and supplies only objectwise maps. No shorter matching proved theorem was found.
   The old `proof_deps` is the singleton spectral-sequence node, which is still used, so
   `No longer needed: None` is complete. The unit's `realized` contains only
   `thm-sc-proper-cohomology` as its statement and has no steps; its route is preserved.
5. **DAG agreement — pass.** Compared the node JSON with the repository: only the two
   proof-step texts change. Step 1 accurately records transport of HX/HZ and extraction of
   the canonical generator and cocycle equations. Step 2 records positive-row induction,
   the bottom transition equation, the iterate induction, and the cokernel/filtration
   induction actually present in Lean. Both cite the existing spectral-sequence node;
   `proof_deps` remains their union, and the document-based `proof_origin` remains correct.

Second reading changed only this report: added the independent review and explicit trust
qualification. No repair of the Lean proof or node was needed.
