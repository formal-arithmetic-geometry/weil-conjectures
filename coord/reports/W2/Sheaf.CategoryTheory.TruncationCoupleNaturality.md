## What changed

Proved `CategoryTheory.TruncationCouple.raw_naturality` in
`Sheaf.CategoryTheory.TruncationCoupleNaturality`, retaining every existing public
signature, definition and import. Added fully proved private helpers for localization
comparison, descent of the truncation inclusion, a canonical triangle morphism, and
transport through the bridge with the arithmetic equality morphisms.

The proof follows the existing node's four steps. The alpha and projection squares
come from `DerivedCategory.truncation_triangle`. The boundary square uses
`Functor.homologySequenceδ_naturality` on its image under the right derived functor.
The abutment square descends the natural truncation inclusion. The final square uses
the natural isomorphism obtained by composing the single-functor shift comparison,
right-derived-functor shift comparison and homology shift comparison. The descended
single-cohomology map is identified with the specified `homologyMap` using the
localization comparison and `homologyFunctorFactors`.

The proof works with arbitrary derived morphisms rather than chosen complex
representatives. No lower bound, invertibility of abutment maps or degree restriction
is introduced. The existing unit record has no realized steps affected by this work;
no unit route is bypassed. The DAG proof and dependencies already describe this
argument, so no node edit is necessary.

Validation: `lcompile.py` compiles the module without errors or warnings.
`#print axioms CategoryTheory.TruncationCouple.raw_naturality` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. Every line is at most 100 characters.

## Proved and sorry left

Closed: `CategoryTheory.TruncationCouple.raw_naturality`
(node `lem-pc-raw-truncation-couple-naturality`), the module's sole original hole.
All five required naturality equations are proved.

Remaining sorries in the item: none. Added sorries: none. Split-off statements: none.
The axiom check also confirms that this theorem does not depend on `sorryAx` through
its imports. This is a proof, not a decomposition.

## No longer needed

None. Both original imports remain necessary: `TruncationCouple` supplies the public
objects and maps, and `TruncationTriangle` supplies their derived naturality.
The proof uses the existing localization, derived-category, bridge and triangulated
right-derived-functor dependencies. No planned node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. Direct searches by Loogle, LeanFinder,
the project grep search and local `rg` found the needed localization and homology
sequence ingredients, rather than a ready-made raw-couple naturality theorem.
The existing `truncation_triangle` statement is sufficient for its three squares.

Some direct `simp` attempts on partially unfolded truncation and degree transports
failed because of semireducible dependent object types. Fully proved private transport
lemmas, proved by substitution of equal degrees and cancellation of bridge isomorphisms,
resolve this without changing definitions or compiler options. The original
Grothendieck hypothesis on B is explicitly retained in the proof to preserve the
existing declaration's full interface even though the naturality argument does not
otherwise need that hypothesis.


## Second reading by W2

1. **Interface unchanged — pass.** Read the full repository/sandbox diff and
   compared all four existing declarations with the declaration parser. The
   signatures of `abutmentMap`, `singleIso`, `homologyMap` and `raw_naturality`
   are unchanged; the three definition bodies, existing docstrings, imports,
   universe declarations and variable block are byte-identical. The theorem's
   signature was also compared byte for byte. The elaborated type retains both
   Grothendieck hypotheses. No change record or forced adaptation is needed.
2. **Kernel proof — pass.** Independently compiled the delivered module through
   `lcompile.py`, without errors or warnings. Compiled a scratch copy with
   `#print axioms CategoryTheory.TruncationCouple.raw_naturality`: precisely
   `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Scanned the
   complete delivered source for holes and forbidden declarations/options:
   none. New private definitions are explicit composites and a triangle
   morphism with proved squares; no arbitrary witness is chosen. The existing
   boundary choice is from `existsUnique_boundary`, which determines it uniquely.
3. **Split-off statements — pass, none.** No new public statements, nodes or
   holes were introduced. Checked the private localization comparison,
   descent, transport and bridge-cancellation arguments. Zero morphisms,
   zero objects, negative degrees, and truncation degrees below a complex's
   lower bound introduce no exceptional hypothesis; the equalities of total
   degrees hold for all integers. The boundary map has the required total
   degree increase of one and bidegree `(2,-1)`.
4. **Route and pruning — pass.** Read `truncation_triangle`, the couple maps and
   bridge construction. The proof uses its canonical triangle squares rather
   than choosing representatives of derived morphisms. Independent searches
   used the localization-transformation viewpoint: LeanFinder found
   `Localization.liftNatTrans`, `fac` and `liftNatTrans_app`, already used here;
   grep found `Functor.homologySequenceδ_naturality`, also already used.
   Loogle did not recognize the unqualified localization identifier. Local
   searches found no shorter existing raw-couple theorem. The identical
   localization helper in `TruncationTriangle` is private and unavailable to
   this module. Both imports are needed, with the triangle import correctly
   proof-only. Every old proof dependency is still used; `## No longer needed`
   is complete. The unit `sk-thm-picard-duality` has empty statement/step
   realization lists, and no unit route is bypassed.
5. **DAG agreement — pass.** Read node
   `lem-pc-raw-truncation-couple-naturality`, its four proof steps,
   `proof_deps` and `proof_origin`, and checked them against the proof. They
   describe localization descent, the three triangle squares, inclusion
   naturality and the composite shift comparison exactly as implemented.
   All five original dependencies remain relevant; no node edit is needed.

Second reading changed only this report by appending the independent checks.
No Lean repair was needed. One original hole is closed, none added; this is
one proved theorem, with zero split-off statements and no pruned modules.
