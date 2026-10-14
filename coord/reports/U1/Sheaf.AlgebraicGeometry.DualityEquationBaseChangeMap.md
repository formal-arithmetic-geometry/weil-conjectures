## What changed

Reviewed `AlgebraicGeometry.dualityEquationBaseChangeMap` and its existing node
`def-sc-duality-equation-base-change-map`. The current repository baseline already
has the direct inverse-square mate construction. This delivery preserves its
signature and definition body byte for byte, clarifies the construction docstrings,
and expands the node's proof description. The naturality step explicitly records
`lem-pc-ringed-spaces-derived-pullback-composition`; the mate and conjugate nodes
remain dependencies. There is no new definition construction in this delivery.

The second reader replaced the sandbox's public `Adjunction.Restrict` import with
proof-only `Adjunction.Mates`, matching the current repository. Removed the obsolete
sandbox change record: its Old and New bodies were identical to the current baseline,
and its claim to retain a baseline public Restrict import was stale. No interface
or mathematical definition change remains, so no new change record is needed.

## Proved and sorry left

Holes closed: none (0 of 0 local holes in the baseline).
Holes added or split off: none.
Holes left in delivered Lean: none.

The definition remains an explicit mate of the inverse of the fixed ordinary
base-change transformation, using the supplied right-adjoint adjunctions.
A scratch copy with `#print axioms AlgebraicGeometry.dualityEquationBaseChangeMap`
compiled and reported exactly `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`.
The last is inherited from upstream named theorems; this is not a claim of a
sorry-free transitive closure. No arbitrary existence witness is selected here.

## No longer needed

No imports or nodes are pruned relative to the current repository baseline.
The sandbox's redundant public `Mathlib.CategoryTheory.Adjunction.Restrict` import
was corrected to the baseline's private `Mathlib.CategoryTheory.Adjunction.Mates`.
Every old proof dependency is retained; pullback-composition is additionally
recorded for the comparisons used in the naturality proof. No module is claimed
unreachable from the targets.

## Where the brief, the DAG or earlier work was wrong

The item is a queued definition repair, but its current repository version already
contains the intended repair and no local sorry. The first worker's report described
changes from an older baseline. Its public Restrict import would regress the newer
baseline, whose downstream callers import their proof tools explicitly.
Its updated node also omitted `def-weil-pbc-adjunction-mate` despite using mateEquiv.
Both faults are corrected without changing the existing construction.

The source equation is Stacks Tag 0AA6, equation the project server, used in Tag 0AA8.
The local literature file is unavailable on this machine; read the official pages:
https://stacks.math.columbia.edu/tag/0AA6 and
https://stacks.math.columbia.edu/tag/0AA8 .
No source error is claimed.

## Second reading by U1

1. Compared the sole delivered Lean module with the current repository using diff.
   The universe parameters, derived-category family, all six qcqs space instances,
   f, g, a, a', both restricted-direct-image adjunctions, componentwise hβ and K,
   and the resulting morphism type are unchanged byte for byte. The definition body
   is also unchanged. Only explanatory docstrings differ after correcting imports.
   No target, hypothesis, conclusion, visibility or exported definition changes.

2. Read the full body. β uses precisely the ordinary square's components. Its
   naturality proof transposes the test morphism, moves it through the two natural
   composition comparisons and equality transport, and applies counit naturality.
   Full faithfulness reflects hβ componentwise, pointwise invertibility gives an
   invertible natural transformation, and its inverse is uniquely determined.
   mateEquiv adjf adjf' has the required orientation and its component has the
   stated source and target. No local sorry, axiom, unsafe, opaque, implemented_by,
   extern or holed definition occurs. Local compilation and the scratch axiom check
   passed; only inherited sorryAx accompanies the three permitted axioms.

3. No statements were split off or added, so there are no new holes, edge cases,
   node obligations or duplicate-lemma searches to discharge. Read the existing
   generic secondMate_formula in QCohInverseBaseChangeMate and Mathlib's
   iterated_mateEquiv_conjugateEquiv and conjugateEquiv_comm. The proof first identifies
   the inverse conjugate, applies the inverse mate equivalence to the iterated-mates
   identity, and simplifies its component. This gives exactly the node's displayed
   unit/inverse-conjugate/counit composite for arbitrary auxiliary adjunctions.
   Its categorical hypotheses impose no nonempty-scheme or nonzero-object condition.
   No new arbitrary-witness construction or restatement is introduced.

4. The direct inverse-mate route already in the baseline is the short route; no
   unfinished auxiliary theorem is required. Preserved its minimal imports, each
   used by the statement or body. The old proof_deps are all retained, hence the
   pruning list is empty. Inspected dag/units/sk-thm-picard-duality.json: its realized
   statement and step lists are empty and unchanged. The item's blueprint.from route
   through proper-flat right-adjoint affine base change remains unchanged, and the
   Stacks displayed composite agrees by the generic mates calculation above.

5. Compared the node JSON with the repository. Only proof, proof_deps and their
   explanatory metadata change; the statement, stmt_deps, lean signature and unit
   remain unchanged. Restored the mate node to the final proof step and proof_deps;
   retained the existing Mathlib-based proof_origin, since the implementation uses
   generic mate calculus. The union of step uses equals proof_deps. The additional
   composition dependency records the c1/c2 comparisons used in β's naturality.

Second-reading changes: corrected the proof-tool import, restored the mate
proof dependency and Mathlib proof origin, removed the stale change record, and
rewrote the report against the actual current baseline. No correct proof was rewritten.

Validation: recompiled the corrected module and fresh unchanged repository copies
of FlatPrecomposePus, ProperFlatGlobalHomCompositeIso, QCohInverseBaseChangeMate and
ProperFlatOpenSquareMateIso together in an isolated compatibility sandbox. All five
compiled without warnings (9.8, 9.3, 29.5, 8.6 and 24.0 seconds respectively). The
first deliver3.py dry run passed: CODEX review class for node-file changes. An exact
text check confirms the declaration signature and body are identical to the baseline,
the union of step uses equals proof_deps, and no delivered Lean line exceeds 100 columns.
