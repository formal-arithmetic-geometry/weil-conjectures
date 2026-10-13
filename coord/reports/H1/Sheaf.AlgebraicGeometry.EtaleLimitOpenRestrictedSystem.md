## What changed

Completed and checked the earlier sandbox reduction of
`AlgebraicGeometry.Etale.tailOpenRestrictedSystem_coherence`.
The original theorem now combines four clauses. Its composition clause follows
from a proved private square-coefficient composition lemma, using
`AlgebraicGeometry.Etale.squareUpperStarIso_paste_vert_hom` and naturality.
The cone transition clause applies that same lemma to a stage transition followed
by a cone projection, substitutes `hG`, and cancels the specified coefficient
isomorphisms. The cohomology-leg clause follows by expanding the specified inverse
isomorphism and functoriality. The identity clause specializes the new generic
`AlgebraicGeometry.Etale.openSquareCoefficient_diagram_identity` theorem.

Proof imports added: `WeilConjectures.SixFunctors.BaseChange.Pasting` and
`Sheaf.AlgebraicGeometry.EtaleOpenSquareDiagramIdentity`. Original definitions,
signatures, visibility and public imports are unchanged. The elaborator transparency option
is scoped to the three proofs that use it. The parent DAG proof
records the square-pasting route and the separate identity step.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.tailOpenRestrictedSystem_coherence`
(node `lem-weil-pbc-etale-limit-open-restricted-system`). Its composition,
cone-transition, and cohomology-leg clauses have complete Lean proofs.

Added one strictly smaller hole:
`AlgebraicGeometry.Etale.openSquareCoefficient_diagram_identity`
(node `lem-weil-pbc-open-square-diagram-identity`), in
`Sheaf.AlgebraicGeometry.EtaleOpenSquareDiagramIdentity`.
It asserts only the identity law, for arbitrary diagram restriction squares,
without a composition law, limit cone, cocone or cohomology assertion.
Its entire proof is `:= by sorry`; the docstring gives the unit calculation.
This delivery is a decomposition, with one hole closed and one added (net zero),
not a sorry-free proof. No other delivered declaration contains `sorry`.
The two private helpers in the parent are proved.

## No longer needed

No original imports are removed and no module is claimed pruned.
The old direct proof dependency `lem-weil-pbc-inverse-image-composition` is
removed from the parent's `proof_deps`: its role in composition is replaced by
`lem-weil-pbc-square-iso-pasting`, and its identity role is retained through
`lem-weil-pbc-open-square-diagram-identity`. It is not globally pruned and remains
a statement dependency. The other old dependency,
`lem-weil-pbc-etale-limit-open-cohomology-cocone`, remains directly used.
The inverse-image composition dependency is now used through the separate identity
step. Composition and cone-transition coherence use the existing proved
`lem-weil-pbc-square-iso-pasting` rather than a new associativity lemma.
No node realizing the unit's statement or one of its proof steps is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left a usable reduction but no successful delivery check.
I checked all delivered Lean and both node records. The first dry run found
a file-wide elaborator option from the earlier attempt; I scoped it to the
individual proofs and reran the delivery check.
Attempts to finish the generic identity law using proved left/right unit laws
showed that the pointwise square identity calculation compiles, but its diagram
specialization hits a kernel deterministic timeout (confirmed with a diagnostic
heartbeat bound), and the normal compilation exceeds 60 seconds. Substituting
only pointwise sheaf equalities, using an abstract categorical transport lemma,
and explicitly normalizing identity arrows did not resolve that problem.
These experiments remain in scratchpad files and are not part of the delivery.
The delivered parent uses explicit restricted sheaves and coefficient maps with
construction equalities and compiles within the prescribed limit. The remaining
identity theorem is isolated as a mathematical step, not a restatement of the
four-part parent theorem. No definition has been changed to evade compilation.

Repository search found the proved unit and square-pasting laws. Fresh Loogle
search for `"upperStarComp"` and Mathlib grep for the unit-law names returned no
indexed match; LeanFinder returned topological, module-sheaf and over-site
pullback lemmas, none an exact etale coefficient identity theorem. The previous
attempt's search log records the LeanSearch service error honestly as unavailable.
Sources for the remaining statement are the existing node's Tag 09YQ and Tag
03CB citations. Its unit calculation makes no nonempty, directedness, compactness,
limit or colimit assumption, so empty schemes, empty opens and zero sheaves are
covered without an extra hypothesis.

## New nodes

`lem-weil-pbc-open-square-diagram-identity`, module
`Sheaf.AlgebraicGeometry.EtaleOpenSquareDiagramIdentity`, states the canonical
identity coefficient law across a commuting diagram of restriction squares.
Its sheaves are specified by construction equalities and its coefficient maps by
heterogeneous equalities to `openSquareCoefficient`. The full natural-language
proof identifies those data, substitutes the original identity coefficient,
uses the two inverse-image unit laws, and cancels the pulled-back original unit.
This is precisely the first part of the parent argument. There are no interface
change records and no forced adaptations.

## Second reading by H1

1. **Interfaces: pass.** Read both delivered modules in full and diffed the parent
   against the repository version. All eight existing declarations retain their
   signatures byte for byte; all seven constructions, their bodies, and the public
   import are unchanged. Only two private proved helpers, two plain proof imports,
   three declaration-scoped transparency settings, and the coherence proof are
   added. No target statement or definition changes, and no change record is needed.

2. **Proof and axioms: pass as a decomposition.** Compiled both modules in import
   order with `lcompile.py --all`: the identity statement took 2.8 seconds and the
   parent 32.1 seconds, with no errors or warnings. Also compiled scratch copies
   containing `#print axioms` for every delivered declaration, including both
   private helpers. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the
   constructions and helpers. The parent and the new identity theorem additionally
   use `sorryAx`, exactly as the one remaining identity hole requires. The sole
   textual `sorry` is the entire proof of the public named identity theorem; no
   forbidden declaration or hollow definition occurs. There is one old hole closed
   and one new hole added, net zero, not a complete proof of the import closure.

3. **Split statement: pass.** Checked the new node against every argument and the
   conclusion of `openSquareCoefficient_diagram_identity`. Both diagrams have only
   preorder assumptions; sigma is merely an object map. The square equations use
   the identity arrows; `hF'` and `hψ` specify the actual restricted sheaves and
   coefficients rather than permitting arbitrary witnesses. The docstring's
   calculation uses the proved `upperStarComp_id_left` and `_id_right`: after
   identifying the two scheme arrows with identities, the right unit factor
   cancels the pulled-back original unit, leaving the left unit. This needs neither
   composition coherence nor a limit cone. Empty J is vacuous; singleton diagrams,
   identity inclusions, empty schemes/opens, and zero sheaves all satisfy the same
   calculation without an extra assumption. Read Stacks Tags
   [09YQ](https://stacks.math.columbia.edu/tag/09YQ) and
   [03CB](https://stacks.math.columbia.edu/tag/03CB): they supply the coherent-system
   context and composition of inverse images, respectively; this identity law is
   the explicit unit calculation from those canonical adjoints, not the limit
   cohomology theorem itself. Fresh LeanFinder search for identity compatibility
   of inverse-image functors and a Mathlib grep for square identity/pullback unit
   laws found over-site and module-sheaf analogues, not this statement. Searched
   the current library and upstream sources as well: `squareUpperStarIso_id` is a
   related proved tool with different orientation, not the diagram assertion.
   The new hole is only the first of the four parent clauses, strictly smaller
   than the parent; the other three clauses are actually proved.

4. **Route and pruning: pass.** Read the square-pasting declaration and followed
   the private composition proof: take its component, cancel the mapped inverse,
   and use square naturality. The second parent clause specializes it with
   `hcomposition`. The third specializes it to a transition followed by a cone
   projection, substitutes `hG`, and cancels the specified isomorphisms. The fourth
   expands the cohomology leg and uses the proved inverse-isomorphism helper.
   Neither helper needs a new unproved associativity statement. Both new imports
   are used only in proofs and correctly remain plain imports; the existing public
   import supplies the constructions in the signatures. Read `sk-thm-p1.json` and
   its `realized` routes: this reduction is below the unit's level, and no realized
   statement or step is bypassed. No module/import is pruned. Clarified above the
   one old dependency removed from the parent's direct proof dependency list.

5. **DAG: pass.** Compared the four parent proof steps with the four Lean branches:
   identity specialization, vertical square pasting, its cone specialization, and
   the cohomology coefficient calculation agree. The new identity node has the
   matching verbatim Lean signature, source, complete proof text, chapter/unit,
   creation record, blueprint ancestry and logged searches. Its proof dependencies
   name inverse-image composition and the coefficient construction, and the
   parent's dependency union and `proof_origin` describe the actual reduction.
   The original statement fields are unchanged.

Changes in this second reading: corrected the report's direct-dependency accounting
and added this independent audit; no Lean or node repair was needed. Recompiled the
earlier pointwise-to-diagram proof experiment in scratch: it still exceeds the
60-second limit. Kept that experiment out of the delivery and retained the named,
documented identity hole. No additional hole was introduced during this reading.
