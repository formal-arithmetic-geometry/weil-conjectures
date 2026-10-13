## What changed

Proved `AlgebraicGeometry.singleComplexOpen_pullback_cube` in
`Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCube`, with its statement and both public
imports unchanged. The private helpers extend the pinned composition comparison by equality
transport, derive its three-arrow identity, prove a commuting cube for ordinary derived
pullbacks by six applications of that identity, and identify the existing square definitions
with these comparisons. Naturality and inverse cancellation transfer that calculation to the
open-restriction functors. The existing node's proof now records these steps.

All helpers are proved. The only private definitions compose existing pinned isomorphisms;
they select no new witness and contain no proof holes. No definition or public interface was
changed. A local heartbeat budget applies only to the main theorem's proof elaboration.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.singleComplexOpen_pullback_cube`
(node `lem-pc-t2-open-pullback-cube`). No `sorry` remains in this module and none was added.
This is a proof from the existing composition theorem and constructed comparisons, not a
decomposition into new holed statements. Existing holes in imported theory remain outside
this delivery's scope.

## No longer needed

None. Both public imports provide definitions occurring in the unchanged statement. All three
existing proof dependencies are used: `lem-pc-ringed-spaces-derived-pullback-composition`,
`def-pc-t2-open-pullback-square-iso`, and `def-pc-t2-open-square-comparison`.
No new import, module, or node was needed. In particular, the counit compatibility theorem in
the definition module is not used by this proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The node's plan was sufficient: its associativity calculation
is now Lean code. The calculation uses six triple paths to a common total morphism rather
than the four triples listed in the earlier docstring. The unit's realized statement and
steps are empty; no prescribed unit route was bypassed.

The source check read Stacks Tags 0D5S and 0DJ9 on their official pages; the cited TeX files
are absent from this clone. The proof uses the existing declared associativity refinement of
0D5S and does not infer a new geometric claim from the abbreviated source proof. Search used
LeanFinder for cube coherence, Loogle for functor composition, and the launcher's grep search
plus local `rg`. The existing ordinary module-pullback and source-open unit calculations
provided useful patterns but are not imported.

The first compile could not find three newly landed dependency artifacts. The next build
refresh supplied them, and ordinary compilation resumed without replacing dependencies or
changing the launcher.

## Second reading by E2

1. **Interface unchanged: pass.** Read the complete delivered module and its diff against
   the repository. Extracted `singleComplexOpen_pullback_cube` through its `:= by` and
   compared the signatures byte for byte: identical. Its derived-category instances,
   four scheme arrows, outer equation `h`, opens and containment `hV'`, restriction
   arrow `j`, equations `hj` and `h₀`, object `M`, and both composite conclusions are
   unchanged. Both public imports are unchanged; the additions are private helpers and
   a local elaboration budget. No existing definition or visibility changed and no
   change record is required.
2. **Proof: pass.** The delivered module compiled through `lcompile.py` without errors
   or warnings (47.2 seconds). Read every helper and the main calculation. The
   associativity clause is extracted from the same nested choice that defines
   `singleComplexOpenPinnedComposition`; no independently selected comparison family
   is substituted. `compositionOfEq` and `pullbackSquare` only compose this existing
   data with equality isomorphisms and inverses, with no new existence witness.
   All six three-arrow equations have the correctly oriented commuting-face equations
   and common composite `j ≫ (iU ≫ f)`. Postcomposition cancellation is by an
   isomorphism. The final proof cancels the comparisons on U and V', uses naturality
   at the inverse comparison on V and at `q.app M`, and applies the ordinary cube
   with common outer factors. A text scan found no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern`; all lines meet the 100-character convention.
3. **Split statements: pass, none.** No split-off statement or new node was added.
   The private auxiliary theorems are all proved; the ordinary cube helper is a real
   six-associativity calculation, not a renamed holed assertion. The argument uses
   no nonempty, boundedness, cartesianness, or flatness assumption: identity arrows,
   empty opens and zero objects require exactly the same cancellation identities.
4. **Route and pruning: pass.** Read the pinned composition, square comparison,
   open square construction, composition existence/coherence interface, and
   `dag/units/sk-thm-picard-semicon.json`. Both public imports supply definitions in
   the unchanged statement (`singleComplexOpenPullbackSquareIso` and
   `singleComplexOpenSquareComparison`), so neither is a proof-only import.
   The old three `proof_deps` are all still used and `## No longer needed` is complete.
   The unit has `realized.statement = []` and `realized.steps = [[]]`; no realized
   unit route is bypassed. Independent searches used Loogle for `Functor.map_comp_assoc`,
   LeanFinder for pasting natural isomorphisms of coherent contravariant functors,
   launcher grep for whiskering and `pullHom_pullHom`, and local `rg` over the
   neighboring modules. They found generic naturality/whiskering tools and
   differently shaped coefficient pasting, not a theorem that closes this cube
   directly with the existing pinned family. A pseudofunctor packaging would add
   infrastructure to this direct component proof.
5. **DAG and source: pass.** The only changed node fields are `proof`, `proof_deps`,
   and `proof_origin`. The union of the three steps' `uses` equals `proof_deps`.
   Step 1 matches `compositionOfEq_assoc`; step 2 matches the six paths in
   `pullbackSquare_cube`; step 3 matches `squareComparison_eq`, `openSquare_app`,
   and the naturality/cancellation in the public theorem. Read the official
   [Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S) and
   [Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9). The former gives derived
   pullback composition, and the latter motivates restriction locality. Neither
   prints this cube equation: the proof correctly uses the library's existing
   explicit associativity refinement, with no new geometric claim or extra
   hypothesis imported from the base-change theorem.

Second-reading changes: added this independent review and search evidence to the
report. No Lean or DAG repair was needed; kept the working proof unchanged.

Axiom verification: appended `#print axioms` for the public theorem and all six
private declarations to `scratchpad/AxiomReview.lean`, then compiled that scratch
copy through `lcompile.py` (49.5 seconds, no warnings). Every declaration depends
only on `propext`, `Classical.choice`, and `Quot.sound`; none uses `sorryAx`.
