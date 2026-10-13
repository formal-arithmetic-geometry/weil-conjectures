## What changed

Proved `AlgebraicGeometry.rectangle_qcoh_ordinary_compatibility` in
`Sheaf.AlgebraicGeometry.RectangleQCohOrdinaryCompatibility`, keeping its statement,
visibility, docstring, and imports unchanged. The proof follows the existing node's route.
Updated the node's proof steps and proof origin to describe the implemented transport
and cancellation helpers; its proof-dependency list is unchanged.

Two proved private helpers implement the transport calculation. First,
`cancel_pasting_comparison` moves an inverse conjugate comparison through a functor map
by naturality and cancels the comparison isomorphisms. Then `upper_pasting_transport`
eliminates the two projection equalities and applies that calculation to the upper
pasting identity. It takes the comparison and adjunction families explicitly, avoiding
repeated expansion of the large chosen families during checking.

The main proof applies the faithful QCoh inclusion, substitutes the supplied component
formulas, and applies the transported upper pasting identity. The existing
`schemeDerivedBaseChange_horizontal_pasting` identifies the remaining rectangle
component with the successive base-change components. Precomposition with the inverse
bottom comparison cancels its hom component and finishes the equality.

Searches through the prescribed `msearch.py` tools found no exact Mathlib result:
LeanFinder returned general base-change and derivability results, Loogle returned
`conjugateIsoEquiv` and its component formulas, and grep returned no Mathlib match.
Local source search identified the two existing pasting laws used here.

The Stacks source places 0ATM and 08HY were read. Both pasting dependencies' statements and the
QCoh restriction definitions were inspected. The proof needs no invertibility of
ordinary base change and no extra hypothesis on empty schemes, identity arrows, or
zero objects. No statement or definition was changed; no other module was adapted.

The complete proof compiled after publication of the horizontal-pasting module. Lean
warned about the original named quantified proof binders `hL` and `hs`, whose names
are unused in the statement's conclusion. They remain verbatim; a declaration-scoped
`linter.unusedVariables` setting suppresses those signature warnings without affecting
other declarations or elaboration. The required `deliver3.py --no-push` dry run printed OK: clean compilation, the
axiom probe, and preflight passed, except for the expected second reading that the
independent reader supplies. Nothing was pushed. The project parser reports no changed signatures and no remaining
or newly added holes.

## Proved and sorry left

Closed the sole hole, `AlgebraicGeometry.rectangle_qcoh_ordinary_compatibility`
(node `lem-sc-rectangle-qcoh-ordinary-compatibility`). No holes were added, and no
`sorry` remains in the delivered module. Both private helpers are fully proved.
This is a proof from existing declarations, not a decomposition into new holes.

## No longer needed

None. The public QCoh import supplies the statement's definitions; both proof imports
are used. The existing proof dependencies and the unit's route remain needed.

## Where the brief, the DAG or earlier work was wrong

The horizontal-pasting source was already proved but initially absent from the local
published build. Work continued on the available upper-pasting calculation while awaiting the
normal build refresh; the published dependency subsequently arrived and full validation passed. No duplicate statement was introduced.

The existing mathematical proof plan was correct. Private helpers implement its
elementary equality transport and cancellation steps; no new node is needed.

## Second reading by G4

1. Public interface: PASS. Read the complete repository/sandbox diff. The existing
   theorem signature is byte-for-byte identical, as checked separately by extracting
   the text from its declaration through the proof delimiter. Its visibility,
   docstring, imports, and existing definitions are unchanged. The only Lean additions
   outside the proof are two proved private helpers and a declaration-scoped linter
   setting. No change record or forced adaptation is needed.

2. Proof and axioms: PASS. Independently compiled the delivered module with
   `lcompile.py`: exit 0, no warnings, 52.0 seconds. Compiled a scratch copy with
   `#print axioms` for the main theorem and both private helpers: exit 0, 51.2 seconds.
   Both helpers use only `propext`, `Classical.choice`, and `Quot.sound`. The main
   theorem uses those three and inherited `sorryAx` from existing open dependencies;
   it is not a claim that its entire dependency closure is closed. The delivered
   module contains no `sorry`, prohibited declaration, hollow definition, or new
   arbitrary witness chosen from an unproved existence theorem. Read the faithful
   inclusion reduction, both component substitutions, equality elimination in
   `upper_pasting_transport`, naturality/cancellation in
   `cancel_pasting_comparison`, and both final pasting applications.

3. Split statements: PASS (none). No statement was split off and no hole was added.
   The private helpers are elementary, fully proved intermediate calculations,
   not renamed restatements of the item. With identity comparisons their calculation
   reduces to identity cancellation; empty schemes and zero objects impose no
   additional conditions because only categorical identities are used.

4. Route and pruning: PASS. Read both imported pasting statements and the QCoh
   restriction definitions. Checked the cited sources,
   [Tag 0ATM](https://stacks.math.columbia.edu/tag/0ATM) and
   [Tag 08HY](https://stacks.math.columbia.edu/tag/08HY), against the implemented ordinary
   pasting route. Independent local searches for rectangle compatibility and pasting,
   and launcher Mathlib searches for naturality and comparison cancellation, found
   the existing pasting laws and elementary naturality tools already used here;
   no shorter geometric result was identified. The public import supplies signature
   definitions; the two plain imports supply the two applied pasting theorems.
   Every old proof dependency remains used, so `## No longer needed` is complete.
   Read `dag/units/sk-thm-picard-duality.json`: its current `realized` record has empty
   statement/step lists, and this delivery neither changes it nor bypasses a unit
   step. The existing node-level route is retained.

5. DAG agreement: PASS. Compared the entire node JSON with the repository version.
   Only `proof` and `proof_origin` differ. The three steps describe precisely the
   faithful-inclusion reduction, transported upper pasting, and horizontal pasting
   followed by inverse comparison cancellation. Verified that the union of their
   `uses` is exactly the unchanged `proof_deps`; checked each dependency's recorded
   Lean module and declaration. No new nodes require additional fields.

Second-reading changes: appended this independent review and clarified the inherited
`sorryAx` limitation. No Lean or DAG repair was necessary. Holes closed: one,
`AlgebraicGeometry.rectangle_qcoh_ordinary_compatibility`; holes added: zero;
statements split off: zero; imports/modules pruned: none.
