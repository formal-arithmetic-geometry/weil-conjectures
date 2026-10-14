## What changed

Proved `AlgebraicGeometry.affineBaseChangeModelIsosCore` by a bottom-square construction and
propagation. The existing wrapper
`AlgebraicGeometry.exists_affineBaseChangeModelIsosOfSchemeComparisons` keeps its signature
and proof. Both signatures and all existing visibility are unchanged.

Added `Sheaf.AlgebraicGeometry.AffineSquareKFlatModelIso`, with the proved public theorem
`AlgebraicGeometry.nonempty_affineSquareKFlatModelIso`. This is an object comparison in one
commuting affine square, independent of the index diagram. Its private helpers explicitly
construct the module pushforward equivalence, localize it, and identify the inverse of any
supplied localized pushforward equivalence with derived pullback by left-derived uniqueness.
The public proof composes this identification with the existing natural affine K-flat formula
and the derived composition comparisons.

Added `Sheaf.AlgebraicGeometry.AffineModelComparisonOfBottomModels`, stating the remaining
propagation theorem. Its hypotheses are bottom-stage object identifications, the acyclic-tensor
criteria, and transition-compatible affine coordinates. It has no original Γ(Y)-models, no map
r, no initial equivalence e, and no first-projection equations. The main proof constructs its
bottom identifications using the proved square theorem, derives the acyclic-tensor criteria
from the native K-flat hypotheses, applies scalar-extension preservation, and supplies the
transition equations. No arbitrary data is defined by choosing from a mere existence theorem;
the only new definition is the explicit private module pushforward equivalence.

Replaced the direct proof import of `AffineDerivedPullbackTensorTilde` in the item with the two
new modules and the native K-flat criterion API. That affine comparison remains used by the
proved single-square module and by the remaining propagation argument.

Validation: all three sandbox modules compile cleanly in dependency order using lcompile.py.
The original and new statements were checked on identity arrows, zero complexes, zero rings,
empty spectra, non-flat ring maps, and arbitrary stage chain maps. Propagation uses the natural
comparison at the stage of a chain map; it does not assume that map descends to Γ(Y).

## Proved and sorry left

Closed the existing hole in `AlgebraicGeometry.affineBaseChangeModelIsosCore`
(node `lem-pc-affine-base-change-model-isos-core`). The public wrapper remains proved.
The initial dispatch copy had the hole directly in the wrapper; the read-only checkout
refreshed during this session to the separate core declaration, and this delivery preserves
that current interface rather than removing either declaration.

Also proved the new theorem `AlgebraicGeometry.nonempty_affineSquareKFlatModelIso`
(node `lem-pc-affine-square-kflat-model-iso`), and the private helpers
`AlgebraicGeometry.inverse_iso_pullback` and `AlgebraicGeometry.module_model_acyclic`.

One hole added, and the only sorry left in the delivery:
`AlgebraicGeometry.affineModelComparisonData_of_bottom_models`
(node `lem-pc-affine-model-comparison-of-bottom-models`). Its proof is exactly `:= by sorry`.
No sorry remains in the assigned module or in the single-square module.

Accounting: one existing hole closed, one lower hole added. This is a decomposition, with net
hole reduction zero, not a complete proof of the geometric propagation. The fully written
square proof and the acyclic-tensor conversion/scalar-extension calculation are actual proved
parts; the remaining theorem isolates propagation after those parts have been discharged.

## No longer needed

Removed the item's direct proof import
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`; it remains required transitively
by the proved square lemma and remains in the remaining propagation node's proof plan.
No module is claimed pruned from the targets' entire import closure.

The core's direct proof dependencies
`lem-pc-affine-derived-pullback-tensor-tilde`,
`lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-pc-perfect-hom-transport`, and `def-pc-complex-scalar-extension-hom`
are replaced by the square and propagation nodes. They remain needed below those nodes.
The core retains `def-pc-module-kflat-complex` and `lem-pc-kflat-extension-of-scalars`.
No unit statement or realized unit proof step is bypassed; the unit's realized lists are empty.

The independent limit first-projection equation `hgeom.2.1` is not needed by the new proof:
the bottom first-projection equation and the finite/limit transition equations suffice.
The existing signature still includes it unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing natural affine comparison gives existence of a natural isomorphism for each ring
map, but its public statement does not specify cross-ring-map composition coherence. Therefore
one cannot simply choose those isomorphisms independently and claim the two conjugated Hom
equations. The remaining propagation theorem explicitly owns that coherence obligation; its
proof plan pins comparisons by the derived counits and uses scalar-extension associativity.
The single-square theorem deliberately asserts no coherence between independently chosen squares.

LeanSearch was attempted and returned Internal Server Error. LeanFinder, Loogle, and local
source searches succeeded. Stacks Tags 08DW, 09RE, 0D5S and 06Y1 were read. No statement is
marked disputed, no target statement or definition is changed, and there are no forced
adaptations of modules held by other groups.

## New nodes

`lem-pc-affine-square-kflat-model-iso`: proved object comparison in one commuting affine
square. Its module is `Sheaf.AlgebraicGeometry.AffineSquareKFlatModelIso`; its proof uses
localization uniqueness, the tensor-pullback adjunction, the affine K-flat natural comparison,
and derived pullback composition. It is strictly smaller than the original theorem: one model,
one square, no diagram, no scalarExtensionHom equations.

`lem-pc-affine-model-comparison-of-bottom-models`: remaining propagation from two bottom-stage
models through compatible affine coordinates. Its module is
`Sheaf.AlgebraicGeometry.AffineModelComparisonOfBottomModels`. This is the diagram-coherence
part after construction of the bottom models, with a source and a full proof plan in its
node and docstring. The bottom identifications and acyclic-tensor hypotheses are proved in
the assigned module, rather than being restatements of its original Γ(Y)-model hypotheses.

No change record is required: existing statements, definitions, public imports and visibility
are unchanged. The two new public statements each have their own new node; their modules are
imported privately for the assigned proof.

## Second reading by U2

1. Compared the assigned module with the read-only repository using diff and the
   declaration parser. Both existing declaration statements are byte-for-byte
   unchanged, as are their visibility and docstrings. The wrapper proof is unchanged.
   There are no existing-definition changes, target changes, or forced adaptations.
   Verdict: pass.
2. Compiled all three modules in dependency order with lcompile.py; all succeeded
   without compiler warnings. Scratch copies with explicit `#print axioms` checked
   the square theorem, its two private helpers, the acyclic-tensor helper, the core,
   the wrapper, and the remaining propagation theorem. The square theorem and all
   private helpers use only propext, Classical.choice, and Quot.sound. The propagation
   theorem, core and wrapper additionally use sorryAx, as reported above. There is
   exactly one delivered sorry, in the named propagation theorem, and no forbidden
   declaration or hollow definition. Its conclusion affineModelComparisonData is
   Prop, not a data-valued construction; the proof consumes its proof directly and
   introduces no arbitrary chosen witness from this unfinished existence statement.
   Verdict: pass as a decomposition, not an axiom-clean completion of the core.
3. Read both new statements, their docstrings, their nodes, and the existing affine
   comparison and Hom-transport APIs. The square proof explicitly constructs exact
   transport and uses left-derived uniqueness; its public conclusion asserts only
   an object isomorphism. Propagation removes the initial models over Γ(Y), r, e,
   and all first-projection equations, taking already constructed bottom models
   instead. Thus it isolates the remaining coherence part and does not restate the
   assigned core. Checked identity transitions (including identity scalar extension),
   zero models/rings and empty spectra, non-flat scalar extension, arbitrary bottom
   identifications, and chain maps that do not descend to the bottom. No directedness
   or colimit assumption is needed for these constructions. The counit-pinned affine
   comparisons must be constructed coherently in the remaining proof; choosing
   arbitrary witnesses of the existing natural-isomorphism theorem is insufficient.
   This is explicitly the obligation retained by the docstring and report, not an
   assertion that the available bare existence API proves coherence automatically.
   New LeanFinder queries on localized inverse pushforward and K-flat scalar extension,
   a Loogle query, and local searches for bottom models, inverse transport, and
   leftDerivedUnique found component APIs but no replacement for the remaining
   propagation theorem. Verdict: pass; the remaining hole cannot be closed merely
   by composing the presently exposed natural-isomorphism existence statements.
4. Read the proof from the core down: it constructs the bottom square comparisons,
   converts native K-flatness to acyclic-tensor preservation, proves scalar-extension
   preservation using the existing API, then applies propagation. The new public
   imports supply statement types or instances; proof-only dependencies use plain
   imports. No unnecessary proof dependency was found. Compared the old proof_deps:
   all four replaced direct dependencies are listed under No longer needed and remain
   needed transitively. No whole-closure module is claimed pruned. Read the unit
   sk-thm-picard-semicon.json; its realized statement list and its sole realized step
   list are empty and unchanged. Verdict: pass.
5. Compared the core node: only proof, proof_deps and proof_origin differ from the
   repository. In all three delivered nodes, proof_deps is exactly the union of the
   proof steps' uses. Both new nodes carry their source, proof plan, searches,
   provenance, chapter/unit and Lean record, and their recorded Lean signatures
   match the modules verbatim. The square node describes the completed proof, and
   the propagation node describes the reported open coherence obligation.
   Verdict: pass.

Changes by the second reader: added this independent review and its compilation,
axiom, signature, dependency, edge-case and search evidence. No repair of Lean
proofs, signatures, definitions or nodes was necessary. Accounting remains one old
hole closed and one lower hole added; net reduction zero and no closure module pruned.
