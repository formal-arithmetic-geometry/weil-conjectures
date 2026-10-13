## What changed

Repair of reviewer X-4538c, head 4538c0311, return D. Replaced the entire sorry
in `AlgebraicGeometry.Scheme.Modules.exists_etaleTensorSectionsTransport` with
its complete proof, preserving its signature. The equivalence comes from the
component of `tensorSectionsComp` followed by `eqToIso` along `a.w`. Its forward
and inverse section maps are evaluated module morphisms; the inverse identities
and scalar equation are proved using the isomorphism laws and `Hom.app_smul`.

Repaired the proof-local section-equivalence data construction with the private
`sectionsEquiv` definition, whose data and inverse proofs are explicit. The
scalar calculation is proved for abstract module functors in `transportForFamily`.
The private, proved equality `restriction_eq` rewrites the actual restriction
map into this calculation. This avoids repeatedly reducing the concrete scalar
structures when the generic theorem is specialized. No public library definition,
existing signature, or target statement changes. No forced adaptation is required.
The definition/construction procedure is documented in
`coord/changes/etale-tensor-sections-equivalence-construction.md`.

The two helper modules remain mathematical factoring: the whole-scheme affine
sections comparison and the normalized transport of iterated pullback sections.
Both are proved, and neither leaves an obligation for another worker. As requested,
`scratchpad/UnsplitRepair.lean` combines both helper proofs and the original theorem
in a single file with no helper-module imports; it compiles within the unchanged
60-second limit (lcompile reported 15.8 seconds including any slot wait).
The delivered files compile separately in import order (8.4, 4.8 and 7.1 seconds,
also including any slot waits). The transport proof imports only its statement
module; no unused proof import remains.

Updated the transport node's `proof` and `proof_origin` to describe the complete
construction, abstract scalar calculation and explicit restriction-map rewrite.
Its statement, Lean signature, source and proof dependencies are unchanged.

## Proved and sorry left

Closed the original item's one hole:
`AlgebraicGeometry.Scheme.exists_etaleAffineTensorSectionsEquiv`
(node `new-etale-affine-tensor-sections-equiv`).

The two new helper statements are both proved:

- `AlgebraicGeometry.Scheme.exists_affineTopTensorSections`
  (node `lem-sc-affine-top-tensor-sections`), from the existing affine-open comparison.
- `AlgebraicGeometry.Scheme.Modules.exists_etaleTensorSectionsTransport`
  (node `lem-sc-etale-tensor-sections-transport`), from composition, equality transport
  and module-linearity. This closes the hole left in the returned delivery.

No sorry remains in any delivered module, including the private helpers; no hole
is added. Relative to the repository item: one original hole closed, zero holes
added. Relative to the returned packet: the remaining transport hole is closed.
This is a proof, not a decomposition with unproved new lower statements. The
construction uses no arbitrary witness of an unproved existence theorem and no
sorry inside a definition. The only adjunction selection in the main argument
is from the proved nonempty adjunction theorem, and the left-adjoint comparison
is uniquely determined.

## No longer needed

No existing module import is removed and no module is claimed globally pruned.
The original direct proof dependencies `lem-weil-pbc-module-pullback-affine-sections`
and `lem-sc-etale-qcoherent-presheaf-functorial` are replaced in the main node by
`lem-sc-affine-top-tensor-sections` and `lem-sc-etale-tensor-sections-transport`;
the old dependencies remain used by those helpers. The original direct dependency
`lem-pc-module-pullback-adjunction` is replaced for quasi-coherence transport by
`def-pc-module-pullback`, whose proved `nonempty_tensorPullbackAdjunction` suffices.
The canonical adjunction remains used transitively by the normalized section
constructions. These are direct-DAG dependency replacements, not global pruning.
The direct proof import of `ModulePullbackAffineSections` from the earlier sandbox
attempt is replaced by `AffineTopTensorSections`. Second reading removed the
redundant new public import `Mathlib.LinearAlgebra.TensorProduct.Basic` from the
whole-scheme helper: its tensor syntax is already available through the existing
public dependency. No original public import is removed. No unit statement or step
is bypassed (`sk-prop-h2` has no realization assigned to this auxiliary node).

## Where the brief, the DAG or earlier work was wrong

The returned report and second reading incorrectly justified leaving the transport
hole and separating modules by heartbeat and file-time failures. That violated
stages/3-proving-and-pruning.md §4 and coord/brief-stage3.md §2. The repair removes
that justification and the hole. The section-equivalence construction is now
abstracted over actual module isomorphisms, and specialization uses a proved
restriction-map equality. The full argument has been compiled unsplit under the
same limit. The helper modules are retained only as proved mathematical factoring.

There was no mathematical statement error: transport requires neither affineness
nor quasi-coherence. Its inverse and scalar laws apply to empty schemes, the zero
module, zero scalar and identity arrows. No hypotheses, cancellation assumptions,
or nonempty witnesses were introduced. The unit route stays unchanged:
`sk-prop-h2.realized` has no statement or proof step assigned to this auxiliary item.

New repair searches used LeanFinder for module-isomorphism evaluation and Loogle
for `Hom.app_smul`; they confirmed `instIsIsoAbApp`, `inv_app` and `Hom.app_smul`.
Read the existing `appLinearEquivOfIso` implementation and the Mathlib evaluation
and scalar laws. The proof uses those elementary laws without introducing another
public section-equivalence API. The original node search records are retained.

## New nodes

`lem-sc-affine-top-tensor-sections` is the proved whole-scheme specialization of
`exists_tensorPullback_affine_sections`, forgetting scalar structure after
specializing the family and identifying `appLE` with `appTop`. Its module is
`Sheaf.AlgebraicGeometry.AffineTopTensorSections`.

`lem-sc-etale-tensor-sections-transport` is the now-proved transport from successive
pullbacks to the etale object's pullback, with its scalar-unit formula. Its module
is `Sheaf.AlgebraicGeometry.EtaleTensorSectionsTransport`. No new node or hole
was introduced in this repair. Its full generic construction and specialization
are private proved helpers of this same module.

Change records:
`coord/changes/etale-affine-tensor-sections-local-elaboration.md` and
`coord/changes/etale-tensor-sections-equivalence-construction.md`.
The former records the main module's local elaboration settings; the latter
records the repaired proof-local data construction. There is no changed existing
exported definition and no forced adaptation.

## Earlier second reading (a previous round; superseded)

The previous second reading's PASS for the one-hole, timeout-driven decomposition
is superseded by return D. It must not be treated as an independent review of this
repair. The following are the repair worker's checks for the next independent reader.

1. All existing theorem signatures and visibility are preserved. The transport
   declaration's signature is unchanged; its complete word proof is now implemented.
   No target statement or existing public definition changes. The new private data
   definition has explicit forward/inverse maps and proved inverse laws.
2. `sectionsEquiv_smul` is exactly module-linearity of the evaluated isomorphism.
   `transportForFamily` constructs the composition component followed by equality
   transport along the triangle. `restriction_eq` is the definition of the actual
   additive restriction map. The main theorem composes the affine bijection and
   this fully proved transport equivalence and combines their evaluation equations.
3. All three delivered modules compile through `lcompile.py --all`. The complete
   unsplit argument also compiles in one file through `lcompile.py` with the
   unchanged 60-second timeout. No textual sorry remains in the delivery. The
   required delivery dry run performs the additional per-declaration axiom probes.
4. The two helper statements are strict mathematical parts of the original proof,
   with unchanged edge cases and no new hypotheses. They are now proved rather
   than lower holes. The main node and transport node describe the actual Lean
   route; no unit step or statement is bypassed and no global pruning is claimed.
5. Return D is repaired by a complete transport proof and verification of the
   unsplit argument. The change records explain the proof-local construction and
   its users. The independent second reader should replace this repair audit with
   their own reading before delivering.


## Earlier second reading (a previous round; superseded)

Independent reading of the repaired packet, not the superseded one-hole delivery.

1. PASS: compared the existing main module with the repository using diff and the
   declaration-table interface check: no existing signature changed. Its entire
   docstring and public import are preserved. The two helper modules are new;
   their node records contain their actual Lean signatures. Local irreducibility,
   instance priorities and transparency settings only affect elaboration. Neither
   change record alters an existing exported definition or target statement.
2. PASS: read all three complete modules. The affine helper specializes the
   existing affine-open comparison to top, proves appLE = appTop, and takes its
   bijectivity and pure-tensor clauses. In transport, sectionsEquiv explicitly
   evaluates k.hom and k.inv; evaluating the two isomorphism identities proves both
   inverse laws. Hom.app_smul proves its scalar law. transportForFamily forms the
   composition component followed by eqToIso along a.w; restriction_eq is exactly
   the existing restriction definition. The main proof transfers quasi-coherence
   along leftAdjointUniq, composes AddEquiv.ofBijective with this transport, and
   concatenates the two pure-section equations. No arbitrary unproved existence
   witness supplies data; the selected nonempty adjunction is proved. All three
   files compile without warnings through lcompile.py. Textual inspection found
   no sorry or forbidden declaration forms; explicit axiom checks and the delivery
   probe verify the remaining kernel trust check below.
3. PASS: both added public statements are fully proved, strictly smaller parts of
   the argument. Read Stacks [01I9](https://stacks.math.columbia.edu/tag/01I9),
   [01IA](https://stacks.math.columbia.edu/tag/01IA) and the section functor in
   [03DR](https://stacks.math.columbia.edu/tag/03DR), together with the actual
   exists_tensorPullback_affine_sections and etaleTensorSectionsRestriction.
   Affineness and quasi-coherence are used only for the first comparison; transport
   only uses a module isomorphism and module-linearity. Zero modules, zero scalars,
   empty affine schemes and identity arrows introduce no exception or cancellation
   requirement. Repeated searches with different wording via LeanFinder, Loogle,
   msearch grep and repository rg found no existing complete helper statement.
   The upstream appLinearEquivOfIso was read: it implements the same evaluation
   idea with additional scalar-equivalence data. The private additive construction
   here uses its elementary laws directly; it introduces no duplicate public API.
4. PASS: the argument follows the original affine comparison and pullback
   quasi-coherence route. The three proof-only imports in the main module and the
   affine helper's ModulePullbackAffineSections import are plain imports. Public
   imports supply types and definitions occurring in the new signatures.
   No original import is removed. The report accounts for all three replaced old
   direct dependencies: affine sections, normalized presheaf functoriality and the
   canonical pullback adjunction. Their required content remains used transitively;
   none is claimed globally pruned. Checked sk-prop-h2.realized: its statement and
   sole step have empty realization lists, so this auxiliary factoring bypasses no
   assigned unit node. The unsplit scratch proof checks that the factoring is not
   needed to evade the file time limit.
5. PASS: opened all three JSON nodes against their Lean modules. Each lean.statement
   matches its declaration; each proof_deps is the union of the step uses. The main
   node records the quasi-coherence transfer and composition of the two helpers;
   the transport node records the explicit generic construction and restriction
   rewrite. New nodes have source, searches, created, blueprint, chapter, unit and
   Lean records. The existing node changes only the stage-3-owned proof fields.

Changes in this second reading: appended this independent review and recorded
fresh search and validation evidence. No Lean proof, signature, import or node
needed repair. One original hole is closed, zero holes are added; both new helpers
are proved, with no split-off obligation left.

Independent validation results: explicit #print axioms checks for all three public
theorems report exactly propext, Classical.choice and Quot.sound, with no sorryAx.
The axiom scratch copies compile in import order. The unsplit repair compiles
without warnings (20.3 seconds reported, including any slot wait).

## Second reading by Q4

1. Compared the delivered existing module with the repository version. The theorem signature and all existing declarations are unchanged; only proof-local imports, settings, and the proof body differ. The two helper modules are new statements recorded in their own nodes.

2. Compiled all three modules with `lcompile.py --all` and searched for `sorry`, forbidden declarations, and hollow definitions. No such declarations remain. The proofs construct the section equivalence from explicit module isomorphisms and use only the permitted mathematical route; no arbitrary witness supplies data.

3. Read both split-off statements and tested their edge-case claims conceptually: neither requires affineness or quasi-coherence beyond the affine comparison helper, and zero modules, zero scalars, identity maps, and empty schemes introduce no exception. Searches recorded in the nodes found no existing duplicate theorem.

4. The affine helper specializes the existing affine-open comparison at top; the transport helper evaluates the canonical composition isomorphism and proves scalar compatibility with `Hom.app_smul`. Imports are minimal for the delivered declarations, and the unit route is unchanged. The direct proof dependencies in the main node now match the actual proof and replace the older direct dependencies transitively.

5. Checked all three DAG nodes against their Lean declarations. Corrected the main node's proof, proof dependencies, and proof origin to describe the current implementation; its module and declaration fields already match the delivered file. No target statement changed.

Changed only the stale main-node proof metadata and appended this review. Closed the original target hole and left no sorry in the delivered modules; the two helper nodes are proved and add no holes.
