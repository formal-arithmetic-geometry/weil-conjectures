## What changed

Current return: reviewer X-cce17 passed the mathematical packet at cce175316,
but landing failed while reading the absent, unrelated
`WeilConjectures.DeligneLaumon.AffineLine.Endpoints` source. This repair follows
the requested fresh-base and server validation:

- Ran the authorized delivery tool with `WEIL_SERVER_COMPILE=1`; it fetched
  `sheaf-dag`, rebased the packet on `6cf0d3d2b58312afaddc03ff739134abca5d042f`,
  compiled locally and on the server, and passed its preflight without pushing.
- Rebased the two existing node copies' maintainer-owned `lean_audit` fields to
  that base. Only their already reviewed proof/Lean fields remain outgoing changes.
- Audited the full delivered project import closure: 49 modules, no missing
  project source, and no dependency on `AffineLine.Endpoints`. The current base's
  source scanners already guard missing files. No unrelated source is fabricated.
- Additionally checked both exact delivered proof bodies together against the
  server's published build through `lcompile.remote` (12.2 seconds, exit 0).
  This scratch check makes the new public helper available to its consumer before
  landing; `lcompile.py --all` separately checked the actual module boundaries
  (2.6 and 14.6 seconds). Its axiom output confirms the reported upstream witness
  hole and only the three allowed axioms for both public homotopy theorems.
- The accepted Lean signatures, visibility and proof bodies are preserved. No
  theorem, import, definition or target statement changes in this landing repair.
  The old independent mathematical reading below is retained as historical review;
  the dispatcher supplies the fresh second reader.

Evidence is retained in `scratchpad/server-repair-check.txt`,
`scratchpad/landing-repair-import-audit.json`, and
`scratchpad/landing-repair-packet-audit.json`. The report records this return and
its actual checks, rather than resubmitting the old packet without validation.

Earlier mathematical and metadata repairs retained in this packet:

Repaired both findings in reviewer X-fe77b's return of head fe77b841a:

- C4: added `new-j1-qcoh-ordinary-tensor-resolution-coordinates-witness`, attached
  to the existing `AlgebraicGeometry.qcoh_ordinary_tensor_resolution_coordinates_witness`
  in `Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinatesFamily`.
  `lean.statement` contains its verbatim signature. That module is not changed or copied.
- C3/C4: added `new-t4-augmented-resolution-lift-homotopy`, stating exactly the existing
  public `ModuleCat.augmented_lift_homotopy` in
  `Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy`, with its verbatim
  signature, complete proof steps, source and required node metadata. Updated the
  helper's declaration-docstring blueprint reference to that node.
- The coordinate node's second proof step and `proof_deps` now cite the generic node.
  The quotient node attaches only its quotient theorem and records its actual use
  of the generic helper as a proof dependency.

Both records attach existing declarations; no theorem, module, or proof hole is added.
All signatures, visibility, imports and proof bodies are unchanged from the returned
sandbox. The coordinate Lean file is byte-identical. Literal extraction checks each
attachment against the existing declaration. The Family module is read only.

The earlier duplicate-proof repair is retained: reuse the shared augmented helper
and Mathlib's `Homotopy.prevD_chainComplex`. Its private-to-public visibility change
remains documented in `coord/changes/augmented-lift-homotopy-public-api.md`.
This metadata repair makes no further interface change.

Three kinds of searches were recorded for each new node. LeanSearch returned
Internal Server Error; Loogle and source searches completed. Compile, axiom probe
and delivery dry run are repeated for the repaired packet. The old second reading
is saved only in the scratchpad; its no-new-nodes finding is superseded and requires
an independent fresh reading.

## Proved and sorry left

Direct holes closed relative to the repository: **0**. Direct holes added: **0**.
This is a returned-delivery repair, not a new proof or decomposition.

Neither delivered Lean module contains `sorry`. The complete proof bodies of
`AlgebraicGeometry.exists_qcoh_ordinary_tensor_resolution_coordinates`, its private
semilinear tensor helpers, `ModuleCat.augmented_lift_homotopy`, and
`ModuleCat.quotient_tensor_resolution_lift_homotopy` are preserved.

The existing directly used hole remains
`AlgebraicGeometry.qcoh_ordinary_tensor_resolution_coordinates_witness`, now attached
to `new-j1-qcoh-ordinary-tensor-resolution-coordinates-witness`, in the unchanged
`Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinatesFamily`. It needs the
normalized affine comparison construction and its geometric restriction square.
The generic augmented helper is proved and supplies comparison independence, not
that geometric square. The new attachment adds no hole or split-off. No net
closure count is claimed beyond the maintainer's pinned sorry ledger.

## No longer needed

This metadata repair removes no import. Relative to the repository, the earlier
proof repair removes `Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionNaturality`
and its `AlgebraicGeometry.qcoh_ordinary_tensor_resolution_comparison_independence`,
node `new-j1-qcoh-ordinary-tensor-resolution-comparison-independence`. This item was
its only source importer when audited; that module is not edited.

The coordinate node no longer cites
`new-h2-quotient-tensor-resolution-lift-homotopy` for generic augmented lifting.
The shared Lean module remains imported for its generic helper, now attached to
its own node. The quotient theorem is not used by the coordinate proof. The
quotient node now cites the helper's node instead of claiming its generality only
through `lean.declarations`.

The quotient node also removes its old direct proof dependency
`def-weil-pbc-projective-module`: the generic helper handles projective lifting,
while projectivity remains in the quotient theorem's unchanged statement.
This does not claim to prune that definition globally.

The duplicate local `AlgebraicGeometry.augmented_lift_homotopy` and
`AlgebraicGeometry.prevD_chain` remain removed, with existing declarations reused.

These eight original comparison dependencies are not direct coordinate dependencies:

- `lem-pc-affine-chart-total-tensor`
- `lem-pc-affine-tilde-kflat`
- `lem-pc-kflat-open-restriction`
- `lem-pc-module-bounded-flat-kflat`
- `lem-pc-open-kflat-tensor-homology-comparison`
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-spec-module-tilde-sections`
- `new-affine-derived-tilde-homology-comparison`

The new witness record retains them as its construction's proof dependencies.
No global pruning of those nodes or modules is claimed.

## Where the brief, the DAG or earlier work was wrong

The latest X-cce17 return identifies a landing/source-scan failure, not a
mathematical rejection. Fresh server compilation succeeds, and the missing endpoint
is outside the delivered import closure. The repair adds no substitute endpoint,
proof hole or infrastructure edit. The final dry run is repeated after rebasing the
node metadata and recording these checks.

C4 was correct: the witness was already declared and used, with a blueprint tag,
but no corresponding node existed. The missing record now attaches it in place.

C3/C4 was correct: the quotient homotopy statement does not assert generic lifting
in an arbitrary abelian category. A separate node now matches the exact generic
helper, including an arbitrary exact target complex, without projective target
terms or an epimorphic augmentation. The coordinate proof cites that node.
The quotient wrapper also records its own application of that helper.

The existing witness supplies one comparison per basic inclusion. The coordinate
proof uses both normalizations sM and sN and a homotopy to transfer that square to
every supplied comparison. The repair does not replace geometric naturality by
lift independence, add another endpoint, or change a mathematical statement.

Degree zero, zero objects, arbitrary rings, unbounded K and empty charts are
retained. No target, definition, unit record or route changes. The scalar cut
proposed in the route note is outside this metadata repair.

## New nodes

`new-j1-qcoh-ordinary-tensor-resolution-coordinates-witness` attaches the existing
Family witness with its exact signature and records the affine K-flat construction
and normalized geometric restriction argument. The already existing hole still
needs that construction; no new Lean declaration or `sorry` is introduced.

`new-t4-augmented-resolution-lift-homotopy` attaches the already proved generic
helper in its existing quotient homotopy module. Three proof steps record the
initial projective lifts, residual lifting induction and assembly by
`Homotopy.mkInductive`. The helper's blueprint tag names the new node. No hole remains.

Change record: `coord/changes/augmented-lift-homotopy-public-api.md`, updated to cite
the helper's own node instead of the quotient node's declaration list.


## Earlier second reading (a previous round; superseded)

1. **Signatures and visible changes: PASS.** Compared both delivered modules with
   their repository versions using `diff` and the declaration parser. Every
   pre-existing declaration's statement is byte-identical. The sole visibility
   change is the declared private-to-public promotion of
   `ModuleCat.augmented_lift_homotopy`, recorded in
   `coord/changes/augmented-lift-homotopy-public-api.md`; its proof is unchanged.
   No definition or target statement changes. The Family module is not delivered.
   The three new private declarations implement semilinear tensoring directly.

2. **Proof and axioms: PASS, with the reported upstream hole.** Compiled the two
   delivered files in import order with `lcompile.py --all`: no errors or warnings.
   Read the projective lifting induction, the tensor balancing construction, the
   pure-tensor homotopy calculation, and the final use of both section
   normalizations. There is no `sorry`, prohibited declaration or hollow
   definition in either delivered file. Fresh scratch copies with `#print axioms`
   cover every declaration: all tensor helpers and both public homotopy theorems
   use only `propext`, `Classical.choice`, `Quot.sound`; the coordinate theorem also
   uses `sorryAx` through the explicitly reported existing geometric witness.
   No arbitrary data is defined by choosing a witness of an unproved existence
   theorem. The witness is eliminated only within the coordinate theorem's proof.

3. **Split statements and source: PASS.** No new Lean statement with `sorry` is
   introduced. The two new nodes attach existing declarations, and their
   `lean.statement` strings were checked literally against those declarations.
   The witness asks for one normalized comparison per inclusion, leaving the
   universal comparison-independence argument to the parent; it is not a renamed
   replacement of that parent proof. Its affine comparison construction remains
   open and cannot be closed by a short homological algebra lemma. Checked degree
   zero, zero coefficients/objects, the empty affine chart, arbitrary rings and
   unbounded K: neither the witness construction nor the transfer requires an
   extra hypothesis. The generic helper also permits a non-epimorphic augmentation
   because it lifts only through kernels. Repeated semantic and type searches
   with different wording: Mathlib's `ProjectiveResolution.liftHomotopy` requires
   a projective target resolution, while `IsKProjective.homotopyZero` uses
   integer-indexed acyclic complexes. Neither directly replaces this helper.
   Source searches found the existing witness and shared helper, which are reused.
   Checked the cited [Stacks lifting proof](https://stacks.math.columbia.edu/tag/00LS),
   [affine tensor comparison](https://stacks.math.columbia.edu/tag/08DX),
   [K-flat sheafification](https://stacks.math.columbia.edu/tag/08DV),
   [tensor quasi-isomorphism comparison](https://stacks.math.columbia.edu/tag/06YT)
   and [associated-sheaf functoriality](https://stacks.math.columbia.edu/tag/01I9).

4. **Route and pruning: PASS.** The coordinate proof first uses the existing
   geometric witness, identifies b by sN and the two augmentations by sM, tensors
   the shared augmented homotopy, and transfers the witness equation using
   `Homotopy.homologyMap_eq`. The imports of the witness and helper are private;
   the public imports supply objects appearing in the public statement, including
   `moduleRings`, `IsKFlat`, quasi-coherence and `CochainComplex.singleFunctor`.
   The removed Naturality module has no other source importer in this checkout.
   `## No longer needed` lists all eight old coordinate dependencies and now also
   the quotient node's removed projectivity dependency. Read
   `dag/units/sk-thm-picard-duality.json`: its statement, steps and `realized`
   fields are unchanged; no unit or chapter route is bypassed.

5. **DAG agreement: PASS.** All four delivered nodes' `proof_deps` equal the union
   of their proof steps' `uses`. The coordinate node cites the exact witness and
   generic lifting nodes; the quotient node cites the same generic lifting node.
   Each new attachment has source, complete proof steps, search records, creation,
   blueprint provenance, chapter, unit and exact Lean attachment metadata. Existing
   nodes change only the permitted Lean/proof fields. The coordinate and quotient
   statements remain unchanged.

Second-reading changes: completed `## No longer needed` with the removed quotient
node dependency `def-weil-pbc-projective-module`, and added this independent review.
No Lean proof, signature, import, definition or node needed further repair. Direct
holes closed: 0 of 0; added: 0; new split-off holes: 0. This delivery repairs the
returned metadata/API packet and makes no new hole-closure claim.

## Second reading by T4

1. **Visible interface: PASS.** Independently diffed both delivered Lean modules
   against the repository and compared all existing declaration signatures with
   the project's declaration parser. Every existing statement is byte-identical.
   The sole visibility change is the recorded promotion of
   `ModuleCat.augmented_lift_homotopy` from private to public; its binders and proof
   are unchanged. Read `augmented-lift-homotopy-public-api.md` and checked that no
   existing consumer could refer to the formerly private name. No target or
   definition changes. The Family module remains outside this delivery.

2. **Proof and axioms: PASS with the declared upstream hole.** Fresh
   `lcompile.py --all` compilation succeeded for both actual files (2.7 and 14.7
   seconds), without errors or warnings. Read the projective residual-lifting
   induction, the semilinear tensor construction, its pure-tensor homotopy
   identity, and the two uses of injective section normalizations in the parent.
   Fresh scratch copies of the current bodies printed axioms for all nine
   declarations: eight use only `propext`, `Classical.choice`, `Quot.sound`; the
   coordinate theorem additionally uses `sorryAx` through the existing reported
   geometric witness. Neither delivered file has a `sorry`, forbidden declaration,
   hollow definition or definition selecting arbitrary data from an unproved
   existence theorem. The witness is eliminated inside a theorem proof.

3. **Remaining statements: PASS.** No Lean statement or proof hole is split off
   by this packet. Both new node attachments literally match their existing Lean
   signatures. Read the unchanged witness and its new node: it supplies one
   normalized geometric square per basic inclusion, while the parent proves the
   separate universal comparison-independence step. This is a real reduction,
   not a renamed parent. Checked degree zero (the preceding differential is
   zero), zero objects and coefficients, the empty affine chart, arbitrary rings,
   non-epimorphic generic augmentation, and unbounded supplied K. Repeated
   LeanFinder and Loogle searches with homotopical-projectivity and mapped-homotopy
   wording, plus source searches in both library roots. Mathlib's
   `ProjectiveResolution.liftHomotopy` requires a projective target resolution;
   integer-indexed `IsKProjective.homotopyZero` does not directly replace the
   generic augmented helper. `Functor.mapHomotopy` handles a single additive
   functor, whereas this tensor construction also changes the coefficient ring
   and coefficient module. The already proved shared helper is reused. Read
   Stacks Tags 00LS(2), 08DX(2), 08DV, 06YT and 01I9 to check the lifting and
   affine-comparison source route. The existing geometric witness is not a
   short homological-algebra hole that this reading can close.

4. **Route and pruning: PASS.** The proof uses the existing witness, identifies
   the coefficient maps through sN, identifies augmentations through sM, tensors
   the shared lift homotopy, and applies `Homotopy.homologyMap_eq`. The two
   proof-dependency imports are private; the public imports provide notions in
   the public statement. Compared old and new dependency sets: all eight removed
   direct coordinate dependencies and the quotient node's removed projectivity
   dependency are listed under `## No longer needed`; the eight remain below
   the witness node. The removed Naturality import has only this source importer.
   Read `dag/units/sk-thm-picard-duality.json`; its statement, step and realized
   fields are untouched. This local comparison reduction bypasses no unit route.

5. **DAG: PASS.** For all four delivered nodes, `proof_deps` equals the union of
   proof-step `uses`. The coordinate and quotient nodes cite the exact generic
   helper node, and the coordinate node also cites the witness node. All four
   `lean.statement` attachments match the actual declaration text. The two new
   nodes have sources, complete proof steps, three search kinds (including the
   recorded unavailable semantic service where applicable), creation and
   blueprint provenance, chapter, unit and Lean metadata. Existing nodes change
   only permitted proof/Lean fields; their statements and maintainer fields are
   unchanged.

Second-reading changes: added this fresh independent review and current-body
scratch axiom probes; no Lean or DAG repair was necessary. Holes closed: 0 of 0
in the delivered modules; holes added: 0; newly split-off holes: 0. The upstream
`AlgebraicGeometry.qcoh_ordinary_tensor_resolution_coordinates_witness` remains
open as explicitly reported above. This returned-delivery repair claims no new
net hole closure.
