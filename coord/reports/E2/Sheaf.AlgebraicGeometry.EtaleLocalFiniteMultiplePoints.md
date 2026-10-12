## What changed

Replaced the sole `sorry` in `AlgebraicGeometry.exists_etale_local_finite_multiple_points`
with a complete Lean reduction following Stacks 02LM. Its statement and public imports are
unchanged. The proof derives finite residue extensions from isolatedness, invokes a residue
splitting construction, transports isolatedness to the enumerated lifts, proves global
injectivity from input injectivity and per-list injectivity, invokes elementary localization,
and composes the two étale maps and their distinguished-point equalities.

Added two modules, each with one public intermediate theorem. `EtaleSplitResiduePoints`
packages the initial finite separable extension, prescribed-residue-field neighborhood,
and tensor-prime enumeration. It assumes only finite residue extensions, and produces no
finite opens. `ElementaryLocalizeSplitPoints` packages the application of 02LL to the
already enumerated isolated lifts, pullback pasting, residue-field transport, and exhaustion
verification. It assumes explicitly that the incoming extensions are finite purely
inseparable, and does not assume the incoming base morphism is étale. Thus neither theorem
is a renaming or repackaging of the original theorem. The original proof supplies several
substantive hypotheses and composes the results.

Updated the original node's proof route and added matching nodes for both intermediate
statements. The unit route is retained: this is a split within the existing 02LM argument,
with the existing 02LL theorem retained as an intended dependency of elementary localization.

## Proved and sorry left

The item's single theorem `AlgebraicGeometry.exists_etale_local_finite_multiple_points`
now has a compiling proof with no internal `sorry`; this is a reduction, and its imported
proof obligations remain open.

The two new sorries are:

- `AlgebraicGeometry.exists_etale_split_residue_points`, node
  `lem-weil-pbc-etale-split-residue-points`, in
  `lean/Sheaf/AlgebraicGeometry/EtaleSplitResiduePoints.lean`.
- `AlgebraicGeometry.exists_elementary_localize_split_points`, node
  `lem-weil-pbc-elementary-localize-split-points`, in
  `lean/Sheaf/AlgebraicGeometry/ElementaryLocalizeSplitPoints.lean`.

Each is a named public theorem with the proof exactly `by sorry`, a sourced complete proof
in words, and a node with its full verbatim Lean signature. The existing
`finiteDimensional_residueField_of_isOpen_singleton_asFiber` and
`isolated_fiber_point_base_change` are used without changing their modules or statements.

## No longer needed

Removed four direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.EtaleLocalFiniteMultiplePointsElementary` (used by the second
  intermediate theorem).
- `Sheaf.AlgebraicGeometry.EtaleNeighbourhoodPrescribedResidueField` (used by the first
  intermediate theorem).
- `Sheaf.AlgebraicGeometry.FibreProductPointResidueField` (used by both intermediate
  theorems).
- `Sheaf.FieldTheory.SeparableSplitPurelyInseparableResidueFields` (used by the first
  intermediate theorem).

These imports are relocated, not pruned from the mathematical argument. No original nodes
or modules become unneeded in the transitive proof closure. No new public imports were
added to the item. The two intermediate theorems retain the proof dependencies needed for their subarguments.
The second reading removed redundant `Mathlib.AlgebraicGeometry.Morphisms.Finite` and
`Sheaf.AlgebraicGeometry.FibreProductPointResidueField` imports from
`ElementaryLocalizeSplitPoints`: Fiber already exposes finiteness, and the elementary
theorem supplies both residue isomorphisms. Exhaustion only needs the point correspondence.


The complete list removed from the original node’s DIRECT `proof_deps` is below.
These dependencies remain in intermediate proof routes or statement/definition dependencies;
none is claimed pruned from the target closure.

- `def-pc-fibre-product`.
- `def-pc-scheme-fibre`.
- `def-weil-etale-morphism`.
- `def-weil-finite-integral-morphism`.
- `def-weil-pbc-finite-purely-inseparable-extension`.
- `def-weil-pbc-separable-algebraic-extension`.
- `def-weil-residue-field`.
- `lem-weil-pbc-cartesian-square-pasting`.
- `lem-weil-pbc-etale-local-finite-multiple-points-elementary`.
- `lem-weil-pbc-etale-neighbourhood-prescribed-residue-field`.
- `lem-weil-pbc-fibre-product-point-residue-field`.
- `lem-weil-pbc-fibre-product-points`.
- `lem-weil-pbc-lft-base-change`.
- `lem-weil-pbc-separable-split-purely-inseparable-residue-fields`.

## Where the brief, the DAG or earlier work was wrong

No error in the original statement or six-step mathematical plan was found. The omitted
verification in Stacks is recorded explicitly in the elementary-localization docstring
and node, including why the elementary base residue map makes each remaining lift unique.
Lean's dependent fibre-point type requires explicit equality transport (`Eq.rec`) for
isolatedness; rewriting the displayed projection equality alone did not solve that goal.

Both new statements were checked on the empty family (identity neighborhood, empty lists),
the identity scheme morphism, and a separable residue extension such as Spec C over Spec R.
The latter requires the initial residue splitting: a unique point of a finite fibre alone
does not imply a purely inseparable residue extension. For repeated inputs, the first
intermediate theorem intentionally guarantees injectivity only within each list; the
original input distinctness supplies injectivity of the whole sigma family in the main
Lean proof. The second intermediate theorem assumes global injectivity explicitly.

LeanSearch returned an unavailable-service response, recorded in searches.jsonl without
an absence verdict. LeanFinder, Loogle and source searches found no matching simultaneous
scheme theorem. Mathlib's separated quasi-finite finite-open theorem requires a separated
morphism and does not give the initial residue splitting for this statement. The local
Stacks source was read from the available source mirror; citations retain the project's
canonical literature path.

## New nodes

`lem-weil-pbc-etale-split-residue-points`: the first half of 02LM, finite residue extensions
and common separable splitting through the enumeration of points with purely inseparable
residue extensions. Inherits chapter `sec-proper-base-change` and unit `sk-thm-p1`.

`lem-weil-pbc-elementary-localize-split-points`: the second half of 02LM, application of
02LL to those enumerated points followed by pullback pasting and the final verification.
Inherits the same chapter and unit. No definition changes or change records are needed.

## Second reading by E2

1. **Visible declarations — pass.** Read all three delivered modules and diffed the item
   against the repository. The sole existing declaration’s signature and docstring are byte
   for byte unchanged; only its proof and private imports differ. The two additional modules
   are new, each declaring one theorem. There are no definition or target changes and no
   change records are required. The original node differs only in `proof`, `proof_deps` and
   `proof_origin`; its existing normalized `lean.statement` is retained unchanged.
2. **Proof and trust — pass as a reduction.** Compiled all three modules in import order
   through lcompile.py, with no errors or warnings. Read the complete proof: residue finiteness
   uses the original isolatedness; Eq.rec transports that exact hypothesis to the projected
   lift; sigma injectivity uses input injectivity and each list’s injectivity; the last step
   composes the étale maps and point equalities. The item has no internal sorry. Each new
   obligation has exactly one public named theorem with body `by sorry`. There are no
   forbidden declarations or hollow definitions. Scratch-copy `#print axioms` checks of
   all three theorems show exactly propext, Classical.choice, Quot.sound and sorryAx. Thus the item remains dependent on open lemmas, as reported.
3. **New obligations — pass.** Read Stacks 02LM in
   `/home/ubuntu/c1-stacks-review/more-morphisms.tex`, lines 12018–12090, and Schemes 01JT
   in `/home/ubuntu/c1-stacks-review/schemes.tex`, around lines 3265–3315. For residue
   splitting, read the actual statements of the common separable-splitting theorem, prescribed
   residue-field neighborhood theorem and tensor residue-field theorem: they supply finite
   spectra, a compatible field isomorphism, and both projection compatibilities, exactly
   what the four steps require. This lemma needs neither isolatedness nor local finite type
   and gives no finite opens. For localization, read 02LL and its Lean declaration: it
   gives an elementary base residue isomorphism, finite opens, unique points, projection
   equalities and point residue isomorphisms. Pullback pasting transports these data; the
   commuting residue square follows from residueFieldMap_comp; finite generators and
   purely inseparable powers transport across its isomorphisms. Exhaustion projects to a
   listed y and then uses 01JT: tensoring with an isomorphic base field gives a field with
   one prime. The localization lemma assumes splitting and isolatedness already supplied
   by the main proof, and makes no étaleness assumption on φ. Neither is a renamed item.
   Checked n=0, identity scheme morphisms, repeated inputs (allowed only for per-list
   injectivity in splitting), separable Spec C over Spec R (two split points), and a finite
   purely inseparable extension (one tensor prime even when the tensor ring is nonreduced).
   If some m_i=0, hex forces the corresponding pair-fibre to be empty; later base change
   cannot introduce points projecting to that empty fibre. The new theorem docstrings give
   the complete mathematical proofs and the nodes match their signatures verbatim.
   Independently searched LeanFinder for radicial residue splitting after separable base
   extension, Loogle for residueFieldMap (finding the composition/naturality lemmas), and
   msearch grep for isolated/residue étale localization; also searched lean/Sheaf and the
   upstream algebraic-geometry/étale sources. No duplicate simultaneous scheme theorem
   was found. The upstream ring results and Mathlib’s separated quasi-finite finite-open
   theorem do not close either full obligation in a few minutes. The first Loogle query
   used a namespace as an identifier and was invalid; the subsequent residueFieldMap
   query succeeded and is the usable search. No absence claim relies on the invalid query.
4. **Top-down route and pruning — pass after report repair.** The proof really reduces the
   original sorry, supplying hypotheses that the two subarguments omit. The original 02LM
   route, including 02LL, residue splitting and fibre-product enumeration, remains intact.
   Read `dag/units/sk-thm-p1.json`, including its realized statement and four step lists:
   no unit realization is bypassed or changed. No shorter matching library theorem was
   found. Removed the two redundant localization imports. Expanded No longer needed to
   list EVERY old direct proof dependency removed, distinguishing relocation from pruning.
5. **DAG agreement — pass after clarification.** Checked all new node fields, source and
   blueprint lineage, self-contained hypotheses and clauses, verbatim Lean signatures,
   status, created record, chapter and unit. Every proof_deps equals the union of step uses.
   The item’s six steps match its Lean reduction. The new routes cite the existing
   non-elementary results actually needed. Clarified localization step 3 using
   Scheme.residueFieldMap_comp and the explicit generator/power transport, and marked
   this short transport elementary; it does not require another tensor-residue theorem.

Changes by this second reader: removed two redundant imports from ElementaryLocalizeSplitPoints;
added blueprint references to both new module docstrings; clarified the elementary residue
transport in its node; completed the old dependency list and import explanation in this report.
No theorem signature, definition, or proof body was changed.
