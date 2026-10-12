## What changed

Repair of return X-4d255 (reviewed head 4d2559dfb): the independent review passed,
but landing timed out waiting for the project's merge lock. This repair rebuilds
the delivery on the current origin/sheaf-dag through deliver3.py --no-push and
reruns local compilation, server compilation, and preflight. The approved Lean
proofs, signatures, imports, and node records are preserved. No merge lock is
removed or bypassed; the second reader remains responsible for delivery.

Repaired return X-01328 point by point. Moved the two named intermediate sorry theorems
out of WeilConjectures.ConstructibleSheaf.LocallyConstantReduction into separate modules:
Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration and
Sheaf.ConstructibleSheaf.LocallyConstantRetraction. Each module has the required module,
public imports, module docstring, exposed public section, explicit universes, and no
implicit variables. Each theorem docstring gives its exact source place and full argument.
The original theorem combines the same two strictly smaller conclusions using obtain
and construction of the existential tuple. Its new imports are proof-only.
Restored the original module and theorem docstrings verbatim from the repository.
Updated both new node Lean records and sources, defined F_ℓ as ℤ/ℓℤ (and explained its
Lean universe lift) in both statements, and updated the parent node to the combining proof.

## Proved and sorry left

AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_reduction
has a complete Lean proof from the two intermediate statements. Of the original module's
one sorry, one is reduced; this is not an axiom-free proof of its dependency closure.
The two remaining named sorry theorems are:

- AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_cover_filtration,
  in Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration,
  node split-locally-constant-cover-filtration.
- AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_retraction,
  in Sheaf.ConstructibleSheaf.LocallyConstantRetraction,
  node split-locally-constant-retraction.

Both retain exactly their previous signatures. The zero sheaf gives a length-zero
filtration; a trivial representation admits the identity cover; degree one gives the
identity trace splitting. The prime-to-ℓ hypothesis excludes degree zero.

## No longer needed

No original public import was removed. The parent node's detailed monodromy and trace
proof dependencies are now used through the two component nodes rather than directly.
The cover/filtration node no longer uses lem-weil-pbc-finite-etale-trace-degree or
Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree to justify fibre cardinality. That node
and module remain necessary to the retraction argument; they are not globally pruned.
No other node or module is claimed to be globally unnecessary.

The complete list of former direct parent proof dependencies replaced by the two
component nodes is:

- `def-weil-geometric-point`
- `def-galois-fibre-functor`
- `cor-galois-lisse-representations`
- `def-weil-pbc-geometric-stalks`
- `lem-weil-pbc-sylow-subgroup-prime-index`
- `thm-galois-fundamental`
- `def-galois-categories`
- `def-weil-connected-scheme`
- `lem-weil-pbc-finite-etale-trace-degree`
- `thm-galois-lc-etale`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `lemma-weil-pbc-finite-l-group-filtration`
- `def-weil-pbc-inverse-image`
- `def-weil-pbc-finite-etale-trace`
- `def-weil-pbc-etale-sheaves`

All remain reachable through the component plans; none is claimed globally pruned.


## Where the brief, the DAG or earlier work was wrong

Return X-4d255 concerns a landing infrastructure timeout, not a proof defect.
The prescribed fresh base and compilation are handled by the delivery tool;
there is no mathematical correction required by that return.

The returned delivery placed both new sorry declarations in the source module, used
one-line docstrings, did not define F_ℓ in the node statements, and gave vague source
places. These have all been repaired. Exact cover source: etale-cohomology.tex,
Lemma 0A3R (lemma-pullback-filtered), with Lemma 0DV5
(lemma-locally-constant-on-connected) and Remark 0DV6
(remark-functorial-locally-constant-on-connected). Exact retraction source: the trace
characterization and composite following Definition 03SE (definition-trace-map),
Section 03SH (section-trace-method). Tags and labels were checked in the local Stacks source.

For C4, cover step 1 now explicitly uses finite local freeness, locally constant fibre
dimension, invariance under base change, and the geometric-fibre splitting theorem:
def-pc-finite-locally-free,
lem-weil-pbc-finite-locally-free-degree-locally-constant,
lem-weil-pbc-fibre-degree-base-change, and lem-galois-geometric-fibre.
The step explains why the number of field factors is the dimension and the number of
geometric lifts, and why comparison at the chosen point forces that number to be d.
Its proof_deps are exactly the union of the updated steps' uses.
The geometric-fibre node is used as a tool for the field-factor decomposition, not to
replace the unit's locally constant reduction route.

The earlier second reading incorrectly claimed that the old delivery preserved the
existing docstrings byte for byte and introduced no imports. That old delivery had
shortened both original docstrings. The stale second-reading text has been removed;
a new independent reading is required. This repair restores both original docstrings
and adds the two proof-only imports. The earlier claim that sorry dependencies were an
obstacle was also incorrect: this stage permits reduction to named sorry statements.

## New nodes

split-locally-constant-cover-filtration is the existing delivery's new intermediate node,
now realized in lean/Sheaf/ConstructibleSheaf/LocallyConstantCoverFiltration.lean.
It supplies the connected prime-to-ℓ cover, uniform geometric-fibre size, and filtration.
Its geometric-fibre dependency list has been corrected as described above.

split-locally-constant-retraction is the existing delivery's new intermediate node,
now realized in lean/Sheaf/ConstructibleSheaf/LocallyConstantRetraction.lean.
It supplies the retraction for a given finite étale cover of prime-to-ℓ uniform fibre size.
No further node, change of definition, change of existing signature, or change record
is introduced by this repair. The original parent node's statement and the unit route
are unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered source module with the repository using diff. The entire
   existing theorem signature, both docstrings, and original public imports are byte
   for byte unchanged. Only the proof and two proof-only imports differ. The two
   additional modules declare genuinely new, separate component statements; no existing
   definition or target statement changes. Verdict: pass.
2. Compiled all three modules locally in import order without errors or warnings.
   Independently appended `#print axioms` to scratch copies of each declaration: each
   uses only propext, Classical.choice, Quot.sound and sorryAx. The latter is expected
   from the two explicitly reported named intermediate theorems. There is no sorry
   in the parent proof, no definition in the delivery, and no forbidden declaration
   or compiler escape. Scratch probes were removed. Verdict: pass as a partial reduction,
   not an axiom-free closure proof.
3. Read both intermediate statements and their full docstring proofs. The cover lemma
   omits the trace conclusion; the retraction lemma works on an already specified cover
   and proves no filtration. Neither restates the item. Checked zero-dimensional G
   (length zero), trivial monodromy (identity cover), degree one (identity trace),
   and degree zero (excluded by nondivisibility). A Sylow subgroup gives the required
   prime-to-ℓ index, and the fixed-vector induction gives rank-one trivial quotients.
   Searched Mathlib with new leanfinder, loogle and grep queries and searched both the
   repository and upstream source. No duplicate or directly applicable replacement was
   found. Existing trace declarations concern abelian sheaves; transporting them to
   these module-valued functors requires additional comparison work, so the retraction
   cannot be closed in a few minutes. Verdict: pass.
4. The parent proof directly combines the two components on the same cover. All
   imports serve either public signatures or the two proof applications, and the new
   proof imports are plain import. Enumerated every old direct proof dependency under
   No longer needed, distinguishing replaced direct edges from global pruning. Read
   dag/units/sk-thm-p1.json and its realized entries: the finite-group filtration and
   trace route for the curve calculations remains intact. Verdict: pass.
5. Read all three delivered nodes and checked each proof_deps against the union of
   its steps' uses, the parent proof against its two applications, and both verbatim
   Lean statement records against the modules. The new nodes have sources, natural
   language arguments, search records, provenance, chapter, unit and blueprint origin.
   Repaired empty stmt_deps by citing the conventions actually used, including the
   distinction between geometric lifts and fibre-scheme points. Updated the parent's
   Lean record to say its own proof is sorry-free while its dependency closure is open.
   Verdict: pass after these metadata repairs.

Second reading changed only node metadata and the report: refreshed new-node searches
with the actual logged second-reading queries (LeanSearch unavailable; other services
and grep searched), added the new nodes'
statement convention citations/dependencies, corrected the parent's Lean status and
line, and made the replaced dependency list explicit. No Lean proof, signature,
definition, docstring or import was changed by this reading.

## Second reading by V1

1. Compared the existing module against the repository with diff. Its theorem signature,
   original public imports, module docstring and theorem docstring are byte for byte
   unchanged. Only the two plain proof imports and the proof differ. The additional
   modules introduce new declarations; there are no definition or target changes.
   Verdict: pass.
2. Compiled all three modules locally in import order without errors or warnings.
   Appended independent `#print axioms` probes to scratch copies of all three theorems:
   each uses only propext, Classical.choice, Quot.sound and sorryAx. The probes were
   removed. The two reported component theorems contain the only sorries; both have
   named declarations, full docstring arguments and matching nodes. No definition,
   forbidden axiom declaration or compiler escape is present. Verdict: pass as a
   partial reduction; the dependency closure remains open.
3. Read both split statements and arguments and verified their boundaries: cover and
   filtration supplies no retraction; retraction takes a specified cover and supplies
   no filtration. Checked the zero sheaf, trivial monodromy, degree one, and degree
   zero (excluded by nondivisibility); a nontrivial unipotent representation is handled
   by the invariant-vector induction. Checked the sources independently at
   [Stacks 0A3R](https://stacks.math.columbia.edu/tag/0A3R),
   [Stacks 0DV5](https://stacks.math.columbia.edu/tag/0DV5), and the trace description in
   [Stacks 03SH](https://stacks.math.columbia.edu/tag/03SH).
   Ran fresh leanfinder, loogle and Mathlib grep queries using averaging, split mono,
   and Sylow/flag terminology, and searched the project and upstream declarations.
   No directly applicable replacement was found. The existing trace-degree statement
   uses AddCommGrpCat sheaves, and the representation results still require transport
   to the stated sheaf filtration; neither component closes in a few minutes.
   Verdict: pass.
4. Read the parent proof from its conclusion downward: it combines the two smaller
   conclusions for exactly the same v and d. Both original public imports are needed
   for signatures; both added imports are proof-only and plain. Checked every former
   direct dependency against the complete No longer needed list. Read the unit
   sk-thm-p1 and its realized steps: its locally constant reduction by finite-group
   filtration and trace splitting is preserved. No module is claimed globally pruned.
   Verdict: pass.
5. Read all three node proofs, dependencies, provenance and Lean records. Checked
   programmatically that each proof_deps is the union of the steps' uses, every cited
   node exists, and both new Lean statement records match their signatures verbatim.
   The parent node describes precisely its two applications. Both new nodes have
   sources, search records, creation data, blueprint origin, chapter and unit.
   Verdict: pass.

Second reading changed only the report and the two new nodes' search metadata, adding
fresh independently executed searches. No Lean repair was necessary. One of the
original module's one sorry is reduced to two strictly smaller named statements;
no global pruning is claimed.
