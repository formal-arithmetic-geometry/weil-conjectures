## What changed

`AlgebraicGeometry.etaleSetSectionLift` now has a combining Lean proof, with its
original signature and docstring unchanged. Two intermediate steps are separate
modules, one named statement per module: affine lifting, and construction of a finite
compatible local family conditional on affine lifting. These implement the original
DAG's two-step route rather than replace it. Neither is a restatement of the general
lifting assertion: one assumes the source affine; the other constructs only local
sections, with compatibility and local image equations, and does not glue them.

The assigned module proves the private helper `sectionComparison_naturality` by
naturality of the adjunction unit, composition isomorphism, equality transport, and
pullback-pasting isomorphism. It supplies the affine hypothesis, obtains the local
family, glues it using `IsSheaf.existsUnique_amalgamation_ofArrows`, and proves the
image equality using `IsSheaf.hom_ext_ofArrows` on the covering at the limit.
Sections are represented as morphisms from `PUnit.{u + 2}` in the category of types.
There is no hidden nonemptiness assumption on the cover: a zero-member covering
is handled by exactly the same gluing and separatedness proof.

All three modules compile together through the prescribed `lcompile.py --all`.
Only sandbox sources form this delivery. The original DAG entry is updated to the
actual combining proof; the two new entries retain its affine-site and finite-cover
proof plans, with complete proofs in words and the corresponding planned imports.
No existing public interface changes and no change record is needed.

## Proved and sorry left

Proved `AlgebraicGeometry.etaleSetSectionLift`
(node `lem-weil-pbc-sets-section-lift`) from the two new intermediate statements.
Also proved the private helper `AlgebraicGeometry.sectionComparison_naturality`.
There is no sorry in the assigned module.

Hole accounting: one original hole is closed syntactically and two new holes are added.
This is a decomposition, not a completed sorry-free proof of the original declaration.
The original declaration still depends on `sorryAx`; zero of the one original
declarations is proved independently of open statements. The private naturality
helper uses only `propext`, `Classical.choice`, and `Quot.sound`.

Exactly two new whole-proof sorries remain:

- `AlgebraicGeometry.etaleSetSectionLift_affine`, node
  `lem-weil-pbc-sets-section-lift-affine`, module
  `Sheaf.AlgebraicGeometry.EtaleSetSectionLiftAffine`.
- `AlgebraicGeometry.etaleSetSectionLift_local_family`, node
  `lem-weil-pbc-sets-section-lift-local-family`, module
  `Sheaf.AlgebraicGeometry.EtaleSetSectionLiftLocalFamily`.

Each is public, has exactly `:= by sorry`, and has its source and complete proof in
words in its docstring and its node. The general theorem is therefore reduced, not
yet independent of sorry axioms. The affine site comparison and finite common-stage
construction are the work for the next workers.

Edge cases checked mathematically before stating the intermediates: empty affine
objects have one sheaf section; an empty covering gives vacuous local compatibility
and requires only a nonempty tail; a constant or singleton index system satisfies
both statements; no separatedness of the base is added; the qcqs hypotheses give
finite affine cover and overlap refinements, and all affine refinement objects have
qcqs structure maps. The local family's compatibility is quantified over arbitrary
pairs of arrows with equal composites, exactly what the sheaf gluing API requires.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.AffineEtaleInverseImageComparison`
- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`
- `Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`
- `Sheaf.AlgebraicGeometry.EtaleSetSectionComparisonLaws`
- `Sheaf.AlgebraicGeometry.EtaleSetSectionEventualEquality`
- `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
- `Sheaf.CategoryTheory.ColimitSiteSections`
- `Mathlib.CategoryTheory.Limits.Connected`
- `Mathlib.CategoryTheory.Sites.Equivalence`
- `Mathlib.CategoryTheory.Sites.EqualizerSheafCondition`

These imports belong to the still-open affine or finite-family steps and are retained
there as proof-plan imports. Their original DAG nodes are likewise retained as
proof dependencies of those new nodes. No original node or module is claimed
unneeded in the whole target closure. The two new proof imports suffice for the
assigned module; its existing public import of `EtaleSetSectionComparison` supplies
the public comparison and composition-unit definitions.

The following old nodes are no longer direct proof dependencies of the assigned
node (all remain needed transitively through the two new statements):

- `lem-weil-pbc-affine-etale-site-colimit`
- `lem-weil-pbc-affine-etale-site-topos`
- `lem-weil-pbc-colimit-constant-connected-diagram`
- `lem-weil-pbc-colimit-of-sites-sections`
- `lem-weil-pbc-etale-qcqs-cofinal-finite-coverings`
- `lem-weil-pbc-limit-affine-transition`
- `lem-weil-pbc-sets-affine-etale-inverse-image-comparison`
- `lem-weil-pbc-sets-section-comparison-laws`
- `lem-weil-pbc-sets-section-eventual-equality`
- `lem-weil-pbc-site-equivalence-sheaf-transport`

No module is pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

The earlier missing-olean failure has cleared: the original module and its public
comparison dependency now compile. The unverified naturality draft from the earlier
attempt was repaired and typechecked. The initial conditional-descent experiment
was replaced by the concrete compatible-family statement and a real gluing proof;
it is not part of the delivery. During that initial experiment copies were mistakenly
written in the read-only repository; the original module was restored immediately
and the experimental added module removed. All retained work is in the sandbox.

The supplied local literature checkout lacks the Stacks tex files, so the cited
primary sources were read online: https://stacks.math.columbia.edu/tag/09YQ,
https://stacks.math.columbia.edu/tag/09YN, and
https://stacks.math.columbia.edu/tag/03Q4. Tag 09YQ is the abelian cohomology theorem;
Tag 09YN supplies the set-valued site-section assertion. The finite-cover reduction
here is the degree-zero set-valued adaptation of the existing DAG plan. LeanSearch
returned Internal Server Error; LeanFinder and Mathlib/source/blueprint searches
found no exact lifting or common-stage-local-family replacement. Mathlib supplies
both the final gluing and separatedness statements used in the completed proof.

## New nodes

`lem-weil-pbc-sets-section-lift-affine`, in
`dag/nodes/sec-proper-base-change/`, records the affine special case with the
original affine-site proof dependencies. Its module is
`lean/Sheaf/AlgebraicGeometry/EtaleSetSectionLiftAffine.lean`.

`lem-weil-pbc-sets-section-lift-local-family`, in the same node directory, records
construction of a finite compatible common-stage local family from the affine
lifting hypothesis and eventual equality. Its module is
`lean/Sheaf/AlgebraicGeometry/EtaleSetSectionLiftLocalFamily.lean`.

Both inherit the original unit `sk-thm-iff` and blueprint ancestry. That unit's
realized statement and steps are preserved. No new definition or interface change
is introduced, and there are no change records.

## Second reading by C2

1. **Visible interface: pass.** Compared the main module with the repository using
   `diff -u`, and separately compared the existing theorem signature as raw text:
   byte-for-byte identical. Its original docstring and sole public import are
   unchanged. The only other delivered Lean files are new modules, and they add
   the two reported statements. No definition, target, existing statement or
   public import changes; no change record is necessary.
2. **Proof and axioms: pass as a decomposition.** Recompiled all three modules in
   import order through `lcompile.py --all`, without errors or warnings. Read the
   four-factor naturality proof, the PUnit representation of sections, the stage
   amalgamation, and the limit-cover separatedness argument. There are exactly
   the two reported `:= by sorry` theorems and no forbidden declarations or hollow
   definitions. A scratch copy with `#print axioms` shows only the three permitted
   axioms for the private helper, and those axioms plus `sorryAx` for the original
   theorem and both intermediates. No axiom-free completion is claimed.
3. **Split statements: pass.** Affine lifting is a proper special case of the
   original assertion. The conditional local-family theorem constructs compatible
   local sections and covering data; the original module performs the genuine
   remaining gluing and image-equality argument. Neither is the original assertion
   renamed. Both have source citations, complete mathematical proof docstrings,
   and matching nodes. Checked empty W, an empty cover, a singleton index, constant
   systems, and a nonseparated qcqs base. In particular, affine cover members and
   finite affine overlap refinements have qcqs structure maps because the base is
   qcqs, so affine lifting and eventual equality apply. Compatibility for arbitrary
   equal-composite arrows follows by restriction from equality on overlaps.
   Read Stacks [09YN](https://stacks.math.columbia.edu/tag/09YN),
   [09YQ](https://stacks.math.columbia.edu/tag/09YQ), and
   [03Q4](https://stacks.math.columbia.edu/tag/03Q4): the set-valued assertion uses
   the sites theorem, not the abelian cohomology theorem alone. Independent
   LeanFinder queries about descending inverse-image sections and moving finite
   representatives to one common index returned structure-sheaf continuity and
   filtered finite-diagram bounds, respectively, not either new theorem. Loogle
   and source grep confirmed the existing sheaf gluing APIs. Read the upstream
   SectionContinuity and the fixed-site local-lift/representative results: they
   concern abelian/module-valued sheaves and do not replace the varying-site
   set-valued assertions here. Neither remaining hole can be closed by a brief
   application of the found declarations.
4. **Route and pruning: pass after report repair.** The original affine-site route
   and finite-cover route remain below the unit. Read `sk-thm-iff.json`: its
   realized statement and sole step still name
   `lemma-weil-pbc-property-iff-acyclicity` and are unaffected. The assigned module
   needs only its public comparison import and two proof imports. The new open
   statements retain the planned proof-dependency imports. Corrected the omitted
   removal of FullAffineEtaleTopos, and explicitly listed every old direct node
   dependency removed by the reduction. None is pruned from the whole closure.
5. **DAG agreement: pass.** For every delivered node, compared the Lean signature
   with its recorded signature after whitespace normalization and checked that
   proof_deps is exactly the union of the proof steps' uses. Read the three proof
   records against the Lean: naturality, affine specialization, local family,
   gluing, and separatedness match. New nodes have source, statement dependencies,
   proof origin, search records, split status, creation metadata, blueprint ancestry,
   chapter, unit and Lean records. The existing node changes only the allowed
   proof fields; its other fields and original Lean signature are preserved.

Second-reading changes: report only. Clarified that one closed hole plus two added
holes is a decomposition, added the missing removed import and all removed direct
node dependencies, and recorded this independent review. No Lean proof or statement
needed repair. One limitation of the retained affine proof plan was also checked:
`colimitSite_sections_bijective` currently supplies fixed-site filtered-colimit
section evaluation, rather than the entire varying-site 09YN comparison by itself.
The future affine proof must construct and verify that stage-section comparison;
the mathematical docstring specifies it, and this delivery leaves it open honestly.
