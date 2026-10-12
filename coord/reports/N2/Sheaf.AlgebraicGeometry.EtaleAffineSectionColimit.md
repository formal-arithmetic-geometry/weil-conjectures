## What changed

Wrote a reduction of AlgebraicGeometry.etaleStageSectionCocone_isColimit using the existing
etaleSetSectionLift_affine for representatives and a new same-stage equality lemma for
identifications, combined by Mathlib Types.FilteredColimit.isColimitOf'. The theorem's
signature and specified cocone are unchanged. The prerequisite stage diagram and cocone
modules were copied into the sandbox because their source files were present while their
compiled objects were absent from the supplied build. Compiling all sandbox files succeeds,
and deliver3.py --no-push reports OK.

## Proved and sorry left

Hole closed: AlgebraicGeometry.etaleStageSectionCocone_isColimit (1 of 1 original
item holes), by reduction to representative existence and same-stage equality. Hole added:
AlgebraicGeometry.etaleAffineSection_sameStageEquality
(lem-weil-pbc-affine-section-same-stage-equality). The existing imported
AlgebraicGeometry.etaleSetSectionLift_affine remains sorry; it is not added by this delivery.
This is a decomposition, not a net proof. Empty affine objects have singleton sections;
constant systems and singleton index types satisfy the new assertion with identity arrows.

## No longer needed

Removed direct proof imports AffineEtaleInverseImageComparison, AffineEtaleSiteColimit,
EtaleSetSectionComparisonLaws, ColimitSiteSections, FullAffineEtaleTopos,
LimitAffineTransition, Mathlib.CategoryTheory.Limits.Connected and
Mathlib.CategoryTheory.Sites.Equivalence. Their nodes remain needed beneath affine lifting
and same-stage equality; no claim that their modules leave the targets' closure is made.
No mathematical dependency from the original site's argument is pruned globally.
All eight old direct proof_deps are absent from the item's new proof_deps:
lem-weil-pbc-affine-etale-site-colimit, lem-weil-pbc-affine-etale-site-topos,
lem-weil-pbc-colimit-constant-connected-diagram, lem-weil-pbc-colimit-of-sites-sections,
lem-weil-pbc-limit-affine-transition,
lem-weil-pbc-sets-affine-etale-inverse-image-comparison,
lem-weil-pbc-sets-section-comparison-laws, and
lem-weil-pbc-site-equivalence-sheaf-transport. They remain dependencies of the
lifting theorem or of the new equality lemma's mathematical proof plan.

## Where the brief, the DAG or earlier work was wrong

The supplied compiled build omitted the stage diagram and cocone objects even though their
source modules were present. Compiling those source prerequisites in the sandbox resolves
the tooling issue. The original node already notes that ColimitSiteSections is only a fixed-site evaluation result,
so it cannot alone implement the varying-site identification. Existing affine eventual
equality depends on this item and cannot be imported without an import cycle. The new
same-stage assertion uses one stage and one arrow, rather than that two-stage assertion,
and omits the representative-existence part of the colimit universal property.
Static retry review checked the Mathlib isColimitOf' signature, the lift signature,
the cocone legs, and the filtered-over instance: the proposed combination fits those
interfaces, but this is not a compiler validation. import_direction.py confirmed the
affine lifting import has no cycle. The unit sk-thm-iff realizes its statement and
step at lemma-weil-pbc-property-iff-acyclicity; this auxiliary reduction does not
bypass that unit realization. The original item's blueprint ancestor is null; the new node records the strict-henselian
H0 ancestor carried by affine lifting and the surrounding continuity chain.

## New nodes

lem-weil-pbc-affine-section-same-stage-equality states only equality detection for two
sections at one stage. Its proof follows 09YN and unit-compatible affine-site transport;
it must not be proved by importing this item or its downstream eventual-equality theorem.
Searches ran through msearch: LeanSearch was unavailable; LeanFinder returned section
extensionality and structure-sheaf continuity, not this arbitrary-set assertion; grep
found the Mathlib filtered-colimit recognition criterion. Blueprint search for sections
found continuity for module sheaves but no independent same-stage set-valued assertion.

## Second reading by N2

1. PASS: Compared every delivered existing module with the repository using diff.
   The item changes only proof imports and its theorem body; the theorem signature
   and docstring are byte-for-byte unchanged. The stage diagram and cocone copies
   are byte-for-byte unchanged, including their explicit data constructions. There
   are no statement/definition changes or change records.
2. PASS: Compiled all four modules in import order with lcompile.py, without errors
   or warnings. The only delivered sorry is the named new equality theorem. Checked
   forbidden declarations and attributes; none occur. Explicit #print axioms probes
   for the item, the equality lemma, the diagram and the cocone report only propext,
   Classical.choice, Quot.sound and sorryAx from open dependencies. Neither diagram
   nor cocone chooses data from a mere unproved existence theorem: their data is
   explicit, with only functor/cocone laws supplied by a named theorem.
3. PASS: The new lemma supplies only the injectivity condition of the filtered-set
   colimit recognition theorem, while existing affine lifting supplies surjectivity.
   It is strictly a part of the argument, not the colimit theorem renamed. Checked
   empty objects, constant identity systems and singleton index categories; identity
   arrows give the asserted equality. Read Stacks 09YN and 0EYL online: the former
   is the varying-site section formula for sheaves, including set-valued sheaves;
   09YQ is an abelian cohomology theorem and is contextual, not the set-valued premise.
   The docstring and matching new node give the transport argument and thinness step.
   Searched afresh with LeanFinder for injectivity detected at a finite index and
   Loogle for isColimitOf', plus rg on Sheaf and the upstream library. Hits concern
   structure sheaves or fixed-site/module-valued sections. The apparent set-valued
   eventual-equality match imports this item and cannot be used without a cycle.
4. PASS: Checked the Mathlib recognition theorem and the direction of both equalities
   and the opposed arrow. All new proof imports are used: affine lifting, same-stage
   equality, the Over cofiltered instance from Filtered.Final, and the Types criterion.
   Public imports are unchanged and needed by signatures. No shorter independent
   theorem was found. All old direct DAG dependencies are now explicitly listed under
   No longer needed; they are not claimed globally pruned. Read sk-thm-iff.realized:
   its statement and step stay at lemma-weil-pbc-property-iff-acyclicity. This auxiliary
   decomposition changes no unit realization or chapter route.
5. PASS: The item's two proof steps and proof_deps match the two geometric theorem
   applications in Lean; proof_origin names the Mathlib combination. Checked the new
   node's signature, statement dependencies, source, proof plan, search evidence,
   creation metadata, blueprint, chapter/unit and Lean record. The new hole agrees
   with the report. Existing node fields outside stage-3 ownership stay unchanged.

Second reading changed only this report: made hole counts and declaration names
explicit, enumerated every removed old direct proof dependency, and recorded the
independent checks. No Lean proof or statement required repair. Net holes closed
minus added is zero; this delivery is a decomposition, not a net proof.
