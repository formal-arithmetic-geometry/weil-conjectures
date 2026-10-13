## What changed

Replaced the incomplete earlier sandbox split. The original theorem
`AlgebraicGeometry.formalComparison_completed_affine_data` now has a complete Lean proof,
with its signature and public imports unchanged. Its proof imports two new modules:
`Sheaf.AlgebraicGeometry.CompletedAffinePullbackObjects` and
`Sheaf.AlgebraicGeometry.FormalComparisonFlatTransportSquare`.
The second reading added plain proof imports of `FormalSystemsPullback`,
`FlatBaseChangeMapSections` and `FlatBaseChangeResolutionIso` to the remaining
obligation, matching its recorded proof plan and retaining those dependencies.

The first new theorem is proved from existing declarations: it constructs the geometric
pullback objects, coherence, flatness and extended-ideal equality, with no comparison
morphisms as input or output. The remaining obligation is
a generic flat-base-change diagram theorem for already supplied coherent pullbacks; it
has no affine chart or adic completion base and does not assume or construct `α`.
The main theorem explicitly constructs `α₀ = eqToHom(hG) ≫ g*α ≫ δ.inv`, proves its
completion equation by the inverse law, and proves its adjunction equation from the
transport squares and `hα`. The private proved helper `transport_comparison_comp` contains
only the categorical composition calculation, avoiding costly elaboration over the
concrete completed schemes. No existing definitions or statements were changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.formalComparison_completed_affine_data` (node
`lem-weil-pbc-formal-comparison-completed-affine-data`). There is no sorry in the original
module. The private helper `AlgebraicGeometry.transport_comparison_comp` is also proved.

The new theorem `AlgebraicGeometry.completedAffine_pullback_objects` (node
`lem-weil-pbc-completed-affine-pullback-objects`) is proved, as is its private helper
`AlgebraicGeometry.coherent_pushforward`. Flatness and the ideal equality use existing
Mathlib and affine-ideal declarations; the object and coherence proofs use existing
formal pullback and proper direct-image declarations.

Only one strictly smaller obligation is split off, with the whole proof `:= by sorry`,
a source and a full proof in words: `AlgebraicGeometry.formalComparison_flat_transport_square`,
node `lem-weil-pbc-formal-comparison-flat-transport-square`.

This is a decomposition: one original hole closed, one new hole added (net 0).
It is not a sorry-free proof of the transitive dependencies. The main theorem combines
geometric data and diagram data by an actual construction and calculation; neither new
statement is the original theorem with its hypotheses repackaged.

## No longer needed

Removed the unused `Mathlib.AlgebraicGeometry.Modules.Tilde` import from both new
modules. No existing library import or planned dependency is pruned: all five original proof
nodes remain needed below the two new theorems. The original module had only public
imports used by its statement, and all are kept unchanged. The earlier unpublished
`FormalComparisonCompletedAffineDataCore` module, its node
`new-formal-comparison-completed-affine-data-core`, and its proof import are removed from
the sandbox; they were not library modules and are not claimed as library pruning.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox attempt selected `α₀` in its core existence theorem without tying
it to a completion comparison, then left the final completion equation as a sorry in
the original proof. Such arbitrary core data do not supply that equation. The new
split constructs `α₀` after obtaining `δ`, so the completion equation follows formally.
The geometric object construction is now proved from existing declarations. The natural
base-change squares remain the sole new obligation.

The existing formal-system pullback theorem gives an existential completion isomorphism
but does not publicly state its equation with quotient projections. The flat-base-change
statements are resolution-level and use the opposite pullback ordering. They do not
directly provide the ordinary-pushforward natural transformation and mate/quotient
squares used here. These specific missing interfaces, including the projection-order
transport, are spelled out in the remaining obligation and its proof plan. No unit
route is bypassed: this node is below the realized unit steps and retains the original
flat-completion, coherent-pullback, proper-direct-image and natural-base-change argument.

Checked small cases before stating the obligations: unit ideals give zero formal
diagrams, the zero ideal gives ordinary module diagrams, and zero modules, zero rings
and empty schemes cause no additional hypotheses. General flat base changes in the
second obligation need not be faithfully flat: the construction uses only base change
and quotient pullback, and never detects a property by faithfulness of completion.

## New nodes

`lem-weil-pbc-completed-affine-pullback-objects` records the completed chart geometry and
coherent object construction. Its module is `CompletedAffinePullbackObjects.lean`.

`lem-weil-pbc-formal-comparison-flat-transport-square` records the natural quotient and
unit squares for a general flat base change with supplied coherent pullback objects.
Its module is `FormalComparisonFlatTransportSquare.lean`.

Both new nodes are in `dag/nodes/sec-proper-base-change/`, have the parent's unit
`sk-thm-p1`, actual LeanSearch/LeanFinder/grep search records, sources, proof steps and
verbatim Lean signatures. LeanSearch returned HTTP 500 and is recorded as unavailable.
The generic affine ideal-extension theorem is used as an existing closed tool; it does
not replace any unit-level argument. The geometric node now also records the
affine-extension, finite-section and
finite-presentation criteria used by its proof. The parent node is updated only in
`proof`, `proof_deps` and `proof_origin` to describe
the construction now written in Lean. No change record or forced adaptation is needed.

## Second reading by J1

1. Compared the original module with the repository using `diff -u` and separately
   compared the complete text from `theorem formalComparison_completed_affine_data`
   to `:= by`: its signature is byte for byte identical. The existing docstring,
   public imports and all existing definitions are unchanged. The existing node
   changes only `proof`, `proof_deps` and `proof_origin`; no change record is needed.
   Verdict: no visible statement or definition changed.

2. Read all three delivered modules, including the two private proved helpers.
   The only textual hole is the whole proof of the public named theorem
   `AlgebraicGeometry.formalComparison_flat_transport_square`, with its blueprint
   node and detailed source/proof docstring. There are no new definitions, hidden
   proof holes, axioms, unsafe code or alternative implementations. The construction
   of alpha zero is explicit composition with delta inverse; its completion equation
   is the inverse law, and its adjunction equation is the proved categorical
   composition calculation. The geometric objects have exact underlying-object
   equalities; no arbitrary global data are defined from mere existence.
   Local compilation and axiom-check results are recorded below.

3. Read Stacks Tags 088B (completed-base-change paragraph), 0887 (termwise formal
   pullback) and 02KH (flat base change), and the existing declarations
   `exists_formalSystemsPullback`, `flatBaseChangeMap_sections`, and
   `flatBaseChangeResolutionBeta_isIso`. The remaining obligation isolates natural
   base-change and quotient/unit compatibility; it supplies no alpha and assumes
   the geometric objects already given. Thus it is a strict part of the argument,
   not a renamed copy of the original item. Flatness alone suffices: properness
   gives qcqs, and coherence gives quasi-coherence. Quotient pullback is right exact;
   base change applies to F and its quasi-coherent quotients. Naturality with quotient
   projections gives h-kappa-zero, and the mate equation gives the unit square.
   Uniqueness of left adjoints supplies a natural automorphism to accommodate the
   supplied adjunction. For J=0 these are ordinary base-change diagrams; for J=1
   every quotient is zero. Zero modules and empty spectra give zero maps and require
   no extra hypotheses. Also checked identity base change and nonfaithful flat base
   change: no detection-by-faithfulness step occurs.
   Searched the project and upstream source with `rg`, then independently ran
   LeanFinder on natural flat base change compatible with units and quotients,
   grep on baseChange/unit/quotient, and Loogle on `Adjunction.leftAdjointUniq`.
   The results give general adjunction tools, not the missing diagram theorem.
   The resolution-level interfaces and private quotient-projection comparison
   do not close this theorem in a short direct application. Verdict: true, needed,
   strictly smaller obligation; retained as a decomposition, net zero holes closed.

4. Read the original five proof dependencies and `dag/units/sk-thm-p1.json`, including
   `realized`. Neither the item nor its new nodes replace a realized unit statement
   or step. The geometric proof follows completion flatness, ideal extension,
   coherent formal pullback and proper direct image. The parent combines it with
   the remaining flat squares by constructing alpha zero and checking both equations.
   All five old dependencies remain below the new nodes, so no old proof dependency
   or library module is claimed pruned. Statement-facing imports remain public;
   added proof-plan imports are plain. Verdict: the unit route is retained.

5. Read all three node JSON records against their Lean declarations. The parent
   has exactly the two lemmas used by its proof as direct dependencies, plus an
   elementary alpha-transport calculation. The geometric node records the affine
   ideal, completion flatness, coherent pullback, finite-section/finite-presentation
   and direct-image inputs actually used. The square node records the three
   interfaces required by its unfinished proof. New nodes have source, steps,
   dependency union, proof origin, search records, creation/blueprint metadata and
   matching Lean signatures. Verdict: the records follow the code and remaining plan.

Changed only the missing three proof-dependency imports in
`FormalComparisonFlatTransportSquare.lean` and this report. The original proof and
both new statements were retained.

Validation: `lcompile.py --all` compiled all three delivered modules without errors
or non-sorry warnings. A scratch import audit with `#print axioms` for
`AlgebraicGeometry.completedAffine_pullback_objects`,
`AlgebraicGeometry.formalComparison_flat_transport_square`, and
`AlgebraicGeometry.formalComparison_completed_affine_data` compiled successfully;
each lists only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
The geometric theorem therefore also still depends on existing upstream holes,
although its own body and private helper have no sorry. The delivery tool additionally
probes all declarations, including the private helpers. No claim of a sorry-free
transitive proof is made.
