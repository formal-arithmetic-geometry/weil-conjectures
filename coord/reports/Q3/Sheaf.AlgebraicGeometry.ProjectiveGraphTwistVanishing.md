## What changed

Repair of the import-pruning return: removed the two duplicate private declarations
`AlgebraicGeometry.Scheme.Modules.tensorPullback_invertible` and
`AlgebraicGeometry.Scheme.Modules.homOfGlobalSection_appTop_one` entirely. The
coordinate-chart proof now uses the existing proved
`AlgebraicGeometry.tensorPullback_invertible` and
`AlgebraicGeometry.homOfGlobalSection_appTop_one` from
`Sheaf.AlgebraicGeometry.ProjectiveAmpleInvertible`. Its `import all` exposes those
private helpers without changing any public import or existing public signature.
Updated the parent's first proof step and proof dependencies to record this reuse.
The second-reading section below records the previous delivery, before this repair;
the fresh independent second reading of this repair is recorded at the end.

Proved the original body of
`AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_graph_twist`
from one strictly local vanishing statement, keeping its signature and public imports
unchanged. Added only ordinary proof imports and proved private helpers in its module.
No definition, existing statement, other module, or target was changed.

The geometric part is actual Lean: the finite coordinate charts and their coordinate
sections prove affine-base ampleness; uniqueness of tensor-pullback adjoints compares
tensor and ordinary pullback. The closed graph and its restriction over each affine
open give the precise isomorphism to the specified integral twist. This extends the
coordinate-chart argument in ProjectiveAmpleInvertible locally to arbitrary finite
coordinate types without changing that module. It avoids coordinate reindexing and
also includes empty coordinates.

The global part is also actual Lean: prove coherence of the tensor unit, choose
thresholds on affine opens, obtain a finite subcover by compactness, take their Finset
supremum, glue zero restrictions with `Modules.isZero_of_iSup_eq_top`, and transport
through the higher-direct-image image of the left unitor.

Added `Sheaf.AlgebraicGeometry.AffineOpenTwistVanishingIndependent`, containing just
vanishing restricted to one specified affine open. Its statement has arbitrary F and
L, no graph or projective-embedding hypothesis, and no uniform bound over the base.
Updated the parent's proof and dependency records to describe the written proof.
The unit route (projective graph, Serre vanishing, finite affine cover) is retained.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_graph_twist`
(node `lem-pc-m1-projective-graph-twist-vanishing`). Its module has no remaining `sorry`.
Every private helper is proved, including affine chart ampleness and graph restriction.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_twist_on_affine_open`
(node `lem-pc-q3-affine-open-twist-vanishing-independent`). This is exactly the
single-affine-open cohomological step; its entire proof is `:= by sorry` and its
source and proof in words are in its docstring and node. The hole does not include
projective-graph ampleness, finite-cover selection, maximum bounds or global gluing.
Those are proved in the parent. This delivery is a decomposition (one hole closed,
one added, net zero), not an unconditional axiom-closed proof of the target.

Both delivered modules compile in import order without warnings. No arbitrary data
is chosen from mere unproved existence: the tensor-pullback adjunction is compared
with the usual adjunction by uniqueness of left adjoints, giving precisely the
isomorphisms used here. There are no new definitions and no data holes.

## No longer needed

The fresh second reader also removed the redundant direct proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`: the unchanged public
import of `WeilConjectures.AlgebraicGeometry.Modules.Invertible` already supplies
its declarations, including `isZero_of_iSup_eq_top`. The repaired parent compiled
cleanly after removal. No public import was changed.

This repair removes the duplicate helper proofs rather than adding aliases.
The direct proof import of `Sheaf.AlgebraicGeometry.SectionNonvanishingZeroLocus`
is replaced by `import all Sheaf.AlgebraicGeometry.ProjectiveAmpleInvertible`.
Also removed direct proof imports of
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection`,
`Sheaf.AlgebraicGeometry.AmpleIso`, and
`Sheaf.AlgebraicGeometry.NonvanishingTensorPullback`: the new import supplies their
needed declarations. These nodes remain mathematical dependencies; no claim of
global pruning is made for these four modules. The repaired parent has three
private proved helpers instead of five. Both delivered modules compile without
warnings after all four redundant direct imports are removed.

The original module had no proof-only imports to remove. The second reader removed
three redundant added proof imports: `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`,
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`, and
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`. Their needed declarations
remain available through the public imports of CoordinateSection and
NonvanishingTensorPullback; their nodes remain mathematical proof dependencies.
The attempted RelativeSerreVanishing import was removed before delivery because it
would close an import cycle.

The parent no longer needs `lem-pc-chow-relative-ample` or its module
`Sheaf.AlgebraicGeometry.ChowRelativeAmple`. In particular, its geometric and twist
component modules are not imported for this proof. The parent directly proves the
closed-graph and affine-local ampleness clauses that it needs. The old reindexing
step is unnecessary: finite standard charts work for every finite coordinate type.
This is pruning for this item's route; it makes no claim about other target branches.

The old direct dependencies `lem-weil-pbc-coherent-serre-vanishing` and
`lem-pc-restrict-derived-direct-image-open` are now in the new affine-local node's
proof plan rather than the parent's direct dependency list. They remain needed
mathematically and are not claimed as globally pruned.

`RelativeSerreVanishing`, `CoherentSerreVanishing`, `Cohomology.DirectImage`,
`Cohomology.DirectImage.FiniteFreeComplex`, and the proper-coherence modules are
not imported by either delivered module. Their mathematical statements are not
claimed redundant elsewhere.

## Where the brief, the DAG or earlier work was wrong

The previous delivery copied two helper proofs that the library already had with
identical statements. The maintainer's return correctly requires reusing them.
They are private, so the repair uses `import all` and qualified names. The import
cycle check accepts this import. No interface change or forced adaptation is needed.

The stated ChowRelativeAmple interface requires the base morphism g to be proper,
whereas this item only assumes it separated; it also fixes ULift (Fin (m+1)) and
uses tensor pullback. These are interface mismatches, not false mathematics.
The explicit chart and pullback-comparison proof avoids those extra assumptions.

The existing RelativeSerreVanishing theorem has the right mathematical interface,
but its import of Cohomology.DirectImage reaches DirectImage.FiniteFreeComplex,
IntegralIdealProperCohomology, ChowFiniteCohomologyWitness,
ChowTwistFiniteCohomology, and this very module. The import-direction check refuses
that cycle. CoherentSerreVanishing likewise reaches this module through
ClosedImmersionSerreVanishing, AffineMorphismCohomologyEdge,
Cohomology.DirectImage.AffineMorphism, and the same proper-coherence chain.
Neither may be imported here despite their intended lower position in the DAG.

The new affine-local node records this problem: its future proof must use an
acyclic implementation of affine Serre vanishing and the open-restriction
comparison, without importing the existing proper-coherence chain. Its
mathematical proof-dependency DAG does not reach the parent; the problem is the
broader Lean module imports. No unheld module was adapted to work around it.

LeanSearch was unavailable (HTTP internal error); the recorded LeanFinder and grep
searches gave no matching vanishing theorem. The Stacks statements were checked
at Tags 02O5, 02O1, 0B5T and 01PS. The generic coordinate proof follows the already
proved library ProjectiveAmpleInvertible implementation.

## New nodes

`lem-pc-q3-affine-open-twist-vanishing-independent` is the strict affine-local part
of the Tag 02O1 argument, before the finite-cover maximum. It is stated in
`lean/Sheaf/AlgebraicGeometry/AffineOpenTwistVanishingIndependent.lean` and recorded
in `dag/nodes/sec-picard-framework/lem-pc-q3-affine-open-twist-vanishing-independent.json`.
It has one named public theorem, its exact signature, source, complete proof plan,
three kinds of Mathlib search, and the parent's chapter and unit. Empty affine
opens give zero restrictions; degree zero is excluded, and the threshold applies
to all positive degrees using the finite affine Cech bound. No change record is
needed because no existing interface changed.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository: the affine-local module is
   new; the sole existing public theorem's signature is byte-for-byte identical,
   including universes, instances, the integral-model pullback and both quantifiers
   n and q. Its original public imports and docstring are unchanged. The other
   added declarations are private proved helpers. No definitions or targets change,
   and no forced adaptations or change records are needed. Verdict: pass.

2. Compiled both modules in import order with lcompile.py, without warnings. In
   scratch copies printed axioms for all five private helpers, the original public
   theorem and the new affine-local theorem. Each helper uses only propext,
   Classical.choice and Quot.sound; both public theorems additionally use sorryAx.
   The only delivered sorry is the entire proof of the named affine-local theorem.
   There are no axiom/unsafe/opaque/extern/implemented_by commands, data holes,
   definitions, or arbitrary constructed objects from unproved existence. The
   adjunction witnesses used in the geometry are axiom-closed, and left-adjoint
   uniqueness supplies exactly the comparison isomorphisms needed. Verdict: pass
   as a one-for-one decomposition, not an axiom-closed solution.

3. Read Stacks Tags [02O1](https://stacks.math.columbia.edu/tag/02O1),
   [0B5T (4)](https://stacks.math.columbia.edu/tag/0B5T) and
   [02O5](https://stacks.math.columbia.edu/tag/02O5) directly. The new statement retains
   Noetherian base, proper morphism, coherent quasi-coherent F and an invertible L,
   but requires ampleness only over the specified affine V and concludes only
   vanishing restricted to V. Properness gives a quasi-compact separated source
   over affine V, so a finite affine Cech cover bounds degrees independently of
   the twist; the maximum of the remaining Serre thresholds works for all q>0.
   The cited affine comparison, quasi-coherence of higher images and affine
   tilde/Gamma counit detect zero, and open restriction gives the conclusion.
   Checked empty V and empty source (threshold zero), zero F, identity morphism
   over an affine scheme, and projective space with its usual twist. Degree zero
   must be excluded, as it is; n=0 is not asserted to vanish unless the chosen
   threshold allows it. No counterexample or missing hypothesis found.
   Repeated LeanFinder and Mathlib grep searches using cohomology of ample line
   bundles and eventual tensor-power vanishing rather than the worker's wording;
   no match. Searched repository and upstream Serre statements: the upstream
   ample theorem is over a field, while CoherentSerreVanishing has the correct
   affine-ring mathematics but its imports reach this item. RelativeSerreVanishing
   likewise closes a module cycle. These cannot supply a short acyclic proof.
   Blueprint searches for Serre and affine twisting found no identical local
   statement. The remaining hole has its source, full prose proof, exact signature
   and node. It excludes both the proved geometry and global gluing, and is
   strictly a part of the argument. Verdict: pass.

4. Read the proof from the public theorem downward: coherence of the unit follows
   from finite presentation on the locally Noetherian source; local thresholds
   are chosen on affine opens; compactness selects a finite cover; Finset.sup
   bounds every selected threshold; isZero_of_iSup_eq_top glues; higherDirectImage
   maps the left unitor to remove the unit. In the geometry, separatedness of g
   supplies the closed graph, base change supplies its restricted closed immersion,
   and pullback composition identifies its twist with the specified integral
   pullback. The finite coordinate chart argument includes empty N without
   reindexing. Reviewed the existing ProjectiveAmpleInvertible proof: its fixed
   coordinate and affine-base interfaces do not directly cover this local helper.
   Removed the three redundant imports named above and recompiled successfully.
   All seven remaining added proof imports serve explicit declarations in this
   proof. No longer needed lists all three old proof_deps: ChowRelativeAmple is
   bypassed, while Serre vanishing and open restriction move to the local node's
   proof plan. The unit sk-thm-picard-coherence still follows the 02O5 projective
   graph/Serre route; its realized fields are empty and unchanged. Verdict: pass.

5. Checked the parent's four proof steps against the actual helpers and gluing
   argument, and both nodes' proof_deps against the union of step uses. The new
   node's Lean statement matches its theorem verbatim. Read the cited proper
   base-change, coherent Serre, affine cohomology/sections, finite-support and
   affine tilde/Gamma statements: they supply the facts claimed in the local
   proof plan; open restriction is used after taking cohomology. Traversed the
   new node's mathematical proof dependency closure (763 nodes): it does not
   reach the parent. Corrected the new node's blueprint.from.node from the
   non-blueprint parent to lem-pc-coherent-hi, with the graph-twist vanishing
   sentence as place and the intermediate ancestry in via. Existing node fields
   outside lean/proof/proof_deps/proof_origin remain unchanged. Verdict: pass.

Second reading changed only three redundant proof imports, the new node's
blueprint ancestry, and this report. No proof body, existing statement or
remaining-hole statement was changed. One original hole closed, one local hole
added, net zero; the geometric helpers are axiom-closed.


## Second reading by Q3

Fresh independent reading of the import-pruning repair, 2026-10-13. The earlier
second-reading section describes a superseded round and is not this verdict.

1. Compared the complete parent with the repository using diff and compared its
   existing theorem signature as literal text: byte-identical. Universes, finite
   coordinate type, Noetherian base, separated g, proper p, closed j, triangle
   equality, injective resolutions, integral pullback and both n/q quantifiers
   are preserved. The original public imports and docstring are unchanged. The
   affine-open module is new; there are no changed definitions, other existing
   modules, change records or target interfaces. Verdict: pass.

2. Compiled both delivered files in import order with lcompile.py, without
   warnings. Printed axioms in sandbox scratch copies for all three private
   helpers and both public theorems. Each geometric helper has only propext,
   Classical.choice and Quot.sound. Both public vanishing theorems additionally
   have sorryAx, explained by the sole new named affine-open hole. There is no
   sorry in the parent, no data definition, no forbidden axiom/unsafe/opaque/
   extern/implemented_by construct, and no arbitrary witness from an unproved
   mere existence theorem. The chosen tensor-pullback adjunction comes from the
   proved adjunction theorem, and left-adjoint uniqueness gives the comparison.
   Verdict: pass as a decomposition, with one original hole closed and one added.

3. Read the new statement and its node against Stacks
   [02O1](https://stacks.math.columbia.edu/tag/02O1),
   [0B5T](https://stacks.math.columbia.edu/tag/0B5T) and
   [02O5](https://stacks.math.columbia.edu/tag/02O5). Over V the morphism remains
   proper over an affine Noetherian base, F remains coherent/quasi-coherent,
   and the hypothesis is exactly ampleness of the invertible restriction.
   Tag 0B5T (4) gives degreewise thresholds; the finite affine Cech cover of the
   separated quasi-compact source bounds all positive degrees independently of
   n, so a finite maximum suffices. Affine-base comparison and quasi-coherence
   detect zero; open restriction and tensor compatibility give the conclusion.
   Checked empty V/source, zero F, identity over an affine scheme and the usual
   projective twist. q=0 is correctly excluded; n=0 is not asserted below the
   existential bound. The local hole excludes the actual graph geometry and
   global gluing, so is strictly part of the argument, not a renamed parent.
   Repeated LeanFinder, Loogle and Mathlib grep searches with eventual coherent
   cohomology/ample tensor-power wording, and searched both Lean roots. No
   matching acyclic shortcut found. Read CoherentSerreVanishing and upstream
   Cohomology.Serre: the former and RelativeSerreVanishing would close import
   cycles (verified by traversing imports); the upstream ample result is over
   a field. The remaining theorem cannot be closed in a few minutes by these
   interfaces. Its docstring supplies the source and full proof in words, and
   its matching node has the required fields and prior three-kind searches.
   Verdict: pass.

4. Read top-down: graph ampleness supplies each affine restriction; coherence
   of the tensor unit follows from finite presentation over a locally Noetherian
   source; local thresholds feed a compact finite affine subcover and Finset.sup;
   isZero_of_iSup_eq_top glues, and the higher-image left unitor removes the unit.
   The geometry uses the separated graph lift, base-change closed immersion,
   and explicit composition/restriction isomorphisms of the integral twist.
   Its finite coordinate charts also handle empty N. The returned duplicate
   helpers are absent and reused from ProjectiveAmpleInvertible via import all.
   Removed the redundant added proof import of Modules.Sheaf, available through
   the unchanged public Modules.Invertible import, and recompiled cleanly.
   The three remaining proof imports supply the local vanishing, coherence
   criterion, and coordinate/adjunction helpers. No longer needed accounts for
   every old proof_deps: ChowRelativeAmple is bypassed; Serre vanishing and open
   restriction move into the local node's plan. The graph/Serre/finite-cover
   route of sk-thm-picard-coherence is retained; its realized record is unchanged.
   Verdict: pass.

5. Checked both nodes' proof_deps equal the unions of their steps' uses, the new
   Lean statement is verbatim, and the parent's only changed fields are proof,
   proof_deps and proof_origin. The parent's chart/restriction/coherence/gluing
   steps follow the actual proof. The new node's blueprint ancestry points to
   lem-pc-coherent-hi via the recorded graph/Chow intermediates; its chapter and
   unit match the parent. Traversed its mathematical proof dependency closure:
   676 nodes, none reaching the parent. The module-cycle obstruction is recorded
   rather than worked around by changing an unheld module. Verdict: pass.

Second reading changed only one redundant proof import and this report. No
proof body or theorem statement changed. Closed:
AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_graph_twist.
Added hole:
AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_twist_on_affine_open.
This remains a one-for-one decomposition, net zero, with three axiom-closed
geometric helpers and the ChowRelativeAmple route pruned for this item.
