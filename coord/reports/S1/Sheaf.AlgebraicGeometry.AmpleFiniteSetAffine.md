## What changed

Proved `AlgebraicGeometry.Scheme.exists_affineOpen_of_isAmple` in
`Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine`, with its signature and visibility unchanged.
Added the fully proved private helper `exists_basicOpen_between_finite_and_open`:
for a finite subset of an open W in Proj, graded prime avoidance produces one
positive-degree standard open containing the subset and contained in W.
The ideal is explicitly the span of all positive-degree homogeneous generators
whose standard opens lie in W. Its homogeneity, containment in the irrelevant
ideal, noncontainment in the point primes, and the resulting open containment
are proved in Lean.

The main proof applies the existing ample-to-Proj theorem, takes W to be the
coborder of its image, and pulls the affine standard open back along the
closed immersion into W. Added the proof-only import
`Mathlib.AlgebraicGeometry.Morphisms.Immersion` for this factorization.
Replaced the proof-only basis-wrapper import with
`Sheaf.AlgebraicGeometry.ProjStandardOpenProperties`; its already proved basis
clause is enough, and Mathlib proves affineness of a positive-degree chart.
Updated the item's DAG proof and proof dependencies to this argument.

Source checked: Stacks `properties.tex`, label
`lemma-ample-finite-set-in-affine` (Tag 01ZY), case (3) reduced to case (4),
including the boundary and prime-avoidance argument. The local literature copy
is in `/home/ubuntu/work-bp/sheaf/literature/stacks-project/properties.tex`.
The unit record `sk-thm-curveestimate` and its source were read; this changes
only a below-unit proof, retaining the ample-to-Proj and prime-avoidance route.

## Proved and sorry left

Closed 1 of 1 item holes:
`AlgebraicGeometry.Scheme.exists_affineOpen_of_isAmple`
(node `lem-sc-ample-finite-set-affine`). No sorry remains in the delivered module.
Added 0 holes and 0 public declarations. The private helper is fully proved.
This is a proof from existing dependencies, not a decomposition into new holes.

Existing dependencies still containing sorry, not modified by this delivery:
`AlgebraicGeometry.exists_isOpenImmersion_proj_of_isAmple`
(node `lem-sc-ample-proj-open`) and
`HomogeneousIdeal.exists_homogeneous_mem_notMem_of_isPrime`
(node `lem-sc-graded-prime-avoidance`).

Edge cases: empty E uses the empty finite family of primes, which the avoidance
theorem explicitly permits; empty Proj and the zero ring are included. No
nonempty, closed-point, Noetherian, or separated hypothesis is introduced.
The boundary factorization works for arbitrary open immersions, and the
containment argument uses only the ideal span and the definition of D_+(f).

Validation: the final module compiles with the prescribed local compiler
without errors or warnings. `deliver3.py S1
Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine --no-push` printed OK: compilation
and preflight passed except for the independent second reading, which the
second reader supplies. Nothing was pushed.

## No longer needed

Removed import `Sheaf.AlgebraicGeometry.ProjStandardOpenBasis` and direct proof
dependency `lem-sc-proj-standard-open-basis`. That unproved wrapper is unnecessary
on this route: the proved `Proj.standardOpenProperties` basis clause and Mathlib
`Proj.isAffineOpen_basicOpen` supply its two parts directly. Its underlying module
`Sheaf.AlgebraicGeometry.ProjStandardOpenProperties` and node
`lem-weil-pbc-proj-standard-open-inclusion` remain needed.
No other modules or nodes are pruned. The finite selection of chart generators
in the previous plan is unnecessary because graded prime avoidance assumes
finiteness only of the prime family, not of the ideal's generating set.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid. Its finite generator selection is
unnecessary, and its final closed-immersion argument is already implemented by
Mathlib's coborder factorization and affine-preimage results. The original
statement is retained; the second reader updated the proof docstring to match the implemented route; the DAG now records the precise
implementation. No interface corrections or forced adaptations are needed.

Searches actually run: LeanFinder query about a finite subset on an ample scheme
returned affine-local and Proj chart lemmas but no exact theorem; Loogle query
`IsAffineOpen, IsClopen` failed to resolve the unqualified identifier; grep query
`isClopen.*[Aa]ffine|[Aa]ffine.*isClopen|finite.*basicOpen` found no exact theorem.
Direct source searches located the already proved standard-open basis clause
and the coborder affine-preimage proof. No new nodes were introduced.


## Second reading by S1

1. PASS: compared the sole delivered module and node against the repository with diff.
   The existing theorem signature is byte-for-byte unchanged; visibility and the sole
   public import are unchanged. No definitions, target statements or change records
   are added. Only proof fields of the existing node change.
2. PASS: independently compiled the file with lcompile.py (no errors or warnings).
   The module contains no sorry, axiom, unsafe, opaque, implemented_by or extern, and
   introduces no definition. Scratch-copy #print axioms checks on the private helper
   and public theorem give exactly propext, Classical.choice, Quot.sound and sorryAx.
   The latter is expected from the existing graded-prime-avoidance and ample-to-Proj
   dependencies, not a new hole. The ideal is explicitly constructed as Ideal.span;
   the existential witnesses are used inside proofs, never to define arbitrary data.
3. PASS: zero statements split off and zero new holes. Read the helper line by line:
   the basis supplies a generator avoiding each point prime, span_le supplies the
   converse containment outside W, and avoidance supplies the positive-degree chart.
   Empty E allows f = 0 in degree 1; empty Proj and zero rings are included. A singleton
   reduces to an ordinary standard chart; no closed-point or separatedness assumption
   enters. Independently searched Mathlib via msearch grep with
   finite.*subset.*affine|affine.*neighbou?rhood|basicOpen.*Finite|Finite.*basicOpen,
   and searched the upstream and Sheaf geometry sources with ample/finite terms.
   No exact replacement was found (curve and finite-type results have extra hypotheses).
4. PASS: read Stacks properties.tex, lemma-ample-finite-set-in-affine, and the unit
   sk-thm-curveestimate record and source. The route stays below the unit statement;
   ample-to-Proj and graded prime avoidance remain used. Each proof-only import is
   actually used and remains plain import. The only old proof_dep removed is
   lem-sc-proj-standard-open-basis, fully listed under No longer needed. No further
   pruning or short proof was found. The unit realized record is preserved.
5. PASS: the node's proof, proof_deps and proof_origin match the implemented basis,
   generated-ideal avoidance and coborder pullback argument. Read Mathlib's
   liftCoborder construction and its closed-immersion instance. No new node is needed
   for a split-off hole because none is introduced.

Second reading changed only the existing theorem's proof docstring: removed the stale
citation to the pruned basis wrapper and described the all-generators ideal and coborder
factorization actually used. No proof, signature, definition, import or DAG repair was needed.
