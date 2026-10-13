## What changed

Replaced the zero/positive-cardinality split with the actual acyclic-resolution argument in
`Sheaf.AlgebraicGeometry.FiniteAffineCechModelDerivedComparison`. Its existing theorem signature,
visibility and docstring are unchanged. All original public imports are retained because they occur
in the signature. The new resolution theorem, `PlusHomology` and `PlusCompatibility` are imported
privately for this proof.

Added `Sheaf.AlgebraicGeometry.FiniteAffineCechModelAcyclicResolution`, containing one named geometric
hole: an augmented complex of acyclic module sheaves whose ordinary pushed complex is chain
isomorphic to the specified section model. The main proof now extends that resolution by zero,
applies the existing bounded-below acyclic-unit theorem, transports along the existing unbounded
compatibility isomorphism, and composes with the localized augmentation and chain isomorphism.
It keeps the independently supplied source and target derived localizations throughout.

Removed both proposed cardinality-case modules and their nodes. Corrected the target node's proof,
proof dependencies and proof origin. Added a node attachment to the exact existing public
acyclic-unit theorem, without adding another Lean declaration for it.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Scheme.Modules.finiteAffineCechModel_derivedComparison`
(node `lem-pc-finite-affine-cech-model-derived-comparison`) by a complete Lean reduction.

Added one hole, `AlgebraicGeometry.Scheme.Modules.exists_finiteAffineCechModel_acyclic_resolution`
(node `lem-pc-finite-affine-cech-model-acyclic-resolution`). Its entire proof is `by sorry`, with the
construction and complete natural-language proof in its docstring. No other delivered declaration
contains sorry. The proposed `finiteAffineCechModel_derivedComparison_zero` and
`finiteAffineCechModel_derivedComparison_positive` holes were removed before delivery.

This is a decomposition: one original hole closed and one lower hole added, net zero holes closed
against the repository baseline. It does not claim the total derived comparison is sorry-free.
The completed part is the derived comparison from an ordinary acyclic resolution; the remaining
statement contains no derived localization or total derived isomorphism.

Both delivered files compile cleanly with lcompile.py. A scratch copy with `#print axioms` shows
only propext, Classical.choice, Quot.sound and sorryAx for the delivered declarations. The reused
acyclic-unit theorem and unbounded compatibility have only the three permitted standard axioms.
There are no axiom, unsafe, opaque, extern or implemented_by declarations and no new definitions.
Existential resolution witnesses occur only as local witnesses inside the main theorem's proof.

## No longer needed

No original public import was removed. No module is claimed pruned from the targets' import closure.

The target's old direct proof dependencies `def-pc-finite-affine-cech-model`,
`lem-pc-affine-open-pushforward-acyclic`, `lem-pc-alternating-cech-computes`,
`lem-pc-cech-sheaf-resolution`, `lem-weil-pbc-separated-affine-open-intersection`, and
`lemma-weil-pbc-leray-acyclicity` are no longer direct dependencies of its proof. The geometric ones
are retained below the new resolution node; the model definition remains a statement dependency
and public import. Leray acyclicity is retained below the new exact acyclic-unit source node.
`src-right-derived-functor-plus-compatibility` remains a direct dependency.

The undelivered zero/positive-case modules and nodes are removed, not counted as library pruning.

## Where the brief, the DAG or earlier work was wrong

The first worker's case split did not carry out any of the general argument: the positive-cover
statement retained its entire conclusion and excluded only the degenerate cover. The two
auxiliary docstrings and node statements were incomplete, their purported searches were not
sufficient evidence, their Lean statement strings contained literal Unicode escape sequences,
and the target node was not updated to follow its changed proof. They are superseded here.

The existing `CechSheafResolution` declaration gives the unnormalized resolution, not a chain
comparison to the increasing-tuple model. `AffineAlternatingCechResolutionCore` needs a universal
family of derived localizations and extra base-change data. Neither states the new underived
resolution lemma with these hypotheses. Importing `CechResolution` or
`AffineOpenPushforwardAcyclic` here creates a real import cycle through
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`, `FiniteFreeComplex`,
and the proper-flat model modules back to this item. Those modules were not imported or adapted.
Their geometric conclusions are recorded in the lower node's mathematical proof plan.

The source's existing acyclic-unit theorem was mentioned in another node's proof but lacked its
own statement attachment. It is now recorded explicitly rather than attributed to the weaker
homology-only statement of the Leray node. No library tooling or repository files were edited by
hand, and no other agent was started.

## New nodes

`lem-pc-finite-affine-cech-model-acyclic-resolution` states the geometric, ordinary-complex part
of the original proof. It requires no derived localizations. Its proof plan retains the sheaf
resolution, ordered comparison, affine-intersection and affine-open acyclicity route, and names
the existing tilde-Gamma adjunction and pushforward comparison nodes for the term identifications.
LeanSearch was unavailable; fresh LeanFinder and Loogle queries and source grep are recorded.

`src-right-derived-functor-plus-acyclic-unit` attaches the existing closed theorem
`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic` in the source-library
`PlusHomology` module. Its statement records exactly the assumptions on both abelian categories,
enough injectives in the source, additivity, left exactness, derived localizations, boundedness
below and termwise right acyclicity. It adds neither Lean code nor a hole.

No statement or definition changes and no change records are required.

## Second reading by E1

1. Compared the original and delivered target with diff, and programmatically compared the exact
   theorem signature substring through `:=`: byte-for-byte identical. The two HasDerivedCategory
   universe parameters remain independent; f, F, cover, affineness, separatedness, quasi-compactness
   and quasi-coherence hypotheses are all unchanged. There are no adapted modules or changed
   definitions. Verdict: pass after replacing the vacuous cardinality reduction.

2. Compiled the original three proposed files, then both repaired delivered files, in import order.
   The repaired files compile cleanly. Inspected all bodies for forbidden declarations and sorry;
   the only delivered sorry is the listed resolution theorem. Compiled the scratch copy with
   explicit axiom printouts for both delivered declarations and both reused comparison results.
   The lower hole accounts for sorryAx; the two source comparison results are sorry-free. Verdict:
   valid decomposition with its remaining dependency reported, not a sorry-free total proof.

3. Read the existing CechSheafResolution, CechResolution, AffineOpenPushforwardAcyclic,
   AlternatingCechComputes, AffineAlternatingCechResolutionCore, FiniteAffineCechModel and source
   PlusHomology/PlusCompatibility declarations. Independently searched with the increasing-tuple
   resolution and acyclic-unit queries in the new nodes, rather than trusting the first report.
   Checked the source pages for Stacks Tags 01XB, 01XD, 01FK, 01FM, 01EO and 01I6. The lower theorem
   is a genuine pre-localization construction: its conclusion specifies an actual chain
   isomorphism and termwise ordinary acyclicity, without asserting the target's derived isomorphism.
   For r=0, iSup of the empty family is bottom, so the cover forces X empty and both complexes zero.
   For r=1, the sole cover open is top; X is affine and the degree-zero model is ordinary f_*F,
   with higher terms zero and affine acyclicity. For F=0 or empty tuple intersections the products
   are zero. For repeated cover members the increasing-tuple insertion contraction still applies;
   when p+1>r the index type is empty. Verdict: true and strictly a part of the argument; its
   natural-language proof and complete node are supplied. The closed acyclic-unit theorem is reused,
   not restated as new Lean code. No arbitrary witness defines data.

4. The main proof now implements the existing acyclic-unit theorem and bounded-below/unbounded
   compatibility directly. Its isomorphisms have the right endpoints and orientations: the final
   composite is Q(C) to Q(f_*K) to Rf_*(QK) to Rf_*(F[0]). The new geometric lemma carries the
   remaining section/sheaf comparison rather than the whole derived result under a new name.
   All imports are needed by signatures or proof references; the removed draft helpers are gone.
   Checked dag/units/sk-thm-picard-coherence.json: the realized fields are empty and unchanged.
   The affine Cech route is retained; no unit step is replaced. Verdict: pass, with net-zero hole
   progress reported and no modules claimed pruned.

5. Updated the target's proof plan to the actual three-step Lean reduction. Its proof_deps is
   exactly the union of the steps' uses. Both new nodes have source, self-contained statement,
   dependency lists, proof steps, proof origin, three search kinds, created/blueprint/chapter/unit
   fields and a Lean attachment. The lower theorem's recorded signature is copied verbatim from
   the file; the source node points to the existing theorem and documents its section parameters.
   Verdict: pass after repairing the omitted target-node update and replacing the deficient nodes.

Changes made by this second reading: removed both zero/positive restatements and their nodes;
added the underived acyclic-resolution lemma and its proof docstring; completed the real derived
comparison using the existing source theorems; attached the precise closed acyclic-unit node;
updated the target DAG plan; and replaced the inaccurate progress and pruning report.
