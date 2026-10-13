## What changed

Proved `AlgebraicGeometry.bounded_graded_module_map_descent` from the existing
one-module and one-map descent theorem. Two new proved helpers separate the
construction of a bounded model family from descent of its successive maps.
The target conjugates each desired map by the term comparisons, applies the map
helper, and proves the final commuting equation by composing comparisons and
cancelling inverse isomorphisms. Its signature and public imports are unchanged.
No existing definition or statement was modified; no adaptations are required.

The family helper constructs zero terms as the free sheaf on PEmpty, proves their
finite presentation via finite locally free data, and chooses a common upper stage
for the finite supported family. Tensor pullback preservation and the composition
isomorphism supply the term properties and comparisons.

The map helper uses finite-set induction: descend one more conjugated map, pull
all previous data to that new stage, and preserve their comparison equations by
naturality of the inverse comparison. Applying this to [a,b-1] handles the finitely
many interior maps. Outside this interval, a zero source or target gives the
required equation. This avoids a separate multiple-transition coherence lemma.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.bounded_graded_module_map_descent`, node
`lem-pc-bounded-graded-module-map-descent`.

Also proved both new public helper theorems:
`AlgebraicGeometry.bounded_graded_family_descent`, node
`lem-pc-bounded-graded-family-descent`, and
`AlgebraicGeometry.bounded_graded_map_compatibility`, node
`lem-pc-bounded-graded-map-compatibility`.

No sorry remains in any delivered module; no new hole is added. These proofs use
the existing `finitePresentation_module_map_descent` and tensor-pullback interfaces,
whose upstream dependencies remain tasks in the existing DAG. This delivery does
not claim to close those upstream dependencies or the overall target closure.
All new definitions are concrete private functors or canonical comparisons.
Stage/model witnesses are eliminated within theorem proofs, never chosen as data
in a definition from a mere unproved existence statement.

All three modules compile in import order without warnings using lcompile.py.
The delivery dry run also checks every declaration with its axiom probe.

## No longer needed

Removed the target's direct proof imports
`Sheaf.AlgebraicGeometry.FinitePresentationModuleMapDescent` and
`Sheaf.AlgebraicGeometry.TensorPullbackFinitePresentation`; their declarations
are used in the two new helpers instead. The original target dependencies
`lem-pc-fp-module-map-descent`, `lem-pc-tensor-pullback-finite-presentation`,
and `def-pc-module-pullback` remain needed in the helpers' proofs.

The map helper does not use a separate associativity coherence theorem or the
canonical-comparison equality returned by one-map descent. It uses naturality of
the returned inverse natural isomorphism at each induction step.
`def-pc-tensor-pullback-composition-iso` is required only by the family helper's
explicit comparison. No existing node or module becomes globally unreachable;
there are no whole modules pruned. All delivered proof imports serve the actual
proofs, and each node's proof/proof_deps records that proof.

## Where the brief, the DAG or earlier work was wrong

No error in the original statement or DAG argument was found. An unpublished
scratch map statement initially demanded descent at the original model stage;
Tag 01ZR clause (2) allows enlargement. This was corrected before delivery. The
final helper includes k ≥ j, and the proof repeatedly enlarges the stage.

Read Stacks Tag 01ZR, Lemma 32.10.2 clauses (1) and (2), at
https://stacks.math.columbia.edu/tag/01ZR; read the existing Lean signatures and
their nodes. The unit sk-thm-picard-semicon has empty realized statement/step lists;
this construction retains its finite-presentation descent route.

Checked empty and singleton intervals, zero families, boundary maps, zero rings
and empty schemes. The index i provides Nonempty I. For empty support, the family
is explicitly zero at some stage above i. For singleton support all successive
maps have a zero source or target. No affine hypothesis on Xi is introduced,
and no square-zero equation is used or asserted.

Searches: LeanFinder returned finite-presentation predicates and instances only;
Loogle `Finset, Directed` returned the finite-upper-bound tool, but no sheaf descent
theorem. LeanSearch was unavailable with Internal Server Error. msearch Grep and
rg across both roots found affine graded scalar-extension descent, which cannot
replace this statement for nonaffine Xi. Blueprint searches for bounded graded
and finite-presentation data found no duplicate scheme-family theorem.

## New nodes

`lem-pc-bounded-graded-family-descent`, module
`Sheaf.AlgebraicGeometry.BoundedGradedFamilyDescent`, records the proved bounded
term construction, with no maps in its statement.

`lem-pc-bounded-graded-map-compatibility`, module
`Sheaf.AlgebraicGeometry.BoundedGradedMapCompatibility`, records the proved
finite-set induction for maps between fixed descended term models.

Both nodes carry complete statements, verbatim Lean records, sourced proof steps,
three kinds of search evidence, and the item's chapter and unit. Their blueprint
references follow the existing item's ancestor and descent branch. The original
node was updated only in proof, proof_deps and proof_origin. No change record is
needed, since no existing interface was changed.

## Second reading by P3

1. Compared the delivered target module with the repository using diff and checked
   its theorem signature byte for byte. Only its proof and two private imports
   changed; the public imports, statement, definitions, and docstring are unchanged.
   The two helper modules are new. No change record or adaptation is required. PASS.
2. Read all three modules in full and compiled them in import order with lcompile.py:
   no errors or warnings. No delivered theorem contains sorry, and no forbidden
   axiom, unsafe, opaque, implemented_by, extern, or kernel-check bypass occurs.
   The private definitions are actual base-change functors and a canonical
   composition comparison. Descent witnesses are used only inside proofs, never
   chosen into a public definition. Scratch #print axioms for all three public
   theorems returned only propext, Classical.choice, Quot.sound, and sorryAx.
   Upstream sorryAx is permitted and remains disclosed;
   this delivery closes one local hole, not every upstream dependency. PASS.
3. No statement is split off with sorry. Both new public statements have proofs,
   source references, proof docstrings, and matching nodes. The family helper
   contains no maps; the map helper starts with fixed models. Neither merely
   renames the original item. Checked reversed, empty, and singleton intervals:
   Icc a (b-1) processes exactly the interior maps, and the zero-source/target
   cases cover both boundary maps. The given index supplies a nonempty preorder;
   no nonzero-ring or nonempty-scheme assumption is used. Independently searched
   LeanFinder for finitely many sheaves and arrows over inverse systems, Loogle
   for zero and finitely presented sheaves, msearch grep for simultaneous/finite
   diagram descent, and rg over both Lean roots. The hits concern scheme maps
   or affine scalar extension, not this possibly nonaffine sheaf-family result.
   Checked Stacks Tag 01ZR clauses (1) and (2) against the reductions. PASS.
4. The target first descends terms, conjugates the maps, descends them by finite
   induction, and composes comparisons. Each induction step transports all earlier
   data and uses inverse naturality, so no independent associativity-coherence
   hole is needed. No shorter matching theorem was found. Proof-only dependencies
   use plain imports; public imports supply signature notions. The original three
   proof dependencies are all retained transitively in the helpers, as explicitly
   recorded under No longer needed. No whole module is pruned. The unit record
   sk-thm-picard-semicon has empty realized statement and step lists; its route
   is not bypassed. PASS.
5. Checked that each node's Lean statement exactly matches its declaration and
   proof_deps is the union of proof-step uses. The existing node changes only
   proof, proof_deps, and proof_origin; all new-node required fields are present.
   Traced zero preservation to nonempty_tensorPullbackAdjunction in TensorPullback,
   which belongs to def-pc-module-pullback; the separate canonical-unit theorem
   lem-pc-module-pullback-adjunction is not an additional dependency. PASS.

Changes made by the second reader: clarified that zero preservation uses the
existing module-pullback node in both helper proof records, and corrected the
original node's proof-origin note to call this a complete local proof (one hole
closed, none added), rather than a decomposition with outstanding new holes.
Added this independent review. No Lean proof or signature needed repair.
