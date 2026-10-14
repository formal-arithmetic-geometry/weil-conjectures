## What changed

Filled `AlgebraicGeometry.pinned_tensor_square_left_summand` along the existing DAG route.
The proof inverts the pinned source injection formula, transports the specified
pullback-stalk components along the tensor-map restriction equation, and applies
`Scheme.Modules.module_pinned_tensor_stalk_square`. It then combines the mapped
pullback tensor injection equation, the bifunctor-map injection equation, tensor-stalk
naturality, and the pinned target injection formula.

Added the proved private helper `summand_chase`, which combines these seven equations
in an arbitrary category and cancels the target isomorphism. Explicit local functor
and component types and extraction of the goal's lets keep elaboration within the
single-file limit. Existing declaration statements, definitions, visibility, imports,
and the DAG route are unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.pinned_tensor_square_left_summand`
(node `lem-pc-pinned-tensor-square-left-summand`), the module's one original hole.
The private helper `AlgebraicGeometry.summand_chase` is also fully proved.

Holes added: zero. Sorries left in the delivered module: none.
No additional modules or declarations with `sorry` are delivered.

## No longer needed

None. All existing imports and all six recorded proof dependencies remain needed;
the proof follows the recorded route and introduces no new dependency nodes.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The module tensor/stalk square was present
in the repository but absent from the compiled baseline during initial development;
it became available after the library refresh. No workaround or duplicate declaration
was added. `D.map_id` explicitly selects the categorical identity lemma, avoiding the
unrelated programming-functor lemma named `Functor.map_id`.

## Second reading by G4

1. Compared the delivered module with the repository version. The theorem signature
   is byte for byte identical after restoring one extra space before its proof.
   All original instances, definitions, declaration visibility, and imports are
   unchanged. There are no adapted modules or interface change records. Pass.
2. Compiled the delivered module locally with lcompile.py without errors or warnings.
   A scratch copy with explicit `#print axioms` for
   `AlgebraicGeometry.pinned_tensor_square_left_summand` and the private
   `AlgebraicGeometry.summand_chase` compiled cleanly; both use only `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Inspected the source:
   no sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition.
   The helper follows by associativity, its seven hypotheses, and cancellation
   of the final isomorphism. Pass.
3. No statements were split off and no holes were added. The new private helper
   is fully proved in an arbitrary category; it imposes no additional hypothesis
   on the existing public theorem. The argument requires neither boundedness nor
   nonzero modules or stalk rings, so zero objects and unbounded complexes cause
   no exception. All choices in the proof refer to the existing specified maps;
   no arbitrary existence witness is introduced as new data. Pass.
4. Read the pinned stalk comparison, the specified pullback-stalk components,
   and the proved module tensor-stalk square. Searched local Sheaf/upstream
   declarations using tensor-square, stalk, and summand terminology, and read
   Mathlib's `HomologicalComplex.ι_mapBifunctorMap`: the submitted proof already
   uses that direct summand lemma and the existing module square. No shorter
   independent library theorem was found. The six original proof dependencies
   are used, the public imports provide objects or instances in the statement,
   and every plain proof import supplies one of the recorded equations. Nothing
   is newly pruned. The unit `sk-thm-picard-semicon` has empty `realized` lists;
   its route is unchanged and no unit step is bypassed. Pass.
5. Compared the node's proof, proof_deps, and proof_origin with the seven local
   equations and their final chase. The existing plan already describes this
   exact route, including the ring-map transport and cancellation of the target
   comparison, so its records require no alteration. There are no new nodes. Pass.

Second reading changed only the extra space at the end of the existing theorem
signature and added this review record. The mathematical proof required no repair.
