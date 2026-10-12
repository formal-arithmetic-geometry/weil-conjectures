## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.PerfectObjectCompact` by a complete
categorical proof from `perfect_tensor_hom_duality` and the compactness of the derived
structure sheaf. The existing theorem signature, universes and public imports are unchanged.
A proved private helper checks the canonical direct-sum map using additive natural Hom
equivalences and the coproduct comparison. Both tensor adjunctions restrict to D_QCoh, so
left-adjoint preservation of coproducts replaces the termwise K-flat calculation.

Added `Sheaf.AlgebraicGeometry.DerivedTensorUnitCompact` for the geometric structure-sheaf
step. Its existential object is determined up to isomorphism by the tensor unit; no definition
chooses data from this theorem. Both modules compile cleanly with lcompile.py --all. The second reading removed four
redundant private Mathlib imports, whose declarations are already available transitively.
The item DAG proof now follows the written Lean proof. Its original docstring describes
the source argument, which the proof implements using the adjunction shortcut.

## Proved and sorry left

Closed: `AlgebraicGeometry.perfectObjectCompact` (lem-pc-perfect-object-compact).
Added: `AlgebraicGeometry.exists_compact_derivedTensorUnit`
(lem-pc-derived-tensor-unit-compact), the only direct sorry in this delivery.
This is a decomposition: one upper hole closed and one strictly smaller geometric hole
added, net zero holes. The target module itself has no sorry. The existing dependency
`AlgebraicGeometry.perfect_tensor_hom_duality` remains unproved in the library.
The private `compact_of_homEquiv` helper is fully proved.

The remaining theorem only concerns the structure sheaf, has no perfect-object hypothesis,
and does not assert compactness of arbitrary perfect objects. The combining proof restricts
two adjunctions, proves coproduct preservation and additivity, constructs natural additive Hom
equivalences and checks the canonical map on every summand. It is not a renamed target.

## No longer needed

Removed direct proof imports:
- `Sheaf.Algebra.Homology.KFlatResolution` (lem-pc-kflat-resolution).
- `Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums`
  (lem-pc-derived-ambient-direct-sums).
- `Sheaf.AlgebraicGeometry.DerivedAdjoint` (lem-pc-ringed-spaces-derived-adjoint).
- `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums`
  (lem-pc-derived-direct-image-preserves-direct-sums).
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`
  (lem-pc-affine-qcoh-derived-equivalence).

Also removed redundant private imports during the second reading:
- `Mathlib.CategoryTheory.Adjunction.Restrict`.
- `Mathlib.CategoryTheory.Adjunction.Additive`.
- `Mathlib.CategoryTheory.Adjunction.Limits`.
- `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`.
Their declarations are already available through the retained imports; compiling with
all four removed succeeds.

The K-flat and explicit tensor-total-complex route is no longer needed by this argument:
lem-pc-kflat-resolution and def-pc-tensor-complex-sheaves are removed from the item's direct
proof dependencies. They can remain transitively needed by the already recorded derived
monoidal/duality constructions; this delivery does not claim their whole-library deletion.
The other four removed imports are relocated to the new structure-sheaf lemma's proof plan,
not globally pruned. derivedQCohDirectSums and its existing public import remain required.
No unit-level statement or step is bypassed; the item's unit record has empty realized lists.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The plan's tensor/direct-sum calculation is longer
than necessary because perfect_tensor_hom_duality already gives tensoring by the dual as a
left adjoint. The global-sections-to-Hom and tensor-unit-to-degree-zero-structure-sheaf
identifications are not directly supplied by the recorded declarations, so the remaining
geometric step is isolated with its full argument.

Edge cases checked: an empty family gives zero on both sides of the comparison; the proof
uses the same direct-sum extensionality argument without a nonemptiness assumption. For the
empty scheme, the structure sheaf and tensor unit are zero and the conclusion still holds.
On Spec(A) the new statement becomes compactness of the rank-one free module in D(A), not
compactness of arbitrary modules. It requires both quasi-compactness and quasi-separatedness.
The structure morphism uses ULift(Z) when necessary to respect the scheme universe.

Searches: LeanFinder found no scheme compactness theorem, Loogle did not know the project's
IsCompactObject name, and Mathlib plus both project roots had no structure-sheaf compactness
statement. LeanSearch returned service unavailable (Internal Server Error); no absence verdict
is claimed for that service. Blueprint searches for compact structure and compact unit found
no existing blueprint statement. The unavailable local Stacks source was checked at
https://stacks.math.columbia.edu/tag/09M1; its forward argument uses the H^0 coproduct fact.

## New nodes

`lem-pc-derived-tensor-unit-compact`, at
`dag/nodes/sec-picard-framework/lem-pc-derived-tensor-unit-compact.json`, states compactness
of the derived structure sheaf, represented by an object isomorphic to the fixed derived
monoidal unit. It retains the original geometric proof route through derived adjunction,
direct-image coproduct preservation and the affine derived equivalence. Its Lean module is
`lean/Sheaf/AlgebraicGeometry/DerivedTensorUnitCompact.lean`. No change record is needed:
no existing definition or statement changed.

## Second reading by X2

1. Compared the delivered PerfectObjectCompact module with the repository using diff.
   The entire existing perfectObjectCompact signature, its universes, docstring, and
   three public imports are byte for byte unchanged. There are no existing definitions
   changed and no undeclared statement change. Only its proof, a proved private helper,
   and private proof imports change. DerivedTensorUnitCompact is a new module.
2. Compiled both modules in import order with lcompile.py --all. Both compile without
   errors or warnings. The only direct sorry is the named theorem
   exists_compact_derivedTensorUnit. No forbidden declaration or hollow definition is
   introduced. Scratch-copy #print axioms shows compact_of_homEquiv uses exactly
   propext, Classical.choice, and Quot.sound; perfectObjectCompact and
   exists_compact_derivedTensorUnit additionally use sorryAx from open statements.
   Read the helper's commuting square: DirectSum.addHom_ext reduces it to naturality
   on each inclusion; the coproduct comparison is an isomorphism because G is a left
   adjoint. Cancellation uses the injectivity of the additive Hom equivalence.
3. Read Stacks Tag 09M1, Proposition perfect-proposition-compact-is-perfect, forward
   proof, at https://stacks.math.columbia.edu/tag/09M1. Its H^0 coproduct argument gives
   the structure-sheaf case isolated by the new theorem. Checked CompactSpace and
   QuasiSeparatedSpace against the qcqs hypotheses. The fixed derived tensor unit
   represents O_X in degree zero, so the new conclusion is compactness of this one
   object, strictly smaller than compactness of every perfect object. On Spec(A) it
   concerns A[0]; on the empty scheme the unit is zero. An empty index family gives
   the zero comparison, and the helper requires no nonemptiness. The existential U
   is determined up to isomorphism by the fixed tensor unit; no definition selects
   an arbitrary witness. The new theorem has its source, full natural-language proof,
   and matching node. Read the derived adjunction, affine equivalence, ambient sums,
   and direct-image sums declarations used in its plan: they supply the adjunction,
   the structure-sheaf image of A[0], cohomology of sums, and preservation of sums.
   No quick closing proof is supplied by these interfaces: the unit/single-complex
   identification and Hom(A[0],-) cohomology comparison still need formalization.
   Repeated searches with different words through msearch LeanFinder, Loogle, grep,
   and rg on both local project roots and upstream found no existing matching
   structure-sheaf compactness declaration. Loogle's unknown project identifier is
   recorded as unavailable for that identifier, not evidence of mathematical absence.
4. The proof uses the shortest available categorical route: both adjunctions and
   quasi-coherent closure are provided by perfect_tensor_hom_duality; restricting
   them makes dual tensor preserve coproducts without redoing K-flat calculations.
   Reviewed every removed old proof dependency: kflat-resolution and
   tensor-complex-sheaves disappear from the direct route; ambient sums, derived
   adjunction, direct-image sums, and affine equivalence move to the structure-sheaf
   lemma. The report names all six old dependencies absent from the new direct list.
   Public imports remain needed for the signature. Checked
   dag/units/sk-thm-picard-duality.json: realized.statement is empty and its sole
   realized.steps entry is empty, and neither this record nor its route is changed.
5. Compared the existing node diff: only proof, proof_deps, and proof_origin change.
   The three steps match obtaining compact U, restricting dual tensor adjunctions,
   and the explicit natural direct-sum comparison. proof_deps is exactly their uses
   union. The new node has its statement dependencies, source, proof steps and uses
   union, proof_origin, logged searches, creation record, blueprint ancestry, chapter,
   unit, and verbatim Lean statement. No circular dependency or restatement of the
   original target is introduced. Verdict: sound decomposition, one hole closed and
   one strictly smaller hole added; no net hole reduction claimed.

Changed during second reading: removed the four redundant private Mathlib imports
listed under No longer needed, checked compilation with all four removed, and expanded
this report. No theorem statement, proof body, definition, or DAG record was changed.
