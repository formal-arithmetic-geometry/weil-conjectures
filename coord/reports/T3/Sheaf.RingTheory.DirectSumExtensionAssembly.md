## What changed

Proved `LinearMap.extension_descends_of_summands` in
`Sheaf.RingTheory.DirectSumExtensionAssembly`, with its signature and visibility unchanged.
The existing proof import `Sheaf.Algebra.ExtOneDirectSum` supplies only its surjectivity clause.
Two proved private helpers, `glue_extension_maps` and `extension_map_ext`, construct a compatible
map through a quotient and establish that the summand maps and the kernel generate the extension.
No public imports, definitions, or statements changed.

The summand pullback is a submodule of `T`, rather than the kernel in
`T × (S ⊗[R] C j)`, so the hypothesis's universe `z` is respected. After descending these
pullbacks, Ext-one surjectivity supplies the R-extension. Quotient factorization and a tensor
lift construct its comparison with `T`; flat exactness and tensor surjectivity prove that
comparison bijective. The node's proof and dependencies now describe this implemented route.

Validation: single-file compilation passes without warnings; every Lean line is at most
100 characters. The proof treats arbitrary index types, including the empty type, without
finiteness or nonemptiness assumptions. No new statement needs an edge-case check: no
statement was introduced or changed. The helper arguments also apply to zero modules and
zero rings, and choose no arbitrary data in a definition from an unproved existence theorem.

## Proved and sorry left

Closed the one original hole: `LinearMap.extension_descends_of_summands`
(node `lem-weil-pbc-direct-sum-extension-assembly`). No holes remain in the item and
no holes were added. Both private helpers are completely proved.

This proof uses the existing named theorem `LinearMap.extOne_directSum_bijective`
(node `lem-weil-pbc-ext-one-direct-sum`), which remains `sorry` in its own module.
Thus the delivery closes an upper hole from an existing planned dependency; it does not
claim an axiom-free proof of the entire import closure or introduce a new decomposition.

## No longer needed

No original import was removed: the three public Mathlib imports support the statements,
and `Sheaf.Algebra.ExtOneDirectSum` is required for assembly. A trial explicit proof import
`Mathlib.LinearAlgebra.Isomorphisms` was removed after compilation showed the existing
imports already provide its declarations.

Removed `lem-weil-pbc-tensor-commutes-with-colimits` from this node's `proof_deps`:
the implemented route never identifies the tensor of the direct sum with a direct sum of
tensors. Its categorical colimit modules are unnecessary for this proof. No project
module implementing this node is recorded, so no additional Sheaf module is pruned here.
The injectivity clause of `LinearMap.extOne_directSum_bijective` and the tensor/pullback
comparison of the old plan are also unnecessary; its module remains needed for surjectivity.
Flat tensor exactness, tensor right exactness, and all statement definitions remain needed.
No unit realization is bypassed or removed.

## Where the brief, the DAG or earlier work was wrong

The DAG plan is valid but longer than necessary. The comparison can be constructed from
compatible summand maps by finite-support gluing; no tensor/colimit isomorphism or
comparison of base-changed pullbacks is needed. The original docstring records the earlier
plan and was preserved. The node now records the actual proof.

The named source file is absent from this machine's literature checkout. Read the official
Stacks page https://stacks.math.columbia.edu/tag/05EG instead: the proof explicitly omits
the details of direct-sum Ext compatibility. The quotient/gluing details above fill that
omitted argument and are marked as an agent proof in `proof_origin`.

Searches before proving: LeanFinder for extension descent with a direct-sum quotient,
Loogle for `LinearMap.baseChange`, and Mathlib grep for extension descent/Ext-one/pullbacks;
none gave a direct theorem. Additional LeanFinder and source grep found tensor exactness
and direct-sum APIs. LeanSearch for flat base change and summand pullbacks returned
Internal Server Error, recorded as unavailable rather than no match. Blueprint search
`extension direct sum` returned no matches. No new nodes were needed.

## Second reading by T3

1. PASS: Compared the complete delivered module with the repository version and checked
   the existing theorem signature byte for byte. Its signature, visibility, docstring,
   and all imports are unchanged. Only the proof and two proved private helpers were added;
   there are no public definitions or interface changes and no change record is required.
2. PASS: Compiled the module locally with `lcompile.py` (8.1 seconds, no warnings).
   A scratch copy prints axioms for the target and both private helpers. The helpers use
   only `propext`, `Classical.choice`, and `Quot.sound`; the target additionally uses
   `sorryAx` through the existing planned `LinearMap.extOne_directSum_bijective`.
   The delivered module contains no `sorry`, forbidden declaration, or hollow definition.
   The chosen extension witnesses occur inside a theorem proof, not a data definition.
3. PASS: No statement was split off and no new hole or public statement was introduced.
   Read both helper proofs: the direct sum of quotient maps is surjective, its kernel
   is the componentwise image of the injections, and the induced map kills that kernel.
   The empty index type reduces to generation by the kernel alone; singleton and zero
   modules introduce no exception. Independent LeanFinder search for maps determined
   by kernel and summand preimages found only direct-sum decomposition and unrelated Baer
   extension lemmas. Loogle confirmed the first isomorphism theorem already used in the
   proof; Mathlib and project grep found no replacement assembly theorem.
4. PASS: Read the summand submodule construction, Ext surjectivity invocation, quotient
   gluing, tensor lift, and final injectivity/surjectivity argument from the target down.
   The submodule construction respects universe `z`. Both endpoints are fixed throughout.
   Imports supply the statement's flatness, direct sums, and base-change API; the Ext import
   is correctly private. The only removed old dependency is
   `lem-weil-pbc-tensor-commutes-with-colimits`, already named above. Inspected
   `dag/units/sk-thm-p1.json`: no realized statement or step is bypassed by this change
   below the unit level. No shorter direct theorem was found that warrants rewriting
   the working proof.
5. PASS after repair: Compared the original and delivered node records. Only `proof`,
   `proof_deps`, and `proof_origin` change; the statement and Lean record stay identical.
   The four proof steps match the Lean construction, and their uses have exactly the
   recorded dependency union. Added the existing Mathlib-backed node
   `def-weil-pbc-quotient-module` to step 3 and `proof_deps`, since `liftQ` and
   `quotKerEquivOfSurjective` explicitly factor through the kernel quotient.

Second-reading changes: repaired the missing quotient-module dependency in the DAG and
added this review. The Lean proof required no changes. Closed holes remain
`LinearMap.extension_descends_of_summands` (one); added holes remain none.
