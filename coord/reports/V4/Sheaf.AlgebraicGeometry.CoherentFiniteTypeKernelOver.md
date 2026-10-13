## What changed

Replaced the only sorry in Sheaf.AlgebraicGeometry.CoherentFiniteTypeKernelOver
by a complete Lean combination of two strictly separate steps of the stated proof.
The original declaration, its binders, universe and conclusion are unchanged.
Extract finite local generating data from hF; each generating family's finite index
instance comes from hq.isFiniteType. Compose its free epimorphism with the
restriction of φ and invoke coherent_iterated_slice_relations. Feed the resulting
family of finite type kernels to finiteType_kernel_local_generators.

Added the two helper modules and their nodes, and updated the original node's
proof, proof_deps and proof_origin to match this argument. No definitions,
existing statements, target declarations or other modules were changed.

The source was read at Stacks https://stacks.math.columbia.edu/tag/01BY (part (2),
second paragraph of proof) and https://stacks.math.columbia.edu/tag/01BV (condition (2)).
The local source path recorded in the DAG is absent on this machine, so the official
source pages were used. Mathlib Generators.lean, Free.lean, PushforwardContinuous.lean
and Sites/Over.lean were read. LeanFinder and Loogle found finite generator APIs,
but no kernel theorem with the required slice interface. LeanSearch was attempted
for both new statements and returned Internal Server Error, recorded as unavailable.
Blueprint searches for 01BY and 01BV found no duplicate statement for either helper.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.RingedSpace.coherent_finiteType_kernel_over
(node lem-weil-pbc-coherent-finite-type-kernel-over): no sorry remains in the item.

Added two holes, each in its own new public theorem with source and complete proof:

- AlgebraicGeometry.RingedSpace.coherent_iterated_slice_relations in
  Sheaf.AlgebraicGeometry.CoherentIteratedSliceRelations
  (node lem-weil-pbc-coherent-iterated-slice-relations).
- AlgebraicGeometry.RingedSpace.finiteType_kernel_local_generators in
  Sheaf.AlgebraicGeometry.FiniteTypeKernelLocalGenerators
  (node lem-weil-pbc-finite-type-kernel-local-generators).

This is a decomposition: one upper hole closed, two lower holes added (net -1).
Neither helper restates the item. The first concerns only maps with finite free
source on a double slice, and has no F or finite type source hypothesis. The second
has no coherence assumption; it descends finite type kernels of composites on a
chosen cover and does not even require finite generating families. The item uses
hF and hG in different steps, and combines both helpers in Lean.

All three modules compiled together in import order through lcompile.py.
The local generator datum's four universe arguments are explicitly u: leaving the
covering universe implicit caused type inference timeouts on q.generators i.
Compilation with the explicit universes finishes within the single-file limit.

Edge cases checked mathematically: U empty, V empty, and an empty free basis satisfy
the relation statement; rank zero is covered by hG. In the criterion, φ zero gives
local quotients of its free sources; φ monic gives the zero kernel. Infinite local
free generating families are allowed because finiteness is imposed on their
composite kernels. Cover refinement also works for the vacuous empty-open cover.
No data is constructed from an unproved existential helper: q is supplied by the
finite type hypothesis, and the two new helpers are propositions about fixed data.

## No longer needed

Removed import Sheaf.AlgebraicGeometry.CoherentFiniteTypeSubKernel and removed
lem-weil-pbc-coherent-finite-type-sub-kernel from this node's proof dependencies.
The broader theorem packages both the coherent-submodule result and kernel result
on a ringed space; this proof uses neither package, instead formalizing the needed
free-relations and local-image steps directly on the slice.

Its proof-only dependencies
lem-weil-pbc-ringed-space-module-exactness-local-lifting and
lem-weil-pbc-module-finite-type-image-extension remain mathematical dependencies of
the local-generator criterion. They are not claimed globally pruned. The coherent
and sheaf-category definitions remain needed. No unit statement or realized unit
step is bypassed: this item and both helpers lie below the unit-level route.
No other existing module or node is claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The original first step calls the slice identification elementary, but the available
Lean coherence predicate only accepts modules on a ringed space. The imported
coherent_finiteType_submodule_kernel cannot be directly specialized to the category
of modules over (moduleRings X).over U. Mathlib has continuous/cocontinuous iterated
slice functors, but no ready-made finite type transport theorem for these modules.
The two helpers expose the precise transport and descent needed rather than
silently applying a theorem with a different category. No false statement or source
error was found. The original mathematical proof remains valid.

## New nodes

lem-weil-pbc-coherent-iterated-slice-relations records the relation clause on an
iterated open slice with an arbitrary finite basis. The proof forgets the intermediate
inclusion, reindexes by ULift (Fin n), applies coherence at the underlying open,
and transports sectionwise kernels and finite generators back.

lem-weil-pbc-finite-type-kernel-local-generators records the local kernel quotient
and cover refinement step independently of coherence. Its local free sources need
not have finite rank: finite type composite kernels suffice. The proof constructs
the kernel factor, proves it locally surjective, pushes finite generators through
it, and composes the generating covers. No change record is needed: all existing
interfaces are unchanged.

## Second reading by V4

1. **Interface and accidental changes.** Compared the delivered item module with the repository version. The target theorem binders, universes, conclusion, and declaration name are byte-for-byte unchanged; only its proof and proof-only imports changed. The two additional files are new public helper modules, and their declarations are recorded by matching new DAG nodes. No existing definition or target statement was altered.

2. **Compilation and proof form.** Compiled all three sandbox modules with `lcompile.py`, including the item after its helper imports. The item has no `sorry`; the only remaining holes are the two named helper theorems, each a public theorem with a source, proof sketch, and matching node. No axiom, unsafe, opaque, extern, implemented_by, or sorry appears in a definition. The helper statements are propositions about supplied data and do not choose data from an unproved existential.

3. **Truth and strength of split statements.** Checked the edge cases and the interfaces used by the item. `coherent_iterated_slice_relations` is the finite-free relation clause for a coherent sheaf after two open-slice restrictions, with the required finite index instance and no extraneous hypotheses. `finiteType_kernel_local_generators` is the local quotient/descent criterion for a supplied local generating datum; it does not assume coherence and does not require the generating index families themselves to be finite. Neither helper restates the item, and both are strictly smaller propositions needed by the two proof steps.

4. **Shortest route and pruning.** The item obtains local generators from finite type, applies the coherent relation result to each finite composite, and then applies the local kernel descent criterion. This removes the unused `CoherentFiniteTypeSubKernel` import and its proof dependency. The remaining imports are used by the signatures or proof route. The unit route and its realized node are retained; the change stays below the unit level.

5. **DAG agreement.** Checked that the item node's proof steps, `proof_deps`, and `proof_origin` describe exactly the Lean proof, and that each new node has its module, declaration, verbatim statement, source, proof steps, searches, chapter, and unit. The item node records the removed dependency and both new helper dependencies. No statement-change record is needed.

**Changes made in this second reading:** added this review section only; no Lean statement or proof was changed during the review.
