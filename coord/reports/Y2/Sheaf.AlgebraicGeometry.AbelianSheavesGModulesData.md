## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.abelianSheaves_equiv_discreteGModules_core`
with a complete proof from the new theorem `AlgebraicGeometry.Scheme.abelianSheaves_transport`.
The new theorem only constructs the abelian-sheaf/representation equivalence and its
underlying-action natural isomorphism, with no point, stalk comparison, or action-on-germs clause.
The original theorem's signature, universes, hypotheses, public imports and docstring are unchanged.

The main proof constructs the underlying-set natural isomorphism alpha by composing beta,
the supplied j, and Mathlib's canonical `Point.sheafFiberCompIso`. It derives left exactness of
the underlying abelian-group functor from alpha, since the additive stalk is left exact and
forgetting abelian groups reflects limits. It then lifts alpha through
`AddCommGrpCat.leftExactFunctorForgetEquivalence`, using `preimageIso` and `map_preimage`.
The remaining Lean calculation establishes the inverse comparison on germs by injectivity,
uses equivariance of beta, and substitutes the supplied set-valued action equality.
Thus the additive comparison and the entire action implication are proved here.

Added proof-only imports of the new transport module, `Mathlib.Algebra.Category.Grp.LeftExactFunctor`
and `Mathlib.Algebra.Category.Grp.AB`. The AB5 and filtered-colimit instances are explicitly shrunk
to the universe of the point. Updated the original node's proof, proof dependencies and origin.
The transport theorem has its own new module, node, source and proof in words; a second new node
records the exact Mathlib equivalence as a leaf, without duplicating it in Lean.

## Proved and sorry left

Proved (from the named transport theorem):
`AlgebraicGeometry.Scheme.abelianSheaves_equiv_discreteGModules_core`
(node `lem-exc-abelian-sheaves-gmodules-core`). The item's one sorry is gone. This is a decomposition, not a completed proof:
one upper hole is closed and one strictly smaller transport hole is added, for net zero
holes closed in the targets' import closure.

The delivery leaves exactly one named sorry:
`AlgebraicGeometry.Scheme.abelianSheaves_transport`, in
`Sheaf.AlgebraicGeometry.AbelianSheavesGModulesTransport`
(node `lem-exc-abelian-sheaves-gmodules-transport`). Its proof is exactly `by sorry`.
No definition is added, no target or existing statement is changed, and no axiom is introduced.

Both Lean modules compiled together locally with no errors or warnings. The signature comparison
reports no statement change and no interface change. `deliver3.py --no-push` printed OK:
local and server compilation and the preflight passed, apart from the second reading that the
next worker writes. Nothing was pushed.

## No longer needed

Removed the direct proof import `Sheaf.CategoryTheory.EquivalenceInternalModule` from the item's
module. Its node `lem-pod-equivalence-induces-module-objects` is no longer a direct dependency
of the core theorem, but remains a planned dependency of the new transport theorem, which imports
it. It is not claimed to be globally pruned. The finite-action specialization
`CategoryTheory.internalModules_finiteContAction` is not used: it only addresses finite carriers,
whereas these representations have arbitrary carriers in the stated universe.

The other original proof dependency, `def-exc-discrete-modules-category`, remains a
statement dependency and its module remains publicly imported; it is no longer a separate
proof step of the core node. Thus both original proof dependencies are accounted for.

No original node or module is globally pruned. No point, stalk comparison, left-exactness
assumption or germ-action formula needs to be proved by the transport worker.
The explored `Mathlib.CategoryTheory.Sites.Abelian` import was removed: finite products and
preadditivity suffice for the finite biproducts needed by the lifting argument.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing general internal-module transport declaration supplies
transport between internal-module categories, but does not supply their identifications with
abelian-group-valued sheaves or arbitrary discrete continuous representations. Its second theorem
is restricted to finite continuous actions and cannot be used as the identification here.
The new transport theorem states precisely the categorical component still needed.

The core node's second step described lifting j and its germ compatibility as elementary.
Mathlib's left-exact functor forgetful equivalence provides a precise, already proved interface
for that lift. All of its hypotheses are checked in Lean: the source is preadditive with finite
biproducts; the two abelian-group-valued functors preserve finite limits; and the target carrier
universe equals the source hom universe. No sheafification or abelian-category hypothesis is added.

Read Stacks Tag 04JQ (`lemma-equivalence-abelian-sheaves-point`) and Tag 0DV5, proof of (2)-(3),
on the Stacks website, since the local literature checkout holds the indexes only.
The transported group operations, inverse equivalence and equivariant morphisms follow that route.
The new lemma was checked on zero groups, the trivial group, discrete groups, and an arbitrary
non-profinite topological group: the construction requires only open stabilizers and finite
products, never finite orbits, compactness or profiniteness. The final calculation allows zero
sections and x=x', as the unchanged statement requires. The unit record `sk-prop-h2` realizes
no step by this core node, so no unit statement or step is bypassed.

The LeanSearch service returned Internal Server Error; it is recorded as unavailable. Loogle,
LeanFinder and source grep were run and logged. Blueprint searches for abelian sheaves,
commutative groups, module objects and left-exact functors found no duplicate of either new node.

## New nodes

`lem-exc-abelian-sheaves-gmodules-transport` states the equivalence and the natural underlying-action
comparison independently of a point. Its docstring and node explain both internal-module
identifications and transport via `lem-pod-equivalence-induces-module-objects`. It is a strict
part of the original argument: the core proof still constructs i, proves its underlying-map
equation, derives left exactness and proves the germ implication. This node is left with one sorry.

`lem-exc-left-exact-functor-forget-equivalence` records the exact Mathlib declaration
`AddCommGrpCat.leftExactFunctorForgetEquivalence` in
`Mathlib/Algebra/Category/Grp/LeftExactFunctor.lean`, lines 120-127, with hypotheses at lines 39-40.
Its canonical functor is postcomposition with the forgetful functor, exactly as used in the proof.
It is a Mathlib leaf with no new Lean module and no sorry. Neither new node changes a definition
or existing statement, so there is no change record.


## Second reading by Y2

Independent second reader, 2026-10-12. Read both delivered modules, the original module,
all three delivered nodes, the old proof dependencies and their Lean declarations,
and the unit record `dag/units/sk-prop-h2.json`.

1. PASS: `diff` shows only proof-body and proof-import changes in the existing module.
   The complete existing declaration prefix, including docstring and signature through
   `:= by`, is byte for byte identical. No definition or target statement changes.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   No relevant change record was found; none is needed.
2. PASS: both modules compile together locally without errors or warnings. The core
   has zero sorries; transport has exactly its reported public named theorem with
   body `by sorry`. No hollow definition or forbidden declaration/attribute occurs.
   A scratch copy with explicit `#print axioms` compiled: core and transport use
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the Mathlib
   left-exact functor equivalence uses only the three permitted axioms.
   The scratch file is not included in the delivery.
3. PASS: transport is a strict part of the item, independent of p and j, and the
   core proves the additive comparison and full germ implication by a real reduction.
   Checked zero groups, trivial G, an empty site, and arbitrary non-profinite G.
   Finite products of discrete continuous actions are available because their
   stabilizers are finite intersections of open subgroups; no finite-orbit hypothesis
   is used. Integer-module objects are precisely commutative group objects.
   The docstring describes both identifications, their maps, inverse constructions,
   and underlying-action comparison; its node agrees. Re-read Stacks
   https://stacks.math.columbia.edu/tag/04JQ and
   https://stacks.math.columbia.edu/tag/0DV5: the former gives the group-object
   argument and the latter explains product transport. Ran fresh LeanFinder search
   for commutative group objects in sheaves, Loogle for `Equivalence.mapCommGrp`,
   and source `rg` for internal sheaves, transport and group-object equivalences.
   Searches are logged in `searches.jsonl`. `mapCommGrp` supplies transport only,
   not the necessary identifications; no exact existing theorem was found.
   Closing transport requires those two constructions, beyond a few-minute repair.
4. PASS: reviewed alpha, reflection of finite limits, full-faithful lifting and
   the injectivity/equivariance calculation from the top down. The Mathlib leaf
   has exactly the preadditivity, finite-biproduct and hom-universe hypotheses
   used in Lean. All three added imports are proof-only. The public EtaleFieldGsets
   import supplies the Type-to-discrete-TopCat instance needed by the signatures;
   its visibility is unchanged. The internal-module import in transport retains
   that node's planned proof dependency. Both removed original direct proof
   dependencies are accounted for above; neither is globally pruned.
   The unit's realized statement and step lists are empty, so this reduction
   bypasses no realized unit step and changes no unit record.
5. PASS: core's proof steps describe the actual Lean construction; `proof_deps`
   lists transport and the exact Mathlib leaf. Transport's node records its
   identifications and internal-module transport plan, with source, searches,
   creation, blueprint, chapter, unit, and verbatim Lean signature. The Mathlib
   leaf was checked against the local source and adds no Lean declaration or hole.

Changes by the second reader: clarified that this delivery is a one-for-one
hole decomposition with net zero, completed the accounting of old direct proof
dependencies, and added this independent review. No Lean proof needed repair.
