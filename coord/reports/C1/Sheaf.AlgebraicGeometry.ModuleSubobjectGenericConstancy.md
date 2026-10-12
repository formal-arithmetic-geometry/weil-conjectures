## What changed

Replaced the sole `sorry` in `Sheaf.AlgebraicGeometry.ModuleSubobjectGenericConstancy`,
`AlgebraicGeometry.Scheme.exists_dense_open_of_mono_noetherian`, with a complete Lean
reduction. Its signature and original docstring are unchanged. Added proof-only imports of
`WeilConjectures.ConstructibleSheaf.GenericConstancy` and
`Sheaf.AlgebraicGeometry.ModuleSubobjectGenericNeighbourhood`.

The proof first uses the existing generic-constancy theorem on G. On that dense open U,
it proves finiteness of F directly: geometric stalks preserve the monomorphism, and
submodules of finitely generated modules over a Noetherian ring are finitely generated.
The local-neighbourhood statement gives local constancy near each component generic
point of U. Pullback stability supplies finiteness there. The proof takes their union,
proves it dense using `genericPoints.closure`, glues finite local constancy using
`Opens.iSupOpenCover` and `IsFiniteLocallyConstantSheaf.of_openCover`, and transports the
result to the composite open immersion's image in X. The density and pullback-composition
steps are proved, not deferred to new statements.

The new module isolates only the local geometric construction, assumes the target is
already finite locally constant, and concludes local constancy near one component generic
point. It asserts neither a dense open nor finiteness of the source. Thus it is strictly a
part of the argument rather than the original statement renamed. Its source is the
local-neighbourhood argument in [Stacks 09BH](https://stacks.math.columbia.edu/tag/09BH),
proof of (3), before Noetherian induction. Updated the parent's proof, proof_deps, and
proof_origin to match the Lean reduction. No definitions or existing statements changed;
no change record is required.

## Proved and sorry left

Proved from the named local-neighbourhood statement:
`AlgebraicGeometry.Scheme.exists_dense_open_of_mono_noetherian` (1 of 1 original sorries).
The item's module has no direct `sorry` left.

One new public theorem remains `:= by sorry`:
`AlgebraicGeometry.Scheme.exists_open_locallyConstant_of_mono_at_genericPoint`, node
`lem-weil-pbc-module-subobject-generic-neighbourhood`, in
`lean/Sheaf/AlgebraicGeometry/ModuleSubobjectGenericNeighbourhood.lean`.
Its docstring gives the source and the generator-lifting, descent, and quotient-vanishing
argument. The remaining dependency means this is a reduction, not an axiom-free closure
of the original theorem's entire dependency tree.

Both delivery modules compiled locally in import order. The final dry run checks local
compilation, declaration probes, server compilation, and stage-3 preflight.

## No longer needed

No original imports or dependency modules are pruned from the target closure. The second
reader removed the redundant `public import Mathlib.Topology.Sober` from the new module;
its signature already has the required names through the retained imports.

The following old direct `proof_deps` are removed from the parent node and transferred to
the local-neighbourhood node: `def-constructible-constant`,
`def-constructible-locally-constant`, `def-weil-pbc-geometric-stalks`, and
`lem-weil-pbc-noetherian-finitely-many-components`. They remain needed transitively.
All original proof dependencies remain needed either directly or inside the new node: generic constancy for G;
finite components to isolate the local component; Noetherian submodule finiteness; and
the definitions of constant sheaves, local constancy, geometric stalks, and the etale site.
The global proof does not require pairwise-disjoint chosen component opens: arbitrary
chosen neighbourhoods glue along their overlaps through the existing open-cover theorem.
This removes that construction from the global assembly, but does not prune the finite
components node needed in the local construction.

The tempting route through `IsConstructibleSheaf.isFiniteSheaf` in
`WeilConjectures.ConstructibleSheaf.Monoidal` was not introduced: its proof is still sorry,
and direct stalk finiteness avoids that additional open dependency.

## Where the brief, the DAG or earlier work was wrong

No false original statement was found. The plan's dependency signatures provide generic
constancy of G and Noetherian finiteness, but do not themselves construct local constancy
of an arbitrary module subsheaf. In particular, the existing
`AlgebraicGeometry.constant_subsheaf_generic` requires a finite coefficient ring and a
finite underlying module, and cannot be applied to the general Noetherian-ring statement.
`mono_of_mono_generic_stalk` detects monomorphisms of abelian sheaves; it does not give the
required neighbourhood. The new node records the missing local construction explicitly.

Checked the unit `sk-thm-p1`: this auxiliary node is not itself among its realized unit
statement or step nodes. The curve-devissage route is unchanged; this is a split inside
its generic-constancy auxiliary argument. No unit was bypassed.

Edge cases of the new statement: the empty scheme has no component generic point, so the
statement is vacuous; G = 0 forces F = 0 by monicity; a zero generic submodule uses the
constant zero sheaf in the same argument. Reducible X is handled by removing the finitely
many other closed components before the etale trivialization. The proof uses finitely
generated modules rather than finite underlying sets, and makes no reducedness,
normality, connectedness, or domain assumption on X or the coefficient ring.

## New nodes

`lem-weil-pbc-module-subobject-generic-neighbourhood` is the local-neighbourhood step of
Stacks 09BH (3) for a subsheaf of an already finite locally constant module sheaf. Its
conclusion is local constancy near a single component generic point. The new module is
`Sheaf.AlgebraicGeometry.ModuleSubobjectGenericNeighbourhood`; its DAG record is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-module-subobject-generic-neighbourhood.json`.
LeanFinder, Loogle, and grep searches found no matching Noetherian-ring etale theorem.
LeanSearch was attempted and returned Internal Server Error; this is recorded as unavailable.
No change records and no other new nodes were added.

## Second reading by C1

1. PASS. Compared the existing module with the repository using `diff -u`: its sole
   theorem signature and docstring are byte for byte unchanged. The only additions are
   its proof and two plain, proof-only imports. No existing definitions or statements
   changed, and no change record is needed. The second file and its node are new.
2. PASS. Both delivery files compile cleanly through `lcompile.py --all`, including
   after removing the redundant import. Scratch copies with `#print axioms` for both
   declarations show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The only direct sorry is the reported public local-neighbourhood theorem; no forbidden
   declarations or hollow definitions occur. This is a reduction with an open dependency,
   not an axiom-free closure of the original theorem.
3. PASS. Read Stacks 09BH (3) and 09BG against the new signature and docstring. The new
   statement assumes the target already finite locally constant and concerns one component
   generic point; the parent still proves stalk finiteness, density, gluing, and transport.
   It is a genuine local step, not the original dense-open assertion renamed. Checked empty
   X (no generic point), F = G = 0, zero generic submodule, reducible and nonreduced X,
   and arbitrary Noetherian coefficient rings. Finite generation, not finite cardinality,
   is the required input. Independent LeanFinder search for an injective map into a locally
   constant etale sheaf, Loogle search for IsLocallyConstantSheaf with Mono, a logged grep
   with different words, and local rg on both Lean roots found no applicable replacement.
   ConstantSubsheafGeneric needs finite underlying modules and a finite ring;
   LisseGenericKernel only detects monicity. The remaining geometric construction cannot
   be closed in a few minutes from those declarations.
4. PASS, with report correction. Followed the proof from generic constancy of G through
   stalk finiteness, local neighbourhoods, their dense union, open-cover gluing, and the
   composite open immersion. The two new imports are proof-only; the retained public
   imports supply the signatures. Removed the redundant Sober import from the new module.
   The No longer needed section now enumerates every removed old direct proof dependency
   and explains its transfer to the new node; none leaves the target closure. Read the
   realized statement and all steps of sk-thm-p1: this auxiliary reduction bypasses none
   of them and does not change the unit route.
5. PASS. Both node signatures match Lean; each proof_deps is exactly the union of the
   uses fields of its proof steps, and all cited nodes exist. Parent steps match the actual
   proof, including the open-cover and immersion transport. The new node has its source,
   full natural-language argument, provenance, searches, creation record, blueprint, unit,
   chapter, status, and Lean record. The parent's non-stage-3 fields are unchanged.

Changes made by the second reader: removed the redundant public Sober import; corrected
pruning bookkeeping in this report; added this review. No Lean proof or statement repair
was necessary. Local compilation and explicit axiom probes passed; delivery dry-run and
server preflight are the final validation below.
