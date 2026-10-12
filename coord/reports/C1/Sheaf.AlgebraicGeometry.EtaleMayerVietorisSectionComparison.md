## What changed

The assigned theorem AlgebraicGeometry.Etale.etaleSectionShortComplex_pullback_comparison
now has a complete Lean reduction, with its statement unchanged. It constructs a lift
I → g_*J by injectivity and exactness, rather than by derived-category K-injectivity.
The augmentation is extended in degree zero, and successive components are extended
using exact₀ and exact_succ; CochainComplex.mkHom packages them. Pushforward preserves
injectives because its inverse-image left adjoint is exact.

The new module Sheaf.AlgebraicGeometry.EtaleResolutionSectionTransfer constructs the
section chain maps and proves restriction naturality. It builds the three components
of the short-complex morphism explicitly, including the biproduct middle component,
and proves both diagram squares. No unproved existence theorem is used to define data.

The new module Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomology isolates the
remaining Ext calculation for individual section complexes. It requires a prescribed
augmentation-preserving direct-image lift; an arbitrary chain map would not suffice.
It asserts no biproduct or diagram morphism. The assigned module constructs both
middle equivalences using homology of a biproduct and proves the pair and difference
identities from the single-section identities, including the sign in the difference.

Proof imports and proof-local open/attribute commands change in the assigned module. Its public imports, definitions,
statement, universes, and downstream interface remain unchanged. The unit sk-thm-p1
route is unchanged. The three Lean files compile through the supported local compiler.

## Proved and sorry left

Hole closed in the assigned module:
AlgebraicGeometry.Etale.etaleSectionShortComplex_pullback_comparison
(node lem-weil-pbc-etale-mayer-vietoris-section-comparison).
No sorry remains in the assigned module or EtaleResolutionSectionTransfer.

One hole added, with the whole proof exactly := by sorry:
AlgebraicGeometry.Etale.exists_resolutionSection_homology_comparison
(node lem-weil-pbc-etale-resolution-section-homology), in
Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomology.

This is a decomposition, not a sorry-free proof of the import closure: one upper
hole closed and one strictly smaller single-section comparison hole added, net zero.
The lift, section diagram, product identifications, and their assembly are proved.
The remaining statement has its source and complete cocycle proof in its docstring
and node. Edge cases checked in words: degree zero, empty opens, identity g, and
arbitrary opens without a covering condition. Its α augmentation hypothesis is
essential; the zero map for nonzero coefficients does not satisfy it.

## No longer needed

The assigned proof no longer uses the three planned derived-category nodes
lem-weil-pbc-left-exact-injective-resolution-degree-zero,
lem-weil-pbc-dplus-injective-representative, and
lem-weil-pbc-kinjective-hom-derived. No module of these nodes is imported or rebuilt.
Their role in lifting the resolution comparison has been replaced by a proved
recursive injective-extension argument. They have no lean record in this checkout.

Removed direct proof imports from the assigned module:
Sheaf.AlgebraicGeometry.OpenRestrictionPullbackUnit;
WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs;
WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs;
WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance.
The final two were redundant proof-dependency imports present on the current base.
The statements already expose the upper/lower-star and cohomology-map APIs through
EtaleMayerVietorisSectionComplex. No public import has been removed.
The open-restriction/pullback-unit lemma and localization/composition facts remain
part of the new comparison node's mathematical plan; they are not claimed pruned
from the entire target closure. Existing lem-weil-pbc-etale-inverse-image-restriction,
lem-weil-pbc-inverse-image-composition, and def-weil-pbc-cohomology-pullback are moved
from the assigned node's direct proof dependencies into that smaller node's plan.
No other module is claimed globally unreachable.
The remaining removed direct proof dependencies are
lem-weil-pbc-open-restriction-pullback-unit (retained in the smaller homology node
and imported there) and def-weil-pbc-etale-mayer-vietoris-section-complex
(retained through the new transfer node and the unchanged public import).
These are moved dependencies, not globally pruned modules.

## Where the brief, the DAG or earlier work was wrong

The prior missing-olean failure is resolved in the refreshed cache: the unchanged
assigned module compiled at the beginning of this attempt. No library dependency
was copied into the sandbox or rebuilt. The earlier attempt contained no proof
changes worth retaining.

Three planned proof dependencies have no Lean record, despite the queue's normal
stage-3 eligibility rule. They are unnecessary for the implemented lift: pushforward
of J has injective terms, so I admits a chain-map extension into it directly, without
requiring g_*J to be a resolution. The original theorem docstring describes a valid
alternative K-injective route; the updated DAG records the actual elementary route.

An arbitrary short-complex morphism does not admit the asserted pullback identities.
The new single-section statement is conditioned on the precise augmentation equation,
and the assigned proof constructs a map satisfying that equation.

[Stacks Tag 0A50](https://stacks.math.columbia.edu/tag/0A50) supplies the section-complex
construction; [Tag 03F3](https://stacks.math.columbia.edu/tag/03F3) supplies preservation
of injectives and computation of open cohomology by restriction. The simultaneous
Ext/pullback cocycle calculation is the agent-written refinement already specified
by the original node, not claimed as a verbatim statement of either Stacks lemma.
LeanSearch was unavailable; actual LeanFinder, Loogle, and source-grep searches are
recorded in searches.jsonl. Blueprint searches found no matching imported unit.

## Forced adaptations

The returned review found that `resolutionSectionShortComplexTransfer` used the two
naturality helpers in its public definition body while those helpers were private.
In `lean/Sheaf/AlgebraicGeometry/EtaleResolutionSectionTransfer.lean`, lines 99 and
113, `private theorem` was changed to `theorem` for
`terminalSectionPullback_naturality` and `openSectionPullback_naturality`, respectively.
Their signatures and proof bodies are unchanged. This visibility change is required
so the public definition does not depend on private helpers; the adapted module is
held by this delivery.

## New nodes

Definition def-weil-pbc-etale-resolution-section-transfer, module
Sheaf.AlgebraicGeometry.EtaleResolutionSectionTransfer, records the explicitly
constructed section chain maps and short-complex morphism. All its data and
commutation proofs are complete Lean; it adds no sorry.

Statement lem-weil-pbc-etale-resolution-section-homology, module
Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomology, records the remaining natural
Ext calculation on individual section complexes. Its proof plan includes localization,
constant-sheaf Hom/sections comparison, and cocycle compatibility of an
augmentation-preserving lift. It adds the only remaining sorry in this delivery.
No existing signature or definition changes. The conservative static interface check
also flags proof-local open/attribute commands, documented in
coord/changes/etale-section-comparison-proof-local-commands.md. Its sole external
named user, EtaleMayerVietorisSectionDiagram, retains the identical theorem API.

## Earlier second reading (a previous round; superseded)

1. **Interface and statements.** Compared all delivered Lean modules with the repository versions.
The assigned theorem signature and existing declarations are unchanged byte for byte. The new
homology statement is a strictly smaller single-section comparison with the augmentation equation;
it does not restate the assigned theorem. Verdict: pass.

2. **Proof and trust.** Compiled `EtaleResolutionSectionTransfer.lean` and
`EtaleResolutionSectionHomology.lean` directly, and compiled the assigned module after its
imports. The assigned proof has no `sorry`; the only remaining `sorry` is the named theorem
`exists_resolutionSection_homology_comparison`. No axiom, unsafe, opaque, extern, or hollow
definition occurs. The available axiom probe for the completed transfer declarations reports only
`propext`, `Classical.choice`, and `Quot.sound`; the assigned module's full probe exceeds the local
60-second probe limit because of elaboration cost, while ordinary compilation succeeds. Verdict:
pass subject to the delivery tool's standard probe.

3. **Split statements and sources.** Checked the new theorem's docstring, DAG node, source tags
0A50 and 03F3, edge-case discussion, and searches for existing declarations. The statement is true,
uses the prescribed augmentation equation, and is exactly the unresolved single-section part of
the argument. Verdict: pass.

4. **Pruning and route.** The proof uses the explicit recursive injective lift, the explicit
section transfer, and the biproduct homology calculations. Removed proof-only imports are listed
in `## No longer needed`; no public import was removed. The three derived-category dependencies
are unnecessary for this route, and the unit `sk-thm-p1` route and its realized nodes are retained.
Verdict: pass.

5. **DAG consistency.** Checked that each node's `proof_deps` is the union of its proof-step
uses, that the new nodes carry source, blueprint, Lean, and split metadata, and that the assigned
node records the actual recursive-lift route. Verdict: pass.

Changed during second reading: no Lean statements or proofs; added this review section and
scratchpad-only compilation/probe artifacts outside the delivery.


## Second reading by C1

1. **Interfaces: pass.** Compared the delivered assigned module with the repository
using diff and the declaration parser: its existing theorem statement is byte for
byte identical. Its public imports, universe, visibility, and existing definition
interfaces are unchanged. The other two modules are new in the repository; their
statements match their new node records. The proof-local command change is documented
in the supplied change record. No target or coefficient definition is changed.

2. **Proof and trust: pass.** Locally compiled all three files in import order.
Read the recursive injective extension, section-transfer construction and its
naturality equations, and the biproduct projection/difference proofs. There are no
hollow definitions or arbitrary objects chosen from an unproved existence theorem.
The only sorry is the exact named theorem exists_resolutionSection_homology_comparison.
A scratch import probe prints axioms for every public transfer declaration, the
split theorem and the assigned theorem: transfer uses only propext, Classical.choice
and Quot.sound; the split and assigned theorems also use sorryAx as expected.
Scanned all delivered Lean for forbidden trust bypasses; none occur.

3. **Split statement: pass.** Checked the augmentation equation, both coefficient
transports, all six compatibility families, and the natural-language cocycle proof.
The theorem isolates individual section identifications, without the chain-map
existence, biproducts or short-complex squares of the assigned statement. Thus it is
a true, strictly smaller reduction, not a restatement. Degree zero is the augmented
kernel, empty opens give zero groups, the identity map gives the resolution comparison,
and neither the statement nor its argument assumes the opens cover. A zero lift for
nonzero coefficients fails the augmentation equation, so it is not a counterexample.
Read Stacks tags 0A50 and 03F3 directly; the latter proves injective localization and
open cohomology computation. Independently searched LeanFinder for terminal evaluation
and Ext compatibility, Loogle for the fully qualified isoRightDerivedObj API, and
grep for Ext/right-derived resolution comparisons, with queries different from the
first worker. Also searched lean/Sheaf and lean/WeilConjectures. Mathlib has the generic
resolution comparisons; EtaleSheafHExtDerivedComparison proves a natural global
Ext/derived isomorphism but does not state the fixed-resolution section and pullback
compatibilities here. No duplicate complete statement was found. Closing this split
requires the simultaneous section/Ext and inverse-image cocycle calculation, beyond
a few-minute repair. One upper hole closed and one lower hole added remains a
net-zero decomposition, not a sorry-free proof of the import closure.

4. **Pruning and unit route: pass after repair.** Checked every old direct proof
node against the new plan and completed the No longer needed list. The three
unavailable derived-category dependencies are bypassed below the unit level by the
proved recursive lift; the section-complex definition and the localization,
composition, pullback and open-unit dependencies remain through the new nodes.
Read sk-thm-p1.json and its realized arrays: none of its statement or step nodes is
bypassed, and no unit record is changed. Restored OpenRestrictionPullbackUnit as a
plain proof import of the new homology module, where its planned argument needs it.
Replaced that new module's broad public RightDerived import with the narrower public
Preadditive.Injective.Resolution import required by its signature. The assigned
module's existing public RightDerived import stays unchanged.

5. **DAG consistency: pass.** Checked the assigned node's actual recursive-lift,
transfer and homology/biproduct route, and each new node's source, statement,
blueprint, chapter/unit, creation, search and Lean records. For all three nodes,
proof_deps equals the union of proof-step uses. The assigned node changes only proof,
proof_deps and proof_origin; no statement or unit metadata changes. The restored
proof import keeps the split node's stated dependency available for its future proof.

Changed during this reading: restored the split theorem's open-unit proof import,
narrowed its public injective-resolution import, completed the moved-dependency
pruning report, and appended this independent review. Removed the redundant eager dsimp of the entire short-complex definition before
the final existential assembly; this preserves the proof route and the computed
data. No theorem statement or definition data changed. Scratch probes and search logs are
outside the delivery's Lean files.


Compilation note from this reading: one delivery dry run timed out at 60 seconds
on the assigned module, while preceding ordinary runs succeeded in 56–60 seconds.
A scratch profiler located the cost in final-proof type checking. Removed a redundant
eager `dsimp only [etaleSectionShortComplex]` before assembly; that version compiled
in 55.9 seconds. Transparency and wrapper/component-API experiments did not improve
the cost and were discarded completely. The prescribed dry run is retried on the
final sources with the original 60-second limit; no compiler or delivery tool is changed.
