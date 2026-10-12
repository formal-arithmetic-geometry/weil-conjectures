## What changed

Proved `SheafOfModules.homObj_finitePresentation_kernel` with its signature unchanged.
The existing `homObjFreeIso`, biproduct-to-product isomorphism, and product reindexing
provide concrete coordinate isomorphisms. Private proved helpers identify their
projections with evaluation on `freeSection` and restrict the coefficient identity
before applying a local linear map. The theorem constructs both maps and transports
`homObj_precomposition_exact` along an explicit isomorphism of composable arrows.

Refactored the already proved `homObj_precomposition_exact`: moved its generic
kernel-preservation argument into a private proved helper, supplied the object of
the identity-component natural isomorphism explicitly, and used direct rewriting
and `pre_app` for naturality. This reduces elaboration cost without changing the
argument or any existing public signature. The initial unchanged module twice
exceeded the local 60-second compiler limit. The revised first proof compiled in
38.6 seconds, and the coordinate development compiled in 10.4 seconds.

The integrated module compiled without warnings in 49.8 seconds. Scoped the
elaboration options to individual declarations after the first preflight flagged
a file-level option as an interface command.

No imports, definitions used by targets, public interfaces, or assumptions changed.
Updated only proof and proof_origin of the existing node to record the completed
coordinate argument. All helpers are private and completely proved; the private
coordinate definition is a composition of existing, proved isomorphisms.

## Proved and sorry left

Hole closed: `SheafOfModules.homObj_finitePresentation_kernel`, node
`lem-weil-pbc-sheaf-hom-finite-presentation-kernel` (one of one holes in the
refreshed repository baseline).

`SheafOfModules.homObj_precomposition_exact` was already proved by G2; its proof
remains complete. No holes added, no new nodes, and no `sorry` remains in the item.
This is a proof, not a decomposition. Edge cases m = 0, n = 0, the zero module,
and the empty space remain covered by the same finite biproduct and restriction
arguments: no positivity or nonemptiness hypothesis was introduced.

## No longer needed

None newly pruned. The refreshed baseline already removed
`Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting` and its proof
node, together with the old restriction-exactness proof dependency
`def-pur-localized-ringed-site`. The coordinate proof likewise needs neither.
All current imports are retained: `InternalHomFree` supplies the finite free
coordinate isomorphism and the additive instance needed by the first theorem;
`Monoidal.Closed.Braided` supplies contravariant internal Hom limit preservation.
The public imports support the unchanged statements and sheafification instances.
No unit realization or step of the blueprint unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

The initially read module had two holes, but the repository received G2's proof
of precomposition exactness during this session. Refreshed the sandbox to use
that proof and treat only the coordinate theorem as the remaining hole.
The prior node already proposed transport of exactness, so no further local
lifting argument is necessary. Its step 7 described the coordinate theorem as
still open; that step now records the completed explicit transport.

No statement was disputed or changed, and no forced adaptations were needed.
The source file named in the existing node, literature/stacks-project/modules.tex,
is absent in this clone. The proof follows the full source-based argument already
recorded in the item and node and uses existing proved library constructions;
no new sourced intermediate statement is being introduced.

## Second reading by H3

1. PASS: Compared the delivered module and node with the repository versions.
   Extracted both existing theorem signatures through `:= by` and checked
   byte-for-byte equality: both are unchanged. The import block, public section,
   universes, variables, and existing docstrings are unchanged. The new coordinate
   definition and four helper theorems are private. No public definition or
   statement was changed, so no change record or forced adaptation is needed.
2. PASS: Independently compiled the delivered module through lcompile.py with no
   warnings or errors (54.1 seconds). Compiled a scratch copy with `#print axioms`
   for both public theorems, all four private helper theorems, and coordIso
   (45.0 seconds). Every declaration uses exactly propext, Classical.choice, and
   Quot.sound; none uses sorryAx. Searched the delivered source for sorry, axiom,
   unsafe, opaque, implemented_by, extern, and sorryAx: none occurs. coordIso
   composes existing isomorphisms and chooses no arbitrary existence witness.
3. PASS: No statements were split off and no new nodes or holes were added.
   Read each helper proof: leftExact maps the opposite kernel; coordIso_π
   identifies projections; coordIso_apply evaluates basis sections;
   coefficients_apply restricts hc before applying a linear map. None assumes
   positive ranks, nonzero modules, or a nonempty space. Empty finite sums and
   products cover m = 0 and n = 0. Independent leanfinder and loogle searches
   (recorded in searches.jsonl), plus rg on Mathlib, upstream, and lean/Sheaf,
   found no shorter theorem providing these two coordinate formulas together
   with exactness. The existing homObjFreeIso and homObjUnitIso are already used.
4. PASS: The proof closes the upper coordinate hole by transporting the already
   proved precomposition sequence, without lower holes. The public imports
   supply homObj, free/freeSection, zero objects and finite products, exactness,
   the open-set site, and the sheafification instances required in signatures.
   InternalHomFree and Monoidal.Closed.Braided are correctly plain imports: they
   provide the proof's coordinate isomorphism, additive instance, and internal
   Hom limit preservation. No additional old proof dependency is unused.
   `## No longer needed` correctly records no newly pruned nodes or imports.
   Read dag/units/sk-thm-p1.json realized: this below-unit argument bypasses none
   of its statement or step nodes and changes no unit route.
5. PASS: The node changes only proof steps 5--7 and proof_origin. Its unchanged
   proof_deps equal the union of uses in all seven steps. Read their Lean and
   Mathlib records: epi_f implements the abelian exactness leaf, while the
   sheaf Hom, exact-sequence, module-category, and free-presentation dependencies
   correspond to the proof. The new step texts accurately describe the explicit
   coordinate isomorphisms, restriction of coefficients, and isoMk₃ transport.

Changes made by the second reader: this review section only; no Lean or DAG
repair was necessary. One existing hole closed, zero holes added, no split-off
statements, and no newly pruned module.
