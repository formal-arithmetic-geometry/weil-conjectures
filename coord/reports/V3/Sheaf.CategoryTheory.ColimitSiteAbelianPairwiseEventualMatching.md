## What changed

Proved the body of `CategoryTheory.colimit_site_abelian_pairwise_eventual_matching`
without changing its signature. Added private proved helpers `comparison_kernel_iff` and `unit_kernel_mono`.
The comparison helper is generalized in place to coefficient universe `max u v`,
with explicit weak-sheafification instances at S and R. Its same-universe
specialization proves the assigned statement. Both delivered modules reuse the
private `exists_transition` theorem via proof-only
`import all Sheaf.CategoryTheory.ColimitSiteAbelianStageImageRefinement`. Added proof-only imports of
`Mathlib.CategoryTheory.Adjunction.Unique`, `Mathlib.CategoryTheory.Filtered.Final`,
and `Sheaf.CategoryTheory.ColimitSiteAbelianUnitKernelBound`.

The proof combines naturality and compatible-family equality, identifies comparison
kernels by uniqueness of adjoints, applies a raw section-formula kernel bound,
proves directedness of the stage-unit kernels, extracts one kernel using Mathlib,
and constructs the required Under morphism. The assigned node now records this route.
All original public imports and all existing signatures remain unchanged.

## Proved and sorry left

Closed: `CategoryTheory.colimit_site_abelian_pairwise_eventual_matching`
(node `lem-weil-pbc-colimit-site-abelian-pairwise-eventual-matching`).
There is no sorry in the assigned module or its private helpers.

New auxiliary theorem proved: `CategoryTheory.colimit_site_abelian_unit_kernel_bound`
(node `lem-weil-pbc-colimit-site-abelian-unit-kernel-bound`) by reusing the
proved abelian section diagram and the acyclic finite section eventual-zero theorem.
This new proved theorem adds no hole; it is not a pre-existing hole closed.
The delivery closes one original hole and adds zero holes. No sorry remains in either delivered module; the resulting declarations use `propext`, `Classical.choice`, `Quot.sound`,
and transitive `sorryAx` from the still-open raw section sheaf/evaluation route.
They are locally proved reductions, not axiom-complete results. The existing
open declarations are `CategoryTheory.colimit_site_raw_abelian_section_isSheaf`
and `CategoryTheory.colimit_site_raw_abelian_section_evaluation`; neither is
modified or newly stated in this delivery. No net target-closure ledger figure
is claimed here; the maintainer's pinned-baseline ledger determines that figure.

Local compilation of both modules in import order passes cleanly. Kernel-bound
edge cases checked: zero sheaf/zero section, constant identity diagram, empty
source category (no X), and an empty cover (zero matching group).

## No longer needed

Removed both duplicate local `exists_transition` proofs; the existing theorem
in `ColimitSiteAbelianStageImageRefinement` is reused. No modules are pruned.

No original imports removed and no original proof-dependency nodes pruned (the
assigned node originally had no proof dependencies). Its original three steps
are retained with the raw section-formula step isolated.

No original imports were removed from the parent. The three proof-only imports are necessary for the kernel-bound proof; they supply the section diagram, the existing transition helper, and the eventual-zero theorem. The parent still does not import the cyclic section-eventual-equality and finite-unit-zero routes.

## Where the brief, the DAG or earlier work was wrong

Repair of the returned landing: the earlier delivery duplicated two existing
private helpers. Transition existence is now imported and reused in both
modules. `import_direction.py` rejects importing `ColimitSiteAbelianSectionEventualEquality`
into this item because it closes a cycle, so the comparison helper is genuinely
generalized in place to larger coefficient universes with explicit sheafification
instances, as permitted by the return. No existing library module is adapted.
The previous second-reading section has been removed pending a fresh reading.

The assigned node marked its multi-page raw section-colimit construction as
`elementary: true` with no dependencies. That step is substantial and is now a
separate theorem with its source and complete construction argument in the
docstring and node. The naturality and adjunction/unit arguments are proved.

The earlier reading incorrectly treated the acyclic `ColimitSiteFiniteSectionEventualZero` module as unavailable and left the kernel bound as a new sorry. It is present in the current library and supplies exactly the needed transition after the existing section-diagram construction, so the hole can be closed without copying the cyclic finite-unit-zero route.

The local literature/stacks-project/sites.tex is absent. Read Tag 0A35 directly
at https://stacks.math.columbia.edu/tag/0A35 (section formula, presentation,
finite matching equalizer, and adjunction identification); the node retains
the project's canonical source path. No change to the sk-thm-p1 unit's statement
or realized steps; this is below its unit-level route. Blueprint searches for
colimit of sites and kernel found no matching blueprint node, and the supplied
item's ancestor tool returns None.

## New nodes

`lem-weil-pbc-colimit-site-abelian-unit-kernel-bound`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-colimit-site-abelian-unit-kernel-bound.json`,
states that the colimit-site source-unit kernel lies in the supremum of later
source-unit kernels. Its module is
`lean/Sheaf/CategoryTheory/ColimitSiteAbelianUnitKernelBound.lean`.
The raw presentation construction must stay independent of stage-image matching.
LeanSearch was unavailable (HTTP 500); LeanFinder returned generic sheaf results;
Mathlib grep found no varying-site kernel formula. No change records or forced
adaptations are required.


## Second reading by V3

1. **Interfaces — pass.** Compared both delivered modules with the repository.
   The kernel-bound module is new. The assigned theorem's signature is byte for
   byte identical; no existing definition, declaration visibility or public
   import changed. Restored its original docstring. No change record or forced
   adaptation is required.
2. **Proof and trust — pass.** Read both proofs and the reused adjunction-transpose,
   section-diagram and finite-section eventual-zero interfaces. Both modules
   compile locally. Scratch `#print axioms` checks show `propext`,
   `Classical.choice`, `Quot.sound`, and transitive `sorryAx` for both public
   theorems. The section diagram and transition helper have only the three
   standard axioms; finite-section eventual zero depends on still-open raw
   section sheaf and evaluation theorems. This is permitted reliance on open
   downstream nodes, not an axiom-complete proof. No sorry,
   axiom, unsafe, opaque, extern, implemented_by, or hollow definition is added.
   The chosen transition maps come from a proved adjunction theorem and are
   uniquely determined by the unit equations. The section diagram is obtained
   from a proved construction, not an unproved arbitrary existence witness.
3. **Auxiliary statement — pass.** The kernel bound is strictly an intermediate
   source-unit assertion, independent of covering pairs and of the supplied
   alpha/theta families. Its proof actually exhibits membership in a later
   kernel, then inserts that kernel into the supremum. Zero sections and the
   zero sheaf satisfy it; a constant identity diagram has zero kernels; an empty
   source category has no test object. Empty covers are handled by the raw
   eventual-zero dependency's sheaf construction. Its source and complete proof
   docstring and node agree. Fresh LeanFinder, Loogle and Mathlib grep searches
   found no shorter direct replacement; local source searches found the cyclic
   SectionEventualEquality comparison helper and the acyclic declarations used.
4. **Route and pruning — pass.** Checked naturality/compatibility, the two unit
   kernel comparisons, monotonicity, filtered directedness and extraction from
   the supremum. All added imports are proof-only in the parent. The new module's
   public group limits, colimits and filtered-colimits imports supply instances
   needed by its signature; removal tests confirm their role. No original
   proof dependency existed, so none was omitted from No longer needed. No module
   is pruned. Read sk-thm-p1.realized: this work lies below its preserved route
   and does not bypass any realized unit step.
5. **DAG agreement — pass after metadata repair.** Both proof step lists and their
   dependency unions match the code. The new node has the required provenance,
   source, Lean signature, searches and blueprint fields. Corrected its stale
   search verdict claiming that the acyclic eventual-zero module was unavailable,
   and recorded fresh searches. The existing parent node's historical search
   text has the same stale claim; that field is outside stage-3 ownership and
   its new proof/proof_deps/proof_origin correctly record the available route.

Changes in this reading: restored the existing theorem's original documentation;
clarified that one original hole is closed and zero holes are added; corrected
search/provenance metadata and the report's count of proof-only imports. Corrected the first worker
report's false claim of standard axioms only. No proof repair was needed. Checked the cited source directly at
[Stacks Tag 0A35](https://stacks.math.columbia.edu/tag/0A35) and
[Stacks Tag 03CO](https://stacks.math.columbia.edu/tag/03CO).
