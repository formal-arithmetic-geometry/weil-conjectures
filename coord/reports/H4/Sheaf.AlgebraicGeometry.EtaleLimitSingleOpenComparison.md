## What changed

Replaced the sole sorry in `AlgebraicGeometry.Etale.etale_limit_single_open_comparison`
with a proof from two strictly separate intermediate statements. The original
signature, universes, public imports and conclusion are unchanged.

`EtaleLimitOpenCohomologyCocone` constructs canonical cohomology arrows and legs
on inverse-image opens, for any cone and any sheaf cocone. It has no scheme-limit,
compactness, affineness, sheaf-colimit, allowed-stage, ambient H, or ambient B
hypotheses. Its conclusion has no restriction transformation, comparison map,
or certificate. It supplies the algebraic functor/cocone part of the argument.
Its definitions are explicit constructions using `resLE`, `upperStarComp`,
cohomology pullback and coefficient maps; none select an arbitrary witness from
an unproved existence theorem.

`EtaleLimitOpenComparisonCertificate` takes the canonical diagram and cocone as
inputs and certifies their supplied colimit descent. Its conclusion constructs
no diagram, cocone or restriction transformation and asserts no stage-leg
restriction equation. The remaining argument is geometric: restricted scheme
limit, qcqs stages, final tail and restriction preserving the sheaf colimit.

The new cocone module also proves `openSquareCoefficient_cohomology` in every
degree from `cohomologyPullbackFunctorial` and `cohomologyMap_map`. The original
module uses this commuting-square calculation to construct the restriction
natural transformation and prove its naturality. It then uses `colimit.desc`,
`colimit.ι_desc`, the canonical leg formula and the given hB to prove the final
stage-leg equation. This is a decomposition with real assembly, not a renamed
copy of the original existential theorem.

The copied DAG node follows this proof. Both new nodes remain below the unit
level; none of the realizations of sk-thm-p1 is bypassed. All files remain module
files. New statement-level dependencies are public only in the new modules;
the original module imports the new certificate module privately.

## Proved and sorry left

Closed the original module's one hole:
`AlgebraicGeometry.Etale.etale_limit_single_open_comparison`
(node `lem-weil-pbc-etale-limit-single-open-comparison`). It is proved from the
intermediate statements; this is a decomposition, not a claim of a sorry-free
import closure.

Added exactly two named holes:

- `AlgebraicGeometry.Etale.etale_limit_open_cohomology_cocone`
  (node `lem-weil-pbc-etale-limit-open-cohomology-cocone`).
- `AlgebraicGeometry.Etale.etale_limit_open_comparison_certificate`
  (node `lem-weil-pbc-etale-limit-open-comparison-certificate`).

No sorry remains in the original module or in any definition. The public helper
`AlgebraicGeometry.Etale.openSquareCoefficient_cohomology` and its private
composition-transport helper are completely proved. The closed-minus-added
hole count of this delivery is -1; no net hole reduction is claimed.

The statements were checked on empty W, zero coefficients, identity singleton
diagrams, and W = O. The algebraic cocone theorem deliberately does not assume
hL or hc, since arbitrary cocones and arbitrary cones still give canonical
cohomology cocones. The certificate theorem does assume both; its geometric
construction would not certify an arbitrary coefficient cocone as a system.

## No longer needed

Removed these direct proof imports from the original module:

- Sheaf.AlgebraicGeometry.EtaleLimitCanonicalCohomologyDiagram
- Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
- Mathlib.AlgebraicGeometry.AffineTransitionLimit
- Mathlib.CategoryTheory.Filtered.Final
- Mathlib.CategoryTheory.Adjunction.Limits

These dependencies are assigned to the two intermediate modules where needed,
not mathematically discarded. No previously planned node or module is globally
pruned: the original geometric/coefficient route is retained. The parent node's
direct proof dependencies are now the two new nodes. No unit realization changes.

For completeness, all former direct `proof_deps` replaced on the parent node are:

- `def-weil-pbc-scheme-conventions`
- `def-weil-pbc-stage-cohomology-comparison`
- `lem-weil-pbc-cohomology-pullback-functorial`
- `lem-weil-pbc-colimit-initial-full-subcategory`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-etale-limit-canonical-cohomology-diagram`
- `lem-weil-pbc-inverse-image-composition`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `lem-weil-pbc-limit-cone-affine-projections-opens`

These remain statement dependencies or dependencies of the two intermediate
nodes; none is claimed globally unnecessary. The second reading also removed
the redundant public import `Mathlib.Algebra.Category.Grp.Colimits` from the
new cocone module: its required group colimits are already publicly available
through `UpperLowerStar.TopologicalInvariance`.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically reasonable, but its named dependencies do not
package the restricted coherent coefficient system and its canonical cocone.
They give the generic canonical cohomology construction, the open scheme limit,
and the separate inverse-image/colimit tools. The new statements isolate that
unformalized glue without changing any existing interface.

The cited Stacks sources are absent from this machine's literature directory.
Read the already cited sources at https://stacks.math.columbia.edu/tag/09YQ and
https://stacks.math.columbia.edu/tag/01F7; no new literature source is introduced.
Tag 09YQ supplies the coherent-system framework, not a certificate theorem:
the certificate is this library's bookkeeping for its construction. We use no
cohomology continuity theorem to assert the supplied descent is an isomorphism.

Searches were run through msearch.py using LeanFinder, Loogle, grep and
LeanSearch. LeanSearch returned Internal Server Error, recorded as unavailable;
it was not treated as evidence of no match. The successful services found the
open-diagram geometric tools and unrelated section/cohomology restrictions,
not either intermediate statement. Local searches of both library roots found
no duplicate. Blueprint searches for the coherent-system/restriction step found
no matching blueprint node. The new nodes point through the parent to its
existing nearest blueprint ancestor.

## New nodes

`lem-weil-pbc-etale-limit-open-cohomology-cocone`, in
`lean/Sheaf/AlgebraicGeometry/EtaleLimitOpenCohomologyCocone.lean`, isolates
canonical diagram/cocone construction with explicit restricted arrow and leg
formulas. Its source is Tags 09YQ and 01F7; its docstring gives the full argument.
The module additionally gives real definitions for these arrows and proves the
commuting-square cohomology identity used by the original module.

`lem-weil-pbc-etale-limit-open-comparison-certificate`, in
`lean/Sheaf/AlgebraicGeometry/EtaleLimitOpenComparisonCertificate.lean`, isolates
the geometric certification of supplied canonical arrows and legs. Its source
is the same restricted-system construction together with the Mathlib opens
limit and adjunction/finality tools already in the parent plan. Its docstring
gives the full argument. No existing statement or definition changes, no forced
adaptation, and no change record are needed.


## Second reading by H4

1. Compared the existing module with the repository using `diff` and a byte
   comparison of its theorem signature. Verdict: identical hypotheses,
   universes, conclusion and existing public imports. The only existing-node
   fields changed are `proof`, `proof_deps`, and `proof_origin`. No target,
   definition or existing interface is changed; no change record is needed.

2. Compiled all three modules in import order with `lcompile.py`; no errors or
   warnings. Checked every new definition and the actual naturality and stage-leg
   calculation. No arbitrary witness is selected in a definition. The only two
   sorries are the reported named theorems, each with a sourced proof docstring.
   A scratch import module with `#print axioms` for every public declaration
   showed only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for
   the two open theorems and their parent. All explicit constructions and the
   commuting-square theorem use only the three permitted axioms. The scratch
   file was removed before delivery. Verdict: valid conditional proof, with
   exactly the two disclosed holes; not a sorry-free proof of the import closure.

3. Read both split statements and their full proof docstrings against the
   canonical cohomology theorem, inverse-image coherence and the `system`
   certificate constructor. Checked empty W, zero coefficients, identity
   singleton diagrams and W = O: no missing nonemptiness, injectivity or
   continuity hypothesis. The algebraic statement permits an arbitrary cone
   and cocone and supplies only canonical arrows and legs; the geometric one
   certifies the supplied descent and needs no ambient H or B. Each is strictly
   a part of the original argument, not a renamed existential target. Read
   Stacks Tags 09YQ and 01F7 online: their system/functoriality framework is used,
   not their continuity conclusion. Independent searches with LeanFinder
   (commuting-square canonical cocones; quasi-compact inverse-image systems),
   Loogle (`"resLE", "comp"`) and grep (`upperStarComp|cohomologyMap_map|resLE_comp`),
   plus rg in both source roots, found geometric restriction/coherence tools
   and the existing generic cohomology construction, but no duplicate of either
   split statement. Verdict: true, needed reductions; finishing their geometric
   and inverse-image coherence constructions is not a few-minute proof repair.

4. Read the proof from its target downward. The restriction transformation,
   naturality, and stage-leg equation are genuinely proved using the square
   identity and colimit descent. The generic upstream diagram theorem alone
   does not provide restricted coefficient-system coherence or certification.
   Removed the redundant public group-colimits import in the new cocone module;
   its file still compiles. Preserved the proof-tool imports used by the documented
   plans of the two open statements. Completed `No longer needed` with all nine
   former direct proof dependencies, explicitly distinguishing reassignment from
   global pruning. Inspected `dag/units/sk-thm-p1.json` and its `realized` entries:
   no realization is bypassed or changed. Verdict: route retained; no globally
   pruned module and no net hole reduction claimed.

5. Matched the new node statements verbatim to their Lean theorem signatures;
   checked required source, creation, blueprint ancestry, search and Lean fields.
   All three `proof_deps` lists equal the union of their proof-step `uses`.
   The parent records the actual reduction, while the two open nodes retain
   the documented remaining proof plans. Verdict: DAG agrees with Lean.

Second-reading changes: removed one redundant public import from the new
cocone module and completed the pruning/dependency report. No proof or statement
repair was necessary. The delivery closes one original hole and adds two lower
holes (net -1), so its original-hole closure is a decomposition.
