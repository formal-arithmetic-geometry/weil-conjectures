## What changed

Replaced the original sorry in
`AlgebraicGeometry.Scheme.Modules.tensorBoundary_graded_realization`
by a complete Lean combination of the algebraic presentation, homogeneous product,
action comparisons, and boundary naturality statements. Its signature and visibility are unchanged.
The sections, coefficient projections, and section-to-coefficient map are explicit
composites. The existence witness is eliminated inside this existential proof; no
definition chooses data from an unproved existence theorem.

Added `SquareZeroTensorGradedPresentation`, `SquareZeroTensorGradedProductProjection`,
`SquareZeroTensorGradedActionProjection`, and `SquareZeroTensorGradedBoundaryProjection`.
The presentation supplies homogeneous inclusions, degree projections, a kernel coproduct
cofan, homogeneous multiplication, short exactness, and square zero.
The product and action obligations contain no connecting-map assertions.
The boundary-projection obligation is one naturality diagram, with no multiplication or
action assertion. A proved diagonal section projection handles both input terms.

Proof imports are private; the original public imports are preserved.
The new kernel field uses the underlying sheaf-module type required by the target.
Explicitly typed section maps and direct equality compositions avoid expensive unfolding
of derived functors during elaboration. No existing dependency's interface was changed,
and there are no forced adaptations. The change record
`coord/changes/tensor-boundary-graded-realization-proof-local-commands.md` documents the
proof-local command additions that the conservative preflight treats as an interface change.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.tensorBoundary_graded_realization`
(`lem-sc-square-zero-tensor-boundary-graded-realization`).
This is a decomposition into four strictly smaller obligations, not a sorry-free proof
of the entire argument: one original hole closed, four holes added.

Also proved the additive projection evaluation API and the private diagonal-section
projection helper. These introduce no additional holes.

The only holes in the delivery, each exactly `:= by sorry` in its own module, are:

- `AlgebraicGeometry.Scheme.Modules.tensorGradedPresentation_exists`
  (`lem-sc-square-zero-tensor-graded-presentation`): the algebraic graded extension.
- `AlgebraicGeometry.Scheme.Modules.tensorGradedSection_product`
  (`lem-sc-square-zero-tensor-graded-product-projection`): homogeneous quotient products.
- `AlgebraicGeometry.Scheme.Modules.tensorGradedAction_projection`
  (`lem-sc-square-zero-tensor-graded-action-projection`): the two coefficient action squares.
- `AlgebraicGeometry.Scheme.Modules.tensorGradedProjection_boundary`
  (`lem-sc-square-zero-tensor-graded-boundary-projection`): naturality and resolution transport
  for one coefficient projection.

There is no sorry in the original module or in any definition or private helper.

## No longer needed

No module is pruned and no original public import is removed. The following old
`proof_deps` are no longer direct dependencies of the realization proof; they remain
needed in the four new obligations (so none is claimed removed from the import closure):

- `def-sbc-ideal-sheaf-powers`
- `def-sc-invertible-module`
- `def-sc-module-cohomology-boundary`
- `lem-pur-ringed-site-grothendieck-abelian`
- `lem-sc-module-section-boundary-exact`
- `lem-sc-p1-right-derived-triangle-connecting`
- `lem-sc-square-zero-ideal-tensor-unit`
- `lem-weil-pbc-affine-morphism-cohomology-edge`
- `lem-weil-pbc-closed-immersion-unit-quotient`
- `lem-weil-pbc-module-cohomology-fmap-functorial`

The realization now directly uses the presentation, product, action and boundary nodes.
The original construction, AB4, ideal-kernel, affine-edge, and coefficient functoriality
arguments remain in those nodes' proof plans. The right-derived triangle comparison is
part of the boundary diagram's proof plan. The unit `sk-thm-curveestimate` realizes its
statement at `thm-sc-proper-cohomology` and has no realized proof steps at this node;
its route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies do not supply the graded commutative algebra construction
or its homogeneous product and action calculations as ready-made Lean declarations.
The geometric steps and boundary diagram are now four separate obligations, each with
a complete proof in words. The earlier sandbox did not have a compiling final combination;
the combination is now complete. A prototype boundary proof passed a single-file check,
but its artifact-producing check exceeded the compiler limit. It is not part of this
delivery: the independently stated boundary diagram remains a named obligation, and the
prototype remains under scratchpad for the second reader. The unit-wrapper and sequential
checking experiments were reverted. No compiler limit was raised and no check was disabled.

Edge cases checked: n=0, e=0, zero sections, the zero ideal, and the empty scheme.
The arguments use diagonal projections when degrees coincide, not an assumption that
the degrees are distinct. No Noetherian, finite-type, or homeomorphism hypothesis was added.

The source is Stacks Tags 09MS (the graded direct-sum ideal sequence), 0B8S (quotient action),
and 01DZ (cohomology as a delta-functor). These pages were read directly because the local
Stacks source checkout is absent. The construction and action arguments unpack these
sources without assuming their derivation conclusion.

The previous searches are retained in searches.jsonl. Additional LeanFinder searching
for section-boundary naturality returned generic injective-resolution comparison lemmas;
Loogle found `ShortComplex.ShortExact.δ` and its API. Repository searches found no existing
graded realization or canonical section-boundary naturality theorem. The existing
right-derived triangle comparison supplies the needed boundary argument.

## New nodes

`lem-sc-square-zero-tensor-graded-presentation`: purely algebraic extension with its
homogeneous module maps. It asserts no boundary or cohomology action equation.

`lem-sc-square-zero-tensor-graded-product-projection`: product of the explicitly included
quotient sections, before applying a boundary or taking cohomology.

`lem-sc-square-zero-tensor-graded-action-projection`: the two action squares on coefficient
cohomology, independently of any boundary map or resolution presentation.

`lem-sc-square-zero-tensor-graded-boundary-projection`: a naturality diagram for
one degree projection and every compatible resolution. It has no product, action,
or realization-existence assertion.

Change record: `coord/changes/tensor-boundary-graded-realization-proof-local-commands.md`.

## Second reading by N4

1. Compared every delivered module with the repository. Only the realization module
   exists there; its theorem signature and docstring are byte-for-byte unchanged.
   Its original public imports remain. The extra imports are private proof dependencies.
   The other four modules are new. No existing definition or target statement changes.
   The existing node changes only lean/proof/proof_deps/proof_origin; the command additions
   are covered by the change record. Verdict: pass.
2. Read every definition, theorem and the complete final combination. The original
   theorem has no direct sorry. Four named public theorems have exactly `:= by sorry`,
   as listed above, with source/proof docstrings and matching nodes. No prohibited
   axiom, unsafe/opaque declaration or foreign implementation appears. Sections and
   projections are explicit composites of their arguments. T is eliminated inside the
   existential proof; no definition selects an arbitrary witness from its existence
   theorem. All five modules passed artifact compilation under the 60 s limit and the
   delivery's all-constant axiom probes passed. Explicit scratch #print axioms checks
   showed only propext/Classical.choice/Quot.sound plus the expected sorryAx for the
   realization and its four open obligations; both proved projection helpers use
   only the three permitted axioms. Verdict: pass as a decomposition.
3. Checked the four obligations separately. The presentation is the polynomial algebra
   gluing construction for a line bundle, with exactness checked stalkwise. The product
   calculation follows by local lifting through the degreewise quotient and b_multiply.
   For actions, k_colimit exhausts the kernel locally, and its diagonal/off-diagonal
   equations compute the homogeneous component; mono i fixes the quotient action.
   The boundary obligation is naturality for one short-complex morphism, with compatible
   resolution transport. No obligation restates the full realization or assumes a
   boundary product rule. Checked n=0, e=0, coincident degrees, zero sections, J=0 and
   the empty scheme; no extra finiteness assumption is needed. Read Stacks
   [09MS](https://stacks.math.columbia.edu/tag/09MS),
   [0B8S](https://stacks.math.columbia.edu/tag/0B8S) and
   [01DZ](https://stacks.math.columbia.edu/tag/01DZ). Independent LeanFinder searches
   for symmetric algebra sheaves/homogeneous components found TensorPower.galgebra
   and generic tensor/symmetric algebras, not this sheaf construction. Loogle found
   HomologicalComplex.HomologySequence.δ_naturality, which concerns complexes, not
   the canonical moduleSectionBoundary transport. Grep and repository searches for
   symmetric/graded algebra sheaves and section naturality found no duplicate theorem.
   The retained boundary prototype already requires that transport and exceeded the
   artifact compiler limit; it is not a quick closing of the remaining obligation.
   Verdict: true, needed and strictly smaller obligations; decomposition only.
4. Followed the final proof from the realization downward. The final witness and all
   five equations are assembled explicitly, rather than delegated to a renamed copy.
   All public imports provide objects appearing in signatures or definitions, and the
   two new imports of the old module are private. No old closure dependency is claimed
   pruned; clarified the direct dependencies delegated to the new nodes in No longer
   needed. Checked sk-thm-curveestimate.realized: this node is neither its statement
   nor a proof step; no realized route is bypassed. Verdict: pass.
5. Checked every node's proof steps and proof_deps union against the Lean reduction
   and the remaining docstring arguments. New nodes have source, searches, creation,
   blueprint, chapter/unit and Lean records, and each recorded signature matches its
   theorem. The old node's four direct proof dependencies match the four applied
   obligations. Verdict: pass.

Second reading changed the pruning report to enumerate all ten old direct dependency
nodes delegated to the new obligations. Simplified the action step of the Lean reduction from an explicitly typed conjunction
proved by `apply` to a fully supplied theorem application, avoiding redundant expected-type
elaboration. All four valid split-off statements are unchanged. One original hole closed, four added: net -3,
with no module pruned; this is not claimed as a sorry-free proof.

The first artifact-producing compilation timed out in the realization module at 60 s;
all four new modules compiled. The simplified action step compiles in a single-file
check in 17.6 s. No compiler limit was raised, definition changed or proof split to
avoid the limit. The dry run passed final artifact compilation, all-constant axiom probes and
preflight (commit 152da71388). Explicit scratch axiom checks also passed in 15.6 s.
