## What changed

Replaced `CategoryTheory.BigradedExactCouple.finiteCycle_kernel_presentation`'s sorry
with a complete Lean reduction. Its signature, definitions and public import are unchanged.
Added proof-only imports of `Sheaf.CategoryTheory.FiniteCycleDerivedComparison` and
`WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits`.

The proof constructs the epic finite-D lift from the actual alpha-image factorization and
`Subobject.isoOfMkEqMk`, using `pageCouple_image`. It proves the incoming-power recurrence,
the outgoing/incoming image equality, the generic kernel pullback formula, transported
exactness, epicity from the zero following D term, and the full intrinsic kernel calculation.
Only the comparison of original g with derived g remains a separate theorem. All helpers in
the item's module are private and proved. Updated the item's node proof to this route.

## Proved and sorry left

Closed: `CategoryTheory.BigradedExactCouple.finiteCycle_kernel_presentation`
(node `lem-sp-finite-cycle-kernel-presentation`). No sorry remains in the item's module.

Added one sorry: `CategoryTheory.BigradedExactCouple.finiteCycle_derived_comparison`
(node `lem-sp-finite-cycle-derived-comparison`), in
`Sheaf.CategoryTheory.FiniteCycleDerivedComparison`. Its proof is exactly `by sorry`.
This theorem only asserts coherence of two specified maps; it asserts neither epicity nor a
kernel identity and needs no vanishing assumption. The supplied e is uniquely determined by
its composite with monic I. No definition or data construction uses an arbitrary witness of
an unproved existence theorem.

This delivery is a decomposition: one upper hole closed, one strictly smaller coherence hole
added, net zero holes. The image-lift construction and both final exactness consequences are
proved in Lean. It is not a completed sorry-free proof of the original mathematical result.

Validation: both delivered modules compile through lcompile.py. A scratch Lean check proves
the r=0 projection identity directly from projection_zero and factorThru_arrow. The new
statement was also checked at r=0, in the zero category, and with arbitrary integer p,q:
there is no positivity or half-plane assumption; monic I prevents incompatible choices of e.

## No longer needed

No existing import, node or module is removed. ExactCoupleConvergence supplies the objects,
and DerivedCoupleExact supplies pageCouple_image. All original proof dependencies remain
needed. The new argument avoids reconstructing the finite-D epimorphism recursively:
the existing image theorem and the actual image factorization suffice. No additional kernel,
epicity, stabilization, colimit or half-plane lemma is imported or split off.

## Where the brief, the DAG or earlier work was wrong

The existing node's cited declarations do not state the original-g coherence of its second
step. This is the genuinely missing interface isolated in the new node. The original
step-three kernel and epicity consequences have been written in Lean rather than moved into
new holes. No statement was changed or disputed, and no forced adaptation was needed.

The unit record sk-prop-av-pqf-finite has empty realized arrays; this delivery preserves its
route and all existing dependencies. The ancestor tool returned None because the existing
created.item names a module rather than a node. The new node inherits the explicit
thm-sp-half-plane-convergence ancestor already recorded in the item's blueprint.from.
Blueprint searches for exact couple and cycle found no existing node stating this comparison.

The literature files are absent from this clone. Read the Stacks source directly:
[011R](https://stacks.math.columbia.edu/tag/011R), homology.tex label
lemma-derived-exact-couple, and [0AMJ](https://stacks.math.columbia.edu/tag/0AMJ), label
remark-shifted-exact-couple. The raw homology.tex was downloaded into sandbox scratchpad and
its induced-g clauses read. Tag 011R omits its proof; the new node records the induction as
an agent-written expansion. The attempted raw URL for the pinned blueprint file returned
404; its relevant step is also recorded in the existing item's docstring and DAG proof.
LeanSearch returned HTTP 500 (recorded unavailable). LeanFinder returned only generic exact
and snake-lemma declarations; Mathlib grep found no exact-couple-specific comparison.

## New nodes

`lem-sp-finite-cycle-derived-comparison` in
`dag/nodes/sec-abelian-varieties/lem-sp-finite-cycle-derived-comparison.json` states only the
original-g/derived-g equation for a lift with prescribed monic inclusion composite. The proof
in words gives the recursive image lift, uniqueness, base case, predecessor cycle lift,
DerivedMaps.g_comm, cancellation of kernel.ι, and projection_succ. Its new module is
`lean/Sheaf/CategoryTheory/FiniteCycleDerivedComparison.lean`. No change record is needed:
all existing signatures and visibility stay identical.

## Second reading by K3

1. Compared the delivered item with the repository by diff and checked the existing
   `finiteCycle_kernel_presentation` signature byte for byte. Verdict: unchanged.
   Its public import, visibility, universes, category assumptions, `hnext`, `hg`,
   epicity conclusion and exact kernel equality all remain identical. No definition
   or existing interface changed; no change record or forced adaptation is needed.
2. Compiled both delivered modules through `lcompile.py --all`, without errors or
   warnings. Checked all delivered text for forbidden declarations and sorry tokens:
   the item has none, and the comparison has exactly its named theorem's `by sorry`.
   Scratch `#print axioms` checks on both public declarations report only propext,
   Classical.choice, Quot.sound and sorryAx. Each of the five private helpers reports
   only the three standard axioms. The upper result still depends on the open
   comparison, so this is a decomposition, not a sorry-free proof. The actual image
   factorization constructs e; the pageCouple_image witnesses A and I are uniquely
   fixed by their recurrences. No arbitrary unproved existence supplies data.
3. Read `finiteCycle_derived_comparison` together with the actual `DerivedMaps.g_comm`,
   `alpha_comm`, `CycleBoundaryTower.cycleLift_comm`, `projection_succ` and
   `projection_zero` declarations. Verdict: true, needed, strictly smaller than the
   item. It is a map equality without the zero-D hypothesis, epicity or a kernel
   conclusion. Its I recurrence fixes I uniquely; monicity fixes e by he. At zero,
   he and hI0 identify e with the endpoint transport, and factorThru_arrow with
   projection_zero gives the equation; recompiled the supplied scratch base check.
   At one, g_comm identifies the alpha-image lift's composite with derived g with
   original g's cycle lift and quotient. The cycleLift_comm cancellation gives the
   same quotient projection. The zero category has unique maps, and all integer
   bidegrees are admitted, including negative ones. The docstring supplies the full
   induction and endpoint transports. Independent LeanFinder search for iterated
   derived g versus original g returned unrelated snake/homology results. Loogle
   did not locate an exact-couple comparison. Searches of lean/Sheaf, upstream Lean,
   and DAG nodes found no matching coherence statement. Read Stacks
   [011R](https://stacks.math.columbia.edu/tag/011R) and
   [0AMJ](https://stacks.math.columbia.edu/tag/0AMJ), including the induced shifted-g
   description and footnote: they support the construction, with the induction
   correctly identified as an agent-written expansion. The remaining induction
   requires dependent bidegree bookkeeping; it was not replaced with a new hole.
4. Checked the proof downward from the target: pageCouple_image supplies the
   uniquely specified inclusion and image formula; an actual image isomorphism
   constructs the epic lift; only the comparison is assumed; exact_g and exact_f
   yield the kernel and epicity. Found a shorter Mathlib route for the private
   kernel-composite helper: pullback_equalizer specialized to b and zero. Replaced
   its nine-line factorization argument with that one-line application. All imports
   are needed: the public convergence import supplies signature objects, the
   DerivedCoupleExact import supplies pageCouple_image, the comparison import
   supplies the coherence equation, and the upstream Subobject.Limits import
   supplies map_obj_eq_mk and the image lemmas. A scratch removal test for the last
   import fails at map_obj_eq_mk, confirming it is needed. No original proof
   dependency is unused, so No longer needed is complete (none pruned). Read
   dag/units/sk-prop-av-pqf-finite.json: realized statement and step arrays are
   empty; no unit realization or route was bypassed or altered.
5. Compared the existing node by diff: only proof, proof_deps and proof_origin
   change. Checked both nodes' lean.statement verbatim against their declarations
   and proof_deps against the union of their proof-step uses. Verdict: consistent.
   The new node has its source, self-contained statement, definition dependencies,
   three search records, split status, creation and blueprint provenance, matching
   chapter/unit, and complete Lean record. Its proof is the coherence induction,
   not the original epicity/kernel statement under another name.

Changed only the private kernel-composite proof to use Mathlib pullback_equalizer,
updated its explanation in the item's docstring and DAG proof step, and added this
review. No extra hole was closed or added during the second reading. The delivery
still closes finiteCycle_kernel_presentation and adds exactly
finiteCycle_derived_comparison: one upper hole, one lower hole, net zero.
