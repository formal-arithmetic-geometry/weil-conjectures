## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.finite_constant_abelian_refinement`
with a compiling reduction. Its signature and public imports are unchanged.
Added the proof-only import `Sheaf.AlgebraicGeometry.FiniteConstantAbelianNeighborhood`.

The remaining lemma constructs an additive constant-presheaf chart near one point,
with an explicit equality identifying its underlying map with the constant set
sheafification unit followed by a set-sheaf isomorphism. The original theorem proves
local bijectivity from this equality, sheafifies the additive map, composes with the
invertible sheafification counit, and assembles a cover indexed by the underlying points.
No data definition was introduced, and no arbitrary witness was used in a definition.
Both modules compile cleanly with lcompile.py --all.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.finite_constant_abelian_refinement`
(node `lem-weil-pbc-finite-constant-abelian-refinement`).

Added and left: `AlgebraicGeometry.Scheme.finite_constant_abelian_neighborhood`
(node `lem-weil-pbc-finite-constant-abelian-neighborhood`).

This is a decomposition: one upper hole closed and one lower hole added, net zero.
The completed Lean argument proves the local-bijectivity, abelian sheafification,
and covering-assembly steps. The finite-operation chart construction remains.
The new lemma does not assert constancy or the existence of a covering.

## No longer needed

No existing imports removed; no modules pruned from the transitive proof route.
Second reading removed the redundant new-module import
`Mathlib.CategoryTheory.Sites.LocallyBijective`; it is already available transitively.
The parent no longer directly depends on `def-weil-pbc-geometric-stalks`,
`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`, or
`lem-weil-pbc-sets-sheafification-geometric-stalk`; these are still needed by the
new neighborhood lemma and are not globally pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed signature was found. The original dependencies supply
stalks, constant sheaves and cofilteredness but do not state the finite-operation
construction. That missing part is now a precise additive-presheaf chart statement.
Mathlib's `Sheaf.isConstant_iff_forget` requires fully faithful constant-sheaf functors;
these assumptions cannot be imposed on an arbitrary disconnected localized site.

Source checked: Stacks Tag 03RU, Definition 59.64.1, set and abelian clauses
(https://stacks.math.columbia.edu/tag/03RU). It supplies the definitions, not the
refinement theorem. The refinement argument is explicitly marked agent-formulated,
as in the original node. The local literature/stacks-project text is absent on this
machine; the tag was read online. No new independent literature claim is assumed.

Edge cases: an empty U has no points and yields an empty cover via mkOfCovers.
For a nonempty U, empty S cannot be identified with the underlying abelian stalk,
which contains zero. A singleton S gives the trivial abelian group. Disconnected U
is allowed because M and its operations may vary with the chosen point; no globally
constant group law is asserted. The set S and M remain in universe u+1; cover indices
are the underlying points of U in universe u. Restriction along V to U to Y is exactly
the original MorphismProperty.Over.map expression. The unit sk-thm-p1 route is unchanged;
this node is not a unit statement or a realized unit step.

Searches: LeanFinder returned eight hits including isConstant_iff_forget; Loogle
reported unknown identifier for Sheaf.IsConstant, with no hits; LeanSearch was
unavailable (Internal Server Error). The remote grep returned unrelated matches;
local rg and source reads located the local-bijectivity, localization and cover APIs.
Blueprint search for constant abelian returned two unrelated nodes, generic kernel
and constructible finite pushforward, neither an additive finite-chart construction.
The blueprint ancestor tool returned None for the item; the new node retains the
original node's recorded blueprint ancestor and route.

## New nodes

`lem-weil-pbc-finite-constant-abelian-neighborhood` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-constant-abelian-neighborhood.json`
is stated by `Sheaf.AlgebraicGeometry.FiniteConstantAbelianNeighborhood`.
It isolates the transported group law and its compatible additive presheaf map
near a single point. Its docstring records the finite germ-comparison proof.
No change record is needed: all existing statements and public interfaces are unchanged.

## Second reading by G2

1. Interfaces: compared the entire parent module with the repository using diff.
   Its existing theorem signature and docstring are byte for byte unchanged; its
   only added import is private to the proof. No definition or target changed.
   The new module contains one theorem and no data definitions. Verdict: pass.
2. Kernel check: compiled both modules in import order with lcompile.py --all,
   then compiled a scratch copy with #print axioms for both declarations. Both
   lists contain exactly propext, Classical.choice, Quot.sound and sorryAx.
   The sole textual sorry is finite_constant_abelian_neighborhood, as reported
   above. No forbidden declarations, options, or hidden data holes were found.
   The parent's proof chooses witnesses inside a theorem, not a definition.
   Verdict: sound reduction, conditional on the named remaining theorem.
3. Remaining statement: read its signature, docstring and new node together.
   Its hypotheses are exactly Y, G, U, finite S, the specified set chart and
   x in U.left. Its conclusions give V, an actual point over x, finite M, the
   reversed set chart, and an additive presheaf map with the precise underlying
   unit equality. Transporting the group law along the stalk-label bijection
   and restricting the finitely many zero, inverse and sum comparisons proves
   these clauses; restriction of a constant sheaf is canonically constant, and
   naturality of its unit gives the displayed equality. No connectedness is
   used. Empty U makes the point-indexed assertion vacuous; empty S at a point
   contradicts the nonempty abelian stalk; singleton S gives the zero group.
   Disconnected components may have different transported groups. This lemma
   stops before additive sheafification and covering assembly, both proved in
   the parent; it is a proper part of the argument, not a renamed conclusion.
   Read Stacks Tag 03RU, definition-finite-locally-constant, set and abelian
   clauses online: it supplies the definitions, not this refinement theorem.
   Additional LeanFinder search on finite labels and additive charts gave
   condensed/profinite results only. Loogle on the germ-equality name returned
   unknown identifier (not a mathematical nonexistence result). Remote grep
   on abelian charts and finite operations found Point/Basic.lean:224; its
   toPresheafFiber_eq_iff' statement gives exactly the germ comparison used.
   Local rg on Sheaf and upstream ConstructibleSheaf found no duplicate chart
   construction. Verdict: true, needed, and strictly simpler; not closed here.
4. Route and pruning: checked the cover's witnesses against hv and the
   localization W against the original composite map. The underlying equality
   hα gives local injectivity/surjectivity, W_iff turns this into an invertible
   additive sheafification map, and the invertible counit gives constancy.
   Read ConstantSheaf.lean:212--233: isConstant_iff_forget requires full and
   faithful constant functors, so it is not a shortcut on disconnected sites.
   Checked sk-thm-p1.json realized: neither parent nor new node replaces a
   realized statement or step. The three removed direct proof dependencies
   are all listed under No longer needed and retained under the new node.
   Verdict: route retained, no globally pruned module, net-zero decomposition.
5. DAG: compared the parent node against its repository version. Only proof,
   proof_deps and proof_origin changed, and they describe the actual Lean
   cover, local-bijectivity and sheafification steps. The new node contains
   source, proof, union of uses, three logged searches, split status, created,
   blueprint, chapter/unit and Lean record matching the new declaration.
   Verdict: consistent with the delivered reduction.

Second-reading repairs: removed the unnecessary public import
Mathlib.CategoryTheory.Sites.LocallyBijective from the new neighborhood module;
EtaleSheaves already provides the signature and proof APIs transitively, and
both modules still compile cleanly. Clarified the new module's source comments
so that Tag 03RU is credited for definitions only and the finite-operation
argument is explicitly agent-formulated. No existing statement changed.
