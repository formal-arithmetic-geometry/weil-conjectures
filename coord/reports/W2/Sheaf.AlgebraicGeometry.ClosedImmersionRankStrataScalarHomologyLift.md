## What changed

Replaced the sole sorry in
`AlgebraicGeometry.closedImmersion_rankStrata_scalar_homology_lift` by a compiling
reduction to the new `Sheaf.Algebra.Homology.OpenSupportedHomologyApproximation`.
The item's existing signature and public imports are unchanged. No definitions,
other existing modules, target statements, or unit records are changed.

The item proves the negative-degree zero-source case; constructs the open complement
of the closed image of the other rank strata; proves both stalk support conditions
using `closedImmersion_pushforward_stalks` and `Scheme.Modules.pushforwardComp`;
uses a local approximation; proves lifting from a concentrated derived object using
Mathlib's standard t-structure; and proves the final homology equation by naturality
and functoriality. Both new private helpers are fully proved.

Added proof-only imports of the new approximation module, ClosedPushforwardStalks,
and Mathlib's DerivedCategory.TStructure. Removed the item's direct proof-only imports
of DerivedOpenShriekAdjunction and ModuleStalkExact; ModuleStalkExact remains needed below the
approximation lemma. Updated the item's proof route in its DAG node and added the
new approximation node. The report supersedes the earlier rejected delivery report.

Validation: the two delivered modules compile in import order without warnings.
The required deliver3.py --no-push dry run passes except for the second reading,
which is reserved for the next worker. Nothing is pushed.

## Proved and sorry left

Holes closed (1):
`AlgebraicGeometry.closedImmersion_rankStrata_scalar_homology_lift`
(node `lem-sc-closed-immersion-rank-strata-scalar-homology-lift`).
The private helpers `single_lift_of_concentrated` and `rank_term_stalk_zero` are proved.
There is no sorry left in the item module.

Holes added (1): `AlgebraicGeometry.open_supported_homology_approximation`
(node `lem-sc-open-supported-homology-approximation`), in its own new module.
Its proof is exactly `:= by sorry`. This is a decomposition, with net hole count zero,
not a completed proof independent of new holes. The remaining statement is precisely
the local extension-by-zero counit step, without a single-complex lift or any rank,
scheme, or closed-immersion data. The item supplies those parts in Lean.

## No longer needed

Removed direct imports: `Sheaf.Algebra.Homology.DerivedOpenShriekAdjunction` and
`Sheaf.Algebra.Homology.ModuleStalkExact`. ModuleStalkExact and its node remain needed
transitively for the new local approximation. DerivedOpenShriekAdjunction and its
node `lem-sc-derived-open-shriek-derived-adjunction` are unnecessary on this route:
the exact underived adjunction suffices for the termwise counit construction.
The old direct dependency `lem-sc-derived-open-restriction-adjunction-exact` is
now used transitively by the approximation. No whole-library pruning is claimed;
all original logical steps remain, reorganized around the approximation.

The rejected `ClosedImmersionRankStrataScalarHomologyPresentation` module and
`lem-sc-closed-immersion-rank-strata-homology-presentation` node are not imported or
delivered. Their old archived files under scratchpad are outside the delivery.
The different direct-image-algebra `ClopenRankStrataHomologyLift` is not used.

## Where the brief, the DAG or earlier work was wrong

The earlier global presentation theorem was false. For Z = Y = Spec(k), i the
identity, r constantly zero, T^0 = O and all other terms zero, take K concentrated
in degree zero and n = 1 (or n = -1). The other-degree homology hypotheses hold,
but K is not a single complex on its zero degree-n homology. The current reduction
instead produces a concentrated object L with a morphism L -> K and factors maps
from the supported source through H^n(L). It never claims L is isomorphic to K.

The proposed new approximation was checked on U empty (S and L zero), U the whole
space (the counit invertible), S zero, and the previous counterexample. In the last
case the item handles n negative directly; for n positive its rank support is empty
and its source is zero. The factorization is harmless even when other homology of K
is nonzero away from U. No finite-image or nonempty-stratum hypothesis was added.

The local literature checkout is absent on this machine. Read the primary source
pages https://stacks.math.columbia.edu/tag/08BS and
https://stacks.math.columbia.edu/tag/08BT. The former proves K-injective restriction
using the exact left adjoint; the latter explicitly gives the derived adjunction.
The new lemma is an agent expansion of those facts and the existing item's steps,
with the termwise-counit argument written out in its docstring. The unit's realized
lists are empty for this node; no fixed unit statement or proof step is bypassed.

## New nodes

`lem-sc-open-supported-homology-approximation`, module
`Sheaf.Algebra.Homology.OpenSupportedHomologyApproximation`, states the local
extension-by-zero approximation and factorization. Its complete natural-language
proof constructs an exact endofunctor and a termwise counit, so it needs no additional
derived-category universe instance on the open. It has no chosen data definition.
Mathlib semantic, type-pattern, and source searches found the single-degree lemma
used in the item, but no duplicate approximation. LeanSearch was attempted and
returned Internal Server Error, recorded as unavailable. Blueprint search for
extension by zero found no matching module-sheaf approximation statement.
No change record is required: no existing interface changes.

## Second reading by W2

1. Interface: read the full diff of the item against the repository. The signature
   of `closedImmersion_rankStrata_scalar_homology_lift` is byte-for-byte identical,
   including the unrestricted degree-n homology and the arbitrary scalar map a.
   All three public imports, the existing docstring, universes, and visibility
   are unchanged. There are no definitions or forced adaptations in the delivery.
   The existing node changes only proof, proof_deps, and proof_origin. Verdict: pass.
2. Proof: compiled both modules in import order through lcompile.py without errors
   or warnings. Explicit #print axioms in temporary copies checked both private
   helpers, the item, and the approximation theorem. The helpers use only propext,
   Classical.choice, and Quot.sound; the item and approximation additionally use
   sorryAx, exactly as expected from the named approximation hole. No forbidden
   declarations, skipped kernel checks, or data definitions occur. The item has
   zero holes; the new module has precisely its one named theorem hole. Verdict:
   valid reduction, not an independent completed proof.
3. Split statement: read the entire approximation signature and node, and the
   underived exact-adjunction and open-extension-counit-stalk declarations it uses.
   Read Stacks Tags [08BS](https://stacks.math.columbia.edu/tag/08BS),
   [08BT](https://stacks.math.columbia.edu/tag/08BT), and
   [00A7](https://stacks.math.columbia.edu/tag/00A7). These support the exact
   adjunction and stalk descriptions; the approximation is the agent's stated
   termwise-counit consequence, not a verbatim lemma from those tags. Applying
   the exact endofunctor to a representative complex supplies L and b. Its
   homology comparison is compatible with the counit, so counit naturality gives
   the factorization for every a. This requires no global concentration of K or
   derived-category instance on U. Checked U empty, U whole, S zero, n negative,
   empty rank fibers, and K having extra homology outside U: all satisfy the
   claimed construction. The new hole contains neither rank support calculations
   nor the single-complex lift; both are proved in the item, so this is a strict
   decomposition. Repeated semantic search with "homology counit" and "vanishing
   outside the open subset", Loogle search for homology/map/NatTrans, and rg over
   Mathlib, lean/Sheaf, and lean/WeilConjectures. Found homologyMap_mapNatTrans and
   the existing exact adjunction, but no duplicate support-sensitive approximation.
   Closing the approximation needs the termwise exact-functor comparison and stalk
   detection formalization; it is not a few-minute application of a found theorem.
   Its source, complete proof docstring, and node are present. Verdict: pass.
4. Route and pruning: the nonnegative branch constructs the open complement of
   i({r != n.toNat}); closedness comes from the clopen fiber and closed embedding.
   Injectivity of i separates the rank-n support from its complement. The other
   degree supports vanish on this open, using hother and injectivity of toNat on
   nonnegative integers. The negative branch uses only hT and zero source. The
   concentrated-object helper uses Mathlib's standard t-structure and proves the
   required single-homology equation by naturality. The final composition uses
   that equation and the approximation factorization. Read
   dag/units/sk-thm-picard-duality.json: its realized statement and step lists are
   empty, and the local reconstruction route does not replace its Serre-duality
   step. Every old dependency absent from the item's new proof_deps is now named
   under No longer needed, distinguishing transitive use from pruning. Verdict:
   pass after the import/dependency correction below.
5. Nodes: checked the item proof steps against the support helper, approximation
   application, t-structure helper, and final composition. The new node's Lean
   statement matches its theorem and its natural-language statement introduces
   every object and hypothesis. Its source, proof steps and union proof_deps,
   proof_origin, searches, status, created record, blueprint ancestry, chapter,
   unit, and Lean record meet the brief. There is no global-presentation claim or
   arbitrary witness data definition. Verdict: pass after correction.

Changed in this second reading: replaced the approximation's proof-only import
of DerivedOpenShriekAdjunction by OpenRestrictionAdjunctionExact, and removed
lem-sc-derived-open-shriek-derived-adjunction from its proof step and proof_deps.
The termwise construction uses the underived exact adjunction only. Completed
No longer needed to explicitly name all old dependency edges that moved or became
unnecessary. No Lean proof, statement, or definition changed. The outcome remains
one upper hole closed and one strictly smaller hole added, net zero.
