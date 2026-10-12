## What changed

Proved `AlgebraicGeometry.smoothDiagonal_idealConormal_iso_and_rank` with its signature unchanged.
The private, proved `ideal_kernel_iso` constructs a kernel lift and proves it is an isomorphism
on the affine basis. Tensor pullback carries it to the diagonal conormal, and the existing
`diagonalConormal_iso_relativeDifferentials` identifies that with relative differentials.
The existing smooth-differentials local-freeness theorem supplies the rank hypothesis.
The stalk functor maps the comparison to a module isomorphism, whose linear equivalence
transports finrank.

Added and fully proved the reusable theorem
`Scheme.Modules.finiteLocallyFreeOfRank_stalk_finrank` in its own module. For a local
trivialization, its proof builds coordinate maps on stalks by an explicit cocone on
neighbourhoods intersected with the trivializing open. It checks their linearity, the
Kronecker-delta coordinate identities and the coordinate expansion of every germ.
These identities give a linear equivalence with the finite product of the stalk ring.
Finrank follows from that equivalence. Updated both DAG nodes to describe these proofs.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.smoothDiagonal_idealConormal_iso_and_rank`
(node `lem-sc-smooth-diagonal-ideal-conormal-rank`). No sorry remains in the item's module.
The private `ideal_kernel_iso` is also fully proved.

Added and proved:
`AlgebraicGeometry.Scheme.Modules.finiteLocallyFreeOfRank_stalk_finrank`
(node `lem-sc-finite-locally-free-stalk-finrank`). All its private coordinate constructions
and helper lemmas are complete. No holes added or split off: one hole closed, zero added.
The comparison with differentials continues to depend on the library's existing
`DiagonalConormalDifferentials` and its proof dependencies; this delivery does not assert
that those existing lower holes have been closed.

Both delivered modules compile through lcompile.py without errors or warnings.
`#print axioms` for `finiteLocallyFreeOfRank_stalk_finrank` reports only `propext`,
`Classical.choice`, and `Quot.sound`. The main theorem still reports `sorryAx` through
the existing diagonal-differentials comparison dependencies, as expected for stage 3;
there is no new sorry in this delivery.
Edge cases are covered by the actual proof: empty schemes have no point x, rank zero
uses empty finite sums, and rank one gives the structure-ring stalk. Scheme stalk rings
are nontrivial commutative rings, as required by the final finite-product rank calculation.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.DiagonalConormal` and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`: they are supplied
by the comparison module and the new generic stalk-rank module, respectively.
These are redundant direct imports, not modules removed from the target closure.
The generic proof imports only the free-sheaf coordinate identities and the existing
`FlatPullbackStalk` linear-map constructor; the latter module contains no sorry.
The larger `LocallyFreeAffine` import used while developing the proof is unnecessary
and is absent from the delivery. The old direct proof dependency `def-amb-finite-locally-free-module` is replaced by
`lem-sc-finite-locally-free-stalk-finrank`; the definition remains used transitively
by that new lemma. No node or module becomes unreachable by this replacement. The
original diagonal, ideal-sheaf, pullback, smooth-differentials and stalk definitions
remain necessary.

## Where the brief, the DAG or earlier work was wrong

The original DAG marked the entire stalk rank calculation elementary, but the library
had no theorem for the actual module-stalk functor that supplied it. Algebraic
`Module.rankAtStalk` lemmas concern localizations of a ring module and do not directly
identify this sheaf stalk with that localization. The new, proved node records the
coordinate calculation. The ideal comparison was proved by section ranges and an
affine-basis criterion rather than by constructing a pushforward isomorphism.

`blueprint_refs.py ancestor` returned None because earlier stage-3 created.item records
name modules rather than node ids. The new node explicitly preserves the existing
item's recorded blueprint ancestor `lem-sc-finite-duality` and its via chain. The unit
record's Serre-duality statement and proof steps are unchanged. The blueprint-wide
search for locally free nodes found no duplicate of the new stalk-finrank theorem.
LeanSearch returned Internal Server Error and is recorded as unavailable; LeanFinder,
Loogle and Mathlib grep ran successfully and found no exact sheaf-stalk statement.
The local literature checkout lacks the Stacks tex files, so Tags 01C6 and 02G1 were
read on the official Stacks website.

## New nodes

`lem-sc-finite-locally-free-stalk-finrank`, in
`dag/nodes/sec-picard-framework/lem-sc-finite-locally-free-stalk-finrank.json`, records
the generic fixed-rank coordinate calculation at one scheme point, fully proved in
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank`. It is strictly part of the
original node's step 3, and its local trivialization, coordinate germs, and finrank
calculation are implemented. No definitions or existing signatures changed, and no
change records or forced adaptations are needed.

## Second reading by S3

1. **Interfaces — pass.** Compared the delivered main module with the repository using
   `diff -u`, and separately compared the text from its existing theorem name through
   its conclusion: the signature is byte-for-byte identical. Its existing docstring,
   public imports, namespace and visibility are unchanged. The only existing-node
   fields changed are `proof`, `proof_deps`, and `proof_origin`. The additional public
   theorem is in a new module; no existing definition or signature is altered and no
   change record is needed.
2. **Proof and axioms — pass.** Compiled both delivered modules in import order with
   `lcompile.py --all`: no errors or warnings. Read the kernel lift, its zero-composite
   proof, the affine section bijectivity argument, and the reflection of isomorphisms.
   `range_toModulesι_app_eq`, `range_toModulesι_app`, `ker_apply`, and the injective
   kernel inclusions supply exactly the claims used. Read the coordinate cocone's
   naturality, scalar compatibility, delta identities, expansion of every germ, and
   both bijectivity clauses of `localStalkEquiv`. There is no forbidden declaration,
   no sorry in either module, and no data chosen from an unproved existence theorem.
   Scratch copies with `#print axioms` confirm that the new stalk-finrank theorem
   uses only `propext`, `Classical.choice`, `Quot.sound`. The main theorem additionally
   uses `sorryAx` through the existing diagonal-differentials comparison; this delivery
   closes its local hole, not the already open dependencies. The delivery tool also
   probes all declarations, including private helpers.
3. **New statements — pass.** No statement is split off with sorry. The new generic
   stalk-finrank theorem proves strictly the stalk calculation, with no diagonal or
   smoothness assumptions. Read [Stacks 01C6](https://stacks.math.columbia.edu/tag/01C6),
   clause (3), [02G1](https://stacks.math.columbia.edu/tag/02G1), and
   [08S2](https://stacks.math.columbia.edu/tag/08S2): the fixed rank, local
   trivializations, and conormal comparison match the hypotheses and conclusions
   used here. The new theorem is the coordinate-stalk consequence of 01C6, not a
   claim quoted verbatim from 02G1. Checked empty X (no point), r = 0 (empty sums),
   and r = 1 (one coordinate). Nontriviality comes from the scheme stalk ring,
   rather than an extra hypothesis. Repeated Mathlib searches with different words:
   LeanFinder on fibre germs and basis vectors returned the tilde stalk-to-localization
   maps and free sections, not an exact result; Loogle did not recognize this upstream
   class. Grep for fixed-rank/stalk combinations returned no hit. Also searched the
   current library and upstream modules for stalk bases, equivalences, rank and
   freeness. `LocallyFreeRank` computes algebraic localized-module rank, while
   `NonvanishingSectionTrivializes.stalk_generator_bijective` is private and rank one;
   neither supplies this theorem for the module stalk functor.
4. **Route and pruning — pass after report correction.** The main proof first constructs
   the actual kernel comparison, then uses the existing diagonal-differentials
   comparison and smooth differential local freeness, and finally transports finrank.
   No new hole disguises or restates the item. Proof-only imports are plain `import`;
   the new module's public imports supply objects in its statement. Removed direct
   imports remain available through dependencies. The old dependency
   `def-amb-finite-locally-free-module` is no longer direct, but remains necessary
   inside the new proved lemma: recorded that replacement explicitly under
   `## No longer needed`. No module is pruned from the target closure. Read
   `dag/units/sk-thm-picard-duality.json`: the Serre-duality route is unchanged;
   its existing `realized` entries are empty, a pre-existing unit-record gap, not a
   route change made by this delivery. This item is a subordinate diagonal comparison,
   not the unit's key statement, so the unit record is outside this delivery.
5. **DAG — pass after metadata correction.** Checked each proof step against its Lean
   implementation and cited declarations. Main step 1 is the kernel-lift/basis proof,
   step 2 composes with the existing differential comparison, and step 3 uses the
   new stalk-finrank theorem and stalk functor. The new node records exactly the
   coordinate calculation and carries source, searches, creation, blueprint, chapter,
   unit, and Lean fields. Each node's `proof_deps` is the union of its step uses.
   Corrected the new node's `lean.statement` line wrapping to reproduce the actual
   declaration verbatim. The new node's docstring includes the full natural-language
   argument; every coordinate construction is implemented, so no lower hole remains.

Second reading changed only the new node's recorded signature formatting and the
report's account of the replaced direct dependency, and added this independent reading.
The Lean proofs were correct as submitted and were not rewritten. One original hole
closed, zero holes added; no module pruned from the target closure.
