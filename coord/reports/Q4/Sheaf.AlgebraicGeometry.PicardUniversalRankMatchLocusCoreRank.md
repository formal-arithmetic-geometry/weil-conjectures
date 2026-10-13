## What changed

The original existence theorem
`AlgebraicGeometry.Scheme.exists_picardUniversalRankMatchLocus_core_rank` now has a complete
Lean proof from two smaller intermediate theorems. It represents the primal and dual
single-image conditions separately, using the same reference bundle E, and constructs their
intersection as `pullback j₁ j₂`. Mathlib proves that the first projection and its composite
with j₁ are immersions. The proof explicitly projects the original three-clause witnesses,
uses common-neighbourhood refinement in the reverse direction, and proves both directions
of factorization by the projections and `pullback.lift`.

Two proof-only imports were added to the original module:
`Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus` and
`Sheaf.AlgebraicGeometry.PicardUniversalRankMatchConjunction`.
No existing signature, definition, visibility, public import, or docstring changed.
`picardUniversalRankMatchCoreCondition_iff` retains its existing `rfl` proof.

Three new modules state the single-image predicate, its representing immersion, and
synchronization of two independent local witnesses. Their source and complete proofs in
words are in their docstrings and nodes. The single-image locus concerns one arbitrary
finite locally free F, compared to the fixed reference E, and imposes no dual condition.
The synchronization lemma asserts no representing scheme. Neither remaining statement is
a restatement of the original existence theorem.

All four modules compile in import order with the launcher compiler. The first compile
of a narrower import list exposed a missing scheme pullback instance; the definition module
now publicly imports `Mathlib.AlgebraicGeometry.Limits`. A long docstring line was wrapped.
No imports beyond those required by the signatures and the complete proof remain.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.exists_picardUniversalRankMatchLocus_core_rank`
(node `lem-sc-picard-universal-rank-match-locus-core-rank`).
There are no remaining sorries in the original module.

Added exactly two named theorem holes, each the whole proof `:= by sorry`:

- `AlgebraicGeometry.Scheme.exists_picardUniversalSingleRankLocus`
  in `Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus`,
  node `lem-sc-picard-universal-single-rank-locus`.
- `AlgebraicGeometry.Scheme.picardUniversalRankMatch_of_singleRankMatch`
  in `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchConjunction`,
  node `lem-sc-picard-universal-rank-match-conjunction`.

This is a decomposition: one upper hole closed, two strictly smaller holes added,
net holes closed minus added = -1 for this delivery. It is not an axiom-free proof of the
original theorem. The predicate is a real quantified definition with no holes, and no
data-bearing definition chooses witnesses from an unproved existence theorem.

Edge cases checked mathematically: empty test schemes have no points in either predicate,
and the unique morphism to each candidate gives factorization; rank zero is allowed in all
clauses; on a nonempty residue-field test the structure-sheaf unit excludes empty fibres,
so the reference rank is uniquely determined. For f the identity, the one-image condition
reduces to local equality of the ranks of E and F; the two-image condition for E and its
dual holds on all of S. With E of rank zero, the single-image condition for arbitrary F
requires universally zero direct image, showing it does not already assert the two-image
condition. No conclusion uses an arbitrary rank inferred solely from the two direct images.

## No longer needed

None. No original imports were removed. The original node had no named proof dependencies,
so no previous dependency node or module can be pruned by this decomposition. The six
original public imports support its unchanged signatures and remain public.

## Where the brief, the DAG or earlier work was wrong

The core-rank node recorded three non-elementary proof steps with `uses: []` and
`proof_deps: []`; consequently its plan was not already expressed by named Lean dependencies.
Existing `PerfectLowestCohomologyLocus` represents fixed lowest-cohomology rank, but its
signature neither stratifies by the reference bundle rank nor synchronizes independent
local witnesses. Existing `PerfectDirectImageBaseChange` and `PicardFiberRankClopen` provide
tools for the single-image construction; the new node names them in its proof dependencies.
The common-neighbourhood step uses tensor pullback composition and the existing stalk
finrank theorem. The actual parent proof is now accurately recorded by its two dependencies.

Searches: Lean Finder returned general immersion and ring-module rank results; grep of
Mathlib and the source library found no single-image reference-rank representability or
synchronization theorem. Whole blueprint searches for rank match, rank locus, and single
direct image rank found no exact existing node. LeanSearch returned Internal Server Error;
it is recorded as unavailable, not as evidence of absence. The source read was Stacks
Tags 0BDP and 0BDL. This preserves the unit's route and the source's construction of the two
rank loci followed by their fibre product; no unit realization is bypassed.

## New nodes

`def-sc-picard-universal-single-rank-match` records
`AlgebraicGeometry.Scheme.PicardUniversalSingleRankMatch` in
`Sheaf.AlgebraicGeometry.PicardUniversalSingleRankMatch`: the universal local condition for
one direct image, with its rank compared to the same reference bundle E. It does not
redefine the original three-clause predicate.

`lem-sc-picard-universal-single-rank-locus` records the immersion representing this one-image
condition in `Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus`. Its proof stratifies
by E, applies perfect direct image and the lowest-cohomology locus to F alone, and glues
unique local immersions. The generic perfect-complex results are tools from the source
route, not a replacement for any unit statement.

`lem-sc-picard-universal-rank-match-conjunction` records local synchronization in
`Sheaf.AlgebraicGeometry.PicardUniversalRankMatchConjunction`. It intersects the two witness
neighbourhoods, uses a nonempty fibre to identify the ranks at a stalk, and assembles the
three original clauses. It makes no existence or immersion assertion. The stalk-finrank
result is a generic tool.

All three nodes inherit chapter `sec-abelian-varieties` and unit `sk-prop-av-cube`, and trace
their blueprint origin to `thm-sc-theorem-of-cube` through the original core-rank node.
No change records are required: existing interfaces are unchanged.

## Second reading by Q4

1. **Interfaces unchanged — pass.** I compared the entire original module with the
   repository using `diff -u`: the only edits are two plain proof imports and the body of
   `exists_picardUniversalRankMatchLocus_core_rank`. The abbreviation, both theorem
   signatures, visibility, original public imports and original docstrings are byte for
   byte unchanged. There are no adaptations or interface change records.
2. **Kernel and holes — pass as a decomposition.** I compiled all four delivered modules
   in import order through `lcompile.py --all`; all passed, without warnings. I compiled
   a scratch copy with `#print axioms` for the parent theorem, compatibility theorem,
   single-rank predicate and both new theorems. The predicate and compatibility theorem
   use only propext, Classical.choice and Quot.sound. The parent and two open theorems
   additionally use sorryAx, as reported. A source scan found exactly the two named
   whole-theorem sorries and no forbidden declarations. There is no hollow definition:
   the new predicate is explicit quantified data, and the existence witnesses in the
   parent are eliminated inside a proof of a proposition, not chosen to define objects.
3. **Split statements — pass.** I read Stacks Tags 0BDP and 0BDL, and the actual library
   signatures of `picardFiberRank_clopen`, `perfect_derivedDirectImage_baseChange`,
   `exists_perfectLowestCohomologyLocus`, and
   `Modules.finiteLocallyFreeOfRank_stalk_finrank`. The single-image theorem uses flat,
   proper, locally finite presentation f, the universal unit, and finite locally free
   E and F. Properness supplies quasi-compactness, so finite presentation hypotheses
   are available. The structure-sheaf unit forces nonempty connected fibres, making
   the reference rank strata disjoint. Derived base change applies to F because finite
   local freeness and flatness of f give relative flatness. Fixed-rank representability
   is precisely Tag 0BDL; restriction and uniqueness glue the local constructions.
   The conjunction needs no properness: the unit gives a point on the fibre, restriction
   to U intersection V preserves both ranks of E, and the cited stalk-finrank equality
   identifies them. It asserts no representing scheme. Both holes are strictly smaller
   parts of the original argument, not renamed copies of the original theorem.
   I tested the empty base/test schemes, zero-rank E, f=id, and F of a different rank
   for f=id: the last case makes the single-image condition false, as it should.
   I independently searched with msearch Lean Finder for restriction and rank uniqueness,
   msearch grep for Picard/rank loci, and rg in the library and upstream Picard modules.
   These found module-rank tools and special Picard loci, not either full split statement.
   The synchronization proof still needs pullback/restriction identifications and fibre
   nonemptiness; it is not a short application of a currently found theorem, so I did
   not replace its hole by further holes.
4. **Top-down route and imports — pass.** The parent represents the primal and dual
   clauses using the same reference E, then takes the actual categorical pullback.
   The forward direction projects the original witnesses; the reverse direction calls
   synchronization. The factor maps and their pullback lift use the correct equality
   a≫j1=g=b≫j2. IsImmersion follows by base change of j2 and composition with j1.
   The two new parent imports are plain imports. The public imports of the new modules
   provide notions in their signatures; Limits provides scheme pullbacks in the new
   predicate. No old proof dependency is dropped, so `No longer needed: None` is complete.
   I read `dag/units/sk-prop-av-cube.json`: its realized statement and step lists are
   empty; this below-unit refinement does not alter them or bypass the cube route.
5. **DAG agreement — pass.** The parent node changed only proof, proof_deps and
   proof_origin. Its four steps match the dual instance, the two single-image loci,
   immersion pullback, witness projection/synchronization, and pullback lift in Lean.
   Its dependency list is exactly the two new theorem nodes. The three new nodes match
   their declarations, carry their source, creation, blueprint, chapter/unit and Lean
   records, and have genuine predicate/single-image/synchronization roles. The dependency
   union of each proof equals its proof_deps. The existing generic perfect-image and
   stalk-rank results serve as tools, preserving the unit construction.

Changes by this reader: corrected a JSON string escape in the conjunction node's first
proof step, where an intended `\to` had decoded as a tab followed by `o`; appended this
independent review. No Lean proof or statement needed repair. The delivery remains one
original hole closed and two smaller holes added (net -1), with no pruned modules.
