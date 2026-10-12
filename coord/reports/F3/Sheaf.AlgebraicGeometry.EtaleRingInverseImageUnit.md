## What changed

Implemented AlgebraicGeometry.etaleRingInverseImageUnit without changing its signature.
The proof applies sheavesAlgebraicStructuresRing_core on both sites and
Adjunction.liftedCommRingBranch to the recorded set adjunction. It constructs Lr
by composition, proves its forgetful equality, constructs eta by whiskering the
lifted unit and composing the right comparison, and proves the required unit
formula by naturality and cancellation. The original node now records this route.
Replaced the two aggregate proof imports with ring-only components, and added
Sheaf.AlgebraicGeometry.EtaleRingDirectImageComparison as a proof-only import.
Both sandbox modules compile with lcompile.py --all without warnings.

## Proved and sorry left

Closed: AlgebraicGeometry.etaleRingInverseImageUnit
(node lem-weil-pbc-etale-ring-inverse-image-unit). No sorry remains in the item.
Added: AlgebraicGeometry.etaleRingDirectImageComparison
(node lem-weil-pbc-etale-ring-direct-image-comparison), exactly := by sorry.
This is a decomposition: one upper hole closed and one smaller hole added, net zero.
The remaining theorem concerns only the right direct-image comparison and its
underlying map; it asserts no inverse-image functor, unit or adjunction. The item
contains the real construction of the left functor, forgetful comparison and unit,
and proves the unit identity from the generic lifted identity.
Existing dependency holes are used through their existing declarations, not copied.
No data is selected from a new mere-existence theorem: the comparison theorem fixes
its underlying map, and faithful forgetting determines the comparison uniquely.

## No longer needed

Removed proof imports Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects and
Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects. They are replaced by
Sheaf.CategoryTheory.Adjunction.LiftedCommRingBranch and
Sheaf.CategoryTheory.SheavesAlgebraicStructuresRingCore, respectively.
The item no longer uses lem-weil-pbc-adjunction-lifts-group-ring-objects or
lem-weil-pbc-sheaf-algebraic-structures-objects; it uses the ring construction core and the lifted ring branch. The standalone
ring morphism criterion is also unused and has been pruned.
Comparing source import closures before and after gives these modules removed
from this item's closure (other target branches may still need them):

- Sheaf.CategoryTheory.Adjunction.LiftedCommGrpBranch
- Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
- Sheaf.CategoryTheory.SheavesAlgebraicStructuresAbelian
- Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
- Sheaf.CategoryTheory.SheavesAlgebraicStructuresRing
- Sheaf.CategoryTheory.SheavesAlgebraicStructuresRingMorphism

The corresponding removed nodes are
lem-weil-pbc-lifted-comm-group-branch,
lem-weil-pbc-adjunction-lifts-group-ring-objects,
lem-weil-pbc-sheaf-algebraic-structures-abelian-component, and
lem-weil-pbc-sheaf-algebraic-structures-objects,
lem-weil-pbc-sheaf-algebraic-structures-ring-component, and
lem-weil-pbc-sheaf-algebraic-structures-ring-morphism. Their unused abelian/group clauses
are no longer dependencies of this proof. The original continuity and sheaf definitions remain available through
the unchanged public imports. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned sectionwise identification of the right ring-object lift was not a
separately stated declaration. It is now isolated as the smaller intermediate
comparison theorem, with the five operation hypotheses explicitly written out.
Its edge cases include f = id, zero rings, and the empty scheme: the product and
terminal comparisons give respectively coordinate pairing and the unique singleton
map, so the same proof applies without any nonemptiness hypothesis on sections.
The Stacks source is absent from this clone's literature directory; the cited
[00YV](https://stacks.math.columbia.edu/tag/00YV) and
[00YR](https://stacks.math.columbia.edu/tag/00YR) source pages were read directly.
No statement or definition was corrected; no change record is needed.

## New nodes

lem-weil-pbc-etale-ring-direct-image-comparison, in
lean/Sheaf/AlgebraicGeometry/EtaleRingDirectImageComparison.lean, carries the right
operation-identification part of the original step 3. It inherits sk-def-exchange
and sec-proper-base-change, records three kinds of searches (LeanSearch unavailable),
and contains a complete sectionwise proof in words. No change records added.

## Second reading by F3

1. I compared the inverse-image module with the repository version. The theorem
signature is byte-for-byte unchanged, and the proof constructs exactly the three
objects and the displayed underlying unit equation required by
`lem-weil-pbc-etale-ring-inverse-image-unit`. The source was checked at Stacks tags
00YV and 00YR; the ring paragraph explicitly uses the sextuple operations and the
finite-product identity for direct image.

2. Both delivered modules compile with `lcompile.py --all` and have no warnings.
The inverse-image theorem has no `sorry`, axiom, unsafe, opaque, extern,
implemented-by, or hollow definition. The only remaining hole is the named
`etaleRingDirectImageComparison`, and its node, docstring, source, and Lean
statement agree. Its hypotheses include both site-wise ring-object equivalences,
the five operation transport equations, and finite-product preservation; its
conclusion is only the right comparison, so it is strictly smaller than the item.
Edge cases (identity base change, zero rings, and empty sites) impose no extra
nonemptiness assumption and reduce to the same product/terminal identities.

3. I checked the proof route from the top down. The lifted commutative-ring
adjunction supplies the left construction and its generic unit identity; the
new comparison supplies only the right ring-object identification; naturality,
composition, and cancellation are explicit Lean steps. Thus no statement is
restated under another name, and the unit route through `sk-def-exchange` is
preserved. The new node records the two existing ring-core dependencies and the
three search records required by the stage contract.

4. The proof uses `LiftedCommRingBranch`, `SheavesAlgebraicStructuresRingCore`,
and the new comparison. The old aggregate imports and their corresponding
unused group/abelian/ring-morphism dependencies were removed and are listed above;
no public import was added for proof-only material. The unit record remains
realized by the original node.

5. I compared the changed DAG fields with the proof: only `proof`, `proof_deps`,
and `proof_origin` changed on the existing node, while the new node has a matching
module and declaration. Explicit `#print axioms` probes for both declarations show only `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`. The item retains `sorryAx` through
its comparison and existing open dependencies; it is a decomposition, not a
sorry-free proof of the import closure.

Second reading changed the report only: added this review and the explicit axiom
results. No repair to the Lean proof or node records was needed. The sectionwise
comparison requires a substantial operation-transport proof, so it was retained
as the documented split. Fresh LeanFinder, Loogle, and grep searches found no
exact replacement (Loogle does not index CommRingObjCat). I also searched the
ring-core modules and the upstream/library Lean sources for precomposition,
pushforward, and right ring-object comparisons; none states this comparison.
No target statement or definition was changed.
