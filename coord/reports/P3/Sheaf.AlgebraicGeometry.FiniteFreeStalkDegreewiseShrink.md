## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.exists_shrink_degreewise_comm_of_stalk`
with a complete Lean proof from two strictly smaller intermediate statements. The existing
signature, universes, visibility and public imports are unchanged. Added proof-only imports
of `Sheaf.AlgebraicGeometry.FiniteFreeStalkFiniteEquations`,
`Sheaf.AlgebraicGeometry.StalkRestrictionSubopenCompatibility` and
`Mathlib.Data.Int.Interval`. Updated the existing node's proof route to agree with Lean. The second reader replaced
the new finite-equations module's upstream public import with the Mathlib modules
that supply its signature (module sheaves and free sheaves).

The proof constructs the finite interval `[max a (c - 1), min b (e - 1)]`, forms the two
maps in each chain equation, and uses stalk functoriality to apply finite-family equality.
It explicitly constructs the restricted family by conjugating with the restriction
composition isomorphism. On the finite interval the differential equations follow by
functoriality and the chain equations of that isomorphism. Outside the interval one of
the four support bounds makes the source or target zero. The second intermediate lemma
then gives the exact stalk component formula for this constructed family.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_shrink_degreewise_comm_of_stalk`
(node `lem-pc-finite-free-stalk-degreewise-shrink`). No sorry remains in the item's module.
This is a decomposition, not a complete proof independent of new sorries: one upper
hole closed, two lower holes added, net -1 before any pruning effects.

The delivery adds exactly two named public theorem holes, each in its own module:

- `AlgebraicGeometry.Scheme.Modules.exists_shrink_finite_free_map_eq`
  (`lem-pc-finite-free-stalk-finite-equations`): finitely many equations of maps between
  zero-or-finite-free sheaves hold after further restriction if they hold at the stalk.
  It has no complexes or differential compatibility and no stalk comparison conclusion.
- `AlgebraicGeometry.Scheme.Modules.stalkRestrictionComplexIso_map_subopen`
  (`lem-pc-stalk-restriction-subopen-compatibility`): comparison formula for one arbitrary
  component map and one prescribed subopen. It has no existence/shrinking conclusion,
  no differential equations, and no boundedness or freeness assumptions.

Each hole is exactly `:= by sorry`, with a source and complete proof in words in its
node and docstring. The family k is an explicit construction inside the proved theorem;
there is no data definition chosen from an unproved mere-existence theorem.

All three delivery modules compile together without warnings through lcompile.py.
The finite interval argument covers empty intervals, including reversed support bounds;
zero source, zero target and rank-zero free sheaves require no extra equations. The new
finite lemma allows an empty index type. The comparison lemma includes U = V and zero
objects. The unit `sk-thm-picard-perfect` and its steps are preserved: this is the same
finite matrix and zero-germ argument, split below the unit level.

## No longer needed

No import present in the original module was removed. Both original public imports are
needed by the unchanged statement. The proof adds only the two used intermediate modules
and the integer finite interval module. In the new finite-equations module, removed
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`: its extra matrix and
local-freeness declarations are not used by the stated signature or its pending proof.
The module instead publicly imports `Mathlib.AlgebraicGeometry.Modules.Sheaf` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`, alongside the required stalk module.

The parent node no longer directly needs `def-pc-derived-pullback`
(`Sheaf.AlgebraicGeometry.DerivedPullback`): the argument only uses ordinary module
pullback and termwise restriction. It also no longer needs the separate arbitrary
presheaf stalk construction `def-weil-pbc-module-stalk`
(`Sheaf.Topology.PresheafModuleStalkFunctor`). Neither module is imported. The finite
matrix lemma uses structure-sheaf germs already available in Mathlib, and the second
lemma uses ordinary pullback composition. These are pruned dependencies of this item's
proof route; no assertion is made that other targets cease to need them.

Retained `def-weil-pbc-free-module` and `def-pc-stalk-restriction-complex-iso`. New nodes
record the ordinary module pullback notion through `def-pc-module-pullback`, whose
Mathlib declaration is Scheme.Modules.pullback; its alternate tensor encoding is not
imported or used here.

## Where the brief, the DAG or earlier work was wrong

The original proof_deps supplied definitions rather than the matrix-vanishing theorem
or the compatibility of the specified canonical comparisons. Thus simply importing
those modules does not express the plan in Lean. The two new theorems state precisely
these parts, and the original theorem now proves the finite-support and conjugation
glue in Lean. No existing statement was changed or marked disputed.

The blueprint `_section.md` source path named by the unit is absent in this local clone.
The unit JSON and original node/docstring contain the proof text; the new nodes cite
and expand that existing source attribution, and mark their proof_origin as agent.

LeanFinder and local source search found germ shrinking, freeMatrix_pullback,
restrictFunctorComp and pullback pseudofunctor associativity, but no direct theorem
for either new statement. LeanSearch returned Internal Server Error, recorded as
unavailable rather than as a failed match. Blueprint searches for `stalk restriction`,
`finite free stalk` and `germ`, plus searches of the full DAG and library, found no
existing exact statement for either new lemma.

## New nodes

`lem-pc-finite-free-stalk-finite-equations`, in
`dag/nodes/sec-picard-framework/lem-pc-finite-free-stalk-finite-equations.json`, records
the finite matrix/zero-germ part of steps 1 and 2. Its module is
`Sheaf.AlgebraicGeometry.FiniteFreeStalkFiniteEquations`. Its source, proof sketch,
search records and edge cases are explicit.

`lem-pc-stalk-restriction-subopen-compatibility`, in
`dag/nodes/sec-picard-framework/lem-pc-stalk-restriction-subopen-compatibility.json`,
records step 3, for the concrete restriction-composition isomorphism used in the
constructed family. Its module is
`Sheaf.AlgebraicGeometry.StalkRestrictionSubopenCompatibility`. The source and proof
explain the adjunction-unit and pseudofunctor coherence calculation, rather than
asserting arbitrary natural isomorphisms give the requested comparison.

No change records or adaptations of other existing modules are required.


## Second reading by P3

1. **Interfaces unchanged: pass.** Read the repository/sandbox diff of
   `FiniteFreeStalkDegreewiseShrink.lean`: only three plain imports and the proof body
   changed. The original theorem signature, docstring, universes, visibility and both
   original public imports are byte-for-byte unchanged. The two other modules are new;
   there are no adapted modules, definitions, or statement changes.
2. **Proof and axioms: pass.** Compiled all three modules in import order with
   `lcompile.py`. The item has no sorry; the only two delivered sorries are exactly the
   public named theorems listed above. No axiom, unsafe, opaque, implemented_by, extern,
   or hollow definition occurs. The family k is explicitly constructed by conjugating
   the restricted g with C. A neighbourhood is obtained in a theorem proof, not put
   into a data definition. Scratch copies with `#print axioms` check all three names;
   the only axioms are propext, Classical.choice, Quot.sound and the reported sorryAx.
3. **Split statements: pass as decomposition.** Read both complete signatures,
   docstrings and nodes. Finite equations concern maps of sheaves without differentials
   or comparison conclusions; stalk compatibility concerns one prescribed subopen and
   arbitrary component map, with no existence conclusion. Neither restates the item.
   For the finite lemma, restricted finite bases give finite matrices, freeMatrix_pullback
   and fromSpecStalk_appTop identify the coefficients with their germs, and the germ
   equality criterion gives the finite intersection. Checked empty index types, zero
   source/target, rank zero and V=U; no nonempty-rank assumption is hidden. For coherence,
   read the concrete stalkRestrictionComplexIso definition and Mathlib's
   restrictFunctorComp, restrictFunctorIsoPullback (leftAdjointUniq), and pullback
   associativity: the comparisons are canonical, and their units agree with restriction
   maps. This gives the stated conjugation formula also for U=V and zero terms.
   Independent searches used LeanFinder for equality of finite locally free maps at one
   stalk, Loogle for restrictFunctor/pullback, and grep for stalk equality/coherence.
   They found ingredients, not either complete statement. Also searched lean/Sheaf and
   lean/WeilConjectures. The existing restrict_chainMap_of_stalk_local only gives some
   extension of a chain map, not this prescribed conjugation of an arbitrary component;
   its private pullback_triangle does not handle restriction/pullback coherence. Neither
   hole closes by a short application of the available results.
4. **Reduction and pruning: pass.** The finite interval is exactly the intersection of
   the possible support of P^n and Q^(n+1). hft uses pullback functoriality, hV supplies
   the restricted equations, and C's hom/inv chain equations transport them to k. Outside
   the interval, omega identifies one of four zero terms and eq_of_src/eq_of_tgt closes
   the equation. This includes reversed and empty support intervals. Every added proof
   import is used. Both old discarded proof_deps are listed under No longer needed;
   no claim of global unreachability is made. Read sk-thm-picard-perfect.json: its
   realized fields remain unchanged, and the finite matrix/zero-germ route is retained
   below its unit level.
5. **Nodes match Lean: pass.** The parent proof has the three actual steps: finite-family
   equality, explicit conjugation plus support bounds, and componentwise coherence.
   Its proof_deps are the union of the step citations and its origin identifies the
   agent reduction. Each new node has the matching verbatim Lean statement, source,
   full proof sketch, actual recorded searches, split status, creation record, chapter,
   unit, and blueprint ancestry. No existing statement/stmt_deps were changed.

Changed only the new finite-equations module's imports to remove an unnecessary upstream
public dependency, and updated this report. The Lean argument and both split statements
were retained. The delivery closes one original hole and adds two smaller holes: net -1,
not a completed proof independent of sorryAx.
