## What changed

Proved `AlgebraicGeometry.Scheme.depth_three_local_cohomology_vanishing` in
`Sheaf.AlgebraicGeometry.Morphisms.DepthThreeLocalCohomologyVanishing` without changing
its signature, visibility, existing docstring, or public imports. Added proof-only imports
`Mathlib.RingTheory.Depth.Rees` and `Mathlib.CategoryTheory.Abelian.Projective.Ext`.

The proof extracts a regular sequence of length greater than two from the supremum defining
depth, applies Mathlib's Rees theorem to each quotient by a maximal-ideal power, and proves
that the evaluated Ext diagram and its colimit are zero. The proved private helper
`old_ext_two_isZero` bridges Mathlib's old Ext functor and derived-category Ext using
`ProjectiveResolution.isoExt` and `ProjectiveResolution.extMk_eq_zero_iff`. Updated the
item's DAG proof and dependencies to record this argument.

Verified the source [Stacks, Section 47.11](https://stacks.math.columbia.edu/tag/0AVY),
particularly Lemma 47.11.1's supported-module Ext vanishing and colimit argument.
Single-file compilation succeeds with no warnings. The proof handles the zeroth ideal
power explicitly (empty support); positive powers have the same zero locus as the maximal
ideal. Extracting a length greater than two also avoids any assumption that depth is finite
or that its supremum is attained.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.depth_three_local_cohomology_vanishing`
(node `lem-sbc-depth-three-puncture-h-one-local-vanishing`). One of one original holes closed.
The private helper `old_ext_two_isZero` is fully proved. No sorry remains in the module,
and no hole or new axiom was added elsewhere. This is a complete proof, not a decomposition.

## No longer needed

No original import, node, or module was removed. Removed the redundant trial proof import
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`; it is already available through the
necessary Mathlib imports. Both remaining proof imports are used.

The proof does not need a separate depth-invariance-under-powers theorem, a characterization
of the first nonzero local cohomology degree, or finite-depth/maximum-length results.
No existing node in the item's original proof-dependency list represents these steps
(the list was empty), so there are no modules to prune from that list. The unit's route is
preserved: the item still proves exactly the local cohomology vanishing used above it.

## Where the brief, the DAG or earlier work was wrong

The node had a single non-elementary proof step and no proof dependencies; it omitted the
usable Rees theorem already present in Mathlib. Local cohomology uses the old `_root_.Ext`
functor, while Rees uses `CategoryTheory.Abelian.Ext`; applying Rees alone therefore does
not directly prove a diagram object is zero. The private projective-resolution argument
fills this interface gap without an unproved bridge theorem. Also, Mathlib's ideal-powers
diagram includes exponent zero, not only positive powers; the proof checks that case.

## Second reading by T1

1. **Interfaces: pass.** Read the complete repository/sandbox diff. The existing
   `depth_three_local_cohomology_vanishing` signature is byte-for-byte identical,
   including its universe, CommRing/Noetherian/local hypotheses, depth bound and
   subsingleton conclusion. Its docstring and both public imports are unchanged.
   The only added declaration is the proved private `old_ext_two_isZero`; no
   definition or externally visible statement changed. No change record is needed.
2. **Proof and axioms: pass.** Independently compiled the delivered file through
   `lcompile.py` without errors or warnings (3.7 seconds). Compiled a scratch copy
   printing axioms of both the helper and the main theorem: each uses exactly
   `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Scanned all delivered
   Lean for sorry, axiom, unsafe, opaque, implemented_by and extern: none occur.
   Read `ProjectiveResolution.isoExt` and `extMk_eq_zero_iff`: their degree-two
   cocycle/coboundary argument is the exactness required by the old Ext homology.
   The projective resolution is Mathlib's proved construction; no data is chosen
   from an unproved existence theorem.
3. **Split statements: pass (none).** No new hole or split-off public statement.
   The private helper is fully proved for arbitrary ModuleCat objects, including
   zero modules. Checked the two quotient-support cases k=0 and k>0, all finite
   module requirements of Rees, and extraction of length>2 even for infinite
   supremum depth. The zero ring is excluded by IsLocalRing's nontriviality;
   depth<3 rings cannot satisfy the hypothesis. Read Stacks Lemma 47.11.1 at
   [Tag 0AVY](https://stacks.math.columbia.edu/tag/0AVY): its finite-supported-module
   Ext vanishing and colimit argument agree with this proof.
4. **Route and pruning: pass.** Independently searched repository Lean for local
   cohomology/Ext comparisons and Mathlib's abelian and derived-category sources
   for Ext isomorphisms. Loogle query `"Ext", "homology"` found no replacement;
   LeanFinder query about comparing derived and left-derived Ext returned isoExt
   and extMk_hom, already covered by the helper. The existing DepthExt result
   concerns only residue-field Ext and requires extra finite-depth machinery, so
   it does not shorten this supported-quotient argument. Independently removing
   each proof-only import in scratch copies fails (Rees supplies supported Ext
   vanishing and ModuleCat instances; Projective.Ext supplies extMk_eq_zero_iff).
   The two public imports are needed for the signature. Original proof_deps is
   empty, so no old node/import is omitted from No longer needed. Read
   dag/units/sk-prop-input-spreading.json: the local vanishing is an input beneath
   the unit's depth-extension step; no unit statement or step is bypassed and its
   realized record is unchanged.
5. **DAG agreement: pass.** Only proof, proof_deps and proof_origin differ from
   the repository node. The four steps match Nakayama/supremum extraction, Rees
   for quotient support, the proved Ext bridge, and the evaluated zero colimit.
   proof_deps is exactly the union of uses; the Nakayama and Rees dependencies
   are existing Mathlib leaves, and the depth/regular-sequence/Ext dependencies
   are the definitions actually used. No new node is required for an unproved
   intermediate theorem; no statement or Lean-record field changed.

Second reading changed only this report by adding the independent checks above.
The Lean proof and DAG metadata needed no repair. One original hole closed,
zero holes added, zero split off; nothing pruned.
