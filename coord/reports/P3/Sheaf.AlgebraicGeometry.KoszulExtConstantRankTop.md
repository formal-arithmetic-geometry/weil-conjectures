## What changed

Replaced the single hole in `Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop`
by a compiling coefficient-map argument following Stacks Tag 0BQZ. The original
signature, public imports, and visibility are unchanged. The actual map
`AlgebraicGeometry.koszulScalarExtCoefficientMap` is constructed from the
pullback-pushforward adjunction and derived functoriality; it contains no hole
and selects no witness from an unproved existence theorem.

At each stalk the existing conormal basis and affine conormal frame identify the
chart length with n. Local coefficient bijectivity, the proved module-stalk
isomorphism criterion, and the all-degree self-Ext comparison then give the
claimed isomorphism. The body explicitly computes the length equality, checks
all stalks, and composes the two isomorphisms.

Added two modules with precise remaining parts of the source argument (their
planned proof dependencies are imported privately, as required):
`KoszulExtCoefficientStalkIso` and `KoszulSelfExtExterior`. Updated the parent
node's proof route and added their nodes. No existing definition or statement
was changed; no forced adaptations or change records are needed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.koszulRegularImmersion_ext_constantRank_top`
(node `lem-sc-koszul-ext-constant-rank-top`). Its proof is complete from named
declarations, but this delivery is a decomposition, not an axiom-free proof.
The original module has no remaining sorry.

Added exactly two named holes:

- `AlgebraicGeometry.koszulRegularImmersion_ext_coefficient_stalk_iso`
  (`lem-sc-koszul-ext-coefficient-stalk-iso`): a local bijectivity assertion for a
  specified canonical map in a single length-n affine Koszul chart.
- `AlgebraicGeometry.koszulRegularImmersion_self_ext_exterior`
  (`lem-sc-koszul-self-ext-exterior`): self-coefficient Ext in all nonnegative
  degrees on the regular locus, with no rank hypothesis.

Thus one hole is closed and two are added (decomposition net -1 before the
maintainer's actual closure ledger). Neither lemma restates scalar top Ext:
one computes the local coefficient map, the other computes a different
coefficient object without the rank condition. Each has a source and complete
proof in words. Edge cases checked in the statements and arguments: n=0,
n above a local sequence length for self Ext, empty V, variable ranks on V,
and no regularity away from V. At a point of Z the ambient affine section ring
cannot be the zero ring; the empty-locus cases remain vacuous.

All three modules compile singly in sandbox import order. The parent proof
needs extra elaboration heartbeats to unfold derived coefficient objects and
still compiles in about nine seconds. The independent dry run is recorded by
the delivery tool; there is no push.

## No longer needed

Removed direct proof imports from the parent:

- `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`
  (`lem-sc-derived-hom-finite-free-model`).
- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`
  (`lem-sc-affine-quotient-resolution-sheafification`).
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
  (`lem-sc-derived-internal-hom-restrict-open`).
- `Sheaf.RingTheory.KoszulRegularSequenceDualComplex`
  (`lem-sc-koszul-regular-sequence-dual-complex`).

The first three remain proof-plan dependencies of the new local/self Ext
calculations, so their work is relocated rather than pruned. The normalized
scalar determinant comparison of the fourth is not used by this route.
In particular this argument does not need its intrinsic normalized scalar
Ext roof determinant, generator-independence, or localization comparisons:
canonical coefficient functoriality supplies the global scalar map, and only
the self Ext exterior algebra is glued. No claim is made that these modules
are unreachable from every other target; the closure ledger decides that.

Retained conormal basis and affine conormal frame; retained the statement's
exterior sheaf and internal Hom definitions. No realized blueprint unit step
is bypassed; the new route refines this node below `sk-thm-picard-duality`.

## Where the brief, the DAG or earlier work was wrong

The previous node planned direct normalized determinant gluing. The source
Tag 0BQZ first compares scalar coefficients to self coefficients and uses the
self Ext algebra (Tag 0BQY); this makes the global scalar map canonical and
confines scalar invertibility to a local calculation. The previous route is
not false, but its large normalized comparison is unnecessary here.

Existing imported lemmas do not state either exact sheaf-level comparison;
the finite free model and affine resolution alone do not perform the
coefficient cohomology computation or glue the self Ext algebra. The remaining
steps have therefore been isolated rather than asserted by an unnamed hole.
Mathlib search found no exact comparison. LeanSearch was unavailable (server
error), which is recorded as unavailable, not as evidence of absence. Source
Tags 0BQW, 0BQY, and 0BQZ were read online at the Stacks Project; this clone does
not contain the referenced duality.tex checkout.

## New nodes

`lem-sc-koszul-ext-coefficient-stalk-iso`, in
`dag/nodes/sec-picard-framework/lem-sc-koszul-ext-coefficient-stalk-iso.json`,
matches `Sheaf.AlgebraicGeometry.KoszulExtCoefficientStalkIso`. It isolates the
local top cohomology reduction Hom(K,A) -> Hom(K,A/I), including naturality of
the actual constructed coefficient map and pullback after cohomology. Its
source is Stacks Tag 0BQZ.

`lem-sc-koszul-self-ext-exterior`, in
`dag/nodes/sec-picard-framework/lem-sc-koszul-self-ext-exterior.json`, matches
`Sheaf.AlgebraicGeometry.KoszulSelfExtExterior`. It isolates the all-degree
zero-differential Hom(K,A/I) computation and intrinsic exterior/Yoneda
comparison on overlaps, following Tags 0BQW and 0BQY. Neither new node duplicates
an imported blueprint statement: Koszul/exterior blueprint searches and
library searches found no existing theorem with this conclusion. Both nodes
inherit the parent's blueprint ancestor and unit and include the parent in
their via chain.


## Second reading by P3

1. Compared the delivered parent with the repository by `diff -u`, and separately
   compared the complete text from the theorem name through its conclusion:
   the existing signature is byte-for-byte identical. All existing public imports
   and visibility are unchanged. There are no adapted existing modules or change
   records. The changed docstring accurately explains the new proof route.
2. Compiled all three files in import order with `lcompile.py --all`: no errors
   or warnings. A scratch copy with explicit `#print axioms` checked the actual
   coefficient map and all three theorems. The map uses only `propext`,
   `Classical.choice`, and `Quot.sound`; the theorems additionally use `sorryAx`
   from the two named remaining holes. No forbidden declarations or attributes
   and no holed definitions occur. The map is an explicit functorial construction;
   the parent only eliminates existence proofs in proving a proposition.
3. Read both new statements and their complete docstring arguments against
   Stacks Tags 0BQZ, 0BQY, and 0BQW. The local lemma computes a specified map
   in top degree of one chart; the self-Ext lemma computes a different coefficient
   object and has no rank assumption. They are true, needed parts of the argument,
   not restatements of scalar top Ext. Checked degree zero (empty sequence and
   zero ideal), degrees above chart length, empty V, changing local ranks,
   characteristic two (contractions square to zero), and regularity only near V.
   Independent LeanFinder searches for Yoneda exterior products and reduction of
   dual Koszul cohomology, Loogle on `CategoryTheory.Abelian.Ext`, and Mathlib grep
   for Koszul and self/coefficient Ext found no exact result. The first Loogle
   query `ExteriorPower` was an unknown identifier and was replaced by the valid
   Ext query. Repository searches and rereading the finite free Hom model,
   affine resolution, restriction, and algebraic dual-homology comparison found
   no exact sheaf-level result closing either hole in a few minutes.
4. Traced the parent from the top: existing conormal basis and affine frame give
   m=n; local bijectivity and the proved stalk criterion give the coefficient
   isomorphism; composing with self Ext proves the exact target. The coefficient
   route is the source's route and no shorter existing comparison was found.
   All four removed old proof dependencies are listed above. The first three
   now occur as private proof-plan imports in both new modules; only the old
   normalized scalar determinant comparison is bypassed. This is relocation,
   not a claim of positive closure pruning. Checked the unit record
   `dag/units/sk-thm-picard-duality.json`: no realized statement or step is
   bypassed or changed. Public imports of the new modules support their
   signatures/construction; added proof-plan imports are plain `import`.
5. Checked the parent node's steps against the actual rank calculation,
   coefficient morphism, stalk criterion, and composition. For all three nodes,
   `proof_deps` equals the union of the proof steps' `uses`. Both new Lean
   signatures exactly match their node's verbatim statement field. New nodes
   contain source, searches, origin, creation, blueprint ancestry, unit, chapter,
   and Lean records. The parent node changes only the permitted proof fields.

Second reading changed only the new modules' plain proof imports to match their
recorded dependency plans, and this report. No Lean declaration, definition,
statement, proof body, or DAG route needed repair. Recompilation after this
repair passed for all three modules; the two split holes remain as reported.
