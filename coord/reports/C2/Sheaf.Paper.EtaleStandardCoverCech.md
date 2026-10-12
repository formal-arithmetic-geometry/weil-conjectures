## What changed

Replaced the proof of `AlgebraicGeometry.etale_standard_cover_cech` with a complete Lean
argument from one narrower degreewise restriction-bijectivity theorem. Its statement is
unchanged. The constructed object is exactly the chosen scheme coproduct, with structure map
`Sigma.desc`; all affineness, étaleness, surjectivity and faithful-flatness clauses are proved
using Mathlib. Covering product data comes from the already proved
`SiteCechComplex.exists_of_covering`. The component maps are constructed from its universal
property, not from any unproved existence statement. Projection uniqueness proves every face
compatibility; functoriality and additivity prove differential compatibility. Bijective additive
component maps then assemble using `HomologicalComplex.Hom.isoOfComponents`.

Added `Sheaf.AlgebraicGeometry.EtaleCoproductCechRestriction`, whose only theorem isolates the
bijection on sections in a fixed degree. It takes arbitrary coproduct cocones and chosen product
data; it does not assume affineness, joint surjectivity over the base, or a complex isomorphism.
Updated the item's DAG proof and dependency list to match the implemented argument.

Read Stacks Tag 03OZ, `lemma-cech-complex`, including `equation-sheaf-coprod`, from the available
local copy `/home/ubuntu/c1-stacks-review/etale-cohomology.tex` (lines 2167–2233). The repository
literature tree itself is absent on this machine. Searched the library, all blueprint nodes,
Mathlib via LeanFinder/Loogle/grep, and tried LeanSearch (service returned Internal Server Error).
The source-library `Scheme.Etale.isIso_piLift_of_disjoint` gives the sections argument once the
geometric decomposition has been transported into the chosen site products; it does not perform
that transport. The existing finite set-valued coproduct-sections statement is likewise only a
sections theorem, requiring the coproduct and disjoint-overlap data. No existing theorem directly
supplies the new degreewise statement.

## Proved and sorry left

Closed the local hole in `AlgebraicGeometry.etale_standard_cover_cech`
(node `lem-sc-etale-standard-cover-cech`). All of its proof, including coproduct geometry,
faithful flatness, actual restriction maps, face compatibility and differential compatibility,
is complete Lean.

Added one hole:
`AlgebraicGeometry.etale_coproduct_cech_restriction_bijective`
(node `lem-sc-etale-coproduct-cech-restriction-bijective`). This is the one-degree sheaf product
comparison with the transport from categorical fibre products to the chosen site products.
It is strictly part of the original argument. Therefore this delivery is a decomposition:
one hole closed and one added, net zero; not an axiom-free proof of the original theorem.
No holes remain in the item's module and no other holes are added.

Both delivered modules compile cleanly through `lcompile.py --all`. New-statement edge cases:
p=0 gives restriction from the coproduct to its components; singleton I is restriction along
canonical product isomorphisms; empty I makes all positive-factor products empty and every
abelian section group zero, so both cochain objects have a single element. Arbitrary chosen
products are handled by their projection universal properties. The unit record `sk-prop-h2`
has no realized statement or step pointing to these subsidiary nodes; the standard-cover
replacement route is retained.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.EtaleFibreProductCoproduct` from the
item, replacing it with `Sheaf.AlgebraicGeometry.EtaleCoproductCechRestriction`. The former remains
needed below the new degreewise lemma and is not globally pruned. The item's immediate DAG
proof no longer directly uses `lem-sc-etale-fibre-product-coproduct`,
`def-weil-pbc-abelian-etale-sheaves`, or
`lem-weil-pbc-etale-composition-cancellation`; all remain needed by the new lemma.
No module or node is eliminated from the transitive proof closure. Pruned: none.

## Where the brief, the DAG or earlier work was wrong

The DAG called the sheaf-product passage and comparison with chosen `SiteCechComplex` data a
step from definitions, but there was no stated Lean lemma supplying the chosen-product transport
and its bijection. The new fixed-degree theorem records that missing part. There is no disputed
statement or signature change. Faithful flatness is available directly as Mathlib
`Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`, avoiding manual spectrum transport.
The original proof-dependency module remains used by the new statement's proof plan, and the
new statement's docstring spells out degree zero, off-diagonal and diagonal intersections,
empty objects and the unique Fin 1 tuple. No target signature or definition changed.

## New nodes

`lem-sc-etale-coproduct-cech-restriction-bijective` in
`dag/nodes/sec-curve-estimates/` is the bijectivity of the actual restriction map in a fixed
degree, with arbitrary finite coproduct cocone, chosen products, and a sheaf. Its source is
Stacks Tag 03OZ, the equation and product decomposition. The proof is given in three steps:
geometry via the existing fibre-product distribution node; projection-unique comparison with
chosen site products; sheaf gluing over disjoint open summands and evaluation at the unique
Fin 1 tuple. The geometry, face compatibility and assembly left above it are proved in Lean.
No change record is required: all existing statements and definitions are unchanged.

## Second reading by C2

1. Compared both delivered modules against the repository. The sole existing declaration's
   signature and docstring are byte-for-byte unchanged. The only added declaration in that
   module is a private projection-extensionality proof. No definition or target changed;
   no change record is needed. Verdict: pass.
2. Both modules compiled cleanly through lcompile.py --all. Scratch copies with #print axioms
   showed only propext, Classical.choice, Quot.sound and sorryAx for both public theorems.
   The only local sorry is the named degreewise bijectivity theorem; there is no forbidden
   axiom, unsafe/opaque declaration, external implementation, or holed definition.
   The coproduct and comparison maps are constructed explicitly or chosen using proved
   universal properties. Verdict: pass as a decomposition, not an axiom-free proof.
3. Read the new theorem, its full docstring and node, SiteCechComplex's universal property,
   and the geometric dependency. In degree zero it is coproduct restriction; for singleton
   I it is restriction along uniquely determined product isomorphisms; for empty I the
   nonempty-factor singleton product is empty and its abelian section group is zero.
   Arbitrary product choices give isomorphic products by uniqueness. The statement omits
   the original affine-cover geometry and differential/complex conclusions, so is a strict
   part of the argument, not a renamed target. Independent LeanFinder, qualified Loogle,
   Mathlib grep and repository rg found no exact existing product-transport theorem.
   Verdict: true and needed, with one repair to the proof plan described below.
4. Read the proof from the target downward: coproduct geometry, actual additive restrictions,
   projection-unique face comparison, signed-sum differential compatibility, and component
   isomorphism assembly. Public imports support statement symbols; proof imports are plain.
   The removed direct dependencies are all listed under No longer needed, remain required
   below the split lemma, and no module is globally pruned. sk-prop-h2.realized has no entry
   for either subsidiary node; the standard-cover route and unit route are preserved.
   Verdict: pass.
5. Compared the existing node's changed proof/proof_deps/proof_origin with the Lean argument.
   Checked the new node's source, statement/dependencies, verbatim Lean signature, creation,
   blueprint and chapter/unit fields against its module. Read the local Stacks Tag 03OZ
   proof and equation-sheaf-coprod. Verdict: pass.

Changed the split lemma's docstring and node proof plan to invoke the already proved
Scheme.Etale.isIso_piLift_of_disjoint for the final sheaf-sections step, and added its plain
proof import and existing DAG dependency lem-weil-pbc-disjoint-etale-sections-product.
This avoids planning to reprove existing gluing. The geometric chosen-product transport
remains the single new hole; no Lean statement or completed proof was rewritten.
Closed one original hole, added one strictly narrower hole, net zero; pruned none.
