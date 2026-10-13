## What changed

Replaced the hole in `AlgebraicGeometry.exists_finitePresentation_local_descent_datum`
with a complete Lean assembly of the original two-step plan. The public signature,
visibility, and existing docstring are unchanged. Added two separate statement modules:
`Sheaf.AlgebraicGeometry.FinitePresentationLocalObjectModels` lifts only local objects;
`Sheaf.AlgebraicGeometry.FinitePresentationLocalOverlapModels` lifts the transition maps
between supplied local models at a later stage. The main proof establishes the finite
affine cover at that stage, transports finite presentation and quasi-coherence along
component isomorphisms, and constructs the final descent-data isomorphism using a
proved private helper and `DescentData.isoMk`.

The main module imports these two modules and
`WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent` only for proofs. No public
imports, definitions, instances, or existing statement signatures changed. Updated the
parent node's proof route and created matching nodes with sources and full proof sketches.
The original blueprint unit and its route are kept.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_finitePresentation_local_descent_datum`
(node `lem-pc-fp-local-descent-datum`). There is no sorry left in the item's module.

Added, still sorry:
- `AlgebraicGeometry.exists_finitePresentation_local_object_models`
  (node `lem-pc-fp-local-object-models`), in its own module.
- `AlgebraicGeometry.exists_finitePresentation_local_overlap_models`
  (node `lem-pc-fp-local-overlap-models`), in its own module.

This is a decomposition: one upper hole is closed and two lower holes are added,
so it is not a net reduction of holes. Each lower statement is strictly a part of the
argument. Object lifting asserts no transitions or descent datum. Overlap lifting
assumes already supplied local models and comparisons; it neither descends objects
nor asserts their finite-presentation properties. The preservation and final
isomorphism construction are proved in the main module. The private helper
`nonempty_descentData_iso_of_components` is fully proved.

Edge-case review: the fixed index makes the upper tail nonempty; quotienting the
preorder identifies isomorphic stages. Empty Xi allows empty covers and vacuous local
families, with the unique empty datum. A zero ring or zero module uses a zero finite
presentation and poses no exception to either clause. Initial component comparisons
need not be compatible: overlap maps are defined by conjugation using them. No module
is chosen in a definition from a mere existence theorem; all witness elimination is
inside theorem proofs.

## No longer needed

Removed the main module's direct proof import of `Sheaf.Algebra.FinitePresentationColimit`
and its direct DAG edge to `lem-pc-fp-module-map-descent-affine`. That theorem remains
needed by both lower statements, which import its module. Consequently no whole
module or node is pruned from the target closure. No other imports are removed;
all original public imports are required by the unchanged signature, and the new
proof imports supply the two lifting steps and pullback/isomorphism invariance.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found. The existing affine declaration is a ring/module
statement: applying it to schemes requires the local coordinate-ring, affine sheaf,
and overlap gluing arguments expanded in the two new nodes. It does not itself
supply those geometric conclusions. LeanSearch was unavailable (HTTP Internal Server
Error), recorded honestly; LeanFinder/Loogle and source grep found no direct match.
The Stacks sources are not materialized in this read-only clone; the cited proofs
were read from the official Tag 01ZR and Tag 05N7 pages. The ancestor script returned
None for the module-valued creation chain, so the new nodes inherit the parent's
explicit blueprint ancestor `lem-pc-rf-perfect-base-change` and chain.

## New nodes

`lem-pc-fp-local-object-models`: finite affine local module models, without overlaps,
in `lean/Sheaf/AlgebraicGeometry/FinitePresentationLocalObjectModels.lean`. The proof
uses only the object clause of the affine descent theorem and the finite chart
construction from Tag 01ZR.

`lem-pc-fp-local-overlap-models`: eventual compatible transition maps between the
supplied models, in `lean/Sheaf/AlgebraicGeometry/FinitePresentationLocalOverlapModels.lean`.
The proof uses the map/equality clauses of the affine descent theorem and Zariski
gluing. Componentwise invertibility is stated, leaving the final categorical iso
construction to the proved assembly.

No change records or forced adaptations are needed: existing interfaces are unchanged.

## Second reading by P2

1. Compared the delivered main module with the repository using `diff -u` and
   checked its existing theorem signature byte for byte: identical. Its docstring,
   universe, visibility, and all four public imports are unchanged. The other two
   modules are new statements, not adaptations of existing interfaces. No change
   record is required. Verdict: no accidental interface change.

2. Compiled all three delivered modules with `lcompile.py --all`, in dependency
   order. A scratch copy printed axioms of the original theorem, both new theorems,
   and the private component-isomorphism helper. The first three use only propext,
   Classical.choice, Quot.sound, and sorryAx; the helper uses only the three standard
   axioms. Only the two explicitly reported public theorems contain sorry. There
   are no new definitions or data constructions from unproved existence theorems:
   choosing `e` and eliminating the model witnesses occur inside a proposition proof.
   Verdict: the assembly is checked, conditional on the two documented holes.

3. Read both new Lean statements, their full proof docstrings and DAG nodes against
   [Stacks 01ZR](https://stacks.math.columbia.edu/tag/01ZR), first proof, and
   [Stacks 05N7](https://stacks.math.columbia.edu/tag/05N7), all three clauses.
   For objects, quasi-compactness over an affine base supplies a finite affine cover;
   the affine colimit object clause supplies the local models. For overlap lifting,
   quasi-separatedness over that base makes the finite pairwise and triple overlap
   refinements quasi-compact, so the map and equality clauses apply to finitely many
   comparisons, inverses, refinement agreements and cocycle equations. No affine
   intersection is assumed: it is covered by finitely many affines. The fixed j and
   supplied N and e are inputs to the overlap lemma; it does not perform object
   descent. M needs no extra finiteness assumption there, since e identifies it
   locally with the finite models. Empty covers, zero rings/modules, a one-stage
   system, and equivalent indices of a preorder introduce no exception. The fixed
   index makes the relevant upper tail nonempty. Verdict: both statements are true,
   sufficient, and strictly parts of the original argument, not renamed copies.
   Independent LeanFinder searches used “has a model over one scheme in the inverse
   system” and “become compatible at a common later index”; results concerned generic
   finite presentations and presentation maps, not finite-stage geometric lifting.
   Source searches in Mathlib's algebraic geometry and module-sheaf directories and
   the upstream module library found affine-transition limits, pullback stability
   and Zariski descent, but no theorem that closes these two statements directly.
   The repository's global module-map descent theorem imports this item, so using
   it here would be circular. Neither hole has a short existing-lemma solution.

4. Traced the assembly from the target downward: the object lemma supplies the
   finite affine U, the overlap lemma supplies D on its later pullback V, and the
   main proof shows V affine via the affine transition map, transports both module
   properties along hD, and builds the final iso with eta.comm. FiniteDescent is
   required for its pullback instance and isomorphism-invariance theorem; all three
   added imports are proof-only. The only old proof dependency was the affine
   descent node; its direct edge/import is removed and reported under No longer
   needed, but both lower nodes retain it. No whole module is pruned. Read
   dag/units/sk-thm-picard-semicon.json and its realized field: this delivery changes
   neither it nor any unit-level route. Verdict: genuine decomposition, net -1 hole,
   with no claimed net proof progress or unit bypass.

5. Compared the old and new parent node and checked the new nodes against Lean.
   Parent proof/proof_deps now name the two actual calls and the proved categorical
   assembly. Each new node carries its source, creation, blueprint ancestry, same
   chapter/unit, Lean signature and three search records. Its proof dependencies
   retain the affine descent node. Verdict: node routes and statements agree with
   the delivered declarations.

Changed during second reading: added the missing blueprint node marker to each
new module-level docstring. No signatures, proof bodies or dependency routes needed
repair. Added this independent review; removed the temporary axiom probe from the
sandbox before delivery. This remains a decomposition: one original hole closed,
two lower holes added, and no modules pruned.
