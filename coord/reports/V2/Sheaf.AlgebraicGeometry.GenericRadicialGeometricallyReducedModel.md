## What changed

Proved `AlgebraicGeometry.exists_generic_radicial_geometrically_reduced_model` from the
new radicial preparation theorem and the existing generic flat finite-presentation theorem.
The original declaration's signature and visibility are unchanged. Added only the proof import
`Sheaf.AlgebraicGeometry.RadicialGenericReducedPreparation` to the original module.

The Lean proof obtains the nonempty generic-flat open, descends a principal open through the
base universal homeomorphism, restricts both affine schemes, proves integrality and reducedness,
and transports flatness and finite presentation through restriction-of-restriction isomorphisms.
A proved private helper identifies the geometric morphism properties of restricted fibres
using the pullback square and the residue-field isomorphism of an open immersion. The generic
point and both fibre comparisons are then proved explicitly. No chosen witness defines data
in a public definition; all constructions are local to the theorem proof.

## Proved and sorry left

Closed the sole original hole in
`AlgebraicGeometry.exists_generic_radicial_geometrically_reduced_model`
(node `lem-sbc-generic-radicial-geometrically-reduced-model`).
The original module contains no remaining sorry.

Added one hole, the entire public proof `:= by sorry` of
`AlgebraicGeometry.exists_radicial_generic_reduced_preparation`
(node `lem-sbc-radicial-generic-reduced-preparation`), in the new module
`Sheaf.AlgebraicGeometry.RadicialGenericReducedPreparation`.

This is a decomposition: one upper hole closed, one strictly smaller hole added, net zero.
Preparation gives only a locally finite type family, with neither flatness nor local finite
presentation. Generic flatness, affine shrinking, descent of the shrinking to the original
base, and compatibility of geometric fibre properties are discharged by the original module's
Lean proof. The new theorem is not an application-equivalent renaming of the original result.
The existing generic-flat theorem and its lower dependencies are reused, without modification.

Both modules compiled cleanly with lcompile.py, with the new module compiled first.

## No longer needed

No old proof-dependency nodes or modules have been pruned. The second reading removed
the unused public imports `Mathlib.AlgebraicGeometry.Morphisms.Flat` and
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` from the new preparation module.
Neither property occurs in its signature. The original generic-flat dependency
remains necessary, both for the preparation argument and for the proved final shrinking.
The unit's `realized` lists are empty, and the route through generic flatness, radicial base
change and the final generic-flat shrinking is retained.

## Where the brief, the DAG or earlier work was wrong

The original DAG's radicial extension and fibre-preservation steps had no named proof
 dependencies. The preparation node records those unfinished parts together, with their full
source construction and the existing generic-flat dependency. No mathematical statement or
public interface was changed. Tags 0559 (second proof) and 052A were read online.

No shorter matching declaration was found in the project or Mathlib. LeanFinder returned
integrality and normalization facts rather than the preparation statement. Loogle did not
recognize the unqualified geometric-reducedness identifier. Grep found no applicable radicial
preparation theorem. LeanSearch returned HTTP 500, recorded as unavailable. Searches are logged
in searches.jsonl. Blueprint searches for geometric reducedness and purely inseparable
extensions found definitions, field-specialized tools and smoothness lemmas, but no statement
of this affine radicial preparation.

Edge cases checked for the preparation: characteristic zero uses the trivial inseparable
extension; relative dimension zero still admits the finite inseparable extension; empty
special fibres preserve the equivalence, and the assumed geometrically irreducible generic
fibre excludes an empty source. The base is allowed to be nonreduced before reduction.

## New nodes

`lem-sbc-radicial-generic-reduced-preparation`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-radicial-generic-reduced-preparation.json`, isolates
the reductions and finite inseparable algebra construction before the final generic-flat
shrinking. Its module is `Sheaf.AlgebraicGeometry.RadicialGenericReducedPreparation`.
Its docstring gives the construction, including the denominator scaling, reduction of the
base-changed source, and preservation of geometric fibre spaces. Its source is Tag 0559's
second proof. Its statement has no flatness or finite-presentation conclusion.
No change record is needed: no existing signature, definition, or public import was changed.

## Second reading by V2

1. Compared the original module with the repository using diff. The existing theorem's
   signature, visibility and docstring are byte for byte unchanged. Only its proof, a
   proof-only import and a proved private fibre-restriction helper were added. There are
   no existing definitions or target statements changed, and no forced adaptations.
2. Compiled both delivered modules in import order with lcompile.py after the import repair.
   Both compile without errors or warnings. Checked all delivered source for prohibited
   declarations and holes: exactly one sorry remains, the named public preparation theorem;
   no definitions or arbitrary data choices from unproved existence theorems occur.
   Scratch-copy #print axioms checks on both public theorems show only propext,
   Classical.choice, Quot.sound and sorryAx for each theorem.
   The original theorem still depends on open mathematics; it is not axiom-free completion.
3. Read the preparation signature, its docstring and matching node against Stacks Tag 0559,
   second proof, and Tag 052A. Its omission of final flatness/finite presentation is exactly
   what the original module's genuine shrinking argument supplies. The additional affine-open
   condition supports descent of the shrinking. It is a strict part of the argument, not a
   renamed application-equivalent target. Checked characteristic zero, zero-dimensional
   generic fibre, nonreduced base and empty special fibres. Geometric irreducibility excludes
   an empty generic fibre and ensures a domain after reduction and localization. The scaled
   generator construction is finite radicial over a possibly nonnoetherian domain. Reduction
   commutes with generic localization; embedding the reduced generic ring into the separably
   generated function field proves its geometric reducedness by flatness of field extensions.
   Independently searched LeanFinder for separably generated extensions after finite purely
   inseparable base extension, qualified Loogle for AlgebraicGeometry.GeometricallyReduced,
   and grep for separably generated / geometric-reduced existence results; also searched
   lean/Sheaf and lean/WeilConjectures. Results give component tools, not this preparation.
   No quick proof closing the new hole was found.
4. Read the original proof from its conclusion through the restriction constructions.
   GenericFlatFinitePresentation is genuinely applied; every old proof_deps entry remains
   used. The helper is a short pullback/isomorphism argument using existing Mathlib facts.
   Removed the two unused public Flat and FinitePresentation imports from the new module;
   retained its proof-plan import of GenericFlatFinitePresentation. Checked
   dag/units/sk-prop-normal-form.json: realized.statement and both realized.steps lists are
   empty. The delivery preserves the reductions, radicial extension and generic-flat route;
   it replaces no realized unit step. No old nodes or modules become unnecessary.
5. Checked both DAG nodes against Lean: existing proof_deps names preparation and generic
   flat finite presentation; its proof steps describe the actual shrinking and fibre glue.
   The new node names its generic-flat dependency, has the required source, searches,
   blueprint ancestry, chapter/unit, creation and verbatim Lean statement fields, and
   describes the remaining construction. proof_origin records the actual source route.

Second reading changed only the new module's imports and this report. Verdict: valid
one-for-one decomposition, net zero holes closed, ready for delivery.
