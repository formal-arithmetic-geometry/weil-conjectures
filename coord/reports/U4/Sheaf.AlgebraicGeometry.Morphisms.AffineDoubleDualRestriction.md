## What changed

Proved `AlgebraicGeometry.Scheme.affine_double_dual_restriction` from a new
single-dual restriction comparison, applied twice, and the existing proved
`SheafOfModules.isIso_bidual`. The contravariant internal-Hom functor transports
the first comparison; composition with inverse biduality and the supplied `e`
finishes the proof. Existing signatures and public imports are unchanged.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.affine_double_dual_restriction`
(node `new-affine-double-dual-restriction`). Added one hole:
`AlgebraicGeometry.Scheme.affine_dual_restriction_comparison`
(node `new-affine-dual-restriction-comparison`, module
`Sheaf.AlgebraicGeometry.Morphisms.AffineDualRestrictionComparison`).
This is a decomposition, closing one hole and adding one, with net zero holes.
The new theorem states the single-dual localization comparison for every finite
module, independently of finite local freeness. It neither restates the target
nor assumes an isomorphism to P. The target combines two applications with the
already proved finite locally free biduality theorem.

## No longer needed

None of the original imports or dependency nodes was removed (the original
node had no proof dependencies). No new double-dual comparison, finite locally
free biduality, dual-transport or gluing node is needed in the target: the first
is assembled from the single-dual theorem, the next two use proved source
library declarations, and gluing remains solely in the comparison theorem.
The stalk comparison `new-affine-double-dual-stalk` is not used by this proof.

## Where the brief, the DAG or earlier work was wrong

The original plan cited no Lean declarations for either step. The source
library already supplies proved sheaf biduality in
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual`. It is used directly,
not duplicated as a new hole. No statement or unit route was changed.

Searches: LeanFinder returned tilde and generic sheaf APIs, no dual comparison;
Loogle did not recognize the source-library internal Hom identifier; grep
found no tilde/dual comparison; LeanSearch returned Internal Server Error.
Direct source search found the finite-presentation localization-Hom instance
and the proved internal-Hom and biduality APIs. Blueprint searches for
"localization of Hom", "Hom commutes", and "dual of a finite" found no
matching affine single-dual statement. Stacks Tags 0583 and 0EY6 were read
online; the local Stacks source directory is absent on this machine.

Edge cases checked mathematically: W empty, M zero, rank zero, and M with
nonzero torsion are all permitted by the comparison; its conclusion is only
identification with the sheaf dual, not reflexivity of M. Finite local freeness
is used exclusively in the proved target, after transport along e.symm.

## New nodes

`new-affine-dual-restriction-comparison` isolates localization of the single
module dual and gluing the canonical basic-open comparisons. Its module is
`Sheaf.AlgebraicGeometry.Morphisms.AffineDualRestrictionComparison`; its source,
complete proof in words, and search records are supplied. No change records
or forced adaptations are needed.

## Second reading by U4

1. **Interfaces: PASS.** Read both delivered modules and compared the existing
   module with the repository using `diff -u`. The sole existing declaration's
   signature, universes, hypotheses, conclusion, visibility and docstring are
   byte for byte unchanged. Only two plain proof imports and the proof body
   were added. There are no changed definitions, public imports, change records
   or forced adaptations.
2. **Proof and axioms: PASS, conditional decomposition.** Compiled both files
   in import order using `lcompile.py --all`; neither produced an error or
   warning. Scratch copies with `#print axioms` show only `propext`,
   `Classical.choice`, `Quot.sound`, and the expected `sorryAx` for both
   delivered theorems. Separate checks of `SheafOfModules.isIso_bidual` and
   `SheafOfModules.IsFiniteLocallyFree.of_iso` show only the three permitted
   axioms. The only literal hole is the named, documented single-dual theorem.
   No axiom, unsafe declaration, opaque declaration, implementation override,
   external implementation or hollow definition occurs. The two `obtain`s
   eliminate nonempty isomorphism propositions inside a theorem proving a
   proposition; they do not define objects from arbitrary existence witnesses.
3. **Split statement: PASS.** Checked the new theorem hypothesis by hypothesis:
   commutative Noetherian A makes finite M finitely presented; arbitrary W is
   allowed; the conclusion compares the actual module dual's tilde restriction
   with internal Hom into the actual structure module on W. Tag 0583 supplies
   the localization-Hom comparison. Localized evaluations commute with smaller
   basic-open restrictions and glue, exactly as its complete docstring says.
   Checked empty W, the zero ring, M = 0, rank zero, and torsion modules: none
   requires reflexivity of M. This is one dual comparison, independent of P
   and e, strictly part of the double-dual argument, not a renamed target.
   Independent LeanFinder search for "quasicoherent sheaf internal Hom finitely
   presented module localization", Loogle search for
   `Module.FinitePresentation, LinearMap`, and grep for internal-Hom/restriction
   and affine-Hom comparisons found no exact replacement. Read the nearby
   `affine_finite_free_dual_complex_comparison`: it assumes free modules in
   every degree and cannot handle arbitrary finite M. The existing stalk
   theorem supplies stalk isomorphisms, not a glued sheaf isomorphism. Closing
   the new hole needs the compatible sheaf comparison construction and is not
   a short application of the available APIs. Source pages checked:
   [0583](https://stacks.math.columbia.edu/tag/0583) and
   [0EY6](https://stacks.math.columbia.edu/tag/0EY6).
4. **Route and pruning: PASS.** Read the proof top down: d₂ identifies tilde
   M** on W with the dual of tilde M* on W; the contravariant Hom functor
   sends d₁ to an isomorphism from N** to that dual, so its inverse is the
   required next factor. Finite local freeness transfers from P to N via
   e.symm; inverse biduality and e finish the composition. All added imports
   are plain imports and used. Existing public imports support the unchanged
   interface. The original proof_deps was empty, so there is no omitted
   formerly needed node. The No longer needed section is complete. Read
   `dag/units/sk-prop-input-spreading.json`: its realized fields are empty;
   the depth-two extension step and its structural affine model are retained,
   and no unit-level route is bypassed.
5. **DAG: PASS.** Read both delivered node records and compared the old target
   node with the repository. The changed proof steps and proof_origin describe
   the two comparisons, contravariance and proved biduality. proof_deps is
   exactly the union of uses, namely the new single-dual node. The new node's
   Lean record matches its declaration verbatim and includes source, complete
   proof, searches, creation metadata, blueprint ancestry, chapter and unit.
   Its mathematical statement matches the Lean statement, with no local
   freeness or depth assumption hidden in the prose.

Second reading changed only this report, adding the independent review and
validation evidence. No Lean or DAG repair was needed. One original hole is
closed and one strictly simpler hole is added: decomposition, net zero holes;
no module is pruned. All scratch axiom probes were removed before delivery.
