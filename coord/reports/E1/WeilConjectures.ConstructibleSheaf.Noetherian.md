## What changed

Filled all four original sorry proofs in
`WeilConjectures.ConstructibleSheaf.Noetherian`, preserving every existing declaration
signature and visibility. Added three ordinary proof imports:
`Sheaf.AlgebraicGeometry.IrreducibleStratificationRefinement`,
`Sheaf.AlgebraicGeometry.ConstructibleModuleSubobjectNoetherian`, and
`WeilConjectures.ConstructibleSheaf.DenseOpenUnit`.

The generic-stalk argument proves that the kernel inclusion is zero. Near every section
and point, the existing locally constant chart lemma supplies a constant value n.
The chart image is nonempty open, hence contains the generic point. Lift the given
separably closed geometric generic point into that chart. The kernel inclusion has zero
stalk there, so the filtered-colimit equality criterion supplies a nonempty refinement
where the section vanishes. Thus n = 0 and the section vanishes locally at the original
point. The sheaf condition makes the kernel inclusion zero. This works for the exact
IsSepClosed hypothesis of the source declaration, without strengthening it to IsAlgClosed.

For irreducible strata, refine a witnessing stratification with the existing topological
irreducible-refinement theorem, transport irreducibility through the immersion's
homeomorphism onto its image, and preserve finite local constancy under refinement.
The retained finite-ring binder is explicitly used to preserve the existing signature
and avoid an unused-section-variable warning.

For finite selection, take the geometric generic point of each irreducible stratum.
Its source stalk is finite by finite generation over the finite coefficient ring.
Select one detecting index for each nonzero element of this finite family of finite
stalks. Projection from the finite product proves injectivity at all chosen stalks.
The generic-stalk theorem makes each stratum restriction mono; inverse-image stalk
comparison and joint faithfulness of geometric stalks make the global map mono.
The dependent index set may be empty, so the empty-scheme and zero-sheaf cases are included.

Subobject closure is the finite-ring specialization of the existing, more general
`AlgebraicGeometry.Scheme.constructible_of_mono_noetherian`.

## Proved and sorry left

Closed 4 original holes, by declaration name:

- `AlgebraicGeometry.Etale.mono_of_mono_sheafFiber_of_isLocallyConstantSheaf`
  (blueprint `lem-weil-pbc-lisse-generic-kernel`).
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.exists_stratification_isIrreducible`
  (blueprint `lem-weil-pbc-irreducible-lisse-strata`).
- `AlgebraicGeometry.Etale.exists_finset_mono_pi_lift`
  (blueprint `lem-weil-pbc-constructible-noetherian-finite-selection`).
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_mono`
  (blueprint `lem-weil-pbc-constructible-subobjects-noetherian`).

Holes added: 0. Holes left in the item: 0. No split-offs or new declarations.
The already-complete cardinality criterion is retained unchanged.
These are proofs from the existing library's declarations; their transitive dependencies
are checked by the delivery probe and are not claimed as newly proved in this delivery.

Validation: the complete item compiled locally without errors or warnings through
`lcompile.py` (about 7 seconds). The required `deliver3.py --no-push` is the final check.

## No longer needed

None. No original import was removed, and no module is withdrawn. The three added imports
are all used by the proofs. No blueprint unit or its proof step is bypassed.
The generic and finite-selection proofs stay within their recorded chart, generic-point,
finite-selection and stalk-conservativity arguments. No separate abelian-forgetful
comparison modules or new intermediate statements are needed for these module-valued proofs.

## Where the brief, the DAG or earlier work was wrong

The item has no DAG node with its `lean.module` attached to this source module.
Its docstrings cite the four blueprint nodes, whose `lean` records instead name older
`Sheaf.AlgebraicGeometry` declarations. Consequently there is no module-attached node copy
to update for this proof-only delivery; changing those attachments would misdescribe the
existing Sheaf modules. The proofs implement the same recorded arguments specialized to
the source module's existing signatures. No statement or definition correction was needed.

The existing abelian generic-kernel theorem requires an algebraically closed field,
whereas this source theorem permits a separably closed field. The direct chart argument
avoids introducing a geometric-point comparison solely to bridge that mismatch.

## Second reading by E1

1. I compared the sandbox module with the repository version. Every existing declaration
signature and visibility is byte-for-byte unchanged; the only interface additions are the
three ordinary proof imports listed above. No target statement or definition changed.

2. I compiled the complete module with `lcompile.py`; it finished without errors or warnings.
The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
The four completed declarations use only the allowed library dependencies (and any transitive
open proofs remain outside this delivery).

3. I searched the library and the recorded declarations for duplicate helper statements.
No split-off theorem or new declaration was added, so there are no new holes or duplicate
statements to review.

4. I checked the proof routes from the top downward. The generic-kernel proof uses the
existing locally constant chart and generic-point/stalk machinery; the stratification proof
uses the irreducible refinement; finite selection uses the irreducible strata, finite stalks,
and generic-kernel theorem; and subobject closure uses the existing noetherian theorem. All
three added imports are used by these proofs, no original import is removable, and the unit
route is retained.

5. I checked the four cited DAG nodes and their recorded blueprint routes against the Lean
proofs. The source module has no module-attached DAG node (the records point to the earlier
`Sheaf.AlgebraicGeometry` declarations), so no node metadata can be updated without
misattributing those records. The existing node statements remain unchanged and the source
module's four declarations implement their corresponding routes.

No repair was needed after this second reading; only this review section was appended.
