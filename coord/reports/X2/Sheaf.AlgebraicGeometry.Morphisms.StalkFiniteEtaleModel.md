## What changed

The original module now proves
`AlgebraicGeometry.Scheme.GaloisCover.exists_stalk_finiteEtale_model` from two
strictly smaller property statements about a concrete relative normalization.
Its existing signature and public imports are unchanged. There are no changed
definitions, target statements, or forced adaptations.

The private proved lemma `exists_minimal_boundary` chooses a generic point in
the nonempty closed complement and proves that it has no proper generalization
in that complement. The proof works in the closed subspace using its sobriety,
maximal irreducible components, and T0 uniqueness of generic points. It does
not assume the whole complement is irreducible.

For `f = PA.obj.hom ≫ (c ⁻¹ᵁ U).ι`, the candidate is the pullback of the actual
Mathlib `f.normalization` along the local-family projection. Two new modules
state its finiteness and its conditional etaleness. The first needs neither
the section nor the rational point; the second assumes the concrete morphism
is finite and proves only its etaleness. Both statements fix s and require its
proved minimality property. Neither asserts existence of a model or supplies
the overlap isomorphism.

The remaining argument is complete Lean: form Q from this concrete morphism
and the two property proofs, identify PA with the normalization restricted to
the open, paste the two overlap squares, and lift their canonical isomorphism
through the etale and finite full subcategories. No witness of an unproved
mere existence theorem is chosen. The construction also handles disconnected
covers without assuming an integral total space for PA.

All three modules compile together through lcompile.py in import order with
no compiler warnings. The local source was read at
`pione-lemma-extend-covering`, `pione-lemma-extend-S2`, and
`pione-lemma-purity-smooth-over-depth2`. Mathlib and both library roots were
searched. LeanSearch returned Internal Server Error and is recorded as
unavailable; LeanFinder, Loogle, and grep returned no complete local theorem.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.GaloisCover.exists_stalk_finiteEtale_model`
(node `lem-sbc-stalk-finite-etale-model`). No sorry remains in the original module.

Added two named public holes, each in its own new module, with source and proof:

- `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_finite`
  (`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFinite`,
  node `lem-sbc-stalk-normalization-finite`).
- `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_etale`
  (`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale`,
  node `lem-sbc-stalk-normalization-etale`).

This is a decomposition, not a completed geometric proof: one upper hole
closed and two strictly smaller lower property holes added. The original
statement is assembled from their distinct conclusions and a proved
comparison, rather than moved to another name. Every remaining proof is
exactly `:= by sorry`; there are no holes in definitions or private helpers.

## No longer needed

Removed the original module's direct private imports:

- `Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension`
  (`lem-sbc-generic-fibre-action-extension`).
- `Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull`
  (`lem-sbc-normal-integral-generic-hom-full`).
- `Sheaf.RingTheory.FlatLocalDepthFormula`
  (`lem-weil-pbc-flat-local-depth-formula`).
- `Sheaf.RingTheory.NormalLocalDepthTwo`
  (`lem-weil-pbc-normal-local-depth-two`).

The assembling proof no longer uses these declarations. Their mathematical
roles remain in the new property nodes' plans, so this delivery does not
claim they can be discarded from the mathematical DAG or from other users.
No unit statement or step is bypassed. The original unit's trait case and
depth-two formal-section case remain the two cases of the property arguments.
The only added proof imports in the original module are the two new modules
and Mathlib.AlgebraicGeometry.Normalization.

## Where the brief, the DAG or earlier work was wrong

The original node's steps cite tame normalization, depth-two extension,
power-series full faithfulness and purity only by source tag, with no Lean
interfaces for their local construction. Its four existing dependencies
provide action extension, generic hom extension, and ring depth, not a scheme
model. They cannot alone prove the original conclusion. The missing assembly
is now represented by two precise property obligations instead of an opaque
existence obligation.

The normalization restriction and overlap comparison need no additional
geometric hole: normalization commutes with smooth base change, normalization
of a finite morphism is trivial, and the comparison follows by pasting
pullback squares. These Mathlib facts are used for disconnected PA as well.

Edge cases were checked in the statements and construction: U=top is excluded
only where selecting a boundary requires it; the new statements replace that
condition by an actual s outside U. The finite statement drops the section
and rational-point assumptions. The etale statement keeps both, including the
two generic-section compatibility equations. Neither asserts finiteness of
arbitrary normalization of an arbitrary Noetherian scheme, and neither
assumes connectedness of the total cover.

An additional possible shorter route for the finite property is the trace-dual
basis bound: Mathlib's `IsIntegralClosure.finite` applies to finite separable
extensions of fraction fields of normal Noetherian domains. Turning the
punctured finite etale algebra into the finite product of such extensions,
with the required affine and localization comparisons, is further work; this
alternative is not claimed proved in the delivery.

## New nodes

`lem-sbc-stalk-normalization-finite` states finiteness of the fixed concrete
normalization pullback, with no section hypothesis. Its proof records the
tame trait case and the finite depth-two algebra case, identification with
integral closure, and localization compatibility. Its module is
`lean/Sheaf/AlgebraicGeometry/Morphisms/StalkNormalizationFinite.lean`.

`lem-sbc-stalk-normalization-etale` states etaleness of the same fixed morphism
assuming its finiteness and the split-section data. Its proof records the
split-section trait test, purity, power-series computation, flat descent,
and the fibre criterion. Its module is
`lean/Sheaf/AlgebraicGeometry/Morphisms/StalkNormalizationEtale.lean`.

Both inherit sec-smooth-base-change and sk-prop-input-spreading. Searches of
the imported blueprint and DAG found no matching existing property statement.
The original node's proof, proof_deps, and proof_origin now follow the compiled
assembly. No change record is needed because existing interfaces are unchanged.

## Second reading by X2

1. **No accidental interface changes.** Compared the delivered original module with the repository version. The theorem signature is byte-for-byte unchanged; only its proof, proof-origin documentation, authorship, and imports changed. The two added declarations are new split-off property statements and do not alter existing interfaces.

2. **Compilation and proof audit.** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds without warnings. The original theorem has no `sorry`, while the two new property theorems contain exactly the named `sorry` holes listed above. No definitions contain `sorry`, and no forbidden declarations occur. The remaining `sorryAx` use is confined to those explicitly split-off theorem proofs.

3. **Split statements.** Checked both new statements against the concrete normalization used by the original proof. The finiteness statement is strictly smaller and correctly omits section and rational-point hypotheses; the etaleness statement assumes finiteness and retains the section and generic split-point data. Their source, proof prose, DAG nodes, and Lean signatures agree. Searches recorded in the report found no existing equivalent declaration.

4. **Route and pruning.** The original proof constructs the concrete relative normalization, applies the two property lemmas, and proves the comparison by pullback and normalization identities. The unit route remains represented by the two property nodes; the four former direct proof imports are removed from the original module and listed under “No longer needed.”

5. **DAG agreement.** Verified that the original node’s proof, dependencies, and origin describe the compiled proof, and that each new node records its Lean declaration, source, proof plan, and split status. No target statement or definition was changed.

I repaired no declarations during second reading; the delivered files already passed compilation and the interface, statement, pruning, and DAG checks above.
