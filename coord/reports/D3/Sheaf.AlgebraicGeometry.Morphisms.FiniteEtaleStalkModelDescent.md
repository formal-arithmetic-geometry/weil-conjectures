## What changed

Proved `AlgebraicGeometry.Scheme.FiniteEtale.exists_stalk_neighbourhood_model` in
`Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleStalkModelDescent`, preserving its signature
and existing public imports. Repaired the returned delivery by removing all three duplicate private declarations.
The main theorem now invokes the existing public
`exists_isPullback_of_finitePresentation` directly. Its resulting cartesian model is
passed to a proved private `exists_finiteEtale_refinement`: this has a different task
and signature, starting from an existing finitely presented model and returning a
finite etale model at a stage above the supplied stage. Nonemptiness is derived from
the supplied index. Base-change persistence uses Mathlib
`MorphismProperty.of_isPullback` directly; comparison with Over pullback is local
bookkeeping by `MorphismProperty.cancel_right_of_respectsIso`.
The matching helpers in GenericOpenFiniteEtaleModel are private and cannot be
reused through an ordinary import; no other module's visibility is changed.
No other existing module is changed.

The proof constructs the directed affine-neighbourhood diagram, its canonical stalk limit
cone, and its relative pullback diagram. Mathlib's connected-limit pullback theorem proves
the relative limit property. Finite presentation, finiteness and etaleness descend through
the existing stated dependencies. A common refinement retains both properties. The selected
stage is identified with the preimage open; the inverse cartesian comparison yields the
isomorphism in the finite etale category.

The module compiled cleanly with lcompile.py after removal of the unused proof import.
The DAG proof and dependencies were updated to match this argument. No definitions,
public signatures, target statements or visibility changed. All witness choices occur
inside theorem proofs; no data definition is chosen from unproved existence.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.FiniteEtale.exists_stalk_neighbourhood_model`
(node `lem-sbc-finite-etale-stalk-model-descent`).

Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
The sole new private refinement helper is proved. The proof uses the library's existing
finite-presentation and property-descent declarations; this is a proof from those
dependencies, not a claim that their entire transitive axiom closure is sorry-free.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.FibreProductLimit` and proof dependency
`lem-kun-fibre-product-limits`: Mathlib `isLimitOfIsPullbackOfIsConnected` applies directly
to the relative diagram and its stagewise cartesian squares.

Removed proof dependency `lem-weil-pbc-open-fibre-product`: its general open-fibre-product
image theorem is unnecessary. Mathlib `isPullback_morphismRestrict` directly identifies
the selected stage with the preimage open.

Retained all other original proof imports and the three descent dependencies
`thm-pd-spreading-out`, `lem-weil-pbc-descend-finite`, and
`lem-weil-pbc-descend-etale`, as well as the affine-neighbourhood limit dependency.
These pruning claims concern this theorem's route; other target branches may still
need the removed nodes and module.

## Where the brief, the DAG or earlier work was wrong

The returned first attempt duplicated three private declarations from
GenericOpenFiniteEtaleModel. That was a reuse error, and its earlier second reading
missed it. All three duplicates are removed; the refinement helper now handles only
property descent from a supplied model and additionally records the stage bound.
The old second-reading section was removed because it certifies the returned version;
a fresh independent reading is required. No mathematical or statement error found. The general fibre-product limit comparison
in the original plan is unnecessary for this particular relative diagram. The general
open-fibre-product image statement is also unnecessary for the stage identification.
The blueprint unit route is preserved: stalk spreading by limits and property descent.
Its `realized` lists are empty, so no recorded realization node is bypassed.

The repair uses the existing stated dependencies and the unit text in its DAG record.
No new unproved assertion was introduced.


## Second reading by D3

1. **Statements and interfaces.** I compared the delivered module with the repository version. The public theorem declaration and all existing declarations have identical signatures; only its proof and the proof-only import changed. The DAG statement is unchanged. Verdict: pass.

2. **Proof and axioms.** I compiled the module with `lcompile.py`; it compiles without errors or warnings. The delivered file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The construction uses theorem-local witnesses only. The proof follows the pullback limit, finite-presentation descent, property descent, and open-restriction comparison steps. Verdict: pass.

3. **New or split statements.** No public split-off statement or new node was added. The private refinement helper is proved and has a strictly narrower role than the target: it refines an already supplied finitely presented cartesian model while preserving the stage bound. Its uses of the existing finite and etale descent declarations are exactly the needed property statements. Verdict: pass.

4. **Pruning and imports.** The removed fibre-product-limit and open-fibre-product dependencies are not used by the proof; the direct Mathlib connected-limit and restriction-square lemmas replace them. Remaining imports correspond to declarations actually used. The node proof, proof dependencies, and proof origin match this route. Verdict: pass.

5. **Unit route and truth.** The unit route remains stalk spreading by affine-neighbourhood limits followed by finite-presentation, finiteness, and etale descent. The selected stage is identified with the preimage open by a cartesian restriction square, and the final finite-etale isomorphism is transported along that square. Edge cases are covered by the nonempty supplied index and the directed common-refinement argument. No statement or definition was changed. Verdict: pass.

I changed only the proof-only import, the proof and private helper, the matching DAG proof metadata, and this second-reading report section.
