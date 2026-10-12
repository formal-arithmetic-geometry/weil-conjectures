## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.finiteEtale_genericFibre_hom_extension_exists` with a complete,
compiling proof from two strictly smaller mathematical inputs. The signature and existing
docstring are unchanged. Added two proof-only imports, with one theorem per new module:
`Sheaf.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometry` and
`Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull`.

The proof constructs the generic restrictions as actual Mathlib pullbacks. It restricts
`fη` by their universal properties, pastes the squares, extends over C by generic-point
fullness, and constructs the restriction of that extension using `hY.lift`. A second
application of generic-point full faithfulness, now over Cη, identifies this restriction
with `fη`. Both projection equations are checked explicitly with `hY.hom_ext`.
No definition was added, and no target or existing declaration signature was changed.

The geometric input concerns only C and Cη: integrality, integrally closed stalks, and
their compatible generic-stalk spectrum isomorphism. It mentions no finite covers or
extension problem. The other input concerns the generic POINT of an arbitrary normal
integral scheme, not a smooth family's generic fibre. The theorem being proved combines
them and uses the second input twice. Neither new theorem restates the assigned theorem
or repackages its hypotheses.

All three modules compile cleanly with `lcompile.py --all` (about three seconds per module).
The item DAG now records the two actual inputs and the pullback combination argument.

## Proved and sorry left

Closed the local hole in
`AlgebraicGeometry.Scheme.finiteEtale_genericFibre_hom_extension_exists`
(node `lem-sbc-finite-etale-generic-fibre-hom-extension-existence`).
This is a DECOMPOSITION, not a proof without sorried dependencies: one upper hole closed,
two new lower holes added. The assigned module itself contains no remaining `sorry`.

Every new hole, each the entire proof of a public named theorem in its own module:

- `AlgebraicGeometry.Scheme.smooth_connected_generic_geometry`, node
  `lem-sbc-smooth-connected-generic-geometry`, in `SmoothConnectedGenericGeometry.lean`.
- `AlgebraicGeometry.Scheme.finiteEtale_normalIntegral_generic_hom_full`, node
  `lem-sbc-normal-integral-generic-hom-full`, in `NormalIntegralGenericHomFull.lean`.

Both declarations have complete natural-language proofs, source places, and blueprint tags.
No hole was left in a definition, helper, or partial proof. The parent depends on these
holes transitively and is not claimed to meet the project's final axiom criterion yet.

## No longer needed

None of the baseline imports was removed: all five public Mathlib imports occur in the
unchanged statement's geometry and finite étale hypotheses. The baseline node had no
`proof_deps`, so no previously required node or module can be claimed as pruned.

`GenericFibreCoverDensity` was considered but is not used or imported in the final proof.
It is already used elsewhere, so this is not a claim that it leaves the targets' closure.
No separate density, reducedness, or generic-faithfulness node was created. Uniqueness
in the generic-point input handles the final comparison instead. No fundamental-group,
Galois-action, connected-cover, or Noetherian-normal-components module is imported.

## Where the brief, the DAG or earlier work was wrong

The assigned node's numbered plan consisted of one paragraph with `uses: []`, rather
than named Lean inputs for its non-elementary geometric and generic-point steps. The
new nodes state those inputs and the updated parent plan records their exact use.

Mathlib's `GeometricallyConnected` requires connected (therefore nonempty) fibres and
provides `Surjective c`. With S integral the empty-C branch in the existing docstring
cannot occur; the proof establishes `Nonempty C` directly from `c.surjective` at S's
generic point. This does not change the statement or its meaning.

Normal connected schemes are not used as integral without an additional argument:
the fibres here are smooth over fields, hence locally noetherian, so their normal
irreducible components are open and disjoint. Connectedness then implies integrality.
No Noetherian or quasi-compact hypothesis on the base or the family was introduced.

Sources checked directly: [0BQM](https://stacks.math.columbia.edu/tag/0BQM) gives
full faithfulness at the generic point; [0BQL](https://stacks.math.columbia.edu/tag/0BQL)
identifies connected finite étale covers with normalizations.
[034F](https://stacks.math.columbia.edu/tag/034F),
[033C](https://stacks.math.columbia.edu/tag/033C),
[056T](https://stacks.math.columbia.edu/tag/056T), and
[01UA](https://stacks.math.columbia.edu/tag/01UA) support the geometric argument.
The generic-stalk localization and the Lean pullback glue were written here.

Searches: LeanSearch was unavailable with Internal Server Error for both inputs.
LeanFinder returned the étale forgetful functor's full faithfulness, not generic
restriction, for the extension query; the geometry query returned normalization
integrality and the definition `IsIntegral`, not the required family geometry.
Loogle had no result for the smooth/integral query. Grep of Mathlib, WeilConjectures,
Sheaf, and DAG nodes found the source's field-base regularity/geometric irreducibility
results and `SmoothNormalRing`, but not either complete input. The blueprint search
found no independent blueprint statement of these exact inputs. The existing
Noetherian normal-components theorem has extra hypotheses and does not give generic
extension. The new nodes record these searches.

Edge cases checked mathematically: empty X has its unique outgoing morphism, and
empty Y has no generic incoming map from a nonempty finite étale X. Disconnected
covers are handled by finite products of generic fields; no connectedness of either
cover is used. Taking C=S and c=id gives Cη=Spec K(S), and the geometric isomorphism
is the canonical generic-stalk identification. Over a field the generic-point
restriction is an isomorphism and the full-faithfulness statement is tautological.
Smooth geometrically disconnected families are deliberately not inputs of the
geometric theorem. None of these checks required changing a statement.

A transient compile failure was caused by `GenericFibreCoverDensity.olean` being
absent from the synced compiled library despite its source being present. The final
proof avoids that import and follows the original node's generic-point uniqueness
argument. No build script was changed or bypassed.

## New nodes

`lem-sbc-smooth-connected-generic-geometry`:
`lean/Sheaf/AlgebraicGeometry/Morphisms/SmoothConnectedGenericGeometry.lean` states
normal integrality of the nonempty family and its generic fibre and identifies
their generic stalks. This is the geometric preparatory part of the assigned plan,
with no assertion about finite étale morphism extensions.

`lem-sbc-normal-integral-generic-hom-full`:
`lean/Sheaf/AlgebraicGeometry/Morphisms/NormalIntegralGenericHomFull.lean` states
unique extension from the generic point of an arbitrary normal integral scheme.
Its affine integral-closure argument is the full-faithfulness input of 0BQM.
It is used on C and Cη, after explicit construction and comparison of their
cartesian generic restrictions.

Both nodes are in `sec-smooth-base-change`, unit `sk-prop-input-spreading`, below
the same spreading/action-extension blueprint ancestor. The unit route is preserved.
There are no change records because no existing statement or definition was changed.

## Second reading by Y2

1. Compared the delivered parent module and both new modules with the repository versions. Existing declaration signatures and definitions are unchanged; the parent adds only proof imports and proof text. Verdict: pass.
2. Compiled all three modules with `lcompile.py --all`; compilation succeeds with no errors. The parent has no `sorry`; the two named split-off theorems are the only remaining holes, with no hollow definitions or forbidden declarations. Verdict: pass.
3. Reviewed both split-off statements against their hypotheses and edge cases. Each is strictly smaller than the assigned extension theorem, has a source, proof docstring, blueprint tag, and matching DAG node. Verdict: pass.
4. Checked the proof route for shorter available declarations and imports. The parent uses the two split-off inputs, explicit pullback constructions, and generic-point uniqueness; no baseline proof dependency was available to prune, and `GenericFibreCoverDensity` is not imported. Verdict: pass.
5. Checked DAG alignment and unit route. The parent node records both new proof dependencies and the new nodes remain in `sec-smooth-base-change`, unit `sk-prop-input-spreading`; realized route is preserved. Verdict: pass.

Changed only the parent proof/imports, added the two proof-only theorem modules and their DAG nodes, and appended this review. No statement or definition required repair.
