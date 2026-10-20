## What changed

Retired `Sheaf.AlgebraicGeometry.ExteriorSheafDualExt` in favor of
`WeilConjectures.AlgebraicGeometry.ExteriorSheafDualExt`, as required by this item's
`retire` queue row. Updated `lem-sc-exterior-sheaf-dual-ext` to the upstream module
and its actual upstream signature.

The upstream theorem uses `Scheme.Modules.exteriorPower` and `wedge`, whereas the
three consumers use `exteriorSheaf` and `exteriorSheafSection`. Added the fully proved
`Sheaf.AlgebraicGeometry.ExteriorSheafComparison`: identify the sectionwise
presheaves by identity components (restrictions agree on pure wedges); sheafify;
prove both wedge formulas by naturality of the adjunction unit and inverse laws.
Then transport the upstream extensionality theorem by precomposing with the inverse
comparison on Over U and canceling that isomorphism.

Adapted only the private import and extensionality applications in
`DeterminantDualPairingFunctional`, `DeterminantDualAlternatingFamily`, and
`DeterminantDualPairing`; every existing signature is unchanged. Updated their
three proof-node copies to record the comparison dependency. No upstream file,
target, exterior-sheaf definition, or unit route changed.

Validation: the original item compiled with zero holes; the comparison and all
three consumers compiled together through `lcompile.py --all`, with no warnings.
The dry run passed preflight (CODEX). Its broad axiom probes timed out for three
files; a separate single-file `#print axioms` check then verified all five new
declarations and all three adapted determinant-pairing theorems: each depends
only on `propext`, `Classical.choice`, and `Quot.sound` (3.7 s, compiled).
Edge cases n = 0, empty opens, the empty scheme, and zero rings require no extra
hypotheses: identity sectionwise maps, functorial sheafification, inverse laws and
upstream wedge extensionality all apply unchanged. The comparison is constructed
explicitly, not selected from an existence theorem.

## Proved and sorry left

The item originally had **0 sorries**, and its retired copy has **0**. Holes closed:
none. Holes added: none. Split off: none. This is a retirement/API repair, not a
hole-closing proof or a decomposition.

New fully proved declarations:
- `AlgebraicGeometry.Scheme.Modules.exteriorSheafPresheafIso` (constructed data).
- `AlgebraicGeometry.Scheme.Modules.exteriorSheafIsoExteriorPower` (constructed data).
- `AlgebraicGeometry.Scheme.Modules.exteriorSheafIsoExteriorPower_hom_wedge`.
- `AlgebraicGeometry.Scheme.Modules.exteriorSheafIsoExteriorPower_inv_wedge`.
- `AlgebraicGeometry.exteriorSheaf_dual_ext_compat` (uses the upstream theorem).

All five are recorded by `lem-sc-exterior-sheaf-comparison`. There is no remaining
`sorry` in any delivered Lean module. The three determinant-pairing theorems retain
their existing complete proofs, using the compatibility API for extensionality.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.ExteriorSheafDualExt`. Removed its private
import from all three direct consumers. Its copied extensionality proof is no
longer retained: the official upstream proof supplies the result. The old DAG
node is preserved and points to the upstream twin.

The local `Modules.ExteriorSheaf` construction remains necessary to existing
consumer statements; `Modules.Dual` and the module-sheafification interface remain
necessary. No other node or module is pruned. The comparison depends on the
upstream extensionality node, so the DAG has no self-dependency.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open hole, but the assigned queue item is
actually `retire` with zero holes. Its specific requirement is the human's
2026-10-20 hand-off in `coord/changes/retire-sheaf-twins-20261020.md`.
The upstream twin restates the theorem on its own exterior-power construction;
a bare import rewrite does not repair the API. The explicit wedge-preserving
isomorphism resolves that mismatch without weakening or changing a statement.
No mathematical statement is disputed.

## New nodes

`lem-sc-exterior-sheaf-comparison` records the explicit comparison of the two
presheaves and their sheafifications, both wedge formulas, and transport of
internal-dual extensionality. Source: Stacks Project Tag 03CY,
`sites-modules.tex`, `lemma-sheafification-presheaf-modules`; the exterior-power
universal property and upstream `exteriorPower_map_ιMulti`. No new hole is left.
Mathlib searches ran with leanfinder, loogle, leansearch and grep; the blueprint
search for “exterior sheaf comparison” returned no matching node.

Change record: `coord/changes/exterior-sheaf-dual-ext-retirement.md`.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
