## What changed

Closed `AlgebraicGeometry.koszulRegularImmersion_self_ext_yoneda_surjection`
without changing its signature, universe parameters, public imports, or existing docstring.
The proof factors through the internal dual of the exterior conormal sheaf. It uses
`exterior_dual_pairing_exists` and `exterior_dual_pairing_app_bijective`, the regular
conormal basis and affine frame, and `exteriorSheaf_restrict_iso`. Two proved private
helpers lift sections to stalks and transfer surjectivity across open restriction.
The final argument composes the three maps and their surjectivity on stalks.

Added `Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal` for the remaining
zero-differential Hom-complex calculation and its generator-independent gluing.
This is the dual of the exterior conormal, whereas the item's source is the exterior
power of the dual conormal. Its statement neither constructs exterior Yoneda products
nor asserts that such products generate: those exterior-duality steps are discharged
by the existing determinant lemmas and the Lean proof in the item. The new theorem
has its complete source-based proof in its docstring and its own node. Updated the
item's node to the actual factorization and listed the dependencies of the new node.

The determinant-pairing modules and exterior-restriction lemma are generic tools.
They do not replace the Picard-duality unit's statement or its steps; its `realized`
record lists no node-level constraint on this item. The Koszul computation is retained.
No existing definition, public statement, or consumer module was adapted.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.koszulRegularImmersion_self_ext_yoneda_surjection`
(node `lem-sc-koszul-self-ext-yoneda-surjection`). There is no `sorry` in the item.

Added one hole:
`AlgebraicGeometry.koszulRegularImmersion_self_ext_dual_exterior_conormal`
(node `lem-sc-koszul-self-ext-dual-exterior-conormal`) in
`Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal`.
Its proof is exactly `:= by sorry`. No other holes were added, and no data definitions
were added. This is a decomposition, not a net reduction in holes or an axiom-free
proof of the complete transitive closure.

Both delivered modules compile individually through `lcompile.py`, and the sandbox
set compiles in import order. The required `deliver3.py --no-push` printed OK: local
compilation, the axiom probe and preflight passed, with only the independent second
reading pending. Nothing was pushed. The proof preserves all original hypotheses.
Edge cases checked mathematically: degree zero uses the determinant of the empty
matrix and Hom(B,B)=B; degrees above a chart length have zero exterior and Hom
terms; length zero gives B=A; an empty V has no stalk obligations; zero section
rings and characteristic two cause no division or sign assumption.

## No longer needed

Removed from the item's proof imports:

- `Sheaf.RingTheory.KoszulProjectiveResolution`;
- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`;
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`;
- `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`.

Their nodes (`new-j3-koszul-projective-resolution`,
`lem-sc-affine-quotient-resolution-sheafification`,
`lem-sc-derived-internal-hom-restrict-open`, and
`lem-sc-derived-hom-finite-free-model`) are now dependencies of the residual
Koszul-comparison module. They remain needed transitively and are not claimed as
pruned modules. `Sheaf.RingTheory.KoszulConormalBasis` remains directly used.
No original node or module is proved unnecessary in the full targets' closure.
The original standalone intrinsic-boundary/Yoneda-construction route is unnecessary
for the existential conclusion: determinant evaluation and the dual-conormal Hom
calculation supply the requested morphism.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original DAG's first and third steps had no named
Lean dependencies despite requiring the intrinsic boundary, composition, alternation,
and gluing. Its listed affine-resolution lemmas alone do not state a global Yoneda map.
The replacement uses the already stated all-degree determinant pairing for exterior
duality and isolates the remaining Koszul Hom computation.

`tools/blueprint_refs.py ancestor` reports no ancestor for this module-backed item,
because its `created.item` is a module name. The existing item's explicit
`blueprint.from.node = lem-sc-finite-duality` and `via` chain are therefore used for
the new node. The blueprint text path from the unit record is absent locally; the
unit's statement and steps were read from its JSON record.

## New nodes

`lem-sc-koszul-self-ext-dual-exterior-conormal`: the Koszul Hom complex with quotient
coefficients has zero differential; its terms become the internal duals of the
exterior conormal, and their generator-change/localization formulas give the global
comparison on V. Source: Stacks Project Tag 0BQY, the displayed zero-differential
Hom calculation; Tag 062I for the regular conormal basis. LeanSearch returned HTTP
500 (recorded as unavailable); LeanFinder and source/blueprint searches found no
exact existing statement. It has one named hole and preserves the same local
regularity hypothesis as the item. No change record is needed.

## Second reading by M4

1. **Diff and interfaces.** Compared both delivered modules with the repository versions
and checked the existing theorem signature byte for byte. Verdict: unchanged target
statement and no accidental definition or hypothesis changes.
2. **Compilation and proof hygiene.** Compiled both modules with `lcompile.py --all`;
the item has no `sorry`, while the only remaining `sorry` is the named theorem in the
new split-off module. Searched for forbidden declarations and checked the proof's
composition and stalk-surjectivity helpers. Verdict: clean compilation and permitted
axiom profile as far as the local probe can inspect.
3. **Statements and nodes.** Read the new theorem, its docstring, and its DAG node;
the split statement is the strictly smaller zero-differential Koszul comparison and
does not restate the item. Verdict: true, sourced, and matched by its node and Lean
record.
4. **Pruning.** Checked the imports against names used in the proof and compared the
old and new dependency lists. Verdict: the four former proof-only imports are removed
from the item and retained transitively by the residual comparison theorem; no
additional unused import was found.
5. **Route and unit.** Checked the item's node route and the unit record's realized
fields. Verdict: the determinant pairing, conormal frame, restriction isomorphism,
and Koszul comparison preserve the unit route; no unit statement was bypassed.

I changed only this report by adding this second-reading record; no Lean source,
statement, definition, or DAG node was changed during the reading.
