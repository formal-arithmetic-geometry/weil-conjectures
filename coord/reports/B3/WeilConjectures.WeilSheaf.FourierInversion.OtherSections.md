## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.WeilComplex.nonempty_iso_upperStar_comp_derivedLowerShriek_of_isPullback`
by a distinguished-triangle argument. The new private, proved helper
`AlgebraicGeometry.isIso_triangle_first_coordinate` proves the precise matrix argument:
if A → B → E is distinguished and (p,g):B → D ⊕ E is invertible, then A → B → D is
invertible. It constructs a morphism to the split distinguished triangle and applies
`isIso₁_of_isIso₂₃`. Applied componentwise to two natural transformations, this produces
the required natural isomorphism. Naturality is therefore supplied by the maps themselves;
there is no arbitrary choice of isomorphisms at individual complexes.

Added three new modules under `Sheaf.WeilSheaf.FourierInversion`:
`ProjectiveLineRestriction` constructs q*Rq_* and its restriction map to infinity from
actual pullback-composition isomorphisms and the q-adjunction counit;
`ProjectiveLineDecomposition` states the proper projective-line calculation with its
restriction coordinate; `AffineChartLocalization` states the canonical affine-chart
localization triangle. The latter two are the remaining proof tasks. They concern
different objects and neither asserts an affine-line Thom isomorphism.

The two new proof imports of the item are private. Every existing public import,
declaration signature, attribute and existing proved body is preserved. No other existing
Lean module is changed. The construction contains no choice from an unproved existence
theorem and no data hole. The natural transformations supplied by the split theorems are
eliminated only in the proof of the parent's proposition.

The Mathlib searches in `searches.jsonl` located the split-triangle/five-lemma API but
no projective Weil-complex calculation. The three construction/statement records have
actual LeanSearch, Loogle/LeanFinder and source-grep searches. The proper finite-coefficient
projective-line and projection-formula statements have been read; they require passage
to the native derived category of Weil sheaves, which remains in the proper calculation.
The existing native open-closed theorem identifies only the vertices up to unspecified
isomorphisms and explicitly does not identify the arrows. The new localization statement
retains the needed natural first map and the specific restriction-to-infinity second map.

Edge cases checked mathematically: the zero complex and empty base give zero distinguished
triangles and zero biproduct isomorphisms; nilpotents on the base do not change the two
standard charts or the section identity; no absolute separatedness of X is used. The
projective bundle is trivial, so O(1) restricts to a trivial line at infinity. The generic
matrix argument needs neither semisimplicity nor a cancellation principle for biproducts.

## Proved and sorry left

Original item: one hole. Closed the body of
`AlgebraicGeometry.WeilComplex.nonempty_iso_upperStar_comp_derivedLowerShriek_of_isPullback`.
The other two public theorems in the module were already proved and are unchanged.
The private triangle helper and the restriction construction are complete proofs/data.
The item has zero remaining holes.

Added two named holes, each with its complete natural-language proof and its own module:

- `AlgebraicGeometry.WeilComplex.exists_projectiveLine_trace_decomposition`
  (`lem-pur-b3-weil-projective-decomposition`): the proper projective-line calculation,
  including compatible coefficient passage and native Weil-equivariant realization.
- `AlgebraicGeometry.WeilComplex.exists_affineChart_localization`
  (`lem-pur-b3-weil-affine-localization`): canonical compact localization with the actual
  restriction arrow, retaining naturality through compactification comparisons.

This is a decomposition: one upper hole closed and two lower holes added, not a
sorry-free proof of the Thom theorem. Every remaining proof body is exactly `by sorry`.
No axiom, opaque declaration, hollow definition, or target-signature change is introduced.
All four delivered Lean modules compile separately, in import order, within 60 seconds.

## No longer needed

No existing module, declaration, public import or DAG node is withdrawn. No original
import is removed. The temporary base-Thom and relative-assembly restatements were
rejected during development and are absent from this delivery. They are not claimed
as pruning of repository modules.

The attached trivial-line Lean consequence does not need to import the earlier planned
zero-class realization/exchange modules, the origin-class comparison, or the geometric
stalk conservativity lemma: it uses proper projective cohomology and localization directly.
Those nodes are not declared globally unnecessary. The original node states a stronger,
finite-level zero-section-normalized vector-bundle result, so its previously reviewed
proof and dependencies are retained, with an appended step describing the exact native
Lean specialization. The unit's projective-line/integration route is preserved.

## Where the brief, the DAG or earlier work was wrong

The existing attachment `thm-pur-rank-one-thom` is not an exact statement match: its
natural-language statement concerns the normalized Cartier class for arbitrary rank-one
bundles at finite coefficients, whereas the assigned Lean theorem asserts an unnormalized
natural isomorphism for a trivial line with native rational Weil complexes. This delivery
does not claim the stronger statement has been formalized. It preserves that node's
statement and original mathematical proof, and records the actual Lean specialization
as an additional proof step. The new nodes state their exact native-category interfaces.

My first attempted split was a base-case Thom isomorphism followed by a purported
relative assembly theorem that restated the parent. The delivery gate flagged the
restatement. Identity-functor wrappers did not repair it; those were discarded. The
current split genuinely combines independent proper cohomology and localization
statements by an explicitly proved triangle argument. Neither old split module or node
is included. No historical base-case or relative-assembly result is being relied on.

The recorded build error was a missing buildtree source path, not a Lean proof error;
the current queue row assigns an ordinary proof with one hole. The current source was
restored unchanged before the proof work and successfully compiled.

## New nodes

`def-pur-b3-weil-projective-restriction` records the actual proper cohomology functor
and restriction map, both constructed without holes in `ProjectiveLineRestriction`.
Its section identity uses `ProjectiveLine.infinity_over` and the map is explicitly
built from the existing adjunction counit.

`lem-pur-b3-weil-projective-decomposition` records the proper projective-line matrix
calculation in `ProjectiveLineDecomposition`. Its two coordinates are trace and the
already constructed restriction; its remaining proof is proper projective bundle
cohomology with coefficient and equivariant comparisons, and has no affine term.

`lem-pur-b3-weil-affine-localization` records the compactification/localization step
in `AffineChartLocalization`. It contains no Tate twist, trace, or invertibility
assertion. Applying proper direct image to the canonical open-closed triangle and
tracking the adjunctions proves its conclusion.

No change record is needed: all new public declarations are in new Sheaf modules,
and the only existing Lean change is a theorem proof plus private helpers/imports.

## Related modules compiled before delivery

13 related module(s) compiled against this delivery by deliver3.py: 13 OK.

```json
{"capped": false, "direct": 13, "left_out": 0, "own": {"Sheaf.WeilSheaf.FourierInversion.AffineChartLocalization": "9a75e2cf00c7ed14b93b2b1cf2e40e6b617dc3b5", "Sheaf.WeilSheaf.FourierInversion.ProjectiveLineDecomposition": "e2a57d8f63526325bb8c2ffc3a098b84ab244a74", "Sheaf.WeilSheaf.FourierInversion.ProjectiveLineRestriction": "daafb49d21fd6afd75434fe98f639f5392c59fad", "WeilConjectures.WeilSheaf.FourierInversion.OtherSections": "bcb9969ed89ce98ebf8b98f4ea5f34828aaee34f"}, "results": {"Sheaf.Paper.CommonStageFourierWeightUpper": {"hash": "bd662a08309fe0d97e51aae8dea275ada1b348d3", "status": "OK"}, "Sheaf.Paper.FiniteEtaleLisseWeilImage": {"hash": "3d16cd84ea99969afd6ab655a80dbed697859d7d", "status": "OK"}, "Sheaf.Paper.ProjectiveBundleFormula": {"hash": "31fb9abfc6d0dec36871f0b2bedabecf9fd6a86a", "status": "OK"}, "Sheaf.Paper.SmoothProperPurityHypotheses": {"hash": "74ad1c9d234b141c3438fdf6df71badc6f746fa0", "status": "OK"}, "Sheaf.Paper.VectorBundleThom": {"hash": "24994216f1144863af07746169b823316d8a74bc", "status": "OK"}, "Sheaf.Paper.ZlWeilHeartLocalizationExact": {"hash": "29c54b823032f6001deace41c29951a5b8e8b6f7", "status": "OK"}, "WeilConjectures": {"hash": "a9f1970d653af90a208232c6a0658c40dd10bba9", "status": "OK"}, "WeilConjectures.WeilSheaf.AffineLineCohomology": {"hash": "c2fbfb1465eca69893f01309d2ed3797839bf2d4", "status": "OK"}, "WeilConjectures.WeilSheaf.FourierInversion.Composite": {"hash": "f7eb43564db4e51e4a450822d1c3b032a31c6cfd", "status": "OK"}, "WeilConjectures.WeilSheaf.FourierInversion.Delta": {"hash": "483e7106dc32d09478e6a219b1f8f3a52dd705dd", "status": "OK"}, "WeilConjectures.WeilSheaf.FourierInversion.KernelComposition": {"hash": "0da250595b762d74ca31ca15abc04a6a6e88c396", "status": "OK"}, "WeilConjectures.WeilSheaf.FourierInversion.Vanishing": {"hash": "7b78361fd3f164b3b3d3a805e5602617dff2f91f", "status": "OK"}, "WeilConjectures.WeilSheaf.LowerShriekPackage": {"hash": "a5799841af5f4f9cdb360de02a2d772e9cebde4d", "status": "OK"}}, "seconds": 249, "time": "2026-10-28T14:25:07+0800", "transitive": 0, "version": 1}
```

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
