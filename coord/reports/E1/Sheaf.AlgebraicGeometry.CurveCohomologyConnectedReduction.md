## What changed

Proved `AlgebraicGeometry.bijective_curve_cohomologyMap_of_connected` without changing its
signature. The proof obtains the finite connected-component coproduct, applies the existing
`AlgebraicGeometry.Etale.finiteCoproductCohomologyAssembly` on the source, and explicitly
transports each restriction cohomology group along the constant-sheaf isomorphism. It proves
the transport functions are equivalences using the cohomology identity and composition laws.
The remaining base-change square supplies target product coordinates. Componentwise
injectivity proves injectivity of the total comparison, and componentwise surjectivity,
choice of lifts and the source equivalence prove surjectivity.

Added `Sheaf.AlgebraicGeometry.SmoothCurveConnectedCoproduct`, with a complete proof from
Mathlib and closed upstream theorems. Added
`Sheaf.AlgebraicGeometry.FiniteCoproductConstantBaseChangeSquare`, isolating the target
assembly and its compatibility with canonical constant-sheaf restrictions. The latter is
independent of smoothness, connectedness and algebraic closure; it does not assert comparison
bijectivity and is strictly one part of the original argument.

Replaced the proof import of `Sheaf.AlgebraicGeometry.BaseChangeCurve` by the two new modules.
Retained the assembly import, now used explicitly. Public imports and all existing signatures
are unchanged. Updated the original node's proof, proof dependencies and proof origin, and
added nodes for both new declarations. No definition or statement was changed.

## Proved and sorry left

Proved:

- `AlgebraicGeometry.bijective_curve_cohomologyMap_of_connected`
  (`lem-sc-curve-cohomology-connected-reduction`), reduced to the existing assembly theorem
  and the new base-change square.
- `AlgebraicGeometry.exists_smoothCurveConnectedCoproduct`
  (`lem-sc-smooth-curve-connected-coproduct`). A local `#print axioms` reports exactly
  `propext`, `Classical.choice`, and `Quot.sound`; this geometric step is completely closed.

The item's module has no remaining `sorry`. The only `sorry` introduced by the delivery is:

- `AlgebraicGeometry.Etale.finiteCoproductConstantBaseChangeSquare`
  (`lem-sc-finite-coproduct-constant-base-change-square`). Its proof is exactly `by sorry`;
  the module docstring and node give the complete argument: base change of the coproduct,
  target finite-coproduct assembly, coefficient transport, pullback functoriality and
  constant-sheaf composition coherence.

The pre-existing `AlgebraicGeometry.Etale.finiteCoproductCohomologyAssembly` remains an
imported proof dependency, not an additional sorry introduced by this delivery.

Hole accounting: closed the original hole in
`AlgebraicGeometry.bijective_curve_cohomologyMap_of_connected`; added one hole in
`AlgebraicGeometry.Etale.finiteCoproductConstantBaseChangeSquare`. This is a decomposition,
with net zero holes closed by the replacement. The geometric helper is fully proved and
adds no hole. The original comparison theorem is not yet axiom-clean: its proof still
uses the imported assembly theorem and the split-off square.

Edge cases: the geometry proof uses `ConnectedComponents C` directly and assumes no
nonemptiness of C, so the empty scheme gives an empty family. The final argument uses
functions into products and works unchanged for the empty family. No step requires n
invertible or nonzero: n=0, n=1 and q=0 remain included. The square statement applies to
arbitrary finite scheme coproducts over arbitrary field extensions. Its singleton case is
ordinary cohomology pullback naturality through an isomorphism; its empty case is the
unique map between singleton products.

## No longer needed

Removed proof import: `Sheaf.AlgebraicGeometry.BaseChangeCurve`.

Pruned dependency: `lem-sc-base-change-curve` and its module
`Sheaf.AlgebraicGeometry.BaseChangeCurve` from this reduction's proof route. The comparison
hypothesis is applied to each original component over k; the argument never needs its base
change to be connected or even to be given an IsConnectedCurve instance. Base change of the
coproduct itself is retained in the new square theorem. This does not claim that other target
routes no longer use BaseChangeCurve.

The original direct proof dependency `def-sc-curves` is also absent from the item's new
`proof_deps`: its use in constructing the component curve instances moved into
`lem-sc-smooth-curve-connected-coproduct`, which retains it. Its public Curve import remains,
and the definition is still required by the unchanged signature; this is no module pruning.
No other original imports or original proof dependencies are pruned. The curve definitions,
cohomology pullback and finite-coproduct assembly remain necessary. All unit and chapter
statements and steps are preserved; the new proof follows the same finite-component
reduction before the connected-curve estimate.

## Where the brief, the DAG or earlier work was wrong

The original node's first step asked for integral components and connectedness of the
base-changed components. Neither assertion is needed for this reduction. Noetherian
connected components and the upstream smooth-dimension theorem suffice for the original
components. The original proof dependencies did not actually state the existence of that
finite component coproduct or the normalized coefficient-transport square.

The local clone contains only the literature indexes, not the blueprint or Stacks source
files. The supplied node and Lean docstring contain the first-step proof plan. I checked
Stacks Tags 0A5B and 01F7 online and used the available closed upstream Lean proofs for the
geometry. Tag 0A5B's first paragraph explains the finite-component reduction; it does not
state the full all-coefficient naturality square, which is supplied by the cohomology
functoriality and constant-sheaf coherence ingredients. LeanSearch was unavailable (HTTP
Internal Server Error); this is recorded as an unavailable search, with no mathematical
inference. LeanFinder, Loogle and Mathlib source searches were available.

WANTED: the local literature copy of blueprint sk-prop-ext-invariance, first step, for the
two new nodes; its plan was supplied in the original node and module.

## New nodes

`lem-sc-smooth-curve-connected-coproduct`:
`dag/nodes/sec-smooth-base-change/lem-sc-smooth-curve-connected-coproduct.json`, implemented
by the proved `AlgebraicGeometry.exists_smoothCurveConnectedCoproduct` in
`Sheaf.AlgebraicGeometry.SmoothCurveConnectedCoproduct`. It isolates and closes the geometric
component-decomposition step, valid over every field.

`lem-sc-finite-coproduct-constant-base-change-square`:
`dag/nodes/sec-smooth-base-change/lem-sc-finite-coproduct-constant-base-change-square.json`,
implemented by `AlgebraicGeometry.Etale.finiteCoproductConstantBaseChangeSquare` in
`Sheaf.AlgebraicGeometry.FiniteCoproductConstantBaseChangeSquare`. This is the sole split-off
sorry and isolates target assembly and naturality. Source assembly, coefficient-equivalence
bijectivity and the final comparison-bijection argument are proved in the item's module.

No change record is required: no existing statement, definition or public import changed.


## Second reading by E1

1. Compared the item module with the repository using `diff`, and checked the theorem
   signature byte for byte: identical. The only existing declaration has a changed proof
   and explanatory docstring; no definition, hypothesis, conclusion, or public import
   changed. The two helper modules and nodes are new. No change record is needed. PASS.
2. Compiled all three modules locally in import order with `lcompile.py`: no errors or
   warnings. Scanned all delivered Lean files: the sole `sorry` is exactly the reported
   named square theorem; no forbidden construct and no holed definition. Scratch
   `#print axioms` checks confirm the geometry theorem uses only `propext`,
   `Classical.choice`, `Quot.sound`; the reduction and square additionally use `sorryAx`,
   as reported. PASS as a decomposition, not a completed comparison proof.
3. Read both new statements and their docstrings and nodes. The component construction
   works over an arbitrary field and uses nonempty connected components, without assuming
   the whole scheme nonempty. The square holds for arbitrary finite scheme coproducts:
   pullback preserves their disjoint clopen cover; assembly on the target, coefficient
   transport, and cohomology naturality give precisely the displayed coordinates. It
   neither assumes nor concludes comparison bijectivity. Empty and singleton families,
   n=0, n=1 and q=0 require no extra hypothesis. Independently searched LeanFinder for
   cartesian-square restriction compatibility, Loogle for cohomologyMap/upperStarComp,
   and grep for pullback colimits and cohomology naturality, and searched lean/ with rg.
   No existing theorem states the square. Generic coproduct, cohomologyMap_map and
   functoriality ingredients are already used in its plan. This is a true, strictly
   smaller part of the original argument; closing it requires substantial categorical
   transport, not a short missing tactic. PASS.
4. Read the proof from the top downward. The geometric step uses closed upstream and
   Mathlib results; source assembly and the final product-bijection argument are explicit.
   Proof imports are private; public imports occur in signatures or were retained from
   the original interface. BaseChangeCurve is unnecessary; the original def-sc-curves
   direct dependency moved to the geometry helper and is now explicitly recorded above.
   Read dag/units/sk-thm-vanishing.json and sk-prop-ext-invariance.json: the finite-component
   route is retained, and no realized unit node or step is bypassed or removed. PASS.
5. Checked each node's verbatim Lean statement, proof steps, proof_deps and proof_origin
   against the three modules. Both new nodes include source, searches, created, blueprint,
   chapter, unit and lean records; their dependencies are the named ingredients used in
   the proofs or the remaining square's complete proof plan. PASS.

Second-reading changes: corrected the report's hole accounting to call the delivery a
net-zero decomposition, and completed the list of removed direct dependencies by naming
`def-sc-curves` and explaining its relocation. No Lean proof or statement repair was needed.
