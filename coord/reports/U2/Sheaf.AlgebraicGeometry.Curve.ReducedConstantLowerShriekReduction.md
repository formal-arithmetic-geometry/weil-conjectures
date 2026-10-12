## What changed

Replaced the sorry in `AlgebraicGeometry.IsCurve.exists_reducedConstantLowerShriekReductionData`
with a complete Lean reduction. The proof uses the existing reduced-curve normalization theorem,
constructs the standard pullback of the open immersion, proves surjectivity of the finite
modification from its closed range and dense isomorphism locus, and installs its curve structure.
It splits the constant-coefficient calculation on `(r : k) = 0`, using the existing
Artin–Schreier and Kummer assertion packages. The final localization assembly is stated as
one new theorem in `Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization`.

Added three proof-only imports: `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations`,
`Sheaf.AlgebraicGeometry.ReducedCurveNormalization`, and the new localization module.
Existing public imports and every existing declaration signature are unchanged.
Updated only the proof, proof dependencies and proof origin of the existence node.
Both modules compile cleanly together through the prescribed local compiler.

The new lemma is strictly the localization/finite-component step, rather than a renamed
existence theorem: it contains no normalization witnesses, finite modification, surjectivity,
dense isomorphism locus or cartesian-square conclusion. It assumes the constant calculations
on smooth curves; those calculations and the geometric construction are combined in the
item's actual Lean proof. The unit's Kummer/Artin–Schreier curve-calculation route remains
in `SmoothCalculations`, the module containing `thm-sc-main`'s existing declaration.

## Proved and sorry left

Closed the item's one remaining sorry:
`AlgebraicGeometry.IsCurve.exists_reducedConstantLowerShriekReductionData`
(node `k1-exists-reduced-constant-lower-shriek-reduction-data`).
The two previously proved declarations remain proved and unchanged in substance.
No sorry remains in the item's module.

One new sorry remains:
`AlgebraicGeometry.IsCurve.smoothConstantLowerShriekAssertions_of_constant`
(node `lem-pbc-u2-smooth-constant-lower-shriek-localization`).
Its source and full componentwise proof are in its docstring and node. It isolates the
arbitrary-open localization and finite component assembly, without redoing the constant
Kummer/Artin–Schreier computations or reduced normalization.
The existing imported normalization and characteristic-specific theorem sorries remain
upstream work; they are not new sorries introduced by this delivery.

Edge cases checked against the new statement: empty X or U gives the zero sheaf; U = X
is the constant calculation; a zero-dimensional component has either empty or full open
intersection; on a disconnected smooth curve the open may miss entire components, which
is why density on the whole curve was not added as a hypothesis. Each conditional assertion
retains its own affine, proper, characteristic and coefficient hypotheses.

## No longer needed

No existing import was removed: each remaining import supplies a signature or a declaration
actually used in this module. No dependency was introduced solely to increase the proof graph.

The existence proof no longer separately invokes
`lem-weil-pbc-zero-dimensional-cohomology` (`Sheaf.Paper.ZeroDimensionalCohomology`) or
`lem-weil-pbc-zero-dimensional-field-extension` (the dedicated declaration in
`WeilConjectures.AlgebraicGeometry.Curve.Reductions`). The existing smooth constant packages
already include dimension zero; on a zero-dimensional component localization is zero or
identity. The Reductions module still supplies the unchanged finite normalization transfer.

The existence node no longer has a separate proof dependency on `def-sc-constant-sheaves`
(`AlgebraicGeometry.Scheme.constantZMod`): the proof uses `Etale.constantModSheaf` throughout.
`thm-sc-main` is retained through its SmoothCalculations module and the two characteristic
assertion packages, not bypassed.

The former direct dense-open dependency `lem-weil-pbc-curve-assertions-dense-open`
(`Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions`) is replaced in the new localization plan
by `lem-pbc-q1-dense-open-prime-assertions`
(`Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions`), whose original finite-field module
encoding directly matches the coefficients. This does not assert global unreachability of
DenseOpenAssertions: its use elsewhere, including by the dense-open prime theorem, remains.

Noetherianity, finitely many components, smooth normality, finite pushforward and devissage
are moved into the new localization node's proof dependencies, rather than pruned. Their
modules were not imported into the item because their assembly is precisely the remaining
new theorem. No unit statement or unit proof step was removed.

## Where the brief, the DAG or earlier work was wrong

The normalization node's Lean conclusion does not explicitly include surjectivity, although
the reduction data needs it. This is not a mathematical error: finiteness makes the range
closed, and the dense isomorphism locus lies in the range. The delivery proves the missing
consequence directly, without changing the normalization statement.

The existing dense-open and finite-pushforward assertion packages have an abelian-sheaf /
ULift Z coefficient encoding, while this item uses ULift (ZMod r). The dense-open prime
module gives a matching localization interface. The new lemma's remaining finite-pushforward
assembly must respect the underlying abelian sheaves and their comparison maps; this is
explicit in its proof rather than assumed to be definitional equality.

Mathlib searches: LeanFinder returned eight unrelated constant-section results; Loogle's
closed-map/density query and the Mathlib grep found no assembly theorem. LeanSearch was
attempted and returned Internal Server Error, so no verdict relies on it. Local searches
found the normalization theorem and the two characteristic-specific calculations used here.
Blueprint/tag searches found no existing arbitrary-open smooth localization node.
The referenced Stacks 0A3Q and 03SG proofs were read on their official online pages because
this read-only clone contains only the literature lists, not the downloaded source text.

## New nodes

`lem-pbc-u2-smooth-constant-lower-shriek-localization`, in
`dag/nodes/sec-proper-base-change/lem-pbc-u2-smooth-constant-lower-shriek-localization.json`,
states and plans the finite-component localization step from Stacks 03SG. Its Lean module
contains one public theorem with proof exactly `by sorry`. Its proof separates empty and
nonempty component intersections, applies the supplied smooth constant calculations and
dense-open localization, and assembles by finite pushforward and devissage. The universal
constant-calculation hypothesis permits applying the existing calculations to each component,
including components with conditional hypotheses different from those of the whole curve.
No change record is needed because no existing statement or definition changed.

## Second reading by U2

1. PASS — Compared the full item with the repository by diff. The only Lean changes are
three plain proof imports and the body of the existence theorem. Every existing declaration
signature, definition, and docstring is byte-for-byte unchanged, including the landed
prime-coefficient isomorphism repair. No target or externally visible import changed.

2. PASS — Both delivered modules compile locally in import order with no diagnostics.
A scratch copy printed the axioms of the definition and all four delivered theorems:
only propext, Classical.choice and Quot.sound, together with sorryAx for the transfer,
existence and new localization theorems, as expected from their open dependencies.
There is exactly one delivery-local sorry, the named localization theorem, and no
forbidden declaration or hollow definition. The existence proof independently constructs
surjectivity from the finite closed range and dense isomorphism locus, supplies the actual
pullback square, and combines both characteristic branches with localization.

3. PASS after explanatory repair — Read the new statement, its source proof at
https://stacks.math.columbia.edu/tag/03SG and dense-open proof at
https://stacks.math.columbia.edu/tag/0GJA, and its dependency interfaces. Checked empty X,
empty U, U = X, dimension-zero components, and opens missing entire smooth components.
The hypothesis H is applied componentwise and is strictly the constant calculation;
the split theorem is localization only and does not restate normalization data existence.
New searches with disjoint-union/cohomology terminology (LeanFinder), constantSheaf/IsIso
(Loogle), and disjoint-sheaf/lowerShriek terminology (Mathlib grep), together with local
rg of the curve reduction and assertion modules, found no matching existing theorem.
The existing existential dense-open reductions do not apply to an arbitrary specified j.
Formal closure of localization needs component decomposition and cohomology comparisons,
so it is not a few-minute omitted tactic proof.

4. PASS — All three added imports are proof-only and each is used. The two public imports
supply the signatures. The old direct dependencies removed from the existence node are:
lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-finitely-many-components,
lem-sc-smooth-normal, lem-weil-pbc-zero-dimensional-cohomology,
lem-weil-pbc-zero-dimensional-field-extension, lem-weil-pbc-curve-assertions-dense-open,
lem-weil-pbc-curve-assertions-finite-pushforward, lemma-weil-pbc-eight-curve-devissage,
thm-sc-main, and def-sc-constant-sheaves. Noetherianity, components, normality, finite
pushforward and devissage are retained under the localization node; the dense-open
step uses the matching prime-module interface. The main smooth-calculation route remains
in the imported SmoothCalculations module through its characteristic packages. Read
sk-thm-p1.realized: no unit statement or step is removed or bypassed.

5. PASS — The existing node changes only proof, proof_deps and proof_origin. Both nodes'
proof dependency lists equal the unions of the step uses. The new node has the required
source, searches, created, blueprint, chapter, unit and Lean fields, and its recorded Lean
statement matches the source verbatim. The node and docstring record the same remaining
localization argument and coefficient comparisons.

Changed on second reading: repaired the new localization docstring and matching node proof
to distinguish the canonical underlying-abelian-sheaf comparison from an equivalence of
finite-field modules with abelian groups. Made preservation of affine/proper and primary/
invertible-torsion hypotheses during component assembly explicit. No Lean proof or signature
needed repair. Added the complete direct-dependency removal inventory above.
