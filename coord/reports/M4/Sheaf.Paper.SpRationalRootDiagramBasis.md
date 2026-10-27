## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.spRationalRootDiagramBasis` by an
argument retaining normalized finite-level component formulas throughout the inverse
limit construction. The private `normalizedTower` helper uses the existing
`spRootBasisLevel` declaration and proves all successor squares. Section evaluation
preserves both limit cones; the limit-point isomorphism gives an integral basis with
its projection formulas. Tensor-sheaf extensionality lifts its sectionwise linearity
to the actual internal module on the slice.

For every field inclusion, the proof checks integral naturality on the actual finite
limit projections, using the specified quotient-map square. Rational naturality then
follows from the actual extension-unit normalization of the rational transition and
`Mod.regular_hom_ext`. The proved private `basisNaturality` helper performs that
calculation over abstract module objects, avoiding expansion of the concrete
coefficient definitions. The component action equation is `Mod.act_hom`.

Added `Sheaf.Paper.SpSliceNormalizedScalarExtensionBasis`, stating the remaining
ordinary scalar-extension step for arbitrary commutative internal rings, a module,
and a prescribed slice basis. It retains the extension-unit equation. This statement
has no roots, inverse limits, or field-transition diagram. The item privately imports
this module and `Sheaf.Paper.SpRootBasisLevel`. Updated its DAG proof to this argument.
No existing statement, definition, or public import changes.

Validation: both sandbox modules compile with `lcompile.py`; the full item compiled
in 42.9 seconds with diagnostic profiling enabled. The scalar-extension statement
compiled in 56.3 seconds. Diagnostic options were removed for delivery. The final
required delivery compile validates that version. A separate signature comparison
confirmed that the item's theorem signature is byte-for-byte unchanged. All node
dependencies exist and all Lean lines are at most 100 characters.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.spRationalRootDiagramBasis`
(node `lem-sp-rational-root-diagram-basis`).

Added one hole:
`AlgebraicGeometry.ProEtale.spSliceNormalizedScalarExtensionBasis`
(node `lem-sp-slice-normalized-scalar-extension-basis`). Its proof is exactly `by sorry`.
The new statement is the prescribed-basis scalar-extension step, strictly below the
original theorem. This is a decomposition: one upper hole closed, one lower hole
added, net zero new hole closures. All finite-tower assembly, integral limit and
field naturality, and rational naturality arguments in the item are proved Lean.

The item also uses the already stated `spRootBasisLevel` (currently with `sorry`);
this delivery adds no hole to that declaration. There are no holes in definitions.

## No longer needed

No pre-existing import was removed. The original public import is unchanged.

The item's old direct dependency `lem-sp-root-basis-tower-comparison`
(`Sheaf.Paper.SpRootBasisTowerComparison`) is replaced by direct use of
`lem-sp-root-basis-level`: its unnormalized `Nonempty` conclusion discards the
component equations needed for comparison across fields. The proof reconstructs
its successor-square argument while retaining those equations.

The old direct dependency `lem-sp-slice-scalar-extension-basis`
(`Sheaf.Paper.SpSliceScalarExtensionBasis`) is replaced by the normalized
scalar-extension step. Its existential basis does not specify the extension unit.
Neither old module is withdrawn; other consumers can still use both.
The coefficient-limit theorem and the original Tate twist definitions remain needed.

## Where the brief, the DAG or earlier work was wrong

The original plan requires compatibility of chosen bases across coefficient fields.
The listed tower and scalar-extension statements establish only separate existential
bases and omit their normalizations. Applying them and choosing witnesses would not
prove naturality. The proof now retains finite-level normalization explicitly and
isolates the missing scalar-extension unit equation.

The new statement was checked on zero rings, the empty slice, identity scalar maps,
and an already regular module: the balanced tensor formulas and unit equation are
valid in all these cases. No nonempty-slice or nonzero-ring assumption was added.

## New nodes

`lem-sp-slice-normalized-scalar-extension-basis`:
`dag/nodes/sec-six-functors-basics/lem-sp-slice-normalized-scalar-extension-basis.json`,
realized by `Sheaf.Paper.SpSliceNormalizedScalarExtensionBasis`. This is the ordinary
normalized scalar-extension step of clause (3) of the Tate twist local-freeness proof.
Its proof plan uses the existing normalized internal/section adjunction and slice
sheafification comparisons. No change record is needed: no existing interface changes.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
