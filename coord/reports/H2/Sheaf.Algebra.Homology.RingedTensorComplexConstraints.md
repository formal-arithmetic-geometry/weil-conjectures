## What changed

Proved `CategoryTheory.RingedDerivedNative.complexConstraints` in the assigned module,
following the four-step DAG proof and reusing the existing proved module generator API. The sheafification-unit pairing equals the
lax tensorator of the right adjoint to sheafification. Its naturality, associativity,
braidedness, and unit identities give the ordinary sheaf pure-section formulas.
The adopted source's Koszul braiding and triple-summand associator formulas then give
these formulas for complexes. For both unitors, the inverse component formula and
inverse identities identify the surviving degree-zero summand with the ordinary
module unitor, hence scalar multiplication.

All auxiliary declarations are private and contain no holes. The lax-monoidal
helper is registered only as a section-local instance. The added proof import is
`Sheaf.SecSmoothPurity.ModuleTensorGenerators`, for the existing moduleTmul
naturality, braiding and associator formulas. The item node records that dependency. No public statement, definition, or import changes.

The proof-scope change record is
`coord/changes/H2-ringed-tensor-complex-constraints-proof-scope.md`. It records
the scoped elaboration commands and local instance, with unchanged consumers.

Searches used leanfinder for complex tensor constraint summands, loogle for braiding
and monoidal formulas, msearch grep, and local source searches. The useful existing
lemmas are `CategoryTheory.CochainPullback.moduleTmul_map`,
`moduleTmul_braiding`, `moduleTmul_associator`,
`CochainComplex.Monoidal.ι_braiding_hom`,
`CochainComplex.Monoidal.ι₁₂_associator_hom`, the two triple-summand decompositions,
and `HomologicalComplex.leftUnitor'_inv` / `rightUnitor'_inv`.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.RingedDerivedNative.complexConstraints`
(node `lem-sf-ringed-tensor-complex-constraints`). Added zero holes; zero holes remain
in the delivered module. No statements were split off.

## No longer needed

None. The existing public import and the DAG dependency
`def-pur-sheaf-tensor-product` remain needed. The existing route is retained, with the proved generator calculus reused as a
generic tool. No node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The generator-calculus node from the
smooth-purity unit is used only as a generic proved tool; it does not replace any
step of the Verdier-biduality unit route. That unit has no realized statement or
step attached to this helper node. The formulas require neither K-flatness nor
bounds, and the proof imposes neither. All degrees are arbitrary integers and the
proof works for zero rings and empty sites as well. The specified degree-zero
single-complex comparison is preserved exactly.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
