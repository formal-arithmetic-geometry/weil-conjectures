## What changed

Proved `AlgebraicGeometry.flat_finite_type_dense_presentation` in
`Sheaf.TraceFormula.FlatFiniteTypeDensePresentation`, with its statement and public imports
unchanged. All auxiliary declarations are private and proved.

The proof implements Stacks Tag 081N: reduce to affine sections, choose finitely many relations
that agree at the chosen prime and on a finite principal cover, apply the stated Tag 05I7
stalk criterion and the existing openness-of-flatness theorem, and use flatness with schematic
density to identify the approximation on a neighborhood. Finite presentation then glues.
The density argument tensors the injective map given by finitely many powers of the cover
elements; this also handles an empty cover and zero rings.

Added proof imports for finite-presentation locality, tensor products with finite products,
affine finite-type sections, finite-presentation descent, and flatness after module localization.
The node now records the affine section criteria and the precise finite-power argument.
No source-library file or definition was changed.

Preflight requested a change record for the added file-local namespace opens and scoped
elaboration option. It is at
`coord/changes/flat-finite-type-dense-presentation-proof-scopes.md`; no consumer needs adaptation.

Repair of the return at head `120b248f2`: removed the unnecessary file-level warning option
`set_option warn.sorry false`. The landing hole scanner interpreted its option name as an
unattributed hole at line 31. No proof placeholder was present at that location; removing
the warning suppression leaves every declaration and proof unchanged.

Validation: the repaired file compiled through `lcompile.py` with exit code 0 in 23.6 seconds.
The landing hole scanner reports zero holed declarations and zero warnings; every Lean line
is within 100 columns. The delivery tools repeat the required preflight checks.
The import-direction checks passed for all three added source-library imports.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.flat_finite_type_dense_presentation`
(node `lem-trf-flat-finite-type-dense-presentation`).

There are zero remaining holes in the item, zero holes added, and zero split-off statements.
The proof uses the already stated
`Module.finitePresentation_localizedModule_atPrime_of_flat`
(node `lem-trf-flat-finite-type-flat-point-local`); its existing proof obligation is unchanged.

## No longer needed

None. No imports, nodes, modules, or planned proof dependencies were removed. The proof retains
the finite-relation approximation, stalk criterion, openness of flatness, density argument,
and local gluing of the original plan.

## Where the brief, the DAG or earlier work was wrong

The returned delivery was rejected because the landing scanner counted the warning option
name as an unattributed proof hole. This repair removes that unnecessary option.
No mathematical statement needed correction. The DAG now describes the equivalent finite-power
form of the density injection used in Lean and explicitly records the existing affine section
criteria. The unit route and every public signature are preserved.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
