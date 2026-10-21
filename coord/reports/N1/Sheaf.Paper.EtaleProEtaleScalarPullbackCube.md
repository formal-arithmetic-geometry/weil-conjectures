## What changed

Proved `AlgebraicGeometry.ProEtale.etaleProEtale_scalar_pullback_cube` by
adjunction coherence. Five proved private helpers establish the ordinary
restriction cube, its exact-derived and left-derived forms, compatibility of
mates with top whiskering, and the reverse scalar cube. Cancelling the inverse
scalar comparisons gives the stated forward cube.

The proof accesses the existing private etale normalization theorem through
`import all Sheaf.Paper.EtaleProEtaleScalarMate` and adds the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`. It preserves the
existing public imports, theorem signature and docstring. The node's `proof`,
`proof_deps` and `proof_origin` describe the new route. Obsolete direct tool
approvals are removed as listed below. No other module changes.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.ProEtale.etaleProEtale_scalar_pullback_cube`
(node `lem-sfb-etale-proetale-scalar-pullback-cube`). Holes added: none.
Split-off statements: none. The item contains zero remaining `sorry` tokens.
Its imported `scalarPullbackReverse_isIso` remains an existing proof dependency;
this delivery introduces no hole in that module.

The main theorem and all five private helpers compile without errors or
warnings through `lcompile.py` against the published project build. The
delivery command runs the required axiom probe and preflight before pushing.

## No longer needed

Removed six proof-only imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.RingedTopoiTensorComparisonData`
- `Sheaf.Paper.RingedTopoiTensorComparisonConstruction`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`

Removed from the item's direct proof dependencies:
`def-pur-sheaf-tensor-product`,
`def-weil-pbc-canonical-ringed-tensor-comparison`,
`def-weil-pbc-constant-sheaf`, `def-weil-pbc-site-comparison-morphism`,
`def-weil-presheaf-modules-sheafification`, `lem-pc-kflat-resolution`,
`lem-pur-derived-change-of-rings`, `lem-sfb-ringed-derived-monoidal-comparisons`,
`lem-weil-pbc-canonical-ringed-tensor-comparison-construction`, and
`lem-weil-pbc-ringed-topoi-derived-pullback`.

Removed obsolete direct tool approvals for `lem-pc-kflat-resolution`,
`lem-weil-pbc-ringed-topoi-derived-pullback`, and
`lem-weil-pbc-canonical-ringed-tensor-comparison-construction`.
The remaining approvals retain their original order. Statement dependencies
and public imports are preserved. Existing definitions and the imported
normalization theorem retain their dependencies; no module is globally pruned
or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The ordinary balanced-tensor argument has a shorter alternative using the
published conjugate and inverse-mate definitions. Conjugating the ordinary
restriction cube reduces it to sectionwise right-adjoint coherence. Exact
localization and mate pasting transport that equality to the required cube.
This uses no direct-image comparison isomorphism, geometric finiteness,
boundedness, or exactness of nonflat scalar extension. The scalar-six unit's
comparison route and the item's mathematical statement are preserved.

The retained attempt had not compiled the last three helpers and main theorem.
After publication recovered with the green build at 06:02:08 UTC on
2026-10-21, this session repaired the two-square composition notation,
explicit functor normalization, cancellation, and unused simp arguments.
The final cancellation uses the explicitly qualified categorical
`CategoryTheory.Functor.map_id`, avoiding the functional-functor theorem of
the same short name.
The earlier missing published dependency is resolved.

The first completed preflight identified the extra module-level notation scope
as an interface change. The final proof instead uses `TwoSquare.hComp`
explicitly and restores the original scope command, preserving the module's
existing interface without a definition or statement change.

The same check also treats module-level elaboration options as interface
commands. Both transparency options are now scoped to individual proof
declarations with `set_option ... in`. The project's source-only
`leanindex.interface_changes` check reports no interface differences from
the current item source.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
