## What changed

Proved `AlgebraicGeometry.Scheme.proEtale_finiteLocalConstancy_pullback` with its
original signature. Restrict to constant scalars, use the existing `finiteLocal_iff`
helper to obtain finite constant models, pull their covering family back, compose
inverse images around each cartesian square, and transport the same finite models
back to the intrinsic coefficient encoding. `import all` makes the already proved
private equivalence available without copying its proof or changing its visibility.

Removed the unused private constant-module adjunction construction. Retained the
public coefficient-unit and coefficient-adjunct lemmas, which are used by
`Sheaf.Paper.ProEtaleConstantModulePullbackComposition`. Updated the item's proof
steps, proof dependencies and proof origin to match this shorter route. No existing
public signature, definition of a mathematical object, or target was changed.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.proEtale_finiteLocalConstancy_pullback`
(node `lem-pur-proetale-finite-local-constancy-pullback`). Added 0 holes; 0 sorries
remain in the delivered module. No new nodes or split-offs. The proof uses the
existing library declarations and their existing dependencies.

The final pruned proof compiled through `lcompile.py` in 3.4 seconds with no
warnings. All three public theorem signatures match the original file verbatim.
Axiom checks and delivery validation are recorded by `deliver3.py`.

## No longer needed

Removed direct proof imports:

- `Sheaf.Paper.ProEtaleConstantModulePullbackHomology`
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`

The route no longer directly uses
`lem-pur-proetale-constant-module-pullback-homology`,
`lem-pur-proetale-constant-coefficient-comparison`, or
`def-weil-pbc-proetale-operations`. Their declarations may still be transitive
requirements of the retained public imports and coefficient-encoding lemmas; this
delivery claims no whole-module removal from the global target closure.
`def-weil-proetale-locally-constant-sheaf` and
`def-weil-proetale-geometric-stalk` remain statement dependencies. Their direct
stalk and localized-inverse-image computations need no new proof obligation here:
the existing finite-model equivalence already provides exactly the needed facts.
`def-weil-proetale-inverse-image` remains a proof dependency for base change and
constant-sheaf pullback.

Removed unused private helpers `constantPresheafHomEquiv`, `constantModuleHomEquiv`,
`constantPF`, `constantPFAdj`, `ringUnit`, `constantMF`, `constantGlobal`,
`constantMFAdj`, `constAdj`, `globalDirectIso`, and `constantModulePullbackIso`.
No additional library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned localized module compatibility and general geometric-stalk pullback
comparison need not be constructed again. The existing coefficient-encoding module
already proves the equivalence with finite constant models, and its pullback
compatibility is proved in a separate existing module. Pulling back those models
proves both conclusions directly. The unit record has no realized statement or
proof steps for this auxiliary item; the unit route is preserved.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
