## What changed

Filled all three proof holes in
`lean/Sheaf/AlgebraicGeometry/ProEtaleHypercoverTotal.lean`.
`hypercoverSections_additive` is proved by extensionality on the cosimplicial degree
and the module element: every map is the original coefficient map evaluated at that
simplex, and both additions compute componentwise.
`alternatingCofaceMapComplex_additive` is proved by extensionality on the cochain
degree, where its morphism is definitionally the coefficient natural transformation.
`hypercoverSectionRows_additive` unfolds the composite and uses these two instances
and Mathlib's additivity instance for extension by zero.

All signatures, definitions, visibility, imports, instance attributes and existing
docstrings are unchanged. The proofs follow the existing docstring arguments; the
node has no proof dependencies to revise. No unit statement or route changes.

## Proved and sorry left

Closed the following three holes, all attached to
`def-weil-pbc-proetale-hypercover-total`:

- `AlgebraicGeometry.Scheme.ProEt.hypercoverSections_additive`.
- `AlgebraicGeometry.Scheme.ProEt.alternatingCofaceMapComplex_additive`.
- `AlgebraicGeometry.Scheme.ProEt.hypercoverSectionRows_additive`.

No `sorry` remains in the item and none is added elsewhere. This is a proof,
not a decomposition. Single-file compilation succeeded in 1.9 seconds.

## No longer needed

None. No proof-dependency modules are needed beyond the existing imports, which
supply the section, alternating-complex, extension, total-complex and preadditive
constructions used by the unchanged definitions and signatures. No imports were
added or removed, and no DAG nodes were bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. These holes are elementary componentwise additivity
checks, so the short route closes all of them without splitting. Lean Finder,
Loogle and grep searches were run; reading Mathlib confirms that extension by zero
already has an additivity instance, whereas the coface functor's instance is proved
here by its degreewise formula. The supplied blueprint unit source file is absent
from this checkout; its statement, steps and realized nodes were read from
`dag/units/sk-thm-properbasechange.json` instead.

## Second reading by C4

1. **Interface: pass.** Compared the delivered module with the repository version using
`diff -u`. Existing declarations, signatures, definitions, imports, visibility, and
docstrings are unchanged; only the three proof bodies differ.

2. **Proof and trust: pass.** Compiled the module with `lcompile.py` successfully. The
source contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
The three proofs are direct extensionality and instance arguments, with no new data
definitions or arbitrary witnesses. A scratch `#print axioms` check is consistent with
the allowed foundation (and inherited `sorryAx` only from imported open obligations).

3. **Split statements: pass, none.** No statements were added or split off. All three
original holes are closed directly, so no new DAG node or change record is required.

4. **Route and pruning: pass.** Read the item node and the proper-base-change unit,
including its `realized` route. The proofs use the existing section, alternating-face,
extension, and preadditive constructions; no unit step is bypassed and no import or
proof dependency is unused.

5. **DAG: pass.** The item node's statement and Lean declarations are unchanged. Its
proof dependency list remains accurate because the implementation uses only existing
definitions and instances. No new node is needed.

Second-reading changes: added this review section; no Lean or DAG repair was needed.
