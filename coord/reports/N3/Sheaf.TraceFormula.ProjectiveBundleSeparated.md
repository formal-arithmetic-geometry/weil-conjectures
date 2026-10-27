## What changed

Proved `AlgebraicGeometry.isSeparated_projectiveBundle` in
`Sheaf.TraceFormula.ProjectiveBundleSeparated`, with its signature unchanged.
Over the directed affine cover of the base, the source relative-Proj pullback
square identifies the canonical pullback with an ordinary Proj. Ordinary Proj is
separated, so its morphism to the affine open is separated. Transport along the
pullback isomorphism and apply Mathlib separatedness locality on the target.
This is precisely the argument of Stacks Tags 01OD and 01O2. It requires neither
finite type nor local freeness, and also applies to the zero module and empty
base. Added the private import `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper`.
Updated the existing node's proof and proof dependencies to follow this proof.
The unit statement and route remain unchanged. No statements or definitions changed.

## Proved and sorry left

Closed 1 of the original 1 holes:
`AlgebraicGeometry.isSeparated_projectiveBundle`
(node `lem-trf-projective-bundle-separated`). Added 0 holes; split off 0 statements.
The delivered Lean module contains 0 `sorry`. No other Lean modules changed.

Validation: the proof compiled using `lcompile.py`. The final delivery performs
its required compile and axiom checks again.

## No longer needed

Removed the redundant private imports:
- `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`;
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`;
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`.

The canonical graded algebra is already publicly available through the unchanged
`Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism` import. Its construction already
packages the grading and restriction base-change properties. Therefore this proof
needs no independent application of
`lem-weil-pbc-quasi-coherent-symmetric-algebra` or
`lem-weil-pbc-symmetric-algebra-graded`; removed these direct proof dependencies
and the obsolete top-level tool-use entry for the former. These modules remain
transitively imported by the canonical construction: no global module withdrawal
or elimination of their construction obligations is claimed.

The remaining relative-Proj, ordinary-Proj separatedness, cancellation and
locality dependencies are retained. Mathlib's separatedness locality instance
packages the diagonal and closed-immersion locality argument, so no new modules
are needed for explicit diagonal gluing. No modules withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The plan's separate symmetric-algebra comparison
and grading invocations were redundant after the canonical affine-basis algebra
was constructed. The existing relative-Proj charts and Mathlib's locality API
suffice to implement the source argument directly.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
