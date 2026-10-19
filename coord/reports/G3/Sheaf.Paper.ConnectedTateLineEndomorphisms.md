## What changed

Proved `AlgebraicGeometry.Scheme.connected_tate_line_endomorphisms` in
`Sheaf.Paper.ConnectedTateLineEndomorphisms`, with its original signature and definition
`shiftedFiniteEtaleTateLine` unchanged. Six proved private helpers calculate scalar endomorphisms of the rank-one module,
transport that calculation through linear fully faithful functors and isomorphisms,
specialize it to constant sheaves and complexes, and reflect invertibility.

The named signed multiplication projection of `Scheme.finiteEtaleTwistPullbackData`
(the structured API of `Scheme.etaleFiniteTwistPullback`) provides the
Tate line's tensor inverse. Tensoring with this line is fully faithful and linear,
so the coefficient sheaf's scalar bijection transfers to the line. The degree-zero
embedding and shift transfer it to the required derived object. Linearity then makes
`G.map` bijective on this endomorphism set; lift the inverse and use injectivity to
prove its two inverse equations.

Added proof-only imports of
`WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions`,
`WeilConjectures.CategoryTheory.Monoidal.TensorInverse`, and
`WeilConjectures.SixFunctors.Etale.Derived.Invertible`.
The existing public imports retain the module's public interface. Updated the existing
node's proof and proof origin to describe the implemented argument. Attached a new
DAG node to the existing proved constant-module full-faithfulness
declaration. No other Lean modules or public declarations changed. The theorem-local
irreducibility attribute avoids expanding the constructed Tate line during
proof elaboration; its scope and all downstream users are documented in
`coord/changes/connected-tate-line-proof-scope.md`. Development profiling and
heartbeat options from the interrupted attempt were removed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.connected_tate_line_endomorphisms`
(node `lem-coef-connected-tate-line-endomorphisms`).
No `sorry` remains in this module; no holes or Lean modules were added or split off.
One DAG node attaches a proved existing declaration and introduces no proof obligation.
The proof uses the existing declared `Scheme.etaleFiniteTwistPullback`; closing its
remaining dependency proofs is separate work. This delivery does not claim that all
transitive dependencies are already sorry-free.

Validation uses `lcompile.py` and the required delivery preflight, including its axiom audit. The argument does not assume
that B is nonzero, finite, or a field, and includes N=1, r=0, and arbitrary shifts.

## No longer needed

Removed the proof-only import
`WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections`, using the proved
module-valued constant-sheaf full-faithfulness API in `ModulePointFunctions` instead.
The connected-constant-sections node remains a mathematical dependency; its
module-valued version is already proved in the source library.

The original local-basis overlap and gluing calculation is unnecessary: signed Tate
multiplication gives an inverse, and tensor equivalence transfers endomorphisms from
the unit. The scalar-unit extraction and multiplication by an inverse scalar are
also unnecessary: lift the actual inverse under `G.map`. No existing DAG dependency
node or public export is withdrawn. No whole module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan omitted a shorter route available from
its declared dependencies: the signed multiplication maps supply a tensor inverse,
so there is no need to formalize the local-basis gluing. The source library also
already proves full faithfulness of constant module sheaves on connected schemes
(`Scheme.fullyFaithfulModuleConstantSheaf`). The node now records these tools and
the actual inverse-lifting argument. The unit's statement and route are preserved.

## New nodes

`lem-coef-connected-module-constant-sheaf-fully-faithful` records the existing proved
`AlgebraicGeometry.Scheme.fullyFaithfulModuleConstantSheaf` in
`WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions`. It supplies the exact
module-valued full-faithfulness API used in step 1, with no new Lean file or hole.
Its proof is the connected constant-section calculation followed by the adjunction
criterion for a fully faithful left adjoint. The theorem-scoped irreducibility command is recorded in
`coord/changes/connected-tate-line-proof-scope.md`; all public signatures,
definitions and imports are unchanged.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
