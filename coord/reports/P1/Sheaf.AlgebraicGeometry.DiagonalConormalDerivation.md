## What changed
Added `Sheaf.AlgebraicGeometry.DiagonalConormalMorphism`, splitting the construction of the normalized difference into an O_X-module morphism with the sectionwise formula. The original theorem now obtains its derivation by composing this morphism with the universal relative derivation and is fully proved.

## Proved and sorry left
`exists_diagonalConormalDerivation` is proved. `exists_diagonalConormalMorphism` remains as a named lower-level construction theorem, with source and proof recorded in its node.

## No longer needed

The proof does not use the former proof-only imports
`Sheaf.AlgebraicGeometry.AffineConormalSections` or
`Sheaf.AlgebraicGeometry.BaseChangeConventions` in
`DiagonalConormalDerivation`; the latter was also unused in the new
`DiagonalConormalMorphism` module. They were removed after compiling the files
without them.

## Where the brief, the DAG or earlier work was wrong
The original node's geometric construction was not directly represented by available Lean declarations. It was split into the lower-level morphism existence node.

## New nodes
`lem-sc-diagonal-conormal-morphism-exists`: `lean/Sheaf/AlgebraicGeometry/DiagonalConormalMorphism.lean`.

## Second reading by P1

1. I compared `DiagonalConormalDerivation.lean` with the repository version. The
   declarations `IsDiagonalConormalDerivation` and
   `exists_diagonalConormalDerivation` have unchanged signatures; only the proof
   and its proof-only import were changed. Verdict: pass.
2. I compiled both delivered modules with `lcompile.py --all`. The derivation
   theorem is proved without `sorry`; the only remaining `sorry` is the named
   `exists_diagonalConormalMorphism` theorem, whose source, proof description,
   and node are present. No definitions contain `sorry`, and no forbidden
   declarations were introduced. Verdict: pass subject to the documented split.
3. The new morphism statement is true and is strictly lower-level: it constructs
   the O_X-module morphism and its sectionwise normalization, while the original
   target only asks for the resulting derivation. It is not a duplicate theorem;
   the target proof composes it with the universal relative derivation. The
   statement and its node agree verbatim. Verdict: pass.
4. The proof uses the shortest available route in the delivered library: obtain
   the normalized morphism, postcompose the universal relative derivation, and
   apply its normalization. No imports were removable without changing
   elaboration; the unit route remains represented by the original target node
   and the new construction node. Verdict: pass.
5. The DAG node for `exists_diagonalConormalMorphism` records its Lean module,
   declaration, source, proof route, dependencies, and split status. Its proof
   dependency list matches the construction route, and the target node's proof
   now uses the new declaration. Verdict: pass.

Changed: added the proof-only import of `DiagonalConormalMorphism`, proved
`exists_diagonalConormalDerivation` by composition, and added the named lower-level
construction theorem and matching DAG node. No existing statement or definition was
changed.
