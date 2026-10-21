## What changed

Proved `CategoryTheory.RingedToposMorphism.existsUnique_derivedConstantTowerComparison`
in `Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization` with its original
signature, docstring, public definitions and public imports unchanged.

Private, fully proved helpers implement the six existing DAG steps. The resolving-class
construction gives invertible counits for a computed pair; pointwise Kan restriction along
the full homotopy quotient and uniqueness of left-derived pairs transfer this to the given
pairs. The ratio of the transported counits is natural on resolving representatives.
`exists_natTrans_from_resolvingClass` extends it on the homotopy category; resolutions make
all its components invertible. Localization lifts the isomorphism. Cancelling the tower
counit proves the inverse formula, and resolution naturality plus localization faithfulness
proves uniqueness.

The diagram replacement and pullback invariance declarations supply both resolving classes.
For ordinary complexes use a one-object discrete diagram. For towers use
`AsSmall.{u} ℕᵒᵖ`, apply the existing same-universe diagram theorem, and restrict back to
`ℕᵒᵖ`. Thus arbitrary coefficient and derived-localization universes remain supported.

Added only proof imports of `Mathlib.Algebra.Homology.Functor`,
`Mathlib.CategoryTheory.Limits.Final` and `Mathlib.CategoryTheory.Category.ULift`.
The local priority of the existing limit-preservation sheaf-composition instance avoids
expensive multicospan expansion. Change record:
`coord/changes/T8-constant-tower-normalization-proof-context.md`.

## Proved and sorry left

Closed 1 original hole:
`CategoryTheory.RingedToposMorphism.existsUnique_derivedConstantTowerComparison`
(blueprint: `lem-cbc-derived-constant-tower-normalization`).

Added 0 holes. Remaining holes in the delivered module: none. Split off: none.
All new private theorems and all private constructions are completely proved.
This is a proof from the declared dependencies, not a decomposition.

## No longer needed

None. Every declared proof dependency remains used. No public import, node, module,
upstream declaration or parent dependency is removed. All three added proof imports
support explicit parts of the proof.

Validation: the complete delivered module compiled through `lcompile.py` with exit code 0
in 18 seconds. The source contains no `sorry`; its original theorem signature was checked
against the shared source and is textually unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The plan requires a universe lift when applying
the existing diagram theorem, whose diagram and site universes coincide, to countable
towers at an arbitrary coefficient universe. This is implemented by `AsSmall` and changes
no mathematical object. The DAG proof copy records this implementation detail.

The concrete sheaf-category signature was expensive under the default multicospan
instance route. A local priority for the existing proof from preservation of limits fixes
this without changing any definition or public signature, raising a timeout, or splitting
the module. The abstract counit and comparison helpers keep concrete localization data
out of the cancellation proofs.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
