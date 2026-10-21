## What changed

Completed `SheafOfModules.ringedDerivedPullback_linear` in
`Sheaf.CategoryTheory.RingedDerivedPullbackLinear`, retaining its statement,
universes, hypotheses, and the existing `scalarSectionLinear` construction.

The ordinary pullback preserves scalar identities by the `AlgebraicInverseImage.moduleSMul`
graph equation, naturality of its underlying-sheaf isomorphism, the compatibility `hs`,
and tensor balancing. The sheafification adjunction and extension-of-scalars Hom
extensionality make the sectionwise calculation sufficient for equality of sheaf maps.
The source places read were Stacks `sites-modules.tex`, Tag 03D6
(`definition-pushforward`), `sites-cohomology.tex`, Tag 06YY
(`lemma-derived-base-change`), and `conventions.tex`, `section-algebra`.

For the derived step, compare the natural endomorphisms `LF.map (r • id)` and `r • id`.
Mathlib `Functor.leftDerived_ext` reduces their equality to naturality of `epsilon`;
linearity of ordinary pullback and of `DerivedCategory.Qh` proves the resulting equation.
This avoids the original resolution-by-resolution scalar argument. The existing
`ringedTopoiDerivedPullback` theorem supplies an exact realization, whose additivity
transports to the supplied realization by `Functor.leftDerivedUnique`.

Added the proof-only import `Mathlib.CategoryTheory.Triangulated.Functor` for the
triangulated-functor additivity instance.

The node proof, proof dependencies, proof origin, and obsolete K-flat-resolution
`tool_uses` entry were updated to match. No other module or definition was changed.
The unit's derived-pullback operation and route are preserved.

Validation: the complete proof compiled on the server through `lcompile.py` in
23.9 seconds, with zero holes. The sole linter warning requested an explanatory
comment for the theorem-local heartbeat budget; that comment has been added.
The wall-clock compile limit remains 60 seconds.

## Proved and sorry left

Closed the single original hole in `SheafOfModules.ringedDerivedPullback_linear`.
Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No intermediate statement was split off. `scalarSectionLinear` remains the original
proved construction. Existing dependencies are used through their declared theorems.

## No longer needed

Removed the proof-only imports
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
The corresponding direct proof dependency `lem-pc-kflat-resolution` and its approved
`tool_uses` entry are removed: the left-derived universal property establishes scalar
preservation at all objects without choosing resolutions. The cochain tensor monoidal
structure is also unnecessary for this proof; change of rings uses only the existing
sectionwise tensor construction from `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.
The tensor-product definition node `def-pur-sheaf-tensor-product` remains a dependency
because this construction is essential to the ordinary scalar calculation.

No module is withdrawn. These are removed direct dependencies of this proof; the
existing derived-pullback theorem retains its own K-flat construction and dependencies.
All existing public imports are retained for the statement's exposed interfaces.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The original plan's steps 3 and 4
are longer than necessary: uniqueness of natural transformations into the left derived
functor replaces the K-flat cancellation and extension across resolutions. The exact
K-flat derived-pullback theorem is still used, for additivity, and no flatness hypothesis
on `c` has been introduced. The calculation works for zero scalars and zero modules,
and neither uses nonzero sections nor assumes that every sheafified tensor section is
a pure tensor: the sheafification adjunction and the tensor Hom extensionality theorem
are precisely what justify the generator calculation.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
