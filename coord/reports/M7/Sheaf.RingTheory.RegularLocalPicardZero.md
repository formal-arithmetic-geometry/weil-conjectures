## What changed

Proved `RingTheory.regularLocalPicardZero` without changing its signature. A proved private
helper checks invertibility using the dual evaluation map, localization of Hom for finite
presentations, and locality of bijectivity at maximal ideals. After finite-module descent,
the already-proved source theorems give finite projective dimension and stable freeness of
the projective localization. Mathlib's `Module.free_of_isStablyFree_of_invertible` and
`Module.Invertible.free_iff_linearEquiv` give the required equivalence.

Updated the item node to match this finite-resolution/determinant route. Added three nodes
attaching existing proved declarations, with no new Lean modules or statements. All proof
imports are private. No public interface or source-library file changes. Single-file remote
compilation succeeded in 5.6 seconds; the final delivery check verifies the cleaned version
and its axiom probe.

## Proved and sorry left

Closed 1 of 1 holes: `RingTheory.regularLocalPicardZero`
(`lem-trf-regular-local-pic-zero`). Added 0 holes and split off 0 unfinished statements.
The item's module has zero `sorry`s. The private helper
`RingTheory.invertible_of_prime_localizations` is fully proved.

The existing dependency `Module.exists_finite_localizationAway_model`
(`lem-trf-localized-finite-module-spread`) remains an imported theorem with `sorry` in its
own unchanged module; it is neither added nor restated here. The three new DAG attachments
refer to already-proved declarations. The result therefore still depends on the existing
descent hole, as intended for this stage.

## No longer needed

Removed the private proof imports:

- `WeilConjectures.RingTheory.RegularLocalFiniteModuleResolution`
  (`lem-weil-pbc-regular-local-finite-module-resolution`): only existence of finite
  projective dimension is needed, provided directly by the proved source theorem.
- `WeilConjectures.RingTheory.BoundedFiniteFreeResolution`
  (`stage3-b4-bounded-finite-free-resolution`): the source localization theorem already
  implements localization and splitting, so no explicit bounded resolution is assembled.
- `Sheaf.AlgebraicGeometry.IsRegularScheme` (`def-weil-regular-scheme`, scheme portion):
  the retained public Mathlib import supplies the regular-local ring predicate directly.
- `Sheaf.RingTheory.K0ClassTrivialInvertible`
  (`lem-trf-k0-class-trivial-invertible`): Mathlib's proved stable rank-one cancellation
  performs the determinant argument without introducing a K0 group.
- `Sheaf.TraceFormula.InvertibleModuleK0Class`
  (`lem-trf-invertible-module-k0-class`): stable freeness replaces the K0 computation.

The first two source-library modules may remain needed elsewhere; no declaration is removed.
The K0 group/determinant dependency branch is unnecessary for this proof. Its queue impact
is subject to other consumers. No unit statement or unit step is bypassed: the unit record
`sk-i-curve-zero` does not assign this auxiliary node a separate mandated K0 proof step.
A temporarily added explicit `Mathlib.Algebra.Module.FinitePresentation` proof import was
removed because the required API is already publicly imported by the source dependency.

## Where the brief, the DAG or earlier work was wrong

The original five-step plan is mathematically valid, but predates the adopted source's
proved stable-freeness API. The explicit K0 interface is unnecessary. The replacement
uses the same descent, finite-resolution, localization and determinant argument below the
unit level. Neither the theorem statement nor any definition was repaired or weakened.

Edge cases were checked against the proof: f=0 gives the zero localization and is supported
by the Mathlib cancellation theorem's subsingleton case; f a unit needs no special case;
regular local dimension zero is covered by the finite-projective-dimension source theorem.
The local-invertibility helper works also over the zero ring, using locality of bijectivity
with its empty family of maximal ideals. No nontriviality assumption is added.

Searches used LeanFinder, Loogle, LeanSearch and the Mathlib/source grep, recorded by
msearch.py. Blueprint searches for stable freeness and finite projective dimension found
no duplicate of the three exact attached declarations. Both new source imports passed
`import_direction.py may`. The compile server twice returned no answer; retrying produced
normal compiler diagnostics and a successful compile, without changing any tool.
Preflight caught a file-level `open TensorProduct`; this was confined to the private helper
with `open TensorProduct in`. The interface checker now reports no changes, and the revised
file compiles without warnings in 5.6 seconds.

## New nodes

`lem-trf-regular-local-finite-projective-dimension` attaches the existing proved
`IsRegularLocalRing.exists_hasProjectiveDimensionLE`. It is the finite-projective-dimension
conclusion needed after descent, with the source theorem's universe requirement recorded.

`lem-trf-projective-localization-stably-free` attaches the existing proved
`Module.isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE`. It supplies the
localized splitting argument, with its Noetherian/local, finiteness, dimension-bound,
projectivity and universe hypotheses explicitly recorded.

`lem-trf-stably-free-invertible-free` attaches the Mathlib leaf
`Module.free_of_isStablyFree_of_invertible`. Its determinant/cofactor proof cancels a finite
free stabilizing summand of an invertible module. All three nodes record source locations,
proofs in words and actual searches; none introduces a new hole or a duplicate Lean
statement. There are no change records because no interface changes.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
