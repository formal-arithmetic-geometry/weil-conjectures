## What changed

Proved `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator.exists_tensorPullback_affine`
in `Sheaf.AlgebraicGeometry.Modules.PullbackLocalCoefficient`, preserving its statement
and every import. The proof applies the existing `IsFreeGenerator.exists_pullback`,
restricts the resulting generators and coefficient equation to `V`, and transports
both generators along the natural isomorphism from Mathlib pullback to tensor pullback
obtained by uniqueness of left adjoints of `pushforward g`. Naturality transports the
coefficient equation. A proved private helper, `isFreeGenerator_iso`, proves preservation
of free generators under a module isomorphism by composing sectionwise bijections.

Server single-file compilation passed in 5.2 seconds with no warnings. The existing
proof-dependency import is acyclic. The argument works on an empty open as well, since
restriction and the sectionwise bijections apply to every open, without a nonemptiness
hypothesis. No definition, public signature, or unit route changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.IsFreeGenerator.exists_tensorPullback_affine`
(node `lem-pc-zero-scheme-pullback-local-coefficient`).

Zero holes remain in the item. Zero holes added; zero statements split off.
The private helper `isFreeGenerator_iso` is also fully proved.

## No longer needed

None. No imports removed. The sole planned proof dependency,
`lem-pc-zero-scheme-pullback-full-local-coefficient`, remains used through
`WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`. All existing statement imports
remain necessary for the public interface. No modules or nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The DAG's elementary restriction step compresses
the transport between Mathlib pullback and tensor pullback; the existing theorem
docstring already specifies this comparison, and the proof now implements it using
`nonempty_tensorPullbackAdjunction` and `Adjunction.leftAdjointUniq`.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
