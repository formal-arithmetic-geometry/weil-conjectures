## What changed

Proved `AlgebraicGeometry.IsHProjective.comp` in the assigned module, keeping its
signature unchanged. The proof follows Stacks Tag 01WE and the existing DAG plan:
choose the two finite projective embeddings; base-change the second closed
immersion; identify the iterated projective space with the pullback using
`ProjectiveSpace.isPullback_map`; compose with the binary Segre closed immersion.
The projection identities verify the required factorization over the original base.
No definitions, public imports, or other modules changed.

## Proved and sorry left

Closed the one existing hole: `AlgebraicGeometry.IsHProjective.comp`
(node `lem-trf-h-projective-composition`). Zero holes remain in the item; zero
holes added; zero statements split off. All supporting declarations already exist.

## No longer needed

Removed proof imports:
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product`: the binary Segre
  embedding suffices; the finite-product embedding theorem
  `ProjectiveSpace.exists_isClosedImmersion_pi` is unnecessary for this proof.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: already publicly imported
  by the unchanged statement dependency `Morphisms.Projective`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: already available through
  the existing statement and Segre dependencies.

All five declared proof dependencies of `lem-trf-h-projective-composition` remain
used. In particular `lem-chow-segre` is used through its binary closed-immersion
attachment, so that node is not pruned. No module withdrawal is requested.

## Where the brief, the DAG or earlier work was wrong

None. The pullback square already orders the factors as the binary Segre morphism
expects, so its canonical `isoPullback` supplies the identification directly.
Finite coordinate types may be empty; the construction and the finite product
type require no nonemptiness hypotheses. No unit route changes.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
