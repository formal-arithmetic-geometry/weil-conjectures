## What changed

Proved `AlgebraicGeometry.Etale.lowerStar_closedImmersion_fullyFaithful_leftInverse_essImage`
in `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`, with its statement unchanged.
Full faithfulness and the left inverse use the existing closed-immersion counit API.
The essential-image proof first identifies support in the closed image with zero inverse
image on its open complement. Disjoint-range vanishing proves the forward implication.
For the converse the unit is invertible on the open complement (both objects vanish) and
on the closed subscheme (the triangle identity and invertible counit). The proved
`isIso_of_isIso_upperStar_map` API assembles these two checks by geometric-stalk conservativity.
Added proof-only imports of `WeilConjectures.SixFunctors.OpenClosed.Conservative` and
`WeilConjectures.SixFunctors.OpenClosed.Vanishing`; public imports are unchanged.
Updated `lem-kun-04ca`'s proof and proof dependencies to this route.

Read Stacks `etale-cohomology.tex`, `proposition-closed-immersion-pushforward` (Tag 04CA),
including its proof. The route agrees with that proof. The unit record has no realized
statement or steps for this auxiliary lemma; the unit and chapter routes are unchanged.
LeanFinder found only scheme ideal-sheaf support/full-faithfulness results; Loogle found
the generic essential-image API; launcher grep found no direct result. Local library
search found the closed-immersion, vanishing, inverse-image stalk, and conservative APIs.
The final proof compiled in 4.0 seconds and `#print axioms` reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. No new statements or definitions were introduced.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.lowerStar_closedImmersion_fullyFaithful_leftInverse_essImage`
(node `lem-kun-04ca`). Added 0 holes; split off 0. No `sorry` remains in the delivered module.
This is a complete proof, not a decomposition. Its axiom check contains no `sorryAx`.

## No longer needed

Removed direct imports of `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`, and
`WeilConjectures.SixFunctors.OpenClosed.Stalk`.
`lem-weil-pbc-inverse-image-stalk-germ` is no longer a proof dependency: no explicit
formula on germs is needed, only the existing natural inverse-image stalk comparison
`lemma-openclosed-stalk-upperstar`. Withdrawn its obsolete `tool_uses` approval.
`lemma-openclosed-stalk-lowerstar` is no longer a direct proof dependency: its work is
already encapsulated by `prop-openclosed-lowerstar-fully-faithful`. The underlying closed
pushforward stalk module still occurs transitively in the full-faithfulness proof, and the
geometric-point module still occurs transitively in the conservative API; neither is
claimed to be globally unnecessary. No further modules or nodes are pruned by this proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool defect was found. The original DAG planned explicit germ
compatibility for the unit on the closed image, but the adjunction triangle and the
already invertible counit supply that check directly. The existing docstring still
records the valid original stalkwise argument; the DAG now records the actual Lean route.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
