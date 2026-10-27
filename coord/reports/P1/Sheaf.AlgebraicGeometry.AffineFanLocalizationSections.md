## What changed

Replaced the proof of `AlgebraicGeometry.FineFan.affineFan_localization_sections` by a
complete argument from the existing principal-face and prime-neighborhood declarations.
The original public signature and public imports are unchanged. Added private proof imports
of `MonoidPrincipalOpenFace` and `MonoidPrimeMinimalNeighborhood`. Mathlib's terminal-object
colimit API is already available through the existing imports. All helper declarations
are private and proved.

A sheafification unit is bijective on an open with a point having that open as its smallest
neighborhood: its covering image and equalizer sieves contain the identity. Forgetful
preservation of sheafification and `largeSetSheafification_locallyBijective` provide the
local properties. Evaluation at the greatest prime identifies compatible raw fractions
with the basic localization. Both actual sheafification units and sharpening then give
the canonical basic-section equivalences. Their naturality proves the numerator and
restriction formulas.

The product of generators outside a prime supplies its smallest neighborhood. The actual
colimit germ from that neighborhood is an isomorphism by the terminal-object colimit
lemma. This gives the stalk equivalence and germ formula. Finally `Associates.mk_eq_one`
and the prime-localization units criterion prove the exact zero-germ equivalence.

Updated the item's DAG proof and proof dependencies to this implemented argument.
Read ILO VIII 3.1.1--3.1.4, printed pp.98--99 (PDF pp.104--105), including the unit,
empty-prime, and trivial-cover cases. The unit route is unchanged; the unit's `realized`
record assigns no separate step to this node.

Validation: the final module compiled cleanly through `lcompile.py` in 8.0 seconds.
Static comparison confirmed the unchanged theorem signature and public imports, zero
remaining holes, line widths at most 100 columns, and the exact union of DAG proof uses.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.FineFan.affineFan_localization_sections`
(`lem-trf-affine-fan-localization-sections`).

Item holes: 1 before, 0 after. Added holes: 0. Split-off statements: 0.
No `sorry` remains in any delivered Lean declaration. The existing imported principal-face
and prime-neighborhood statements are used as allowed by this stage; their own proof holes
are not changed by this delivery.

## No longer needed

`lem-trf-monoid-sheafification-trivial-covers`, module
`Sheaf.CategoryTheory.MonoidSheafificationTrivialCovers`, is no longer a proof dependency.
It states the additive generic universal-property formulation. The argument here proves
only the needed multiplicative unit-component bijectivity directly from covering sieves,
using the already imported forgetful-preservation and large-set local-equivalence results.
No import of that module had been present, so no Lean import was removed.

Removed the unnecessary private import of
`Mathlib.CategoryTheory.Limits.Shapes.Terminal` introduced during proof development.
No existing module or declaration is withdrawn. The principal-face, prime-neighborhood,
fine-fan definitions and large-set sheafification dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

The proposed trivial-cover sheafification dependency has an additive Lean interface,
whereas this item's sheaf and stalks take values in `CommMonCat`. Transporting the entire
generic theorem across the additive/multiplicative equivalence is unnecessary: the small
covering-sieve argument proves the exact multiplicative comparison used here. Also, the
raw spectrum presheaf is defined as compatible point-local fractions rather than literally
as the basic localization; the evaluation equivalence is proved explicitly.

No mathematical statement, target, shared definition or existing public interface changed.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
