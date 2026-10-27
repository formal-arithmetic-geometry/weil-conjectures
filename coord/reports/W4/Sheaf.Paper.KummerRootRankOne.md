## What changed

Filled `AlgebraicGeometry.ProEtale.SpTowerClasses.kummerRoot_rank_one` in
`Sheaf.Paper.KummerRootRankOne`, preserving its signature and existing docstring.
Added a private proof import of `Sheaf.Paper.PurTwistRootLocalModels` with access to
its proved `AlgebraicGeometry.Scheme.localTowerCover` helper. This gives exactly
the compatible additive root/coefficient tower trivialization needed here.

All added helpers are private and proved. They flatten towers to the sequence
presheaf, transport the section/restriction/transition equations of `Forget`,
and restrict the resulting diagram isomorphism to each sequence slice. The
constant integer presheaf maps locally surjectively onto the sequence coefficient
ring, so additive chart isomorphisms lift uniquely to module isomorphisms using
Mathlib's locally-surjective scalar restriction Hom equivalence. The vertical
covering criterion and the existing local unit criterion then give rank one.
Updated the item's node proof and proof dependencies to match this argument.

Validation: the complete file compiles without warnings through `lcompile.py`
in 17.9 seconds. The signature, original public imports, 100-character line
limit and absence of holes were also checked directly.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.SpTowerClasses.kummerRoot_rank_one`
(node `lem-sfb-kummer-root-rank-one`).

No holes added, no split-off statements, and no `sorry` remains in the delivery.
This is a proof from existing declarations, not a decomposition.

## No longer needed

No existing import was removed. The direct proof dependency
`det-def-sp-tate-twist-locally-free` (`Sheaf.Paper.TateTwistLocallyFree`) is not
needed: its proved root-cover helper in `Sheaf.Paper.PurTwistRootLocalModels`
already supplies the required diagram isomorphism, without coefficient fields,
completed lines, scalar extension or signed derived twists.

The direct dependency `lem-pur-torsion-sheaf-constant-module`
(`Sheaf.CategoryTheory.TorsionSheafConstantModule`) is also unnecessary for this
proof. The locally-surjective integer map proves linearity directly, uniformly
across the varying quotient-ring levels. This removes that node from this
item's direct proof dependencies; its module can remain transitively needed by
other declarations, so no global module withdrawal is claimed.

No module was withdrawn, and the unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The plan's mathematical argument is valid, but its proposed dependence on the
full Tate-twist theorem and a separate torsion-action uniqueness theorem is
unnecessary. A proved compatible-root diagram cover and Mathlib's scalar
restriction API suffice. The section-site glue is implemented explicitly; it
is not left as a renamed rank-one assertion.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
