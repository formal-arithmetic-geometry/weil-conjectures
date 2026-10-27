## What changed

Restored the previously landed proof of `CategoryTheory.finitarySite_enoughPoints`
from the parent of take-out commit af2f412b751, as requested by the current K3 return.
Restored its fully proved helper module `Sheaf.CategoryTheory.Sites.PointSystemSaturation`
and the corresponding node `lem-trf-point-system-countable-saturation`.
The theorem signature, universes and public imports are unchanged. No definitions or
existing statements change, and no adopted source-library module changes.

The saturation lemma constructs the countable sequence of simultaneous refinements,
its filtered Grothendieck union, and its thin skeleton. The item transports finite-cover
lifts to arbitrary covers using the finite-refinement hypothesis, constructs the point
with `inverseSystemSitePoint`, and checks section separation under the stalk comparison.
The small family is selected using small subobject sets of sheafified representables:
push out each subobject inclusion against itself, select a separating point for the two
coprojections when distinct, and use equalizers and left exactness to separate arbitrary
section pairs. The original item's node is updated only in proof, proof_deps and
proof_origin to record that actual argument.

Both restored Lean sources are byte-for-byte the earlier landed proofs. They compile
cleanly together using `lcompile.py --all` against the current published build:
PointSystemSaturation 10.8 seconds; FinitarySiteEnoughPoints 9.5 seconds.
No change record or consumer adaptation is needed because no existing interface changes.

## Proved and sorry left

Closed the assigned module's one hole:
`CategoryTheory.finitarySite_enoughPoints`
(`lem-trf-finitary-site-enough-points`).
Restored the fully proved public helper
`CategoryTheory.exists_pointSystem_finiteCoverLifting`
(`lem-trf-point-system-countable-saturation`) and its proved private helpers.
Holes closed: 1 of 1. Holes added: 0. Split-off holes: 0.
Every delivered module has zero sorry declarations.

The proof uses the existing declarations `exists_pointSystem_refinement_all`,
`inverseSystemSitePoint`, and `point_family_conservative`.
The source of `Sheaf.Paper.PointSystemRefine` currently retains its separate hole
`CategoryTheory.pointSystemRefine`; its restoration is held by Y3 and is not changed here.
This delivery proves the assigned theorem from its declared dependencies; it does not
claim that the current transitive dependency closure has only standard axioms.

## No longer needed

No module or node is pruned. The item's direct private import
`Sheaf.CategoryTheory.PointSystemRefineAll` is replaced with
`Sheaf.CategoryTheory.Sites.PointSystemSaturation`; PointSystemRefineAll remains necessary
transitively. The direct proof dependency `lem-trf-point-system-refine-all` moves to the
saturation node and remains used. `def-weil-size-convention` is no longer an explicit
proof dependency of the item: the universe convention remains in the statement, while
Mathlib's `wellPowered_of_isDetecting` supplies the actual small-family bound.
The conservative-family and inverse-system-point dependencies remain direct imports.
No public imports, upstream declarations, or approval entries are removed.

## Where the brief, the DAG or earlier work was wrong

The dedicated return explains that this proof chain was taken out after an unrelated
build failure in FiniteTypeTorsionUniversalStar. Restoration is therefore a substantive
proof restoration, not a no-op rebase. Both requested modules have been recovered and
checked against the current library. The current one-cover worker is Y3, so its held
module is left to that restoration rather than adapted without a forced interface change.

The old DAG's size argument indexed over all sheaves, and the old theorem docstring
suggests bounding inverse systems without supplying the bound. The restored proof instead
uses the explicit subobject/pushout/equalizer selection described above. The existing
public docstring remains verbatim; its final proof sketch is corrected by this report
and the updated node proof. No hypothesis, conclusion or universe has been weakened.

Read the Stacks source in sites.tex: lemma-refine-all-at-once (00YP),
proposition-criterion-points (00YQ), and lemma-enough (00YM). A single 00YP refinement
only lifts old Hom germs; the countable iteration is required to lift all union germs.
The union proof verifies finite-stage equality and compatibility explicitly. Empty covers
are included: a Hom germ would force a member of the empty index. Singleton initial
systems, repeated covering arrows, finite refinement of cardinality zero, empty sites,
and empty selected families require no extra hypotheses. The unit route stays unchanged.

## New nodes

Restored `lem-trf-point-system-countable-saturation` in
`dag/nodes/sec-trace-formula/lem-trf-point-system-countable-saturation.json` with the proved
module `Sheaf.CategoryTheory.Sites.PointSystemSaturation`. This is the same mathematical
node and theorem previously landed by J4, absent from the current tree after the take-out.
It gives the strictly intermediate countable-saturation step, not the enough-points
conclusion. Its dependencies are the all-at-once refinement theorem and Mathlib's
filtered-colimit element description. LeanFinder, Loogle, grep and LeanSearch queries
were rerun using msearch.py; they found generic Grothendieck-colimit and thin-skeleton
infrastructure and unrelated results, but no site-specific saturation theorem.
The restored node's current-delivery metadata is K3; old reviewer approvals are omitted.
No new holes or change records are added.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
