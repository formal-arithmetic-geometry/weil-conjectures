## What changed

Proved `CategoryTheory.ObjectProperty.isIso_of_bijective_postcomp_shift_generators` in
`Sheaf.CategoryTheory.LocalizingHomTest`, preserving its signature and all public imports.
The proof implements the five steps of `lem-sf-localizing-hom-test` without new declarations:
extend the Hom hypothesis across isomorphisms to the shift closure of the generators;
complete the morphism to a distinguished triangle; use the inverse-shift adjunction and
Hom exactness to show that maps from shifted generators to its cone vanish; put the
generators in the left orthogonal of all cone shifts; apply localizing minimality and
the zero-cone criterion.

The private proof import of `Mathlib.CategoryTheory.Triangulated.Orthogonal` is replaced by
`WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureGeneration`. Its proved
`shiftsOf` construction and `isLocalizing_leftOrthogonal` instance provide precisely the
coproduct and shift closure argument of steps 3 and 4. No source-library file was changed.
The DAG's proof, dependencies, and the unit route remain accurate and unchanged.

Validation: the item compiled through `lcompile.py` in 2.0 seconds without errors or warnings.
The axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound`.
The delivery preflight checks the declarations' axioms and compiles the item independently.

## Proved and sorry left

Closed one hole:
`CategoryTheory.ObjectProperty.isIso_of_bijective_postcomp_shift_generators`
(node `lem-sf-localizing-hom-test`).

Remaining holes: zero. Added holes: zero. Split-off statements: zero.

## No longer needed

Removed the direct private import `Mathlib.CategoryTheory.Triangulated.Orthogonal` because
the source-library proof import already imports it publicly. Its orthogonality instances
are still used. No mathematical dependency, DAG node, or module is pruned: every declared
proof dependency participates in the proof, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

None. The existing source library already provides the shift-class construction and the
localizing left-orthogonal instance described by steps 3 and 4, so those steps need no
new statement or proof hole. Searches through `msearch.py` (LeanFinder, Loogle, grep) and
local `rg` found these helpers and Mathlib's Hom exactness and zero-cone criterion.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
