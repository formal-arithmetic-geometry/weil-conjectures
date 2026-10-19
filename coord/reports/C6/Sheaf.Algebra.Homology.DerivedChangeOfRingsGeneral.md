## What changed

Proved `SheafOfModules.derivedChangeOfRingsGeneral` by specializing the existing
`SheafOfModules.derivedChangeOfRingsIndependentCoefficients` at coefficient universe
`max u v`, preserving the complete signature. The underlying ring sheaves and K-flat
predicates coincide definitionally; relative essential smallness and sheafification
are already supplied by instances. The server compiler accepts the specialization.
The independent-coefficient theorem is pre-existing; this delivery adds no duplicate
statement or assumption. Added its module as a private proof import and removed four
unused private proof imports. All public imports remain unchanged.

The node `lem-pur-derived-change-of-rings` currently attaches to the cochain-model
interface, rather than this older General interface. Its existing construction and
Lean attachment are retained; an additional elementary proof step records this
compatibility specialization. No new dependency edge or node is introduced.

## Proved and sorry left

Closed 1 of 1 holes: `SheafOfModules.derivedChangeOfRingsGeneral`
(`lem-pur-derived-change-of-rings`). Zero holes remain in the assigned module.
Added zero holes and split off zero statements. This is specialization of an existing
stronger declaration, not a decomposition into newly assumed lemmas.

The pre-existing dependency
`SheafOfModules.derivedChangeOfRingsIndependentCoefficients` still has its own
`sorry`; this delivery does not claim to close that dependency or to make the result
independent of all library holes.

## No longer needed

Removed direct private imports:

- `Mathlib.CategoryTheory.Adjunction.Additive`
- `Sheaf.Algebra.Homology.KFlatResolutionGeneral`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`

This compatibility proof no longer separately constructs the ordinary functor,
resolving class, or derived pair. Their construction belongs to the existing
independent-coefficient interface. Thus `lem-pc-kflat-resolution`,
`lem-pur-left-derived-from-kflat-class`, and
`lem-pur-change-of-rings-kflat-quasi-iso` are not directly applied here; they remain
needed for the general construction and its cochain-model interface, so none of
these nodes is globally pruned. No whole module is claimed to leave the targets'
closure. The unit `sk-def-sf-operations` has no realized proof steps bypassed here.

## Where the brief, the DAG or earlier work was wrong

The standalone change-of-rings K-flat invariance theorem only allows coincident
site universes, whereas this legacy General interface has independent site
universes. Reconstructing that argument is unnecessary: the already-stated
independent-coefficient theorem is stronger and specializes definitionally.
The shared node now records the cochain model, so rebinding its Lean attachment
to the legacy compatibility theorem would be incorrect; the attachment is preserved.
The original assigned file also had one line over 100 columns; it is now wrapped
without changing the declaration type.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
