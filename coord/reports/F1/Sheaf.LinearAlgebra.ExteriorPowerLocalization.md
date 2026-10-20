## What changed

Retired the duplicate Sheaf.LinearAlgebra.ExteriorPowerLocalization in favor of
WeilConjectures.LinearAlgebra.ExteriorPowerLocalization. The existing source theorem
exteriorPower.isLocalizedModule_of_wedge has exactly the same public signature.
The sole direct consumer, Sheaf.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit
(unclaimed), now imports the source module privately; its statement and proof are unchanged.
No source-library file is edited.

Repointed new-v2-exterior-power-localization to the source theorem and updated
its proof plan to the source proof, which applies the existing generic theorem
exteriorPower.isLocalizedModule_of_pure_wedge after installing restricted scalars.
Change record: coord/changes/retire-exterior-power-localization.md.

Validation: the direct consumer compiled alone through lcompile.py in 3.0 seconds.
A separate import/axiom probe compiled in 1.6 seconds; the replacement theorem
uses only propext, Classical.choice and Quot.sound. Public signatures were compared
verbatim. The import graph with the delivered consumer has no remaining importer
of the withdrawn module and introduces no new Sheaf/source twin pair.

## Proved and sorry left

This is a retirement repair with zero original holes: proved 0 of 0 sorries;
added 0 holes and split off 0 statements. No sorry remains in the retired item or
in the adapted consumer. The replacement exteriorPower.isLocalizedModule_of_wedge
(new-v2-exterior-power-localization) is already proved and its axiom probe excludes
sorryAx. This delivery claims one module pruned, not a newly closed proof hole.

## No longer needed

The entire module Sheaf.LinearAlgebra.ExteriorPowerLocalization is withdrawn.
Its proved private helpers extend_multilinear, localized_multilinear_ext and
extend_alternating have no public consumers and are removed with the duplicate.
The consumer no longer imports this Sheaf module.

The withdrawn file's imports Mathlib.LinearAlgebra.ExteriorPower.Basic,
Mathlib.Algebra.Module.LocalizedModule.Basic,
Mathlib.Algebra.Category.ModuleCat.ChangeOfRings,
Mathlib.RingTheory.Localization.Module and Mathlib.Algebra.Module.LocalizedModule.Int
are removed with that file. This does not claim those Mathlib modules are globally
unused; the upstream theorem still publicly imports the same three statement imports.
No additional project module is pruned.

The old direct proof dependencies def-weil-pbc-module-localization and
 def-weil-pbc-exterior-algebra are replaced by new-v2-generic-exterior-power-localization.
Both definition nodes remain statement dependencies and are also used by the generic
theorem; neither node is obsolete. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proof-worker brief describes an item with sorry or an assigned repair.
The queue row actually marks this item retire, and the module has no sorry.
The retirement row's three missing upstream names are private helpers; the sole
public theorem is present upstream with its signature unchanged. The DAG's old
attachment and proof plan described the local proof and have been updated to the
existing source theorem. No mathematical statement is disputed.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
