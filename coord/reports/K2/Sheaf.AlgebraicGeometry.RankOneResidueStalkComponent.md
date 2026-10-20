## What changed

Restored `Sheaf.AlgebraicGeometry.RankOneResidueStalkComponent` in full from its
current rework archive. Replaced its public import of the withdrawn, empty
`Sheaf.AlgebraicGeometry.DerivedPullback` with the canonical
`WeilConjectures.AlgebraicGeometry.DerivedPullback`. Every other byte of the
archived module is preserved, including the theorem signature and its existing
complete proof. Its DAG attachment and dependency on
`lem-sc-residue-homology-rank-one-coefficient` remain intact.

The proof constructs actual source and target linear stalk frames, applies the
existing residue-coefficient theorem, and uses nonzero residue to obtain a unit.
Multiplication by that unit is bijective, giving the asserted stalk isomorphism.
No data is chosen from an unproved arbitrary existence assertion.

The restored item compiles through `lcompile.py` without warnings. Its current
residue-coefficient source was compiled unchanged in the sandbox to make the
recently landed dependency available; that identical source is not delivered.
A temporary `#print axioms` probe of
`AlgebraicGeometry.isIso_localized_stalk_component_of_residue_homology` reports
exactly `propext`, `Classical.choice`, and `Quot.sound`. The probe was removed.
The theorem signature also matches its DAG Lean record verbatim. All lines are
at most 100 characters. The canonical imports pass the import-direction checks.

Change record: `coord/changes/K2-rank-one-residue-stalk-canonical-pullback.md`.

## Proved and sorry left

This is a zero-hole restoration/import repair: the archived item already had
zero `sorry`s, and the restored item has zero. Holes closed: 0. Holes added: 0.
No split-off statements and no remaining holes in the delivery.

The restored complete theorem is
`AlgebraicGeometry.isIso_localized_stalk_component_of_residue_homology`
(node `lem-sc-rank-one-residue-stalk-component`). Its axiom audit confirms that
its proof dependencies are also free of `sorryAx`; this is not a decomposition
or a claim of closing a pre-existing textual hole.

## No longer needed

Removed the obsolete public import `Sheaf.AlgebraicGeometry.DerivedPullback`,
which is already an empty withdrawn module. Replaced it with the canonical
adopted module needed by the statement. No mathematical dependency, DAG node,
unit step or nonempty module is pruned. Both proof-only imports remain needed:
the residue-coefficient theorem and the rank-one free-module isomorphism API.

## Where the brief, the DAG or earlier work was wrong

The assigned item is a rework restoration rather than a theorem with an open
proof hole. Its absence from `lean/` does not authorize withdrawal. The archived
import became obsolete when the duplicate Sheaf derived-pullback module was
withdrawn. The current source's coefficient theorem already imports the canonical
module and has a complete proof, so no further split or new node is necessary.

The current rework row and group return file were checked. There is no current
item-specific return imposing additional mathematical changes. The previous
T1 report described a then-unproved coefficient dependency; the present axiom
audit confirms that dependency is now proved. The original stalk-component
proof and its recorded three-step DAG route remain valid.

The two quarantined consumer modules and all three named applications were read;
they use precisely the preserved signature. There are no live direct importers.
The unit record and its blueprint proof were read and remain unchanged. An empty
open cannot contain the chosen point; the source and target frames both have
rank one; zero coefficients are ruled out by the residue hypothesis. No stronger
hypothesis or weaker conclusion is introduced.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
