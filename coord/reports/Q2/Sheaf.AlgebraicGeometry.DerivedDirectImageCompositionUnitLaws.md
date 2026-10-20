## What changed

Restored Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnitLaws from its rework
quarantine archive, preserving its declaration attachment and full theorem signature.
Made SchemeDerivedDirectImage a public statement import to fix the module visibility
errors recorded in coord/rework.tsv. Its transitive public DerivedCategory import makes
the separate import redundant. Added two private proof imports for the homotopy-category
identity and natural isomorphisms of total derived functors.

Proved derivedDirectImageComposition_unit_laws. The identity functor is right derived
through its invertible localization unit; rightDerivedUnique constructs its comparison.
Deriving the underived identity isomorphism gives the identity pushforward comparison.
For each unit law, precompose the candidate inverse followed by the proposed unitor with
the unit of Rf. The pasted equation hc, identity factorization, and (for the right law)
naturality reduce it to the original unit. rightDerived_ext and cancellation finish.
Proved private transport lemmas supply exactly the id_comp and comp_id eqToHom terms.
A generic lemma combines the two laws for a family of additive functors; specializing it
once to sheaves avoids repeated elaboration of the concrete pushforward constructions.

All private helpers are proved. The identity comparison construction is irreducible with
an explicit API; it uses rightDerivedFunctorNatIso rather than an equality transport of
an entire derived functor, preventing excessive unfolding of the sheaf pushforward data.
The complete proof compiled in 35.8 seconds with command profiling, under the unchanged
60-second limit; diagnostic options are removed from the final file. The delivery tool
supplies the independent axiom and packet checks.

Change record: coord/changes/Q2-derived-direct-image-unit-laws-restoration.md.
The only consumer found, including quarantined modules, is
Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition. Its theorem application uses
the identical interface and requires no adaptation. Its separate quarantine is retained.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.derivedDirectImageComposition_unit_laws
(node lem-pc-derived-direct-image-composition-unit-laws).

Proved 1 of 1 original sorries. Added 0 holes; split off 0 statements. There are no sorries
left in the assigned module or in any added file. This is a proof, not a decomposition.

## No longer needed

Removed the redundant separate import of WeilConjectures.AlgebraicGeometry.DerivedCategory;
SchemeDerivedDirectImage publicly supplies it. Both declared DAG dependencies remain
needed: def-pc-derived-direct-image and def-pc-derived-category. No DAG node or module is
pruned. No definition, declaration, or dependency is withdrawn.

The generic identity results in the large pro-etale LowerStarComp module were inspected
during the shorter-route search. The proof instead constructs the identity comparison
from the localization universal property and imports only the small homotopy-identity and
derived-natural-isomorphism modules, so it does not add a pro-etale import dependency.

## Where the brief, the DAG or earlier work was wrong

The item is currently quarantined, not present at its lean/ path. Its rework row identifies
the preserved archive and the private-import visibility error; it is restored here, not
treated as withdrawn. No return entry for this item appears in coord/returns/Q2.md.

The mathematics of the DAG plan is correct. The complete proof needs neither preservation
of K-injectives by arbitrary direct image nor any additional composition hypothesis beyond
hc. The blueprint unit record is preserved. No target, public theorem statement, or
adopted source-library declaration is changed.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
