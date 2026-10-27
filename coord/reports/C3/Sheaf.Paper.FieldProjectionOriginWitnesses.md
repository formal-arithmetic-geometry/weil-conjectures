## What changed

Proved three existing theorems in `Sheaf.Paper.FieldProjectionOriginWitnesses` without
changing their statements or any definition. The original five-way assembly theorem
is retained. All added helpers are private and proved.

`field_projection_origin_lower_bounds` now applies the existing
`SpTowerP1Uniform.uniformTower_etale_domains` theorem to each normalized object's inverse
realization and transports its lower bound through the realization counit. This is a
generic uniform-tower domain tool, not a replacement of the field-extension unit route.

`field_projection_origin_good_levels` uses `Domains.finite`, equality transport along
`Base.ideals`, and finiteness of the integer interval containing cohomological support.
It handles every actual ell-power quotient, including ramified extensions.

`field_projection_origin_transport` specializes the existing level-witness theorem to
the normalized coefficient unit for F and the identity inclusion. Given its one good
origin, full faithfulness of intrinsic realization identifies the fixed-scalar
comparison images. The invertible units of the derived site-comparison adjunction
then identify any other retained antecedent with it. Homology and derived tensor carry
the isomorphism to the exact constructibility, cohomological, and Tor properties needed.
`transportOrigin` retains this antecedent by definition.

Updated the three corresponding existing DAG nodes' proof, proof_deps, and proof_origin
fields to describe these arguments. Added proof imports
`Sheaf.Paper.TowerUniformEtaleDomains` and
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`. Expanded the remaining holes' documentation into
source-based proof instructions and corrected the five clause docstrings' node labels.
Removed the old trailing diagnostic `#print` commands. Local irreducibility controls
keep category and coefficient-map implementations from expanding during elaboration;
existential witnesses are projected explicitly within the proof.

Validation: the final module compiled cleanly through the server backend of
`lcompile.py` in 50.2 seconds, below the 60-second limit. No profiling options or
diagnostic commands remain. Public signatures and DAG dependency checks also passed.

## Proved and sorry left

The original module had five holes. Closed three, with no new holes or split-off statements:

- `AlgebraicGeometry.ProEtale.FieldProjectionOrigin.field_projection_origin_lower_bounds`
  (`lem-sp-field-projection-origin-witnesses-lower-bounds`).
- `AlgebraicGeometry.ProEtale.FieldProjectionOrigin.field_projection_origin_good_levels`
  (`lem-sp-field-projection-origin-witnesses-good-levels`).
- `AlgebraicGeometry.ProEtale.FieldProjectionOrigin.field_projection_origin_transport`
  (`lem-sp-field-projection-origin-witnesses-transport`).

Two existing holes remain, exactly as named public theorems:

- `AlgebraicGeometry.ProEtale.FieldProjectionOrigin.field_projection_origin_data`
  (`lem-sp-field-projection-origin-witnesses-data`). It still needs normalization of the
  actual degree-zero coefficient system and invertibility of its specified derived
  scalar-adjunction transpose.
- `AlgebraicGeometry.ProEtale.FieldProjectionOrigin.field_projection_origin_level_witnesses`
  (`lem-sp-field-projection-origin-witnesses-levels`). It still needs the exact dualizing
  Tor interval from the smooth charts and the retained finite-level origins. The transport
  proof depends on this existing theorem, as intended by stage 3.

The new lower-bound proof also uses the existing named theorem
`SpTowerP1Uniform.uniformTower_etale_domains`, whose proof remains the next worker's task.
No claim is made that the whole target closure is now free of sorry.

## No longer needed

Removed these unused private imports from the item:

- `Sheaf.Paper.SmoothPurityTowerChartAdmissibility`.
- `Sheaf.AlgebraicGeometry.SmoothAdmissibleCoordinateCover`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection`.
- `Sheaf.Paper.FieldScalarNormalizedSystems`.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`.

The lower-bound and GoodLevel proofs no longer use chart admissibility or tower gluing:
normalized membership and the existing generic domain theorem suffice. Their proof_deps
now record that shorter argument. The transport proof no longer uses an additional
comparison-Tor reflection argument: the exact Tor bound transports from the antecedent
provided by the existing level-witness theorem. It needs full faithfulness, not the
construction of exceptional comparison or scalar extension again.

These are local proof/import removals. The unresolved level-origin theorem and other
consumers still need the geometric dependencies. No library module or DAG node is
withdrawn, and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The three former clause nodes repeated a generic seven-step plan instead of distinguishing
what each clause actually needs. In particular, lower bounds do not need a fresh smooth
chart proof, and GoodLevel follows from the already supplied finite domain. Transport
must compare arbitrary bounded-below antecedents using full faithfulness; merely saying
that realization is changed does not establish the antecedent's properties. The proof now
constructs that comparison and conjugates its derived right-comparison image by
the two invertible adjunction units.

The clause nodes' historical source path says `sk-lem-field-extension`, but the actual
latest blueprint directory is `sk-lem-sp-field-extension`. The edited proof_origin fields
use the actual path; source fields and unit records were left unchanged. There was no
current return or rework row for this module.

The unchanged statements include empty schemes, zero inputs, d=0, identity coefficient
inclusions, and ramified extensions. The new arguments use only equality transport,
full faithfulness, and vanishing under isomorphism, so none excludes these cases.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
