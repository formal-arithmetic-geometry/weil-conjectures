## What changed

Restored the assigned quarantined module. Replaced its obsolete public import of
Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap with the adopted
WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap. The withdrawn
Sheaf module is empty; the original archive failed on unknown identifiers for
strictHenselizationScheme and strictHenselizationStructuralMap. The repaired
module compiles in 21.1 seconds through lcompile.py.

The theorem signature and complete proof are byte-identical to the archive. The
proof composes the stated module/abelian stalk comparison, the restored abelian
original-stalk total exchange, and the pullback/forget isomorphism. Naturality of
cohomologyMap transports the last coefficient isomorphism. The unit route stays
unchanged. The node keeps its Lean attachment and proof dependencies; its recorded
statement is refreshed from the archived source (IsTorsionModuleSheaf, rather than
the obsolete IsTorsionSheaf spelling).

Change record: coord/changes/D2-original-stalk-total-cohomology-restoration.md.
The only direct consumer is quarantined
Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison; its
existing theorem application matches the restored statement exactly. No consumers
or source-library modules are changed.

## Proved and sorry left

AlgebraicGeometry.Etale.projectiveLine_originalStalk_totalCohomologyExchange:
zero holes before, zero after. This is a substantive compile/interface restoration,
not a newly closed proof hole. Holes closed: none. Holes added: none. Split off:
none. No sorry remains in the delivered module.

## No longer needed

Removed the obsolete public import
Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap, replacing it by its
adopted owner. No mathematical dependency, node or module is pruned; all five
recorded proof dependencies are still used. The quarantine archive is preserved.

## Where the brief, the DAG or earlier work was wrong

The archived public structural-map import now resolves to an empty withdrawn
module, so it no longer exposes the types in the original statement. The Lean
record still used the older IsTorsionSheaf name, while the archived source already
uses IsTorsionModuleSheaf. Both bookkeeping/interface defects are repaired without
changing the theorem. The adopted same-named theorem uses the canonical
strictLocalization model; substituting its different hypotheses would not restore
the assigned small-model interface.

Searches: repository rg found the adopted same-named theorem and the precise
existing comparisons used by the archived proof. msearch leanfinder returned
projective-spectrum stalk lemmas, not an exchange comparison; loogle did not know
Etale.cohomologyMap; Mathlib grep found no strict-henselization stalk match. No
new intermediate statement or proof route was necessary.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
