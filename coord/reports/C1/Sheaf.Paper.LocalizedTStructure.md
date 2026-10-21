## What changed

Restored `lean/Sheaf/Paper/LocalizedTStructure.lean` from the exact quarantine path
listed in `coord/rework.tsv`. The assigned module was absent from the library after
the cluster restore. Its archived proof already contains no holes and compiles against
the current dependencies, so no declaration, definition, import or proof needed changing.
The restoration retains every declaration, the existing Lean attachment, and all DAG
dependencies. This restores the module required by its quarantined importers rather than
withdrawing it or substituting an empty module.

Reviewed `AlgebraicGeometry.Scheme.pbc_localized_tstructure` against its eight-step DAG
plan and the current blueprint proposition. The essential-image predicates provide the
shift conditions. Tensor induction on localized Hom proves orthogonality. Applying the
exact localization functor to the integral truncation triangle proves existence. Integral
bounds prove boundedness. The source-library t-exact-functor API supplies natural
truncation comparisons, which identify the rational heart with the image of integral
homology in degree zero. The last tower formula retains its higher-Tor hypothesis and
reindexes the upper integral formula from m-1 to m. The scalar-localization structures
are selected from the existing theorem, whose normalization specifies the shift,
comparison and distinguished triangles up to the equalities used downstream.

Validation: `lcompile.py` compiled the restored module with exit code 0 in 32.8 seconds,
without errors or warnings. A Lean Finder search found generic localization and
truncation infrastructure, but no replacement for this specialized combined result;
Loogle does not index the source-library `Functor.eTruncLTIso`. The existing proof
already uses that source-library comparison API. No shorter replacement is needed.

## Proved and sorry left

The restored theorem `AlgebraicGeometry.Scheme.pbc_localized_tstructure` is fully proved
from its existing dependencies. The quarantine source had zero holes; this session
closes zero of zero holes, adds zero holes, and leaves zero holes in the delivered
module. This is restoration of a previously proved module, not a new proof or a
split into additional obligations. No other Lean module is delivered.

## No longer needed

None. No imports, declarations, nodes or modules were removed. All recorded proof
dependencies remain in use, including the Homology module for the integral heart
object and the integral canonical-truncation theorem for the conditional tower formula.
No quarantined parent or adopted source declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes an item containing holes, but the current rework entry is
a missing-module restoration: the preserved quarantine source is already proved. Its
absence from `lean/` did not indicate unused mathematics. There is no item-specific
return in `coord/returns/C1.md`. No mathematical error or interface repair was needed.
The unit `sk-rem-rest` has no realized proof-step constraints; the existing DAG route
and the explicit higher-Tor condition are preserved.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
