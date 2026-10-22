## What changed

Proved `AlgebraicGeometry.ProEtale.localModel_torBound_descent` with its signature and all
public imports unchanged. The proof transports the stated section-module flatness to internal
tensor flatness, applies bounded-above K-flatness, composes the published module-object derived
pullback/tensor and single-object comparisons, and computes tensor with the local flat models.
It descends homology vanishing through the public condensed cover-conservativity theorem,
applied to the degree-zero single complex of each homology module. Full faithfulness of the
single functor then gives zero homology, and the two t-structure criteria give Tor amplitude.
Three proved private theorems package the generic flat tensor calculation, module zero descent,
and homology zero descent. A fourth private helper, `transportTensorIso`, is the explicit
canonical composite of the given isomorphisms; it chooses no witness and adds no assumption.
All helpers remain in the same file. No other Lean module, public definition or statement changes.
The required change record is `coord/changes/P3-local-model-tor-bound-proof-commands.md`;
it explains the local commands flagged by the scanner and records zero current Lean importers.

The DAG now records this implemented route. The additional generic tools are the existing
internal/section flatness equivalence, bounded-above K-flatness, generic K-flat tensor-with-single
model, condensed module-object tensor pullback comparison, and condensed cover conservativity.
They implement the original local-model calculation and separatedness descent; the unit route
is preserved. The source declaration of the tensor-with-single model is generic even though its
existing node describes its ordinary-module specialization. Likewise the upstream
`leftDerivedUpperStarTensorIso` exposes the comparison whose stronger coherence is recorded
by `new-proetale-derived-module-pullback-monoidal`; this proof needs just the isomorphism.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.localModel_torBound_descent`
(`lem-sfb-local-model-tor-bound-descent`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. This is a proof from existing library declarations,
some of whose imported prerequisites remain open; it does not claim the whole axiom closure is
closed. The argument uses arbitrary test modules and includes zero modules, interval endpoints,
and the empty covering family.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Paper.SiteDerivedTensorRestriction`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`

The following previous direct DAG dependencies are not needed in this proof:
`lem-weil-proetale-weakly-etale-localization`, `def-pur-localized-ringed-site`,
`lem-pc-kflat-resolution`, `lem-weil-pbc-ringed-topoi-derived-pullback`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `lem-pc-bounded-above-flat-kflat-site`,
`lem-trf-site-derived-tensor-restriction`, `def-weil-abstract-derived-category`, and
`def-weil-pbc-sites-and-cohomology`. Existing exact module-object inverse image, its tensor
comparison, generic K-flat computation and cover conservativity replace these direct uses.
They may still occur transitively or be needed by other consumers; no declaration or module
is withdrawn. Obsolete top-level tool approvals for those removed direct dependencies were
removed; no new approval was written.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement repair was needed. The original plan reconstructs
comparisons through general sectionwise ringed-site machinery, whereas published internal
module-object APIs already provide the required comparisons in exactly the coefficient
category of the theorem. Searches through LeanFinder, Loogle, Mathlib grep and the source
library found these reusable APIs. Elaboration and kernel checking exposed costly conversions
through concrete sheaf and derived tensor constructions. The private helpers and local
irreducibility attributes keep the calculations abstract in the same file. The final public
cover-conservativity route compiled in 54.8 seconds with temporary profiling enabled; the
profile attributed 43.3 seconds to kernel checking. Diagnostics were removed for delivery.
Repeated earlier validation attempts received busy-server responses; one preflight required
the local-command change record, which is included. The original unused `hrs` binder is kept
with a theorem-scoped unused-variable linter setting. No compiler limit was raised, no
statement was split off, and no source-library declaration was modified.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
