## What changed

Proved `AlgebraicGeometry.Scheme.open_finite_constructibility_interval` in
`Sheaf.Paper.OpenFiniteConstructibilityInterval`. The complete theorem signature and all public
imports are preserved verbatim. No theorem type or definition changes; two helper modules gain theorem visibility only.

Repair of returned head `90a8da74808`: removed all six duplicate private theorems named
in the return: `realization_constructible_iff`, `extension_constructible`,
`constantPresheaf_zero`, `locallyConstant_of_isZero`, `finite_stalk_of_iso`, and
`finite_stalk_of_isZero`.

The canonical `extension_constructible` in `Sheaf.Paper.OpenExtensionFiniteTor` is now public.
The canonical `locallyConstant_of_isZero`, `finite_stalk_of_iso`, and
`finite_stalk_of_isZero` in `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated` are now public.
Both modules were unclaimed when checked. Their only changes remove `private` from these four
existing proved theorems. Their types, proofs, definitions, public imports, and other declarations
are unchanged. The item imports these two modules and applies those theorems directly. The other
two duplicate helpers are unnecessary after this reuse. The change record is
`coord/changes/B9-open-finite-constructibility-helper-reuse.md`.

The retained proof uses the existing exact-functor derived cohomology comparison, canonical
open-extension constructibility, open-unit and disjoint-pullback identities, and constructs the
prescribed stratification. The strata are indexed by the subtype of `Option (Fin S.n)` outside
the chosen omitted set; coverage excludes an omitted index by its empty domain. The actual
immersions over the ambient scheme are retained, giving reflexive Over isomorphisms.
No arbitrary object is chosen from an unproved mere-existence theorem.

The DAG proof now explicitly records reuse of the helpers in `lem-trf-open-ctf` and
`lem-weil-proetale-dbc-triangulated`. The unit `sk-def-sf-operations` route is unchanged.
The main theorem signature and all original public imports are unchanged.

Validation: lcompile.py --all compiled OpenExtensionFiniteTor (7.7 s),
ProEtaleBoundedConstructibleTriangulated (1.3 s), and OpenFiniteConstructibilityInterval (5.4 s)
without diagnostics. All three pass import_prune_check.py, including the duplicate-statement
check that refused the original delivery. A byte-for-byte comparison confirms preservation of
the main theorem signature; all Lean lines fit within 100 characters.
The unchanged consumer TwistPreservesFiniteness compiled against the sandbox helper overlay
in 8.0 seconds, confirming coexistence with its distinct private helper.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.Scheme.open_finite_constructibility_interval`
(node `lem-sf-open-finite-constructibility-interval`). Proved 1 of 1 original sorries.
No sorries remain in the item or either adapted helper module (zero actual holes in each).
Added zero holes, split off zero statements, and added no axioms.
Imported declarations retain their existing proof status; this is a proof from existing library
results, not a claim that their entire transitive dependency closure is already sorry-free.

## No longer needed

Removed direct proof imports (relative to current source):

- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
- `Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.

The item proof no longer needs `lem-weil-pbc-proetale-ringed-open-closed`,
`lem-weil-pbc-reduced-induced-closed-subscheme`,
`lem-pur-proetale-constant-coefficient-comparison`, or
`lem-pur-proetale-module-pullback-composition`. Exactness is already published for the intrinsic
extension; the derived homology API already performs localization; canonical transported
pullback composition and its coordinate comparison supply the restriction identities. The
complementary scheme in the detailed conclusion is supplied by the caller. Constructibility
itself follows from existing etale-origin and etale-extension results and constructs no reduced
complement here. The ambient Noetherian topology supplies constructibility of every resulting
locally closed stratum, so the supplied constructibility of the original strata need not be used.

The repair also removes the previous packet's direct imports of
`Sheaf.Paper.IntrinsicRealizationOriginComparison`,
`WeilConjectures.ConstructibleSheaf.ExtensionByZero`, and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison`.
Their results are used internally by the imported canonical extension-constructibility helper.
`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated` remains a proof import because its
canonical zero-sheaf and stalk helpers are now used.

These are dependency removals for this proof, not withdrawals or claims that those modules are
unused elsewhere. No source-library declaration or public import was removed. The unit record
`sk-def-sf-operations` has empty realized statement/step lists; its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned packet unnecessarily copied existing private helpers. This repair exposes and
imports their canonical versions instead of duplicating the proofs. No statement is weakened.

The original DAG route was a valid longer plan. It did not identify the already available
finite-module etale-origin argument or exact-derived-cohomology API. The new route avoids
reconstructing those results. No mathematical statement was disputed or weakened.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
