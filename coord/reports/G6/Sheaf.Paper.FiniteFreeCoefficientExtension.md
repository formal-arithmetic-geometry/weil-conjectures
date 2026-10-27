## What changed

The theorem `WeilConjectures.FiniteFreeCoefficients.finite_free_coefficient_extension`
now has a complete Lean proof from two independent categorical results. Its exact signature
is unchanged. Two private proofs in the item close the arithmetic without any new holes:
`stage_ramification` proves the positive ramification exponent, principal-ideal equality and
cofinality; `arrow_finite_free` constructs the quotient basis with the actual Arrow scalar action.
The latter uses integral closure finiteness/freeness and the quotient--tensor isomorphism,
which is shorter than the former adic-completeness route.

The original comparison definitions and structures have moved verbatim to
`Sheaf.Paper.FiniteFreeCoefficientExtensionData`, publicly imported by the item. Public names,
signatures and non-theorem bodies are preserved; no target meaning changes. This interface lets
the new result modules import the definitions independently of the theorem. The extracted data
contains no holes and no new chosen witness. The change record lists all downstream consumers.
No source-library declarations or files change. The old mixed-reduction module now imports the definition interface in place
of the theorem module. Its signatures and proofs are unchanged; this breaks the
cycle when the retained calculus task imports the mixed-reduction lemma. The
old naturality module is untouched.

`NormalizedStageCoefficientCalculus` states the normalized two-site construction without
arithmetic or scheme-isomorphism naturality. `CoefficientMapGeometricSquares` states geometric
naturality for arbitrary finite coefficient homomorphisms, independently of the stage system.
The main proof applies it to each actual stage quotient map and the normalized pro-etale
tensorator, and combines its eight squares with the calculus's two canonical-map equations.
These are strict parts of the argument, rather than aliases of the item's conclusion.

The initial six-file sandbox set compiled successfully. After removing unused proof imports,
the data file also compiled successfully. Profiling a later compile with the derived functors and monoidal instances locally
irreducible also succeeded: elaboration 8.68 s, kernel type checking 18.6 s. Those
local reducibility controls do not change any public definition or attribute. The final full sandbox compile passed with all declared proof-dependency imports:
data 42.5 s, geometric squares 46.2 s, mixed reduction 53.0 s, normalized calculus
46.5 s, item 51.9 s. The original naturality consumer also compiled against the
extracted data. A delivery compile later timed out in the data file. After profiling, scoped local
irreducibility controls around `Sites.Calculus` prevent repeated unfolding of its fixed
scalar, tensor and comparison interfaces; `dual` stays transparent for its endpoint equations.
These controls are restored immediately after the structure and export no attribute change.
The revised data module compiled successfully in 47.0 s without profiling. A later profile
passed in 24.1 s. The data interface also keeps derived tensor/Hom definitions locally
irreducible and excludes the unused GlobalGeometricFrobenius import, which stays publicly
imported by the original item so its exported interface is preserved. The delivery
performs the required compilation and axiom checks.

## Proved and sorry left

Closed in the item: `WeilConjectures.FiniteFreeCoefficients.finite_free_coefficient_extension`
(one original hole); the item now has zero literal `sorry`. Its arithmetic clauses are proved by
`stage_ramification` and `arrow_finite_free`. The final theorem is a decomposition, not a complete
axiom-free proof: its categorical clauses still depend on the following two added holes.

- `WeilConjectures.FiniteFreeCoefficients.normalized_stage_coefficient_calculus`, in
  `Sheaf.Paper.NormalizedStageCoefficientCalculus`; node
  `lem-sf-normalized-stage-coefficient-calculus`.
- `WeilConjectures.FiniteFreeCoefficients.coefficient_map_geometric_squares`, in
  `Sheaf.Paper.CoefficientMapGeometricSquares`; node `lem-sf-coefficient-map-geometric-squares`.

Holes closed: 1. Holes added: 2. Net literal-hole change: +1; this delivery claims a decomposition,
with genuinely completed arithmetic, rather than a net hole reduction. The adapted pre-existing module retains its original hole:
`WeilConjectures.RamifiedReduction.ramified_reduction_comparison_square`
(node `lem-sf-ramified-reduction-comparison-square`). This is not an added hole.
No other delivered module contains `sorry`. Each retained hole is a named public theorem with a complete proof
in words and a matching new node. Existing sorry-bearing proof dependencies retain their own
statements and nodes.

## No longer needed

No module is withdrawn and no entire dependency subtree is claimed pruned. The data extraction
preserves all public imports required by the existing statements and definitions. The following
old proof-only imports are removed from the extracted definition layer; any of them needed by
a retained categorical task are represented by that task's own proof dependencies:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Mathlib.RingTheory.AdicCompletion.Basic`.
- `WeilConjectures.RingTheory.FiniteOverCompleteRing`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.Paper.EtaleUnboundedRestrictionComparison`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `WeilConjectures.Compactification.NagataCompactification`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
- `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange`.
- `Sheaf.Paper.WeilVerdierPreservationStrata`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Paper.FiniteEtaleDescent`.
- `Sheaf.CategoryTheory.AdjointMate`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`.

The main node now directly needs the DVR/absolute-value and integral-closure arithmetic results,
and the two categorical parts. The following former direct proof dependencies are no longer
used directly by the item's assembly:

- `lem-sfb-local-field-integral-basis`.
- `lem-sf-finite-free-derived-scalar-calculus`.
- `lem-sf-finite-free-image-comparison`.
- `lem-sf-finite-free-exceptional-mate`.
- `lem-exc-closed-ambient`.
- `thm-amb-etale-exceptional-adjoint`.
- `thm-nagata-compactification`.
- `lem-weil-pbc-finite-type-over-noetherian`.
- `lem-sf-ringed-finite-free-hom-base-change`.
- `lem-weil-duality-pairing`.
- `lem-sf-finite-free-comparison-transitivity`.
- `lem-sf-ramified-reduction-comparison-square`.
- `lem-sf-finite-free-etale-proetale-transport`.
- `lem-sf-finite-free-comparison-isomorphism-naturality`.

Most remain needed by the normalized-calculus node's proof plan. In particular, finite-free
scalar/image/Hom, mixed reduction, transitivity and site transport are retained there. The old
finite-free isomorphism-naturality statement is not used: it assumes finite freeness and cannot
supply the reduction-arrow squares. The geometric task instead proves the formal naturality
for arbitrary finite coefficient maps. The old node and its declaration are preserved unchanged, since other parents can still
need it. The Nagata theorem is unnecessary for this item: the statement supplies its fixed
compactification. No unused source-library declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The rework row points to an archived quarantine copy, but the current item source is live and
is the source used here; nothing has been deleted. The current G6 return file has no numbered
repair demands. The live claim is G6's item claim.

The original assembly plan does not fit the stated interfaces directly. `Sites.Calculus`
quantifies over every `Arrow`, including exponent-reduction arrows that are generally not finite
free; several stated dependencies, including isomorphism naturality, assume finite freeness.
The finite quotient interfaces also use ULift coefficient rings with field universe u, whereas
stage fields have universe u+1 and unlifted quotient rings. Using them needs coefficient-ring
transport, not a direct application. The normalized-calculus node records that work explicitly.

Both the old naturality module and the mixed-reduction module import this item's definitions
through the item module. Importing them back into the original item would create a Lean cycle.
The definition-only interface removes that architectural obstruction without changing any
mathematics. The mixed-reduction file now publicly imports the extracted data interface, with
no other changes. It was unclaimed when adapted. The old naturality file stays unchanged. The retained calculus task privately imports
its declared proof dependencies, including mixed reduction, and can use them without a cycle.

The unit `sk-thm-sf-compatibility` has empty realized statement and proof-step lists; no realized
unit route is bypassed. The blueprint's positive ramified-level subsystem is retained exactly.
Edge cases checked: exponent one; equal and ramified fields; identity embeddings; arbitrary
reduction arrows; empty schemes; nonflat finite coefficient quotients. The arithmetic uses
e>0 explicitly. The geometric lemma asserts equality of canonical maps, never coefficient
flatness or unconditional invertibility. Its inverse-on-domain terms are preserved under the
scheme equivalence, including their zero branches.

## New nodes

`def-sf-finite-free-coefficient-comparison-data` owns the unchanged comparison definitions,
normalizations, Calculus structure and geometric-square predicates extracted to the data module.
It has no proof hole. The item retains ownership of its unchanged theorem declaration.

`lem-sf-normalized-stage-coefficient-calculus` is the independent construction and coherence of
all five comparisons on both sites, with the two canonical pro-etale arrow equations. It excludes
both arithmetic conclusions and all scheme-isomorphism squares. Its proof plan retains the
finite-free, quotient, mixed-square and site-transport steps from the existing DAG.

`lem-sf-coefficient-map-geometric-squares` is scheme-isomorphism naturality for arbitrary finite
coefficient maps, with the actual tensor/counit normalizations. It is independent of the stage
construction and asserts neither the existence of Calculus nor the five scalar isomorphisms.

Change record: `coord/changes/G6-finite-free-coefficient-data.md`.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
