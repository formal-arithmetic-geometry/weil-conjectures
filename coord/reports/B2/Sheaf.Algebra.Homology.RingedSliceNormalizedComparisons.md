## What changed

The assigned module already has zero textual holes in the current shared source:
K2 supplied its assembly proof earlier on 2026-10-26. This delivery completes both
existing construction obligations used by that assembly:
`Sheaf.Algebra.Homology.RingedSliceTotalTensorComparison` and
`Sheaf.Algebra.Homology.RingedSliceHomComparisonExistence`. Both were unclaimed.
Their signatures, hypotheses, docstrings and public imports are unchanged.

The ordinary tensor comparison conjugates the canonical site tensor restriction
map with the native tensor presentation. Pure sections prove its naturality and
normalization. Restriction preserves coproducts via the underlying abelian-sheaf
adjunction and the module forgetful functor. The proved total-bifunctor comparison
then gives the natural chain isomorphism and its actual generator equation.

The ordinary Hom comparison uses the relocalized internal-Hom isomorphism and the
product projections of the actual Hom-complex functor. Product universal properties,
the two-term differential formula, and pre/postcomposition formulas give the natural
chain comparison and local-family normalization. Functorial K-injective replacement
and fully faithful localization descend it. Inverting the fixed ordinary-to-derived
comparison provides the two augmentation-normalized K-injective models; categorical
cancellation proves their square. A generic cancellation lemma keeps this proof from
rewriting through large concrete functor definitions.

The concrete constructions adapt the corresponding portions of the archived D4
proof recorded in coord/repair-notes. The current small assembly is retained and its
record literal is factored through a private constructor over abstract categories.
The existing proved Koszul comparison is reused. All added helpers are private and
proved; there is no data chosen from a new or undetermined existence assertion.
All delivered code keeps respectTransparency enabled. No shared data definition,
existing instance or attribute, public import, or source-library file changes.

The three node copies follow these proofs. The change record is
`coord/changes/ringed-slice-normalized-comparison-constructions.md`.

Validation: all three changed modules compile without errors or warnings using
`lcompile.py`: Hom 55.7 s, tensor 44.5 s, assembly 28.1 s. Static checks confirm
identical public theorem signatures and imports, zero holes in the delivered
files, and exact agreement between each node's proof uses and proof dependencies.
All four direct importers also compile cleanly against the changed modules:
`RingedSliceEvaluationTranspose` (7.8 s), `AlgebraicSpacePerfectObjectsCompact`
(6.8 s), `RingedSiteSignedDualRestriction` (34.8 s), and
`ModuleObjectRingedSiteDerivedComparison` (45.5 s). The three old failure modules
compile cleanly too: `CompletedPullbackReduction` (10.6 s),
`CompletedTowerDirectImage` (44.0 s), and `PerfectChartTensorComparison` (59.0 s).
Their temporary source copies were checked unchanged and removed; no consumer
adaptation is needed.

## Proved and sorry left

The assigned module starts with zero textual holes and ends with zero. Its theorem
`CategoryTheory.ringedSlice_normalizedComparisons` remains proved with the identical
statement and now uses the completed concrete comparison proofs.

Two existing holes are closed in its dependencies:

- `CategoryTheory.ringedSlice_totalTensorComparison_exists`, node
  `lem-weil-pbc-ringed-slice-total-tensor-comparison`.
- `CategoryTheory.ringedSlice_homComparison_exists`, node
  `lem-weil-pbc-ringed-slice-hom-comparison-existence`.

Holes added: zero. Split-off statements: zero. Sorries left in every delivered Lean
file: zero. This is a proof of the two existing construction obligations, not another
decomposition of the assembly theorem. Zero and unbounded complexes are handled by
the same totalization/product constructions, with no boundedness or flatness premises
added to the ordinary comparisons.

## No longer needed

No Lean module is withdrawn and no existing import is removed. All direct proof
imports supply declarations actually used by the completed constructions. The
existing source and slice Koszul theorem stays imported and used by the assembly.

The tensor node's former direct dependencies
`def-weil-presheaf-modules-sheafification` and
`lem-cbc-sieve-slice-sheafification` are replaced by the proved module-colimit
forgetful interface and the total-bifunctor comparison API. These declarations
remain in the library and may be used within those interfaces; no global pruning
of them is claimed. The Mathlib sheafification module remains a transitive proof
dependency, not an additional direct import of this packet; the sieve-slice node
has no separate Lean module attachment.

The Hom node's former direct
`lem-sp-site-restriction-kinjective-independent-ring` dependency is replaced by the
already proved `lem-pur-kinjective-restrict-localized-universes`, whose signature
matches the current independent site/section universes. Its former module
`Sheaf.CategoryTheory.SiteRestrictionKInjective` is not directly imported by this
proof; its declarations remain untouched. No module is pruned from
the targets' import closure by this delivery.

## Where the brief, the DAG or earlier work was wrong

The assignment names the older D4 red-build repair, but its archive is now marked
resolved and the live repair list has moved on. The current shared source already
has K2's zero-hole assembly and two newly isolated obligations.
Delivering that assembly unchanged would do no proof work. This packet completes
both obligations instead, preserving the current modular proof route.

The archived monolithic proof typechecked but took approximately 110 seconds. Its
profile showed expensive checking of concrete Hom comparisons and the final
assembly. The delivered representation uses bundled product-Hom data, a generic
inverse-comparison cancellation lemma, and the two existing comparison theorem
boundaries so the assembly handles abstract natural isomorphisms. No time limit is
raised and no transparency check is disabled.

The old repair archive also changed the public import of
`LocalizedModuleExactIndependent`; this packet does not repeat that change.
No target is weakened, and the unit's tensor/Hom/signed-exchange route is retained.
There is no second worker reading; the delivery's independent review handles the
changes to the two existing dependency modules and their nodes.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
