## What changed

Replaced the hole in
`AlgebraicGeometry.ProEtale.CondensedRing.continuousFiniteEtaleTrace_exists`
by a proof that explicitly constructs the local sheet sums, descends them, and
checks the exact `FiniteEtaleTraceFormula` on every weakly etale splitting chart.
The original theorem signature and all four original public imports are unchanged.

`FiniteEtaleTraceFormula` now quantifies over `FiniteEtaleModuleChart`, which
bundles exactly the previous Y, g, weak-etaleness, n, t, w and splitting certificate.
Its constructor and projections pack and unpack the same data. The predicate
and the chart wrapper use a shared actual sum
construction, `finiteEtaleTraceSheetSum`. It uses a shared canonical comparison
before taking components. Its fully proved singleton specification fixes that comparison to
exactly `eqToIso.symm` followed by `upperStarComp`; the equation
`finiteEtaleTraceSheetComparison_eq` proves the equality, so the mathematical
normalization is unchanged. Its signature, visibility, attributes, public imports,
quantification over exactly the same splitting data and counit are unchanged. The change record is
`coord/changes/M9-finite-etale-trace-formula-comparison-family.md`; it requests
renewed semantic review for targets using the definition. The sole other direct
consumer is U6's `ContinuousFiniteEtaleTraceImageCharts`; it is copied unchanged
for validation (43.0 seconds) and excluded from this delivery.

The private proof `sheetSum_epi` proves local epimorphy for arbitrary commutative
condensed coefficients. On a positive-degree chart, `epi_sum_of_product` inserts
into one chosen factor of the canonical product comparison and composes with its
inverse. The composite with the sum is the identity. A zero-sheet chart has empty
fibre product; surjectivity makes its base empty, and `module_isZero_empty` proves
that every internal module there is zero. No degree is divided out.

Two new modules isolate the unresolved gluing and overlap-coherence arguments:
`FiniteEtaleSplitHomDescent` and `FiniteEtaleSheetSumCompatibility`. The chart
structure belongs to `FiniteEtaleTraceFormula`; the compatibility predicate is
an actual construction in the descent module. The chart sum is an abbreviation
of the shared, explicitly constructed counit sum.
The shared `finiteEtaleTraceSheetComparison` is fixed by a fully proved singleton
specification to be the actual composition isomorphism;
`finiteEtaleTraceSheetComparison_eq` proves its exact normalization and matches
the canonical product comparison used to prove epimorphy. This interface avoids kernel reduction
through the implementation of `upperStarComp` when taking components of an inline
comparison. The item combines the two remaining statements with the existing
proved canonical product comparison; it has no residual hole in its own proof.

Validation: all four delivery modules compile through `lcompile.py --all`; the
item took 41.4 seconds, and the unchanged U6 consumer took 43.0 seconds. The
remaining delivery modules took 4.4 to 5.6 seconds each. Profiling options and
the temporary consumer copy were removed before delivery. No source-library
module is changed.

## Proved and sorry left

Closed the original textual hole in `continuousFiniteEtaleTrace_exists`, node
`lem-sfb-continuous-finite-etale-trace`. Proved the private helpers
`module_isZero_empty`, `epi_sum_of_product`, `epi_mod_sum_of_sheets`, and
`sheetSum_epi` without holes. The private generic assembly
`finiteEtaleTrace_of_compatible` combines them with the two lower statements.
The public specification `finiteEtaleTraceSheetComparison_exists` and API equation
`finiteEtaleTraceSheetComparison_eq` are proved without holes.

Added exactly two holes, each the whole proof of a named public theorem:

- `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleSplitHom_descent`, node
  `lem-sfb-finite-etale-split-hom-descent`.
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleSheetSum_compatible`, node
  `lem-sfb-finite-etale-sheet-sum-compatible`.

This is a decomposition: one original hole closed, two lower holes added, net
minus one. It is not an independent proof of the original assertion. The genuine
proved part is the construction and local epimorphy argument, including the
empty-chart case, and the Lean combination of the two lower statements.

## No longer needed

No original public import is removed and no module is withdrawn. The new private
proof imports are `Sheaf.Paper.FiniteEtaleSheetSumCompatibility` and
`Sheaf.Paper.SplitProEtaleModuleProductMap`.

The item's proof no longer directly uses the following planned dependencies:

- `def-weil-pbc-continuous-coefficient-module-encoding`, module
  `Sheaf.Paper.ContinuousCoefficientModuleEncoding`;
- `lem-weil-pbc-continuous-module-encoding-restriction`, module
  `Sheaf.Paper.ContinuousModuleEncodingRestriction`;
- `lem-sfb-finite-etale-trace-image`, module
  `Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage`.

The canonical internal product comparison already has exactly the counit and
composition maps in the desired formula. The direct route therefore avoids
transporting the trace across continuous coefficient encodings, the spectral
norm, universe lifts, and the equivalent small site. The named dependencies
remain needed elsewhere, including the unit's integral-image step; no global
pruning of them is claimed.

`lem-weil-pbc-finite-etale-etale-local-split` is no longer a direct dependency of
the item; it is retained in the new generic descent node. The formula and product
comparison nodes remain direct dependencies. The unit's own statement and every
realized step are retained.

## Where the brief, the DAG or earlier work was wrong

The previous DAG proof describes a valid mathematical route but its encoding
restriction theorem only gives an objectwise `Nonempty` presheaf isomorphism.
It does not provide the natural inverse/direct-image comparison, adjunction
normalization, and composition coherence needed to transport the exact counit
formula by a single application. The existing sectionwise trace theorem is proved;
its different module model is the missing bridge, not an unproved trace theorem.

The original inline formula also caused kernel reduction through the large
composition/adjunction construction when comparing normalized sums. A typed
let-bound family alone did not resolve the kernel timeout. The shared comparison
has a fully proved exact equation, and the shared sum constructor removes the
conversion between separately elaborated sums. The remaining raw-chart conversion
also timed out; using the same chart structure in the predicate and descent
removes that conversion while retaining exactly the original mathematical data.

The new route stays internal and makes the unresolved steps explicit. Neither
new theorem restates existence of a trace: one glues arbitrary compatible maps
between arbitrary internal modules, and the other is a coherence equality for
explicitly constructed finite sums, even without finiteness, etaleness or
surjectivity of p. The original theorem requires their real combination and the
proved local right inverses.

Edge cases checked: a non-surjective finite etale map still has a covering by
splitting charts, some with zero sheets, so the generic descent theorem does not
need surjectivity. Overlap compatibility includes empty splittings and different
sheet counts on empty components. Local epimorphy uses surjectivity only in the
zero-sheet case. The zero module and empty base need no excluded rank or
characteristic. All statements concern arbitrary internal modules.

## New nodes

`lem-sfb-finite-etale-split-hom-descent` gives morphism descent on finite splitting
charts and descent of local epimorphy. Its proof plan uses the existing finite
etale splitting, weakly etale localization, internal section-module equivalence,
profinite-point comparison, and proved `SheafOfModules.existsUnique_hom_of_cover`.
Sources read: Stacks `sites.tex`, lemma-glue-maps (04TQ), and
`sites-modules.tex`, lemma-internal-hom (03EM), plus the current blueprint trace
proof. The remaining work is to connect the specified internal inverse images
and their comparisons to localized linear sheaf morphisms and apply gluing.

`lem-sfb-finite-etale-sheet-sum-compatible` states overlap compatibility of the
actual counit sums. Its proof plan uses the proved
`finiteSectionCoproduct_local_permutation`, the profinite-point comparison,
weakly etale localization, and separatedness. Sources read: Stacks
`etale-cohomology.tex`, section-trace-method (03SH), the current blueprint local
trace computation, and the local-permutation declaration and proof. Its remaining
work is the pullback/counit coherence calculation and local reindexing.

Both new statements have full proof docstrings and node records. Searches used
LeanSearch, LeanFinder and Mathlib grep; existing module-map gluing was identified
and reused in the descent plan. Blueprint searches for trace, splitting and linear
homomorphisms found no duplicate of these two internal comparison statements.
The definition presentation change is recorded in
`coord/changes/M9-finite-etale-trace-formula-comparison-family.md`. Its users table
lists every module reported by the downstream declaration search. No source-library
module or another group's proof is changed.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
