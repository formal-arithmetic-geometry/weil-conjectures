## What changed

Replaced the single sorry in
`WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity` by a compiling reduction.
The proof constructs the diagram `E_j = W ×_R D_j`, its cone with apex `W ×_R c.pt`,
and the structure maps to R. It proves the limit property using connectedness and
cartesian projection squares, and proves qcqs and affine-transition hypotheses by
base change. It then transfers representatives and eventual zero witnesses from
absolute global sections, using additive equivalences and their naturality.

Added two proof-only imports for two independent parts of the argument:
`Sheaf.AlgebraicGeometry.GlobalSectionsLimitComparison` and
`Sheaf.AlgebraicGeometry.PullbackSectionsComparison`. The latter explicitly constructs
`pullbackSectionsEquiv` using direct-image evaluation, étale restriction, terminal
evaluation, and inverse-image composition. Its data contains no sorry.
The original module's declarations, universes, hypotheses and conclusions are unchanged.
The extra Mathlib imports and the upstream pullback-square import support the actual
base-change proof; no public import of the original module was added or removed.

## Proved and sorry left

The original `AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit` is proved
from the two named intermediate theorems. Its surjectivity and zero-detection corollaries
continue to use it unchanged. There is no sorry left in the original module.

The two remaining sorries added by this delivery are:

- `AlgebraicGeometry.Etale.globalSections_limit_comparison`, node
  `lem-weil-pbc-global-sections-limit-comparison`: absolute global-section continuity,
  independent of W or pushforward evaluation. Its source is 09YQ in degree zero;
  the docstring explains coinitial directed reindexing and the degree-zero bridge.
- `AlgebraicGeometry.Etale.pullbackSections_comparison`, node
  `lem-weil-pbc-pullback-sections-comparison`: naturality of the explicit equivalence
  for a single cartesian square. It has no limit, qcqs, or affine hypotheses.
  The equivalence itself is implemented, and only its compatibility equation remains.

These are separate parts of the argument, not either conjunct of the original theorem
under a new name. The original module proves the base-change limit and hypotheses,
then combines both parts to produce the witnesses with the original transition maps.
This is a reduction, not an axiom-free proof of continuity.

Edge cases checked mathematically: the zero sheaf and empty W give zero groups;
a singleton identity system gives identity comparisons; arbitrary non-thin cofiltered
index categories require the directed-reindexing step in the global lemma.
The section comparison imposes both projection equations on m, so its claimed
naturality concerns exactly the canonical cartesian map, even for non-separated W.

## No longer needed

The original module removes these proof-only imports:

- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
- `Sheaf.Paper.EtaleRestrictionPullbackUnit`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`

The cohomology, degree-zero, functoriality, inverse-image coherence, and restriction-unit
imports are moved to the new bridge modules as plain proof imports. Direct-image,
inverse-image, restriction, and global-section definitions remain available through
public imports required by the new statements and equivalence. The derived lower-shriek
and topological-invariance imports remain reachable through the cohomology bridge's
existing dependencies; they are not claimed globally pruned.

The original dependency `lem-weil-pbc-limit-affine-transition` and module
`Sheaf.AlgebraicGeometry.LimitAffineTransition` are unnecessary for this proof: the
limit cone is already given, and affine limit projections are not required.
The direct import of `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
for `lem-weil-pbc-scheme-over-limit` is unnecessary: the relative limit property is
proved directly using `isLimitOfIsPullbackOfIsConnected` and the pullback squares.
This does not claim either module is globally unreachable from all five targets.

The remaining old proof dependencies are still needed in the geometric construction or
transitively in the two intermediate arguments (inverse-image composition and coherence, degree-zero
cohomology, cohomology continuity, connected constant colimits, restriction and
pullback-unit compatibility, and the elementwise filtered-colimit criterion).
They have not been pruned or replaced by assumptions. The earlier pruning of
`lem-weil-pbc-etale-finite-data-descent` is retained: it is not reimported here.

## Where the brief, the DAG or earlier work was wrong

The existing cohomology-limit statement is indexed by a directed preorder, while the
source module quantifies over an arbitrary small cofiltered category. The global
bridge records the needed coinitial directed reindexing (existing Mathlib leaf
`lem-weil-pbc-cofiltered-limit-directed-reindex`) rather than silently applying the
preorder theorem to J. The nearby `cohomology_continuity_of_isLimit` also assumes
that the sheaf is torsion and cannot be applied to the arbitrary G of this item.

The existing node's stated route is mathematically usable but its interfaces require
substantial global-sections and restriction glue. The two new nodes isolate that glue
and the original module implements the geometric reduction and element transfer.
The unit record `sk-prop-h2` has no realized statement or step bound to this helper;
its Kummer route is unaffected.

Mathlib searches were run through msearch.py. LeanSearch returned HTTP 500 and is
recorded as unavailable. Loogle and grep found no exact match; LeanFinder found
structure-sheaf continuity, which does not apply to arbitrary étale sheaves.
Existing upstream and Sheaf modules were also searched before introducing the bridges.
The cited Stacks tags 09YQ, 0032, 03CF and 03EF were read on the Stacks website because
the literature files themselves are absent in this read-only checkout.

## New nodes

`lem-weil-pbc-global-sections-limit-comparison` records steps 2–3 and the absolute
part of the earlier route: a fixed pullback sheaf on a cofiltered limit. Its proof
names the existing cohomology-limit, degree-zero, coherence, and reindexing nodes.
Its Lean module is `Sheaf.AlgebraicGeometry.GlobalSectionsLimitComparison`.

`lem-weil-pbc-pullback-sections-comparison` records the comparison in step 4, for a
single triangle and its cartesian base change. Its Lean module
`Sheaf.AlgebraicGeometry.PullbackSectionsComparison` includes the explicit additive
equivalence and leaves only its naturality equation. No existing statement or
public definition was changed, so there is no change record.


## Second reading by P1

1. **Existing interfaces: PASS.** Compared all three delivered modules with the checkout;
   the two Sheaf modules are new. The original module's existing declaration signatures,
   universe and variable blocks, definition body, and corollary bodies are byte-for-byte
   unchanged. Only its proof imports, module commentary, local elaboration options, and
   the main theorem's proof changed. No change record is required.
2. **Proof and axioms: PASS as a reduction.** Compiled all three modules together through
   lcompile.py. A scratch copy with #print axioms checks all eight public declarations:
   unitComparison, unit compatibility, and pullbackSectionsEquiv use only propext,
   Classical.choice, and Quot.sound. The main continuity theorem, its two corollaries,
   and the two named open bridges additionally use sorryAx, as reported. There are no
   forbidden declarations or hollow definitions; exactly the two documented named
   theorems retain sorry. This delivery does not close continuity's axiom dependency.
3. **Split statements: PASS.** Read both full signatures and docstring proofs. The absolute
   lemma is degree zero of [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ), with
   the coinitial directed reindexing justified by
   [Stacks 0032](https://stacks.math.columbia.edu/tag/0032); neither imposes torsion.
   It isolates the global case, while the original proof implements the geometric
   reduction for arbitrary qcqs etale W. The comparison lemma concerns one cartesian
   square and the implemented equivalence; it has no limit hypotheses. Neither merely
   renames the original item. Checked the zero sheaf, empty W, identity singleton
   diagram, arbitrary non-thin cofiltered categories, and identity/composite cartesian
   maps mathematically. Projection equations determine m uniquely, including for
   non-separated W. Independent LeanFinder search for inverse-limit section descent
   found only structure-sheaf continuity, not arbitrary etale sheaves; Loogle for the
   upstream global-section map was unavailable for that non-Mathlib identifier; grep
   for upperStar/restriction found no Mathlib duplicate. Repository searches and reading
   EtaleCohomologyLimitOfSchemes, EtaleCohomologyPullbackDegreeZero,
   EtaleRestrictionPullbackUnit, and LimitPullbackSectionsColimit found no matching
   existing bridge. The last lemma needs modules, a directed preorder, and affine W.
4. **Route and pruning: PASS after repair.** Read the pullback diagram, connected-limit
   argument, qcqs/affine instances, and both witness transfers from top to bottom.
   The global theorem and single-square naturality are separate remaining parts; the
   existing cohomology and restriction-unit interfaces still need this glue. Neither
   bridge has a proof that can be completed in a few minutes from those interfaces.
   sk-prop-h2.realized has no entry for this helper; its Kummer route is preserved.
   Corrected the removed-import inventory above. The old direct proof dependencies
   no longer required are lem-weil-pbc-limit-affine-transition and
   lem-weil-pbc-scheme-over-limit (the latter replaced by the connected-pullback limit
   theorem). The base-change finite-limits, scheme conventions, etale morphism,
   inverse-image and cohomology definition dependencies remain used through existing
   definitions/instances or the new bridge routes. No global unreachability is claimed.
5. **DAG: PASS after repair.** Checked each proof_deps union against its proof steps,
   source, chapter/unit, blueprint provenance, searches, and created/lean records.
   The existing node describes the actual implemented reduction; its sorry_free=false
   correctly records the remaining axiom dependence. Added the bridge route's plain
   imports so its stated open dependencies remain in the target import closure rather
   than disappearing from the queue. Updated both new nodes' Lean statement records
   to literal multiline signatures.

Changes by this second reader: added only plain proof imports to the two new bridge
modules; corrected the report's removed-import inventory and clarified direct versus
transitive pruning; recorded literal new-node signatures. Existing statements,
definitions, and the compiling reduction were preserved.
