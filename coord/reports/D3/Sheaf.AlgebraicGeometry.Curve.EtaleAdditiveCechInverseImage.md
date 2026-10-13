## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.exists_etaleAdditive_cech_inverseImage`
without changing its signature. Its proof now chooses two normalized edge equivalences,
applies their scalar laws, chooses a source representative using the epimorphic
homology projection, constructs a target cycle using the existing ordinary refined-cover
cochain map, and applies the normalized inverse-image class law.

The ordinary cycle construction is fully proved, in private helpers
`additiveOrdinaryCechIso`, `additiveOrdinaryCyclesIso`,
`additiveOrdinaryCyclesIso_i`, and `exists_additiveOrdinary_cycle_transfer`.
It transports module Čech cycles through the exact forgetful functor and the explicit
abelian Čech complex, applies `cechInverseImageCochainMap`, and transports back.
The coordinate formula follows from `cyclesMap_i` and the inverse cycle isomorphism.
No ordinary Ext inverse-image comparison is invoked.

Added `EtaleAdditiveCechNormalization`, containing only real constructions: the
open-subscheme étale inclusion, global and total resolution complexes, the alpha
restriction augmentation components, the beta coefficient augmentation components,
and their normalization predicate. Alpha and beta use the actual restrictions,
`restrictFunctorΓ.inv`, resolution augmentation and total summand inclusions.
No existence witness is chosen in a definition. Normalization quantifies over every
resolution and its normalized Ext-to-sections comparison; it does not stipulate
scalar or inverse-image compatibility.

Added three one-theorem modules for the missing parts of the existing plan:
`EtaleAdditiveCechNormalizedExistence`, `EtaleAdditiveCechNormalizedScalar`, and
`EtaleAdditiveCechNormalizedInverseImage`. Each theorem has its source and a full
proof in words, and its own DAG node. The item's node now follows the actual Lean proof.
All five modules compile together through `lcompile.py --all`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_etaleAdditive_cech_inverseImage`
(node `lem-pbc-etale-additive-cech-inverse-image`). The item's module has no remaining
`sorry`. Its four private helpers are completely proved.

Added exactly three named holes:

- `AlgebraicGeometry.Scheme.Modules.exists_etaleAdditiveCech_normalized`
  (`lem-pbc-etale-additive-cech-normalized-existence`): one-scheme existence,
  with no endomorphisms or scheme morphism.
- `AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_normalized_scalar`
  (`lem-pbc-etale-additive-cech-normalized-scalar`): only scalar compatibility
  for a supplied normalized edge equivalence.
- `AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_normalized_inverseImage`
  (`lem-pbc-etale-additive-cech-normalized-inverse-image`): only the class law
  for two supplied normalized edge equivalences and already matched cycles;
  it asserts neither existence of equivalences nor existence of representatives.

This is a decomposition, not a sorry-free proof of the étale comparison.
The delivery closes one upper hole and adds three lower holes (net -2 before any
independent subsequent work). The cochain-level cycle construction is proved here.
The normalization module contains no holes. No other existing module is adapted.

## No longer needed

Removed direct proof imports from the item's module:
`Sheaf.AlgebraicGeometry.EtaleTensorUnitSectionsNatural`,
`Sheaf.AlgebraicGeometry.EtaleQcoherentULiftFiniteCechComparison`,
`Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalData`, and
`Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalTransfer`.
They are retained in the new lower theorem modules where their arguments are needed.
Consequently none of these four nodes or modules is claimed as globally pruned.
The old proof-dependency nodes removed from the item's direct proof route are
`lem-sc-etale-tensor-unit-sections-natural`,
`lem-sc-etale-qcoherent-ulift-finite-cech-comparison`,
`lem-weil-pbc-etale-resolution-section-canonical-data`, and
`lem-weil-pbc-etale-resolution-section-canonical-transfer`.
All four remain dependencies of the lower theorem modules.
No module or node is globally pruned by this decomposition.

Added proof imports for the three normalized-edge theorem modules and
`CechComparisonSystem` / `CechInverseImageCochainMap`, whose ordinary coefficient
and cycle transport interfaces are used by the fully proved helpers.
The item's public imports and all pre-existing signatures are unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no interface change was needed. The original
plan's description of normalized augmented comparisons was mathematically needed,
but its imported finite Čech theorem only supplied a bare Nonempty equivalence;
it did not supply the alpha/beta normalization or either compatibility law.
The canonical resolution data and transfer statements normalize global resolution
homology, not the edge from it to finite section Čech homology. Those missing
parts are now separate statements rather than an unjustified choice of a natural
comparison. The unit `sk-thm-p1` and its realized curve-calculation route are unchanged.

The proof imports the already existing cochain map, rather than restating the
coordinate transfer. Empty tuple-index types, empty intersections, degree zero,
identity morphisms and scalar zero/one were checked against the normalization and
proof plans. No flatness or affineness hypothesis on g has been introduced.
LeanSearch was unavailable (Internal Server Error). LeanFinder, Loogle, library /
Mathlib grep, and blueprint searches found the ordinary cochain transport APIs
but no theorem supplying the fixed lifted additive normalized edge laws.

## New nodes

`def-pbc-etale-additive-cech-normalization` records the concrete augmentation
components and their class-equation normalization, in
`Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization`.

`lem-pbc-etale-additive-cech-normalized-existence` isolates the one-scheme
quasi-isomorphism computation and its resolution-independent normalization.

`lem-pbc-etale-additive-cech-normalized-scalar` isolates coefficient multiplication
compatibility of a supplied normalized comparison.

`lem-pbc-etale-additive-cech-normalized-inverse-image` isolates the augmented
refinement diagram's inverse-image class identity for supplied matching cycles.

All four nodes inherit the item's chapter and unit and its blueprint ancestry.
Their sources are Stacks Tags 03P2, 01EQ and 01FD; searches are recorded in each.
There are no change records, because no existing statement or definition changes.

## Second reading by D3

1. Interface: PASS. Compared the original item module with the sandbox using
   `diff -u` and checked its sole existing theorem signature byte for byte.
   Every hypothesis and conclusion is unchanged, including universes, arbitrary g,
   degree zero, the multiplication formulas, and the representative coordinates.
   The three public imports are unchanged. The four other modules and their four
   nodes are new; there are no adaptations or interface change records.

2. Proof and constructions: PASS as a decomposition. All five modules compiled
   with `lcompile.py --all`. Explicit `#print axioms` checks on scratch copies
   showed only propext, Classical.choice and Quot.sound for all six normalization
   constructions and all four private ordinary-cycle helpers. The original theorem
   and each of the three named lower holes additionally use sorryAx, as reported.
   The ordinary transfer is an actual cochain map followed by cyclesMap and an
   inverse cycles isomorphism; its coordinate equation follows from cyclesMap_i.
   All three remaining sorries are entire named theorem proofs with docstrings
   and nodes. No forbidden declaration or data chosen from an existence theorem
   occurs in a delivered definition.

3. Lower statements: PASS. Read the explicit alpha at (0,n), beta at (n,0),
   the total differential sign convention, and the canonical comparison's
   global_cocycle field. Read Stacks [03P2](https://stacks.math.columbia.edu/tag/03P2),
   [01EQ](https://stacks.math.columbia.edu/tag/01EQ), and
   [01FD](https://stacks.math.columbia.edu/tag/01FD). The first supplies affine
   quasi-coherent acyclicity; the second constructs the two augmentations; the
   third compares their maps under refinement. These arguments apply to the
   lifted section groups on the small etale site, as explained in the docstrings.
   Normalization is not an assumed compatibility law: alpha and beta are actual
   section maps. Their quasi-isomorphisms make every class admit a matching pair,
   and the canonical comparison's extMk field fixes the global identification.
   Thus the predicate determines a, rather than being an arbitrary naturality
   assumption. Existence uses one scheme only; scalar compatibility uses one
   given normalized edge; inverse-image compatibility uses two given edges and
   matched cycles. Each is strictly part of the original argument. The target
   representative is independently constructed in the proved ordinary transfer.
   Checked n=0 by gluing; empty tuple-index families and empty intersections by
   zero section groups; scalar zero/one by the coefficient formula; identity g
   by restriction. No flatness, affineness of g or positive-degree restriction is
   required. Independent LeanFinder, Loogle and Mathlib grep searches used
   augmentation/edge/coefficients terminology, and library/upstream grep checked
   additive etale Cech comparisons. No exact normalized-edge theorem was found.
   None of the three holes can be closed by the existing bare Nonempty finite
   Cech comparison: its type supplies no augmentation equation. Their full
   augmented-complex proofs remain open rather than being asserted proved.

4. Top-down route and pruning: PASS. Read the original four proof dependencies
   and their Lean interfaces. The proof separates their missing normalization
   laws, uses the existing ordinary cochain map, and obtains source representatives
   from the epimorphic homology projection. The proof-only imports serve these
   steps; the normalization module's public imports supply its definitions and
   signatures, including the total-complex instance. The old direct dependencies
   all remain in the lower modules, so no global pruning is claimed. Read
   dag/units/sk-thm-p1.json, including realized.statement and all realized.steps:
   the curve-calculation / Artin-Schreier route is retained and no unit is bypassed.
   One original hole is closed syntactically and three lower holes are added;
   this is a decomposition with net -2, not a completed etale comparison proof.

5. DAG: PASS. Matched every node's Lean signature against its module, checked
   that proof_deps is the union of proof-step uses and that all dependency IDs
   exist. The item's steps match the existence/scalar assembly, proved ordinary
   cycle transfer, and inverse-image class-law application. The four new nodes
   have the required source, searches, status, created, blueprint, chapter/unit,
   and Lean records; no existing node's mathematical statement is changed.

Second-reading changes: made the four removed direct dependency node IDs explicit
under No longer needed, added the independent search records to the four new
nodes, and appended this review with the axiom evidence and decomposition verdict.
No Lean repair was needed and no signature or definition was changed.
