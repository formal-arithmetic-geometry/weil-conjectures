## What changed

Repaired the returned delivery by deleting the duplicate private theorem
`AlgebraicGeometry.constructible_baseChange_eventually`. The main module now imports
`Sheaf.AlgebraicGeometry.AffineEtaleCoveringEventually` and uses its public theorem
`AlgebraicGeometry.Scheme.affineEtale_covering_eventually`.

The private `canonical_covering_eventually` helper lifts the canonical pullback functors
into the full affine etale categories, constructs their natural first projections, supplies
the canonical pullback squares, and converts between finite precoverage and sieve covering.
Its qcqs diagram hypotheses come from the unchanged main theorem. No existing public
signature, definition or visibility changed; no forced adaptation is required.

The other two modules retain the delivered reduction: `EtaleFactorizationDataBaseChange`
constructs transported arrows and proves their equations by pullback coherence;
`EtaleFiniteFactorizationDataDescent` isolates simultaneous source and two-arrow descent
without a covering hypothesis or conclusion. Updated the main node's proof metadata to
record the existing eventual-covering theorem actually used. The second reader restored
the open data module's planned site-colimit and base-change-limit imports, corrected
its non-affine target descent citation to an existing Mathlib leaf, and removed the
transport node's unused pasting citation.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.etale_finiteCoverFactorizationDescent`
(node `lem-weil-pbc-etale-finite-cover-factorization-descent`). This remains a decomposition:
one upper hole is replaced by one strictly smaller geometric hole.

Proved `AlgebraicGeometry.etale_factorizationData_baseChange`
(node `lem-weil-pbc-etale-factorization-data-base-change`) and private helpers
`pullback_triangle_coherence`, `canonical_covering_eventually`, and `covering_of_iso`.
The duplicate helper `constructible_baseChange_eventually` was deleted, rather than counted
as newly proved.

The only sorry left in the delivery is
`AlgebraicGeometry.etale_finiteFactorizationDataDescent`
(node `lem-weil-pbc-etale-finite-factorization-data-descent`), with source and full proof
in words in its docstring and node. Holes closed: 1; holes added: 1; net: 0.
No definition or private helper contains sorry.

Validation: all three modules compile together with lcompile.py without errors or warnings.
The main proof preserves empty families and arbitrary non-affine auxiliary targets.
The transported models are explicitly constructed; descent witnesses are eliminated only
inside a theorem proof. The required deliver3.py --no-push check is run on this repair.

## No longer needed


Against the repository's current main node, the complete removed direct proof-dependency
list is `lem-weil-pbc-affine-etale-site-colimit`,
`lem-weil-pbc-cartesian-square-pasting`, `lem-weil-pbc-scheme-over-limit`, and
`thm-pd-spreading-out`. The first three remain below the open data-descent node;
spreading-out remains below affine site colimit. The original direct dependency
`lem-weil-pbc-affine-etale-covering-eventually` is retained. The transport node's
unused `lem-weil-pbc-cartesian-square-pasting` dependency is also removed: its Lean
proof is a direct pullback-projection and naturality calculation. None of these
changes establishes whole-library pruning.


Removed the proof-only imports `LimitContainedInConstructible` and
`Mathlib.AlgebraicGeometry.PullbackCarrier` from the returned main module. The former's
constructible-image argument is already proved inside the imported eventual-covering module;
neither module is claimed pruned from the overall import closure.

`AffineEtaleCoveringEventually` and node
`lem-weil-pbc-affine-etale-covering-eventually` are retained and used, correcting the previous
report's pruning claim. The main node no longer directly lists
`lem-weil-pbc-chevalley-constructible-image`, `lem-weil-pbc-limit-contained-in-constructible`,
`lem-weil-pbc-cartesian-square-pasting`, or `lem-weil-pbc-fibre-product-points` as proof
steps: covering geometry is supplied by the existing public theorem, and pullback coherence
is supplied by the proved transport module. These results remain needed transitively.

The original main module's `AffineEtaleSiteColimit` import is removed in favor of the
strictly smaller data-descent module; site colimit remains below
that open data-descent node, and are not claimed globally pruned. `FullAffineEtaleSite`
remains the public signature import. `AffineTransitionLimit` remains needed for affine
cone projections. No whole library module is claimed pruned by this repair.

The unlanded old case modules `EtaleFiniteCoverFactorizationDescentZero` and
`EtaleFiniteCoverFactorizationDescentPositive` and their case nodes remain absent.
The unit's realized statement and steps remain untouched.

## Where the brief, the DAG or earlier work was wrong

The landing return correctly identified that the earlier delivery copied the private
constructible-base-change proof from `AffineEtaleCoveringEventually`. That proof has been
removed completely. Since its original declaration is private, the repaired proof instead
uses the module's public eventual-covering theorem through canonical full affine functors.
It does not change another group's interface or refer to a private implementation name.

The earlier report incorrectly said the eventual-covering package was unnecessary. The
repaired report and DAG now record its use. The previous second reading predates this repair;
a fresh second reading is required and has not been written by this worker.

The remaining data-descent theorem is strictly the object-and-arrow part of the sourced
argument. The wrapper proves covering and further transport from those witnesses.
The source citations and object-descent plan are retained from the delivered node. No
new source reading or closure of the remaining hole is claimed in this repair.

## New nodes

`lem-weil-pbc-etale-finite-factorization-data-descent` in
`Sheaf.AlgebraicGeometry.EtaleFiniteFactorizationDataDescent`: simultaneous affine source
and two-arrow descent, without any covering input or output; the one remaining hole.

`lem-weil-pbc-etale-factorization-data-base-change` in
`Sheaf.AlgebraicGeometry.EtaleFactorizationDataBaseChange`: proved construction of later
arrows, source comparisons and both compatibility equations. These two nodes are retained
from the returned delivery. No additional node or change record is introduced by the repair.


## Second reading by P1

1. **Interface unchanged — pass.** Compared the main module with the repository by
   `diff -u` and checked its complete theorem signature byte for byte. The only existing
   public declaration is `AlgebraicGeometry.etale_finiteCoverFactorizationDescent`; its
   parameters, hypotheses, let-bound comparisons and four conclusions are identical.
   The two auxiliary modules are new. No definitions, target statements, existing
   visibility or public imports changed. Relevant import change records for
   `AffineEtaleSiteColimit` and its dependencies require no adaptation here.

2. **Proof and trust checks — pass, with one declared hole.** Compiled the three modules
   in import order with `lcompile.py`. Scratch copies printed the axioms of every
   delivered theorem, including the private `pullback_triangle_coherence`,
   `canonical_covering_eventually` and `covering_of_iso`. Those helpers and
   `etale_factorizationData_baseChange` use only `propext`, `Classical.choice`,
   `Quot.sound`. The main theorem and `etale_finiteFactorizationDataDescent` additionally
   use `sorryAx`, as expected from the named open geometric theorem. A source scan found
   exactly that one `:= by sorry`, no forbidden declaration or attribute, and no hollow
   definition. In particular T, P, ak, bk, dk and tw are explicit constructions. The
   existential descent witnesses are eliminated within a Prop proof, never used to
   define an arbitrary object for downstream use.

3. **New statements — pass after correcting a citation.** Read both new modules and
   their nodes against [0EYL](https://stacks.math.columbia.edu/tag/0EYL), qcqs proof,
   [01ZM](https://stacks.math.columbia.edu/tag/01ZM),
   [01ZC](https://stacks.math.columbia.edu/tag/01ZC), clause (3), and
   [01YZ](https://stacks.math.columbia.edu/tag/01YZ). Data descent keeps precisely the
   source models, both arrows, affineness and common source comparisons; it drops both
   covering input and covering output. The wrapper supplies the separate covering
   argument, so this is strictly a subproblem rather than a relabelled original theorem.
   For n=0 the data lemma takes the identity stage and empty families; the wrapper uses
   eventual covering of the empty family to force an empty later target. For one source,
   identity transitions, an empty source, and arbitrary non-affine U_q the construction
   and descent argument retain their stated meaning. Étaleness of U_q supplies local
   finite presentation; it does not supply quasi-compactness. The old citation of
   `thm-pd-spreading-out` could not justify descent to such a U_q. Replaced it with the
   existing Mathlib leaf `lem-weil-pbc-finite-presentation-map-limit-factorization`,
   whose declaration was read at Mathlib `AffineTransitionLimit.lean:1232`.
   Fresh Lean Finder, Loogle and Mathlib grep searches, plus `rg` in lean/Sheaf,
   lean/WeilConjectures and the upstream AlgebraicGeometry sources, found morphism
   descent tools and `affineEtale_finite_diagram_descent`, but no simultaneous
   two-target statement allowing non-affine U_q. Closing the remaining theorem needs
   the geometric source-and-arrow descent construction; no quick missing tactic or
   existing exact theorem was found.

4. **Route and pruning — pass after restoring planned imports.** Followed the main
   proof from its conclusion: the source/target isomorphisms transfer the limit cover;
   `canonical_covering_eventually` applies the existing public
   `Scheme.affineEtale_covering_eventually` to explicitly constructed full affine
   pullback functors and projection natural transformations; further transport uses
   the proved `etale_factorizationData_baseChange`. The latter proves associativity
   by comparing pullback projections, then uses naturality for each arrow equation.
   No constructible-image proof is copied. FullAffineEtaleSite supplies signatures;
   the other imports are proof-only. Restored the open data module's planned imports
   of `AffineEtaleSiteColimit` and `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`:
   its docstring and node use their object/arrow descent and base-change limit facts.
   Thus removing the direct site-colimit import from the main module does not claim
   to prune that dependency. Read `dag/units/sk-thm-iff.json`; its realized statement
   and step are `lemma-weil-pbc-property-iff-acyclicity`, untouched by this lower-level
   reduction. The chapter's degree-zero continuity route is retained.

5. **DAG agreement — pass after repair.** Checked all three node signatures against
   their Lean declarations and each proof_deps list against the union of step uses.
   The main node records data descent, the existing eventual-covering theorem and
   proved further transport in exactly the order used by Lean. Corrected the data
   node's second step to cite the existing 01ZC Mathlib leaf rather than the narrower
   finite-presentation theorem. The transport proof uses the definitions and projection
   identities of `MorphismProperty.Over.pullbackComp`, followed by naturality; it does
   not apply `IsPullback.paste_vert_iff`. Marked its two projection/universal-property
   steps elementary and removed that unused proof dependency. New-node provenance,
   sources, Lean records and recorded first-worker searches are retained. No new node,
   changed statement or change record is introduced by this reading.

Second-reading changes: restored two proof-dependency imports in the open data module;
corrected its arbitrary-target morphism-descent citation; removed the transport node's
unused pasting citation; completed the direct-dependency accounting below. Lean proof
bodies required no repair. The delivery remains one original hole closed and one named
strictly smaller hole added, net zero, with no whole-library pruning claimed.
