## What changed

Replaced the final proof hole of `WeilConjectures.IntegralOnSlice.qcqsCompletionUnitLocality` with the three-clause assembly. Its signature is byte-for-byte unchanged. The canonical-unit criterion uses the already proved `roosIntrinsicCompletenessEquivalence` on a good representative, with auxiliary prime 3 or 2, and requires no finiteness or invertibility hypothesis on the scheme.

The restriction assembly proves the finite coefficient projection equation by adjunction naturality. The comparison-descent proof constructs the derived completion comparison by fully faithful restriction along good localization, and uses both prescribed Roos coordinates to identify the actual chain unit, then the ordinary derived counit's naturality and invertibility, the two unit normalizations and good localization to prove the specified derived-unit square. It gives preservation of completeness and the corresponding isomorphism test for a weakly etale arrow followed by an immersion.

The descent step is proved once for an arbitrary fully faithful restriction functor, avoiding repeated expansion of the concrete completion functors during elaboration. A private natural counit isomorphism and its component lemma keep the chosen total-derived construction behind a proved API. The full conjugation calculation is a private theorem over abstract categories and functors, instantiated with the concrete good localization; this avoids kernel expansion of ringed coefficient functors. The assembly treats the existing construction functors as locally irreducible, using their comparison API instead of expanding Kan extensions and chosen total derived functors. `qGood` stays reducible where its representative equation needs its defining object equality.

Preservation of good representatives is transported from the existing `IntegralAmbient.pull_good` through the proved ordinary/ambient comparison; K-flatness and flat terms are invariant under complex isomorphism. The empty-derived-category case is proved directly from terminal sections on the empty scheme.

The finite-tree proof is a strong induction on `d - v.val`. It uses cover conservativity at nonempty leaves, the empty derived category at empty leaves, and open–closed reflection at internal vertices. The root isomorphism detects the original unit. The normalized composite restriction comparison and the canonical-unit criterion give the completeness equivalence.

The 22 existing ordinary-model declarations are moved verbatim into `QcqsCompletionOrdinaryModels` and publicly re-exported by the item module; only their blueprint doc references change. This makes the models available to the separate results without an import cycle. A refreshed downstream check finds seven consumers, listed with current holders in the change record; their interfaces are unchanged and no consumer adaptation is needed. No source-library declaration or target is changed, and no existing construction is replaced by a choice from an unproved existence theorem. The new existence theorems are eliminated inside proofs only.

## Proved and sorry left

Original holes closed: `WeilConjectures.IntegralOnSlice.qcqsCompletionUnitLocality` (1 of 1). This is a decomposition, not a net proof closure: two separate source results remain as named theorem holes.

Added holes:

- `WeilConjectures.IntegralOnSlice.qcqsOrdinaryRestrictionModels` (`lem-fix-qcqs-ordinary-restriction-models`): exactness/coefficient identification, normalized strict quotient/Roos chain comparisons for composite weakly etale/immersion restriction. This is source steps 2–4, omitting the unit square, completeness and every locality conclusion; those are proved separately.
- `WeilConjectures.IntegralOnSlice.qcqsOrdinaryLocalDetection` (`lem-fix-qcqs-ordinary-local-detection`): conservativity tests for arbitrary derived morphisms under isomorphism, open–closed and covering restrictions. This is source steps 5–6 and their isomorphism endpoint; it contains no completion unit or finite tree.

The added theorems have exactly `:= by sorry`, each in its own module, with a full source proof in its docstring and matching node. The criterion, comparison-unit descent, coefficient projection, restriction assembly, composite-unit test, finite-tree induction and main assembly contain no holes. The relocated construction block adds zero holes and preserves all previous proofs. Validation: all eight packet modules compiled successfully on the project server in dependency order. A local unused-binder linter setting preserves the original finite-tree signature verbatim. The required delivery preflight is the final check. The K-flat/flat-term transport and empty-derived-category helpers were also compiled independently. Net explicit hole change for this packet: 1 closed, 2 added, hence -1; it is reported honestly as a decomposition.

## No longer needed

The criterion uses the proved `PrincipalKoszulStrictReplacement.coefficient_datum` directly, so it needs neither the larger `lem-sf-open-quotient-koszul-completeness` statement nor `prop-weil-pbc-koszul-reconstruction`: the existing stronger, independent-universe `lem-pur-roos-intrinsic-completeness-equivalence` identifies exactly the specified unit. The obsolete parent tool-use entries for these two dependencies are removed. Its source declaration and module remain untouched.

All other original planned dependencies remain needed by the two source subresults, as their nodes record; none is claimed pruned merely because a proof module currently has no importer. In particular the exact-product, coefficient, ringed open–closed, cohomology and sheaf-cover results are retained. No Lean module is withdrawn. Whole-blueprint searches for “completion locality” and “ordinary restriction” found no exact replacement statement; the recorded ancestor is `lem-fix-weil-operations`, and its unit realizes no prescribed statement or proof step here.

The following direct imports are removed from the theorem module; its public support-module import re-exports all original public statement imports and keeps the proof imports with the moved constructions:

- `Sheaf.Paper.OrdinaryCompletedIntegralPullback`
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`
- `Mathlib.CategoryTheory.Functor.Derived.LeftDerived`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses`
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`
- `Sheaf.Paper.IntegralAmbientOperationModels`
- `Sheaf.CategoryTheory.ContinuousRingedToposModuleDirectImage`
- `Sheaf.CategoryTheory.RingedToposKFlatPullback`
- `WeilConjectures.Algebra.Homology.KFlatResolution`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.Flat`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.LeftDerivedEquivalence`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`

## Where the brief, the DAG or earlier work was wrong

The unit criterion uses `lem-a1-principal-koszul-strict-replacement` and `lem-pur-roos-intrinsic-completeness-equivalence` as existing tools; the former supplies only the coefficient datum and the latter exactly the specified unit criterion. The restriction proof uses `lem-pur-integral-ambient-operation-models` only for its existing `pull_good` declaration. These replace missing interface glue rather than bypassing a realized unit step.

The old first proof step takes a longer route than needed: the existing intrinsic Roos/Koszul equivalence already compares exactly this unit, with independent scheme/coefficient universes. The coefficient projection formula also follows from the existing completed map and adjunction without any geometric hypothesis.

The geometric dependencies' available inverse-image interfaces frequently specialize the coefficient universe to the scheme universe plus one, whereas this item deliberately has independent universes. Moreover the strict derived-tower result does not itself state the actual chain-level `tau`, both normalized `chi` coordinates and the chosen derived counit equation required here. The new restriction-model result records that precise remaining source argument. The derived counit equation is now proved by localization rather than retained in that result. Similarly the original general open–closed and cover lemmas do not already identify the item's actual ordinary composite restrictions. The local-detection result makes those comparisons and conservativity explicit.

Checked edge cases in the source arguments and assembly: identity morphisms; empty source and base; zero complex; the initial quotient index; a one-vertex tree; empty open or closed child; arbitrary unbounded representatives; and vacuous data when `Fin d` has no root. The chosen unit's shifted-product coordinate is kept equal to zero; no arbitrary triangulated lift is used. The original target statement, definitions and unit route are unchanged.

## New nodes

`def-fix-qcqs-completion-ordinary-models` attaches the relocated, already-proved construction block. Its change record is `coord/changes/E3-qcqs-ordinary-model-relocation.md`.

`lem-fix-qcqs-completion-unit-criterion` records the proved canonical-unit criterion via the intrinsic equivalence.

`lem-fix-qcqs-completion-comparison-unit` records construction of the derived comparison and the proved coordinate/counit/localization descent of the unit equation.

`lem-fix-qcqs-completion-unit-restriction` records the restriction assembly and the composite-unit isomorphism test.

`lem-fix-qcqs-completion-unit-tree` records the proved finite-tree induction and completeness conversion.

`lem-fix-qcqs-ordinary-restriction-models` and `lem-fix-qcqs-ordinary-local-detection` are the two retained source subresults named above. They have actual Lean signatures and source proofs, rather than restating the entire item. The parent node's proof/dependencies now follow the assembly actually written.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
