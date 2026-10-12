## What changed

The original theorem `AlgebraicGeometry.Scheme.Hom.tangentSheafAlong_iso_pullback_tangentSheaf`
is now proved by a reduction to finite locally free duality, with its signature and all
existing definitions unchanged. Its cotangentSheaf is definitionally equal to the library's
relativeDifferentials; the bridge is proved by `rfl`.

New modules:
- `Sheaf.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree`: proves finite local
  freeness for any smooth morphism, allowing the rank to vary. It adapts the existing
  constant-rank affine-chart proof and uses the library's restriction, affine differential,
  section comparison, rank criterion, and open-cover descent declarations.
- `Sheaf.AlgebraicGeometry.DualTensorHomComparison`: isolates the one remaining theorem,
  identifying the sheafified Hom-tensor morphism with the categorical comparison.
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeDualPairing`: proves existence of an exact pairing
  from the existing finite-locally-free Hom-tensor isomorphism and the categorical
  `MonoidalClosed.exactPairingOfIsIso` criterion, using that comparison identification.
- `Sheaf.AlgebraicGeometry.PullbackDualFiniteLocallyFree`: proves pullback compatibility from
  that pairing using `ExactPairing.map` and `MonoidalClosed.ihomObjUnitIso`.

The item's two new imports are proof-only. Every original public import is retained because
it provides the definitions or statements in this module. All five modules compile locally
without errors or warnings using the required launcher. No library-wide build was run.
Sources read: Stacks Project Tags 02G1 and 0FNV at their official web pages; the existing
upstream Modules.Differentials constant-rank proof; the monoidal duality API implementations.

## Proved and sorry left

Proved (possibly relying on the named remaining obligation):
- `AlgebraicGeometry.Scheme.Hom.tangentSheafAlong_iso_pullback_tangentSheaf`
  (node `lem-ag-tangent-along-section-pullback`): the original 1 of 1 sorries is removed.
- `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_relativeDifferentials`
  (node `lem-ag-smooth-relative-differentials-finite-locally-free`): complete proof.
- `AlgebraicGeometry.Scheme.Modules.nonempty_pullback_dual_iso_of_isFiniteLocallyFree`
  (node `lem-ag-pullback-dual-finite-locally-free`): complete proof from the pairing theorem.

- `AlgebraicGeometry.Scheme.Modules.nonempty_exactPairing_dual_of_isFiniteLocallyFree`
  (node `lem-ag-finite-locally-free-dual-pairing`): complete proof from the existing
  Hom-tensor isomorphism and the comparison identification.

Exactly one sorry is left in the delivery:
`AlgebraicGeometry.Scheme.Modules.dualTensorHom_eq_ihomUnitTensorToIhom`
(node `lem-ag-dual-tensor-hom-comparison`), in its own new module. Its proof is exactly
`by sorry`. Its docstring and node describe transposition through the sheafification
adjunction, agreement on pure tensors, and the tensor and unit coherence comparisons.

This is not a renamed version of the original theorem: the remaining statement identifies
two explicit maps for arbitrary modules on a single
scheme, with no morphism, no smoothness and no section, and not even a local freeness
hypothesis. The completed proofs use that identification to construct a duality datum,
map the datum along an arbitrary pullback, and use dual uniqueness. Smoothness is handled
by a separate complete affine argument. The bridge is a concrete coherence calculation,
not an assumption of either the desired isomorphism or dualizability.

Edge cases checked mathematically: the zero module has the empty coevaluation sum and both
triangle identities; the unit module has the usual multiplication pairing; finite free
modules have the finite dual-basis pairing; schemes with varying smooth relative dimension
are covered chart by chart. Empty schemes are covered by the same open-cover descent proof.
The section equation is not needed for compatibility, but remains in the original signature.

## No longer needed

No original import or recorded dependency node was removed. The module had only public
imports supporting its definitions, and no DAG node recorded the original theorem or its
proof dependencies. The proof does not import or use
`Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension` or its node
`lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension`: standard smooth affine charts
and the source library's proved differential comparison suffice. This does not claim that
other targets cease to need that module. No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No DAG node has lean.module equal to the assigned module. Its existing blueprint references
point to `sk-d-tangent`, a unit, not a node for this smooth sheaf theorem; that unit concerns
pointwise tangent spaces and rational actions and has no realized statement or proof steps.
The delivery therefore records the original theorem and its actual route as five new nodes.

The smooth-omega node already records the source library's constant-relative-dimension
result. Its hypothesis is stronger than arbitrary `[Smooth f]`, so it cannot be directly
applied here. The new finite-local-freeness proof handles a separate finite rank on each
standard smooth chart and does not assume a constant relative dimension.

Mathlib search: LeanFinder gives only field-vector-space exact pairings and ring-level
smooth differential freeness. Loogle cannot resolve ExactPairing or SheafOfModules.homObj
in its remote index. LeanSearch returned Internal Server Error; this unavailability is
recorded, not represented as an absence result. Source grep and imported-blueprint searches
found no exact sheaf-pairing theorem. The variable-rank notion is the existing
`def-sc-finite-locally-free-sheaf`, not the constant-rank `def-amb-finite-locally-free-module`.
Searches and their outcomes are recorded in each node.

## New nodes

`lem-ag-tangent-along-section-pullback` records the assigned theorem and the two-step
assembly actually compiled. Its dependencies are the general smooth freeness theorem and
the proved pullback dual comparison.

`lem-ag-smooth-relative-differentials-finite-locally-free` records the complete affine-local
proof of Tag 02G1 without a constant-rank hypothesis.

`lem-ag-pullback-dual-finite-locally-free` records the complete monoidal-functor and dual
uniqueness proof. It uses the proved finite locally free pairing.

`lem-ag-finite-locally-free-dual-pairing` records the completed proof of the duality datum
from the existing Hom-tensor isomorphism and the categorical duality criterion.

`lem-ag-dual-tensor-hom-comparison` records the sole remaining glue calculation, equality
of the explicit sheafified map with the canonical closed-category map. No statement or
definition change record is needed.


## Second reading by R2

1. **Existing declarations unchanged — pass.** Read the entire assigned module and
   compared it with the repository using `diff`. The only changes are two plain,
   proof-only imports, the theorem docstring, and the theorem proof. Every existing
   declaration signature and every definition body is byte for byte unchanged.
   In particular `[Smooth f]`, the section `e`, its equation `he`, and the exact
   `Nonempty` isomorphism conclusion are retained. No change record is required.
2. **Kernel and axiom checks — pass, with the declared open bridge.** Compiled all
   five modules in import order through `lcompile.py`, without errors or warnings.
   Searched all five delivered files for forbidden declarations and attributes and
   for `sorry`: the sole occurrence is the named comparison theorem, exactly
   `by sorry`. A scratch import module printed axioms of all five new/proved
   theorems. Smooth finite local freeness uses only `propext`, `Classical.choice`,
   and `Quot.sound`; the bridge and the three theorems depending on it additionally
   use `sorryAx`, and no other axiom. Removed the scratch module afterwards.
3. **Split statement and duplicate search — pass.** Read the implementations of
   `dualTensorHom`, `PresheafOfModules.dualTensorHom`, `tensorHomEquiv`, and
   `ihomUnitTensorToIhom`: the latter two constructions transpose the same
   evaluation-and-scalar-multiplication map. The remaining equality is true for
   arbitrary modules; it does not assert dualizability or the original pullback
   isomorphism. Checked zero source, zero target, the unit source, and arbitrary
   modules over an affine ring: both formulas give `phi(m) n`, with zero factors
   giving zero. Its source, complete transposition argument, blueprint tag,
   separate module and node are present. Independently searched LeanFinder for
   "sheaf tensor hom comparison evaluation curry dual natural morphism", Loogle
   for "tensor", "hom", "sheaf", and source grep for curry/sheaf and the two
   comparison names. Results are generic tensor-Hom facts, not this equality.
   A scratch `rfl` attempt confirmed that the two maps are not definitionally
   equal; closing their sheafification coherence requires the documented argument.
4. **Top-down route, imports, and pruning — pass.** Read Stacks
   [02G1](https://stacks.math.columbia.edu/tag/02G1) and
   [0FNV](https://stacks.math.columbia.edu/tag/0FNV). Smoothness supplies a finite
   free differential module separately on each standard smooth chart; the proof
   never assumes constant rank. Compared its affine argument against the source
   `isFiniteLocallyFreeOfRank_relativeDifferentials` proof. Checked the descent
   cover and rank-zero/empty-scheme cases. The remaining route uses the proved
   upstream Hom-tensor instance, categorical `exactPairingOfIsIso`, monoidal
   `ExactPairing.map`, and uniqueness `ihomObjUnitIso`; the final inversion has
   exactly the target endpoints. Public imports support signatures or definitions;
   the new proof dependencies are plain imports. No original dependency or import
   is dropped. Read `dag/units/sk-d-tangent.json`: its statement concerns pointwise
   tangent spaces and rational actions, its steps and both realized lists are
   empty. No realized unit step is bypassed or edited.
5. **DAG matches Lean — pass after repair.** Read all five node files, checked
   their Lean signatures, sources, creation records, and that each `proof_deps`
   is precisely the union of its proof steps' `uses`. The final theorem uses
   smooth freeness and pullback duality; pullback duality uses the pairing; the
   pairing uses the Hom-tensor isomorphism and the comparison bridge. Corrected
   the pairing node: the Hom-tensor isomorphism is the statement of existing
   `lem-sc-ext-evaluation`, not the definition `def-sc-finite-locally-free-sheaf`.
   The step now explains that the Lean proof uses the already-proved upstream
   `isIso_dualTensorHom_of_isFiniteLocallyFree` directly, avoiding the still-open
   `Sheaf.AlgebraicGeometry.ExtEvaluation` wrapper. The predicate remains in the
   node's statement dependencies. This is a tool use of the Picard evaluation
   result below unit level, with no change to either unit's route.

Second reading changed only the pairing node's proof-step citation and matching
`proof_deps`, and added this review. No Lean repair was needed. One independent
coherence theorem remains open; the assigned module's original one sorry is
removed by a genuine reduction, not a restatement.
