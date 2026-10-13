## What changed

Preserved the complete signature and docstring of
`AlgebraicGeometry.Scheme.strictPerfect_relativeTensor_roof`. Added proof-only imports
of `Sheaf.AlgebraicGeometry.RelativeTensorRoofComparison` and
`Mathlib.Algebra.Homology.DerivedCategory.Fractions`.

The new comparison theorem asserts only that the two fixed base-ring complexes are
isomorphic in the standard derived category. A fully proved private helper
`common_quasiIso_roof` uses `DerivedCategory.right_fac` to obtain actual chain maps
s and t. From e.hom = inv(Q.map s) ≫ Q.map t it proves
Q.map t = Q.map s ≫ e.hom, hence invertibility of Q.map t. Mathlib's
`isIso_Q_map_iff_quasiIso` establishes both quasi-isomorphisms. The item applies
this helper to the comparison. No definition or existing public signature changed.

The standard base-ring localization has hom universe u+1. It introduces no new
hypothesis: the original hypotheses choose localizations only for structure-ring
module categories. The existence of the roof remains a proposition; no definition
chooses a witness from an unproved existence theorem.

Updated the item's node proof, proof_deps and proof_origin to match this route.
The unit and its realized steps are unchanged.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.strictPerfect_relativeTensor_roof`
(node `lem-pc-strict-perfect-relative-tensor-roof`). Its entire roof-construction
argument is proved by the private helper `common_quasiIso_roof`.

Added one deferred theorem:
`AlgebraicGeometry.Scheme.strictPerfect_relativeTensor_roof_comparison`
(node `lem-pc-strict-perfect-relative-tensor-roof-comparison`), in the new module
`Sheaf.AlgebraicGeometry.RelativeTensorRoofComparison`. Its whole proof is `by sorry`.
Its docstring gives the local K-flat tensor and exact scalar-restriction argument.

This is a decomposition: one hole closed and one added, net zero. The item is not
claimed to be free of transitive sorry dependencies.

## No longer needed

No existing library import or module is pruned. All three original public imports
remain necessary for the statement. The original local tensor proof dependencies
remain needed below the new comparison node; they are not falsely counted as pruned.
The generic roof construction needs only Mathlib, with no additional deferred roof
lemma or second-leg lemma.

Removed the invalid earlier-attempt `RelativeTensorRoofSecondLeg` and duplicate
root-level `StrictPerfectRelativeTensorRoof.lean` from the delivery, along with their
unused records. They were sandbox artifacts, not existing library modules.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox reduction did not compile: its s mapped to the scalar-restricted
K, whereas the proposed second-leg theorem required a map to the tensor complex.
That second-leg statement was also false: the existence of an arbitrary chain map
H→T does not imply that H and T have isomorphic cohomology (take H=0 and T nonacyclic).
It has been discarded, not imported or delivered. The earlier first-leg comparison
alone was vacuous, since the identity of the scalar-restricted K supplies it, and
did not carry any relation to the tensor endpoint.

The old sandbox node's recorded Lean statement and report disagreed with its actual
Lean statement. Its stale W4 review metadata and searches have been replaced by a
new D4 record with the exact new signature and searches actually run in this session.

The actual missing step is the local derived tensor calculation followed by exact
scalar restriction. Existing comparison lemmas are phrased on the open subscheme,
whereas this item uses the localized open site; scalar-restriction/open-site and
localization comparisons must be supplied in that calculation. The general
chain-map roof construction already exists as Mathlib `DerivedCategory.right_fac`.

The new statement was checked on empty opens, L=0, G=0, f=identity, and unbounded G:
all are consistent with the K-flat bounded strictly perfect first factor and exact
scalar restriction. No relative flatness or ordered support interval is introduced.

Sources read: [Stacks 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ), proof's local
tensor calculation; [Stacks 06YH](https://stacks.math.columbia.edu/tag/06YH), the derived
tensor construction; [Stacks 05RT](https://stacks.math.columbia.edu/tag/05RT), saturated
quasi-isomorphisms. Mathlib `DerivedCategory.right_fac` and
`isIso_Q_map_iff_quasiIso` were read in Fractions.lean and Basic.lean respectively.

## New nodes

`lem-pc-strict-perfect-relative-tensor-roof-comparison` records just the local derived
isomorphism of the two fixed complexes, before any chain-map roof is chosen. It is
strictly the tensor-computation part of the original argument. The original theorem
proves the remaining roof construction using Mathlib. The new node keeps the original
local tensor dependencies and records the standard base-ring localization explicitly.
The whole blueprint was searched for "relative tensor" (zero matching blueprint nodes),
and project and Mathlib sources were searched before introducing this statement.
There are no change records because no existing interface changes.


## Second reading by D4

1. **No accidental interface changes.** I diffed the delivered item against the repository version. The
   existing theorem `strictPerfect_relativeTensor_roof` has byte-for-byte identical binders,
   conclusion, and docstring; only proof-only imports, a private helper, and its proof body changed.
   The added comparison theorem is in a new module and is recorded by the new DAG node.
   Verdict: pass.

2. **Proof and trust basis.** Both delivered modules compile with `lcompile.py`. The private roof helper
   has only `propext`, `Classical.choice`, and `Quot.sound`; the two public results additionally depend
   on the intentionally deferred comparison theorem's `sorryAx`. There are no `axiom`, `unsafe`,
   `opaque`, `extern`, `implemented_by`, or hollow definitions, and no anonymous or private `sorry`.
   Verdict: pass, with the one named split theorem explicitly reported above.

3. **Split statement.** `strictPerfect_relativeTensor_roof_comparison` states exactly the derived
   isomorphism needed before choosing a roof; it does not restate the roof existential and adds no
   relative-flatness, support, or degree hypotheses. I searched the project and Mathlib for an existing
   declaration and checked empty opens, zero complexes, identity maps, and unbounded second factors.
   The Stacks tags 0DJQ and 06YH support the local K-flat tensor calculation. Verdict: pass.

4. **Pruning and route.** The proof uses Mathlib `DerivedCategory.right_fac` and
   `isIso_Q_map_iff_quasiIso` for the roof construction and retains all imports needed by the stated
   comparison route. No old proof dependency or public import became unused, and the unit route and
   realized metadata are unchanged. Verdict: pass.

5. **DAG agreement.** The item node records the comparison node, Mathlib roof lemmas, and the actual
   proof origin; the new node records its exact Lean declaration, source, proof steps, searches, and
   split status. The report, Lean signatures, and node metadata agree. Verdict: pass.

**Changes made during second reading:** no Lean or DAG changes were needed; I added this review section
and removed only a temporary scratch axiom-check file.
