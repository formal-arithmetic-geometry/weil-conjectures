## What changed

Corrected `cechComparisonSystem_comparison_connecting` to take a
`CechComparisonSystem U hcover` and conclude the identity using `c.comparison`.
Its proof is the structure projection `c.connecting T hT hg q`. Adapted
`CechComparisonSystemExistence.lean` by removing its now-invalid application of the
old arbitrary-family theorem and leaving the existence construction as its named
`exists_cechComparisonSystem` sorry. Added the corresponding statement and proof-route
updates to the two affected DAG nodes and recorded the interface correction in
`coord/changes/cechComparisonSystem_comparison_connecting.md`.

## Proved and sorry left

Closed 1 hole: `cechComparisonSystem_comparison_connecting`.
One existing hole remains: `exists_cechComparisonSystem` in
`CechComparisonSystemExistence.lean` (node `lem-pc-cech-comparison-system-existence`).
No new theorem statements were added.

## No longer needed

Removed the proof-only import of
`Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystemConnecting` from
`CechComparisonSystemExistence.lean`; the corrected projection theorem cannot be used
to construct a system from an arbitrary comparison family.

## Where the brief, the DAG or earlier work was wrong

The former connecting statement quantified over arbitrary degreewise natural maps,
which do not generally commute with connecting morphisms. The corrected statement
requires the compatibility data already carried by `CechComparisonSystem`. Consequently
the previous existence caller was invalid: its arbitrary comparison witness supplied no
connecting field. The existence theorem remains open for a genuine augmented
injective-Cech construction.

## Forced adaptations

`Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystemExistence` (held by B3) was
adapted because the changed connecting theorem made its old call fail at the argument
`comparison`: the theorem now expects `c : CechComparisonSystem U hcover`. The only
necessary changes are removal of that call/construction and removal of the now-unused
Connecting import; its public theorem signature is unchanged.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

The corrected declaration is exactly the `CechComparisonSystem.connecting` field with
argument order rearranged, so it proves the changed node without assumptions about
arbitrary comparison families. The adapted existence module preserves its public
signature and changes only the invalid proof call and its now-unused import. The DAG
statement change records the old statement, old proof dependencies, and the sole citer.

## Second reading by F2

1. Compared the delivered Connecting and Existence modules with the repository versions.
The Connecting signature is intentionally changed as recorded, while Existence keeps its
public signature and only removes the invalid caller and import. Verdict: pass.
2. Compiled all sandbox modules with `lcompile.py --all`; there are no errors or forbidden
constructs. The sole remaining `sorry` is the named `exists_cechComparisonSystem` theorem.
Verdict: pass.
3. The corrected connecting statement is exactly the `connecting` field of the supplied
`CechComparisonSystem`, so it is true and exactly as strong as needed. No new statements
were added. Verdict: pass.
4. The proof uses only the structure projection and the Existence adaptation is forced by
the interface correction; the Connecting import is removed from Existence. Verdict: pass.
5. The Connecting node records the corrected statement and projection proof; the Existence
node records its direct-construction route and dependency update. The unit route remains
represented by the system existence and connecting nodes. Verdict: pass.

Changed only the two adapted modules, their DAG proof metadata, the interface change record,
and this report. No further repairs were needed.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystemExistence
Original against changed dependencies failed:
```
/tmp/forced-adaptation-ujdlj4cj/lean/Sheaf/AlgebraicGeometry/Cohomology/CechComparisonSystemExistence.lean:52:60: error: Application type mismatch: The argument
  comparison
has type
  (q : ℕ) → TopCat.Sheaf.cechCohomologyFunctor U q ⟶ Sheaf.functorH (Opens.grothendieckTopology ↥X) q
but is expected to have type
  CechComparisonSystem U hcover
in the application
  cechComparisonSystem_comparison_connecting U hcover comparison

(with the modules compiled into /tmp/forced-adaptation-ujdlj4cj/.lbuild) [3.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
