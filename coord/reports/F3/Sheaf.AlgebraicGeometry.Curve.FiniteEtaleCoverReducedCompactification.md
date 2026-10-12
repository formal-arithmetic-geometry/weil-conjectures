## What changed

Proved `AlgebraicGeometry.IsCurve.exists_reduced_cartesian_finite_cover_compactification`
in `Sheaf.AlgebraicGeometry.Curve.FiniteEtaleCoverReducedCompactification`, with its
signature and visibility unchanged. Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` for the dimension
comparison. The proof applies finite Zariski main theorem, takes the schematic image
of the open immersion, proves that image reduced and a curve, and proves the
comparison to the pullback finite, open and surjective. Updated the node's proof
and dependencies to this compiled argument. No definitions or interfaces changed.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.IsCurve.exists_reduced_cartesian_finite_cover_compactification`
(node `r1-finite-etale-cover-reduced-cartesian-compactification`).
No sorry remains in the delivered module; no holes or declarations were added.
This is a proof from existing declarations, not a decomposition. The finite Zariski
main theorem remains an upstream dependency; this delivery does not claim to close
its transitive holes. Local compilation passed without warnings. The construction
and density argument require no nonemptiness, so also handle the empty cover and
zero-dimensional curves. The unit's realized statements and steps are preserved.

## No longer needed

Removed from this node's proof dependencies:
- `def-weil-pbc-scheme-reduction`: there is no separate nilradical reduction;
  the schematic image of the reduced source is reduced already.
- `lem-weil-pbc-integral-incomparability`: the existing quasi-finite dimension
  comparison uses discrete fibres directly.

No original import was removed. No additional proof module is needed for a reduced
closure or for cartesianness. A trial explicit import of
`Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` was removed because
its declarations are already available through the existing imports. The retained
Etale import is necessary: removing it makes `isReduced_of_etale` unknown.
The two nodes listed above are pruned from this argument, not asserted globally
unreachable from every target.

## Where the brief, the DAG or earlier work was wrong

The plan unnecessarily separates schematic closure from reduction. The existing
Mathlib scheme-theoretically dominant factor map has a theorem transferring
reducedness from its source to its target, so the scheme-theoretic image itself is
the desired reduced closure. The planned dimension and cartesian arguments were
mathematically correct; existing proved declarations and a direct topological
argument suffice. There was no statement change or forced adaptation.

## Second reading by F3

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof and one proof-only import differ. Verdict: pass.

2. Compiled the module and the sandbox import set with `lcompile.py`; both pass without errors or warnings. Checked `#print axioms` for `AlgebraicGeometry.IsCurve.exists_reduced_cartesian_finite_cover_compactification`, which reports only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition is present. Verdict: pass.

3. The target statement is unchanged and the proof constructs the finite reduced compactification directly from finite Zariski main factorization and the schematic image. The argument handles empty covers and does not add hypotheses. No split-off statements were added, and no existing library theorem duplicates the target. Verdict: pass.

4. Read the proof top-down. It uses the existing finite factorization, reducedness transfer through the scheme-theoretically dominant image, the quasi-finite dimension comparison, and the direct pullback density argument. The added QuasiFinite import is proof-only; the two dependency nodes removed by the worker are genuinely unused. Verdict: pass.

5. Compared the node's statement, proof steps, proof dependencies, and proof origin with the Lean proof. The unit route remains realized, and the node correctly records the two pruned dependencies. Verdict: pass.

Changed nothing during second reading; the delivered proof and metadata require no repair.
