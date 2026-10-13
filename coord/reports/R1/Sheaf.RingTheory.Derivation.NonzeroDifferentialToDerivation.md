## What changed

Proved `exists_derivation_of_nonzero_kahler_differential` in
`Sheaf.RingTheory.Derivation.NonzeroDifferentialToDerivation` with its signature and
visibility unchanged. Added the proof-only import `Mathlib.LinearAlgebra.Dual.Lemmas`.
`Module.Projective.exists_dual_ne_zero M h` provides a functional detecting the
nonzero differential. `LinearMap.compDer` composes it with the universal derivation;
`Derivation.restrictScalars ℤ` makes the result an absolute derivation without
changing its values. The final nonvanishing proof is definitionally the functional's
nonvanishing proof.

This implements the existing DAG step using both of its Mathlib leaves, with no
change of route or node fields. It does not bypass any realized unit statement or
step. The source's differential-functional step was checked at
[Stacks Tag 07PH](https://stacks.math.columbia.edu/tag/07PH); the local literature
sources are absent on this machine, so the published source was read directly.

## Proved and sorry left

Closed: `exists_derivation_of_nonzero_kahler_differential`
(node `lem-weil-pbc-nonzero-differential-to-derivation`).
One of one original holes proved; zero holes added or split off; no sorry remains
in the delivered module. The file compiled without warnings using `lcompile.py`.
The delivery dry run performs the declaration axiom probe.

## No longer needed

None. Both planned dependencies remain used:
`lem-weil-pbc-vector-space-dual-separates` through
`Module.Projective.exists_dual_ne_zero`, and `def-weil-pbc-kahler-differentials`
through `KaehlerDifferential.D`. No imports were removed and no nodes or modules
were pruned. The two existing public imports were preserved for interface stability.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The existing plan suffices directly,
with Mathlib's composition and restriction operations supplying the glue.

## Second reading by R1

1. **Interface comparison:** Compared the delivered module with the repository
   version. The theorem signature, declaration name, visibility, and surrounding
   definitions are unchanged byte for byte; only a proof-only import and the proof
   body differ. Verdict: pass.
2. **Proof and axioms:** Compiled the delivered file with `lcompile.py`; it has no
   warnings or remaining `sorry`. A `#print axioms` probe reports only
   `propext`, `Classical.choice`, and `Quot.sound`. No forbidden declarations or
   hollow definitions occur. Verdict: pass.
3. **Statements and split-offs:** No new theorem or split-off statement was added.
   The existing theorem is proved exactly as stated, and the proof uses the
   existing dual-separation and Kähler-differential declarations. Verdict: pass.
4. **Route and pruning:** The proof follows the DAG route: a nonzero dual
   functional is composed with the universal derivation and restricted to ℤ.
   `Mathlib.LinearAlgebra.Dual.Lemmas` is required for
   `Module.Projective.exists_dual_ne_zero`; removing it causes an unknown-constant
   error. No unused imports, nodes, or modules were found, and the realized unit
   route is preserved. Verdict: pass.
5. **DAG agreement:** The existing node's declaration, statement, proof
   dependencies, and proof origin agree with the Lean proof. No node fields need
   changing. Verdict: pass.

Changed only the theorem proof and added the proof-only duality import; no
statement, definition, node, or dependency route was changed.
