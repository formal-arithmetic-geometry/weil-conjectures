## What changed

Replaced the proof of `AlgebraicGeometry.torsionEtaleCohomologicalDimensionLE_of_dim_le_one` with a short reduction to the existing upstream theorem
`AlgebraicGeometry.IsCurve.hasTorsionCohomologicalDimensionLE`.  The proof constructs the `IsCurve`
instance from the given dimension bound, splits on `IsAffine X`, and transports the upstream
`Sheaf.H` formulation to the module's derived étale cohomology formulation using
`Scheme.nonempty_sheafH_extDerivedIso`.  Removed all proof imports that the resulting proof does not use.

## Proved and sorry left

The target theorem `AlgebraicGeometry.torsionEtaleCohomologicalDimensionLE_of_dim_le_one` is proved.
No `sorry` remains in the delivered module.

## No longer needed

The original normalization and finite-support route is unused.  The following proof-only imports
were pruned: `Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`, `WeilConjectures.Mathlib.Topology.KrullDimension`,
`WeilConjectures.AlgebraicGeometry.Regular`, `Sheaf.AlgebraicGeometry.ClosedPointField`,
`WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport`, `WeilConjectures.SixFunctors.Finite.Exact`,
`Sheaf.Paper.InverseImageStalkGerm`, `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension`,
`WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension`, and
`Sheaf.Paper.ZeroDimensionalCohomology`.  The unit-route import
`Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations` remains required by the route.  The corresponding DAG dependencies
`thm-weil-pbc-universal-homeomorphism-invariance`, `lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-noetherian-finitely-many-components`, `lem-fin-normalization-extension-finite`,
`lem-sc-dim0-finite`, `lem-sc-normalized-curve-smooth`, `lem-kun-closed-point-field`,
`def-weil-pbc-scheme-conventions`, `lem-sc-normalization-exists`, `lem-sc-iso-off-finite-set-cohomology`,
`lemma-weil-pbc-finite-direct-image-exact`, `lem-weil-pbc-inverse-image-stalk-germ`,
`lem-weil-pbc-torsion-sheaf-characterizations`, `lem-sc-cohomological-dimension`,
`lem-sc-affine-cohomological-dimension`, and `lem-weil-pbc-zero-dimensional-cohomology` are not needed
by this proof.

## Where the brief, the DAG or earlier work was wrong

The planned proof expands normalization, finite-support comparison, and componentwise smooth-curve
arguments, but the source library already proves the complete curve bound in
`AlgebraicGeometry.IsCurve.hasTorsionCohomologicalDimensionLE`.  The only additional glue needed is
the existing `Sheaf.H` to derived étale cohomology comparison.  Thus the planned dependency route was
substantially longer than necessary; no statement was changed.

## Second reading by E4

1. **Signatures:** Compared the delivered module with the repository version. The theorem signature and
   all existing declarations are unchanged; only proof imports and the theorem body differ. **Verdict: pass.**
2. **Proof validity:** Compiled the module with `lcompile.py`; it succeeds with no errors or warnings.
   The theorem has no `sorry`, and the proof uses the existing upstream curve bound and the existing
   `Sheaf.H`/derived étale comparison. **Verdict: pass.**
3. **Split statements:** No new Lean declarations or split-off holes were added. The shortened DAG proof
   dependency is the existing comparison node, and the upstream curve theorem is already in the library.
   **Verdict: pass.**
4. **Pruning and route:** Retained the unit-route `TorsionSheafCharacterizations` import as required,
   while removing the old normalization and finite-support imports. The old dependencies are removed from
   the node's `proof_deps`; the comparison node is used as a generic tool below the unit level.
   **Verdict: pass.**
5. **DAG agreement:** Updated `proof`, `proof_deps`, and `proof_origin` to match the replacement proof;
   the maintainer-owned split report remains unchanged. The target statement and unit record are unchanged.
   **Verdict: pass.**

Changed the theorem proof, removed unused proof imports, and synchronized the node metadata. No holes were
added; one target hole was closed.
