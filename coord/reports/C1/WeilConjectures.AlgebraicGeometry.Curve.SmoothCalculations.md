## What changed

Proved `AlgebraicGeometry.IsCurve.surjective_cohomologyMap_constantModSheaf_two`.
The proof splits on surjectivity of the open immersion. In the isomorphism case it uses
`Etale.cohomologyMap_bijective`; otherwise it proves the source open affine (using the
proper compactification dichotomy and the zero-dimensional case), then applies affine
cohomological dimension two vanishing and constructs the surjection to the zero group.
Removed the redundant proof-only import
`Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension`: C₃ uses
`ConstantModCharPDegreeTwo`, which imports it for its own proof. Also demoted `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension`
to a private proof import, with change record
`coord/changes/SmoothCalculations-proof-import.md`. Its declarations are used only in proofs.

## Proved and sorry left

Proved: `surjective_cohomologyMap_constantModSheaf_two` (`lem-sc-c8`).

Sorries left in the item module:

- `finite_sheafH_constantModSheaf_of_ne_zero` (`lem-sc-c4`)
- `finite_sheafH_constantModSheaf_of_isProper` (`lem-sc-c5`)
- `bijective_cohomologyMap_constantModSheaf_of_ne_zero` (`lem-sc-c6`)
- `bijective_cohomologyMap_constantModSheaf_of_isProper` (`lem-sc-c7`)
- `assertions_constantModSheaf_of_ne_zero` (`lemma-weil-pbc-smooth-curve-kummer-localization`)
- `assertions_constantModSheaf_of_charP` (`lemma-weil-pbc-smooth-curve-artin-schreier`)

## No longer needed

Removed the redundant direct proof import
`Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension`; that module remains required
by `ConstantModCharPDegreeTwo`, so it is not globally pruned. No modules removed.
The edge from `lem-sc-c8` to `lem-sc-c2` is no
longer needed: the proof uses `lem-sc-affine-curve-h2-vanishing` on the pulled-back
sheaf directly. `lem-sc-c2` itself stays required by the smooth-curve calculation
package and the unit route; it is not globally pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG proof's last sentence incorrectly infers surjectivity solely from H²(C)=0
in the affine case. Vanishing of the source alone does not imply surjectivity.
The implemented proof instead establishes affineness of the target open W and
vanishing of H²(W,a*F). It also handles dimension-zero connected curves, which
`IsCurve` allows but `IsConnectedCurve` excludes.

The existing lem-sc-c8 node now follows the implemented argument, retaining the
compactification and affine-open route. Its C₂ dependency is replaced by the more
general affine H² vanishing declaration used on the actual inverse image sheaf.
Topological invariance is used as a tool only for isomorphisms.

The original missing compiled dependency has arrived; the full module now compiles
and the delivery dry run passed before this DAG documentation update. No new nodes
or statements were introduced.

## Second reading by C1

1. Compared the delivered Lean file against the current repository version with `diff`.
   All thirteen existing declaration signatures, section variables, and definitions are
   byte for byte unchanged. The changes are the C₈ proof, removal of a redundant
   private proof import, and import visibility cleanup. No new declarations.
   The proof-only `CohomologicalDimension` import is now private,
   recorded in `coord/changes/SmoothCalculations-proof-import.md`. Verdict: pass.
2. Compiled the module with `lcompile.py --all` successfully without warnings. Compiled
   a scratch copy with `#print axioms` for all thirteen declarations: only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` occur. C₈ still depends on open upstream
   geometric/cohomological results; this is a reduction, not an axiom-free final closure.
   The six unchanged named sorries are exactly those listed above. No forbidden constructs
   or sorry-bearing definitions occur. Verdict: pass as a partial stage-3 delivery.
3. No statements were split off and no nodes were added. Checked the pulled-back torsion
   sheaf and the precise hypotheses of affine H² vanishing. Empty W works; dimension-zero
   C is a singleton because it is irreducible and T₀, so W is a subsingleton scheme and
   affine. The proof also permits the zero coefficient ring and arbitrary `Λ/rΛ`;
   no coefficient hypothesis was added.
   Verdict: pass; no new unresolved lemma to close.
4. Read the proof top down and searched the library for restriction-surjectivity,
   affine-open, and cohomology-map results, and Mathlib via `msearch.py grep` with
   `surjective.*cohomology|cohomology.*surjective|isAffine.*open`. No matching shorter
   cohomological theorem was found. The proof retains smooth compactification and affine
   proper-open reduction, with topological invariance only for an isomorphism. The old
   proof-dependency edge to `lem-sc-c2` is the only removed edge. The unit
   `sk-thm-p1.json` still realizes C₈, and C₂ remains used by the calculation package.
   The removed direct Artin–Schreier import is redundant through the degree-two helper;
   the other imports remain statement dependencies or the plan for the six open proofs.
   Demoted the public proof-only `CohomologicalDimension` import; checked all 100
   downstream modules as documented in the change record.
   The sole downstream module losing source visibility was compiled from an
   unchanged scratch copy against the modified module, without errors or warnings.
   Verdict: pass.
5. Read `lem-sc-c8.json` together with the four dependency declarations and
   `sk-thm-p1.json`. Its proof steps, `proof_deps`, and `proof_origin` describe the actual
   isomorphism/compactification/dimension-zero/target-vanishing argument. Its statement
   and unit realization are unchanged. Verdict: pass.

Second reading corrected the import-removal report, demoted the public proof-only
`CohomologicalDimension` import, added its downstream change record, documented
the axiom status, and recorded this independent review. The Lean proof and DAG
repair were retained unchanged.
