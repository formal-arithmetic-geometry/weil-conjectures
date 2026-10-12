## What changed

Proved `exteriorSheaf_restrict_iso` by assembling mutually inverse morphisms. Added the auxiliary module `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictHomData`, whose theorem states the two-sided hom data and remains the sole postponed proof. The main module imports this auxiliary result.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_restrict_iso`. The auxiliary theorem `exteriorSheaf_restrict_hom_data` remains as one sorry, with node `lem-sc-exterior-sheaf-restrict-hom-data`.

## No longer needed

None; the exterior sheaf definition is still needed by the auxiliary statement.

## Where the brief, the DAG or earlier work was wrong

The planned direct sheafification comparison is substantial. The delivery factors it into explicit mutually inverse morphism data, so the target proof is a genuine categorical assembly from a strictly more concrete intermediate statement.

## New nodes

`lem-sc-exterior-sheaf-restrict-hom-data` records the remaining construction of the comparison morphisms and their inverse identities.

## Earlier second reading (a previous round; superseded)

Pending second reading: the target proof assembles the hom data into an isomorphism; the new node is strictly the construction of the two inverse morphisms.


## Second reading by X2

1. **Interface comparison.** Compared the delivered `ExteriorSheafRestrictIso.lean` with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof body and a proof-only import were added. Verdict: pass.

2. **Compilation and axioms.** Compiled both delivered modules with `lcompile.py --all`; both compile cleanly. The only remaining `sorry` is the named theorem `exteriorSheaf_restrict_hom_data`, which is documented and has node `lem-sc-exterior-sheaf-restrict-hom-data`; the target proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. Its resulting `sorryAx` dependency is solely through that explicitly split theorem. Verdict: pass.

3. **Split-off statement.** The auxiliary statement gives exactly the two morphisms and both inverse identities needed to construct the target isomorphism. It is strictly more concrete than the target and its node, source, proof description, and Lean declaration agree. No duplicate declaration was found in the repository. Verdict: pass.

4. **Route and pruning.** The target proof uses the auxiliary hom-data theorem and packages it directly as an isomorphism, preserving the unit's intended comparison route. The public import of `ExteriorSheaf` is needed by the signatures; the auxiliary module is imported privately because it is proof-only. No unused imports or old proof dependencies remain in the delivered route. Verdict: pass.

5. **DAG consistency.** Updated the target node's `proof`, `proof_deps`, and `proof_origin` to record its actual use of `lem-sc-exterior-sheaf-restrict-hom-data`; the target statement and unit record were left unchanged. Verdict: pass.

Changed during second reading: corrected the target DAG proof metadata and added this review section. No Lean declarations or statements were changed.
