## What changed

Closed the theorem `Hom.isIso_residueFieldMap_of_isClosedImmersion` by applying the existing
`Hom.isIso_residueFieldMap` theorem. The original imports already provide the required
`SurjectiveOnStalks` instance for a closed immersion; no imports were added or removed.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion`.
No `sorry` remains in the delivered module; no new declarations were added.

## No longer needed

None. The module's existing import of `WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism`
is required for `Hom.isIso_residueFieldMap`.

## Where the brief, the DAG or earlier work was wrong

None.

## Earlier second reading (a previous round; superseded)

The theorem statement is unchanged and the proof uses the existing surjective-on-stalks
residue-field isomorphism exactly as specified by the DAG node. No new nodes or route changes
were introduced.

## Second reading by R4

1. I compared the delivered module with the repository version. The theorem signature,
   documentation, definitions, and imports are byte-for-byte unchanged; only the proof term
   differed, and the repair below restores the direct explicit application.
2. I compiled the module with `lcompile.py`; it succeeds with no errors or warnings. There are
   no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. The proof
   invokes the existing theorem `Hom.isIso_residueFieldMap`, whose assumptions are supplied by
   the closed-immersion stalk-surjectivity instance.
3. No statements were split off and no new declarations were added. The existing target theorem
   is unchanged and the imported generic residue-field theorem is already present in the library.
4. The proof takes the shortest available route: direct application of the generic theorem. The
   two Mathlib imports provide the closed-immersion and residue-field interfaces, while the
   `UniversalHomeomorphism` import supplies the generic theorem and its stalk-surjectivity
   infrastructure; none can be removed without breaking elaboration.
5. The DAG node's proof and `proof_deps` agree with the Lean proof, and the unit route remains
   realized through the existing surjective-stalks node. No node or route metadata required
   changes.

I changed only the proof body from an implicit `apply` to the explicit term
`simpa using (Hom.isIso_residueFieldMap i z)`, making the intended theorem application
unambiguous while preserving the exact target.
