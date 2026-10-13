## What changed
Proved `AlgebraicGeometry.Scheme.Modules.exists_additiveCechBeta_homology` in
`Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechBetaHomology`, without changing its signature.
The proof uses the existing beta quasi-isomorphism and Mathlib's exact-functor cycle and
homology comparison isomorphisms. A proved private helper, `mapHomologyIso_inv_π`, supplies
compatibility of the comparison with the homology projection. Updated the item's node to
record this route. No other library module is changed.

## Proved and sorry left
Closed the one original hole: `AlgebraicGeometry.Scheme.Modules.exists_additiveCechBeta_homology`
(node `lem-pbc-etale-additive-cech-beta-homology`). No holes remain in the delivered module;
no holes are added and no statements are split off. The existing proved dependency
`exists_additiveCech_beta_quasiIso` is used as supplied.
The cycle and homology maps are constructed explicitly from comparison isomorphisms.
The original compactness and covering hypotheses are retained, although not needed for
this transport argument. Degree zero and empty complexes need no special case.

## No longer needed
Removed these direct proof imports and direct node dependencies:

- `Sheaf.AlgebraicGeometry.EtaleTensorUnitSectionsNatural`
  (`lem-sc-etale-tensor-unit-sections-natural`).
- `Sheaf.AlgebraicGeometry.EtaleQcoherentULiftFiniteCechComparison`
  (`lem-sc-etale-qcoherent-ulift-finite-cech-comparison`).
- `Sheaf.Algebra.Homology.FirstQuadrantAugmentation`
  (`lem-sc-first-quadrant-column-augmentation`).
Their geometric arguments belong to the existing beta quasi-isomorphism; this delivery
makes no claim that these modules disappear from the entire targets' import closure.
The earlier sandbox copies of BetaClosed and BetaQuasiIso are not delivered or modified.
No blueprint unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong
The previous attempt treated the ULift cycle/homology equivalences as unavailable.
They are already provided by Mathlib's `ShortComplex.mapCyclesIso` and
`ShortComplex.mapHomologyIso` for the forgetful functor followed by ULift. The only
additional glue was their projection compatibility, which is proved here, not postulated.

## Second reading by S2

1. Compared the delivered Lean file with the repository using `diff`, and checked the
   existing theorem signature byte for byte. Verdict: unchanged hypotheses, conclusion,
   visibility and definitions; only a private proved helper, proof and proof imports differ.
   There are no forced adaptations or undeclared interface changes.
2. Compiled the delivered module and a scratch copy with `#print axioms` for the theorem,
   helper and beta quasi-isomorphism. Verdict: no errors, warnings, local `sorry`, forbidden
   declarations or hollow definitions. The helper uses only `propext`, `Classical.choice`
   and `Quot.sound`. The theorem also inherits `sorryAx` through the existing beta
   quasi-isomorphism's dependencies; that dependency itself reports the same inherited
   axiom. This closes the item's local hole, not the remaining upstream obligations.
   The cycle map and additive equivalence are explicit composites, not arbitrary witnesses
   selected as definition data from a mere unproved existence statement.
3. No statements are split off and no holes are added. Verdict: no new holed statements
   require source, edge-case, duplication or node review. The private helper is proved
   generically for every homology-preserving functor, without geometric hypotheses.
4. Read the beta quasi-isomorphism and Mathlib's `PreservesHomology` comparison lemmas;
   searched the library and those Mathlib lemmas for projection compatibility. Verdict:
   the existing geometric chain comparison followed by exact-functor transport is the
   short route; the helper supplies the missing projection identity. Both imports are
   needed, and the proof-only beta import is plain `import`. All three old direct
   proof dependencies are listed under No longer needed. Read `dag/units/sk-thm-p1.json`:
   neither this node nor the pruned dependencies realizes a unit step. The existing beta
   route retains the column augmentation argument; no unit route is bypassed. The
   categorical identities also apply at n = 0, to zero groups and empty complexes.
5. Compared the node JSON with the repository and followed each proof step in Lean.
   Verdict: only `proof`, `proof_deps` and `proof_origin` change; their route and union of
   uses match the beta quasi-isomorphism and the proved categorical transport. No new
   nodes or changes to unit realization are needed.

Second-reading changes: appended this review and clarified the inherited `sorryAx`;
no Lean or DAG repair was necessary. One original local hole closed, zero holes added,
zero split-off statements.
