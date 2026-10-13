## What changed

Added the proof-only module `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso`, splitting the geometric construction into a named intermediate theorem. The target theorem transports local finite presentation across the resulting scheme isomorphism and compiles.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.picardUniversalRankMatchLocus_locallyOfFinitePresentation` by a real transport proof. Added one strictly stronger intermediate theorem, `AlgebraicGeometry.Scheme.picardUniversalRankMatchLocus_exists_finitePresentation_iso`, whose proof remains `sorry` and is recorded by node `lem-sc-picard-universal-rank-match-locus-lfp-iso`.

## No longer needed

No original imports or stated dependencies were removed. The proof uses only the morphism finite-presentation and isomorphism APIs plus the new intermediate construction theorem.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof describes the rank-locus and gluing construction but had no Lean declaration exposing the required comparison with the supplied representative W. The intermediate node makes this missing comparison explicit.

## New nodes

`lem-sc-picard-universal-rank-match-locus-lfp-iso` records the missing finite-presentation representative and its unique isomorphism over S; its Lean declaration is in `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso`.

## Earlier second reading (a previous round; superseded)

The target signature is unchanged. The target proof is a direct transport along the explicit isomorphism supplied by the new intermediate node; no unit-level route is bypassed. The intermediate statement is stronger than the target and leaves exactly the geometric gluing construction for follow-up work.

## Second reading by Y3

1. **Comparison with the repository.** The target declaration has the same hypotheses and
   conclusion byte for byte. The only target-module changes are a proof-only import and the
   proof body; the added module and node are the declared split-off construction.

2. **Compilation and axioms.** Both delivered modules compile with `lcompile.py --all`.
   The target proof has no `sorry`; the only remaining `sorry` is the named intermediate
   theorem `picardUniversalRankMatchLocus_exists_finitePresentation_iso`. Axiom inspection
   shows only the permitted logical axioms together with `sorryAx` for that open theorem.

3. **Statements and split.** The intermediate theorem is strictly stronger than the target:
   it supplies a locally finitely presented representative and an isomorphism over `S`, from
   which the target follows by transport. Its docstring and node record the rank-component,
   fibre-product, and gluing proof, with source Tag 0BDP; it introduces no hollow definition.

4. **Pruning and route.** The proof uses the generic isomorphism transport and finite
   presentation APIs. Existing public imports remain needed by the target interface; the new
   module is imported privately because it is proof-only. No old proof dependency can be
   removed, and the unit's rank decomposition/gluing route is retained in the split theorem.

5. **DAG agreement.** The new node's Lean declaration, statement, source, proof outline,
   chapter, and unit agree with the delivered module. The target node now records the
   intermediate declaration as its proof dependency through the module import.

Changed the split theorem's docstring to give the complete construction in words and replaced
the target's placeholder proof with transport across the supplied isomorphism.

The proof-environment import is recorded in
`coord/changes/picard-universal-rank-match-locus-lfp-proof-import.md`.
