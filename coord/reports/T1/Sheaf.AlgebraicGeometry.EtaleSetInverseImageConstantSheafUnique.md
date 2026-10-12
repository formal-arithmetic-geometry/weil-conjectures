## What changed

Replaced the sorry in AlgebraicGeometry.etaleSetInverseImageConstantSheaf_unique by
injectivity of two adjunction hom equivalences: inverse image/direct image, then
constant sheaf/evaluation at the terminal etale object. The proved source-library
constantSheafAdj_homEquiv_apply identifies the resulting functions with the section
expressions in the hypotheses. Added its module as a proof-only import. The statement
and existing public import are unchanged. Updated the node's proof and proof dependencies.

## Proved and sorry left

AlgebraicGeometry.etaleSetInverseImageConstantSheaf_unique
(new-etaleSetInverseImageConstantSheaf-uniqueness): the proof has no sorry.
No new statements or sorries are introduced. The imported existence module still has
AlgebraicGeometry.etaleSetInverseImageConstantSheaf_exists, but this proof does not use
that theorem: the module supplies only the Hom and Condition definitions.

## No longer needed

No existing import was removed; the public existence-module import supplies the signature.
The old plan's three proof dependencies are unnecessary for this uniqueness theorem:

- lem-galois-constant-sheaf-sets-representable,
  Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable;
- lem-galois-inverse-image-representable,
  Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable;
- lem-weil-pbc-sets-etale-inverse-image-constant-base-change,
  Sheaf.Paper.SetsEtaleInverseImageConstantBaseChange.

Their coproduct and representability proofs are unnecessary on this branch. This is local
pruning only: the existence theorem and other users may still need these nodes. No unit
statement or unit proof step is bypassed; this helper is not in the unit's realized list.

## Where the brief, the DAG or earlier work was wrong

The uniqueness node's old proof described construction and the isomorphism property.
Uniqueness needs only adjunctions and the section equations. LeanFinder found the sheaf
extensionality results; Loogle found Adjunction.homEquiv and homEquiv_unit; local source
search found the already proved constantSheafAdj_homEquiv_apply. A scratch example using
exactly these adjunctions compiled cleanly, including arbitrary and empty E.
The first local target compile could not run because the compiled snapshot lacked
EtaleSetInverseImageConstantSheafExists. After the snapshot refreshed, the actual module
compiled and deliver3.py --no-push printed OK: local/server compile and preflight passed,
with only the independent second reading reserved for the second reader. The sandbox
does not duplicate that dependency. No delivery was pushed.

## Second reading by T1

1. Compared the delivered module with the repository version. The theorem signature and all
   existing declarations are byte for byte unchanged; only the proof and proof-only import
   changed. Verdict: pass.
2. Compiled the module locally and checked `#print axioms`; it compiles without errors or
   warnings, has no `sorry`, and uses only `propext`, `Classical.choice`, and `Quot.sound`.
   Verdict: pass.
3. Checked the route against the existing library and searched for duplicate declarations.
   The proof uses the two adjunction hom-equivalences and the existing
   `constantSheafAdj_homEquiv_apply`; no split-off statements were added. Verdict: pass.
4. Checked pruning and imports. The three former proof dependencies are not used by the proof,
   while the added `ConstantSheafOver` import is proof-only. The unit's realized route is
   unchanged. Verdict: pass.
5. Checked the DAG node against the Lean proof. Its proof steps, empty `proof_deps`, origin,
   and Lean declaration record describe the delivered proof and theorem unchanged. Verdict:
   pass.

I changed only this report by adding the second-reading record; the module and node require no
further repair.
