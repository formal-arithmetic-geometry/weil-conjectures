## What changed

Proved `AlgebraicGeometry.Scheme.root_normalization_generic_stalk_galois_model`
from the existing regular Cartier generic-stalk DVR theorem and the new general
`AlgebraicGeometry.Scheme.cartier_generic_stalk_galois_model`. The original signature,
public imports, and docstring are unchanged. Both added imports are proof-only.

The root equation, prime membership, and transport of regularity are actual Lean
proofs. The private, fully proved `basicOpen_pullback_torsor_square` also constructs
the torsor pullback identification from beta, restriction pullbacks, pasting and
cancellation. It does not assume i is globally mono. The remaining theorem is over
an arbitrary torsor pullback at an integral Cartier DVR stalk and has no root
polynomial, affine chart, beta, or ring-map parameters. The unit route is retained.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.root_normalization_generic_stalk_galois_model`
(node `lem-sbc-root-normalization-generic-stalk-galois-model`).

Added one hole:
`AlgebraicGeometry.Scheme.cartier_generic_stalk_galois_model`
(node `lem-sbc-cartier-generic-stalk-galois-model`). Its whole proof is `by sorry`,
with the source and complete argument in its docstring. There are no other holes
in the delivered modules. This is a decomposition: one closed, one added, net zero,
with the root DVR and torsor pullback parts proved rather than restated.

## No longer needed

No imports removed and no globally pruned modules. The original node no longer
directly depends on `lem-sbc-normalization-stalk-base-change`; that dependency is
retained by the new general model node. The planned direct quotient calculation
A/(t)=H/(g), proof of height one using the principal ideal theorem, and explicit
identification of the generic prime with (t) are unnecessary here: the existing
regular Cartier generic-stalk theorem already gives the DVR at the actual point.
`RootDivisorGenericPrime` is not imported; its independent uses are unaffected.

## Where the brief, the DAG or earlier work was wrong

The original node supplied no Lean declarations for its field-factor construction
and residue comparison steps; these are precisely the remaining general model.
No false statement, changed target, or forced adaptation was found. The generic
model was checked on empty fibres (vacuous), the trivial group (one field factor),
and disconnected covers (a stabilizer for the selected factor), and makes no
invertibility or perfect-residue-field assumption.

An initial dependent DVR-witness elaboration exceeded the heartbeat budget because
it unfolded the concrete scheme's structure sheaf. An explicit witness type and
explicit ambient scheme resolved that issue, without changing definitions or limits.
The referenced Stacks documents were read from their official online pages because
the local literature checkout contains only citation lists.

## New nodes

`lem-sbc-cartier-generic-stalk-galois-model`, in
`lean/Sheaf/AlgebraicGeometry/Morphisms/CartierGenericStalkGaloisModel.lean`, contains
the remaining generic torsor field-factor, integral-closure and residue comparison
argument. It is strictly the part after the DVR and torsor identification proved
in the original module. No existing interface changes and no change records.

## Second reading by P1

1. Compared the delivered root module with the repository version. The existing
   theorem signature and its docstring are unchanged; the proof-only imports and
   private helper are additions required by the proof. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. There are no
   forbidden declarations or hollow definitions, and the only remaining `sorry`
   is the named split theorem `cartier_generic_stalk_galois_model`. Verdict: pass.
3. Reviewed the split statement and node. The generic Cartier DVR model is a
   strict reduction of the root theorem, with the root equation, regularity,
   and pullback construction removed; its hypotheses and conclusion match the
   Lean declaration and its source argument. Verdict: pass.
4. Checked the proof route and pruning. The root proof uses the existing regular
   Cartier generic-stalk DVR theorem, the private pullback-square construction,
   and the new generic model node; the unit route is retained and no old proof
   dependency is silently bypassed. Verdict: pass.
5. Checked imports and declarations. The root module's two added imports are
   proof-only; the new module's public imports support its public statement;
   no duplicate declaration or accidental interface change was found. Verdict:
   pass.

Changed only the report to record this second reading; no Lean or DAG repair was
needed after compilation.
