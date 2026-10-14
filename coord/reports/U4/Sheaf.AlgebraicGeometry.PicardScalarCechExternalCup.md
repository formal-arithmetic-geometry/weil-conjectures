## What changed

Restored `picardScalarCech_externalCup_core` to the repository's original signature,
without `hUc` and `hVc`, and restored its original docstring. Restored the covering
wrapper `picardScalarCech_externalCup` to its original application of that core.
The core is marked `STATEMENT-DISPUTED` and its whole proof is `sorry`: the
comparison predicate does not determine a unique map without the cover condition.
No weaker replacement theorem is asserted.

Removed `PicardScalarCechExternalCupPoint.lean`, its proof import, its new node
`lem-sc-picard-scalar-cech-external-cup-point`, and the false change record
`coord/changes/picardScalarCech_externalCup_core.md`. Removed the unused proof import
`Sheaf.Paper.CechCupPullbackCompat`.

Added the proved private helper `moduleCechComparison_add_kernel`. It states that
adding a module morphism killed by the resolution identification followed by
H(alpha), for every injective resolution, preserves `IsModuleCechComparison`.
Its proof distributes composition over addition and uses the two stated equations.
This is a checked mathematical explanation of the obstruction, not a replacement
for the core and not a claimed formal refutation of it.

Updated both existing nodes: the covering wrapper depends on the core, and the
core records the comparison-kernel obstruction. There is no proof edge from the
core to the wrapper and no point node or point edge. Existing Lean signatures and
visibility are restored; no definitions or target statements were changed.

## Proved and sorry left

Holes closed relative to the repository baseline: none (0 of 1).
Holes added relative to that baseline: none. No decomposition is claimed.

The sole remaining admitted declaration is
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core`, node
`lem-sc-picard-scalar-cech-external-cup-core`. Its original statement remains
unproved and is now disputed. The covering wrapper is still a complete Lean
application of this admitted statement, as it was in the baseline; consequently
its axiom closure still contains the admission. The private kernel-addition
helper is proved without an admission.

The rejected admitted declaration `picardScalarCech_externalCup_point` was removed.
This removal does not count as a hole closed against the baseline, where the
point declaration did not exist.

The single delivered Lean module compiles using `lcompile.py`, without errors or
warnings. No assertion here claims that the punctured-surface example has been
constructed and certified in Lean.

## No longer needed

Removed module and import:
`Sheaf.AlgebraicGeometry.PicardScalarCechExternalCupPoint` and node
`lem-sc-picard-scalar-cech-external-cup-point`. Removed both rejected point-related
proof edges, including the edge inherited by the point from the wrapper.

Removed proof import `Sheaf.Paper.CechCupPullbackCompat` and proof dependency
`lem-sc-picard-cech-cup-pullback-compat`: it is not used by the restored wrapper or
the proved obstruction helper. Its cover-dependent statement cannot prove the
cover-free core. The revised wrapper proof also does not directly use the former
coordinate/refinement/cup dependencies `def-sc-cech-refinement-cochain-map`,
`def-sc-cech-cup-product`, `def-sc-module-cohomology-cup-product`,
`def-sc-field-linear-module-cohomology-operations`,
`lem-sc-picard-external-cech-cup-component`, and
`lem-sc-picard-scalar-cech-comparison`; it uses the core only. The core's recorded
obstruction uses `lem-sc-picard-scalar-cech-comparison` only.

The two public imports `PicardScalarCechComparison` and
`PicardExternalCechCupComponent` stay because the original public signatures need
their definitions. Their transitive imports, and declarations needed by these
signatures, are not claimed to leave the target closure. No genuine cover-case
cup calculation has been proved or pruned by this repair.

## Where the brief, the DAG or earlier work was wrong

Corrections to the returned delivery and its inaccurate second reading:

- The delivered core signature adds cover hypotheses absent from its recorded statement.
  This describes the rejected delivery; the repaired file restores their omission.
- Moving the quantified variables into theorem binders preserves the whole obligation
  and is not a decomposition. The point module and node are now removed.
- The original core statement is not proved by this delivery. It remains admitted
  and explicitly disputed, rather than being silently weakened.
- The previous point node's inherited review records did not certify a new theorem.
  The node is deleted. No replacement admitted lemma or new node is introduced.
- The previous second reading is withdrawn. Its signature, decomposition, proof,
  and DAG claims were incorrect. This worker does not supply a new second reading;
  the independent reader must read the repaired files.

STATEMENT-DISPUTED: The core's cover-free comparison hypothesis permits independent
changes into the kernel of restriction. The defining equation is
c ; resolution-identification ; H(alpha) = H(beta). It does not say that c is a
particular lift of H(beta). The proved private lemma checks this freedom directly
in Lean. The source [Tag 01FD](https://stacks.math.columbia.edu/tag/01FD) explicitly
uses open coverings, so it does not justify removing the cover equalities.

A mathematical counterexample to the original core can be made as follows.
Work over k = C. Let A and S both be products of two elliptic curves, so they are
smooth connected projective surfaces with Gamma(O) = k and nonzero H^2(O).
Fix s in S(k), put S0 = S minus {s}, X = A times S, Y = Spec k, and take structure
sheaf coefficients F and G. Choose a finite affine cover (A_i) of A and set
U_i = A_i times S0; take the singleton full cover V of Y. The U_i cover only
W = A times S0, not X.

For every intersection A_J, normality and codimension-two extension give
Gamma(A_J times S0, O) = Gamma(A_J times S, O) = Gamma(A_J, O).
Indeed, regular functions on a normal Noetherian integral scheme are determined
at codimension-one points, all of which remain after removing A_J times {s};
the second equality follows from properness and Gamma(S,O) = k. Restrictions
agree, so the entire Cech complex for U and O_X is the affine-cover Cech complex
for A and O_A. Its homology is H^p(A,O_A) in every degree.

There is a comparison c0 in every degree given by pullback pr_A^* from H^p(A,O_A)
to H^p(X,O_X). After restriction to W it agrees with the genuine Cech comparison
for the cover U of W. For any injective resolution I on X, the total Cech complex
for U and I computes H^p(W,O_W): injective module sheaves are flasque, their
restrictions to W are flasque, and U covers W. Under this identification H(alpha)
is restriction from X to W and H(beta) is the cover comparison for W. Thus c0
satisfies the defining comparison equation for every I, not merely one resolution.

Choose nonzero eta in H^2(S,O_S). Since S0 is a nonproper surface,
H^2(S0,O_S0) = 0 by [Tag 0G5E](https://stacks.math.columbia.edu/tag/0G5E).
Hence pr_S^*(eta) is killed by restriction to W. It is nonzero on X: restricting
to {a0} times S, for any a0 in A(k), recovers eta. Choose a nonzero
x in H^2(A,O_A) and a k-linear functional lambda with lambda(x) = 1.
Because Gamma(X,O_X) = k, the map
  delta(t) = lambda(t) pr_S^*(eta)
is also Gamma(X,O_X)-linear. For every I its composite with the resolution
identification and H(alpha) is zero. Therefore c0 + delta is another allowed
comparison in degree 2, by the proved kernel-addition lemma. In the other degrees
keep c0. These choices supply all degreewise factor comparison hypotheses.

Use c0 + delta for eX in degree 2, the genuine comparison for eY, and c0 in every
degree for eP, identifying X times_k Spec k with X and O_X external-tensor O_Y
with O_X. The additive Cech identifications in `IsPicardScalarCechComparison`
transport these module comparisons to the required k-linear scalar maps.
The prescribed external cochain cup with the degree-zero unit on Y identifies
with the identity on the U Cech complex. Choose a degree-2 factor cycle representing
x and the degree-zero cycle 1 on Y. Their tensor summand gives a total cycle z:
the tensor differential is zero because both factors are cycles. It satisfies
the displayed cycle-inclusion hypothesis, with p = n = 2 and q = 0.

The left side of the core formula is then pr_A^*(x), whereas its right side is
pr_A^*(x) + pr_S^*(eta). Pullback along the identity product projection and cup
with the scalar unit leave a class unchanged. These two answers differ by the
nonzero class pr_S^*(eta). The degree equality is 2 + 0 = 2, so no nontrivial
transport or sign issue can remove the difference.

This example respects module linearity (Gamma(X,O_X) = k). A simpler proposed
example using disconnected points would not: idempotents in the global ring
forbid its arbitrary extra-component lift. That example is not claimed here.
Empty families and zero coefficients give zero Cech homology and do not detect
this positive-degree obstruction. The original covering wrapper is not disputed;
cover hypotheses make H(alpha) invertible, eliminating precisely this ambiguity.

The core node's old proof asserted comparison cancellation without the hypothesis
needed for that cancellation. Its admitted signature should be reviewed before
further proof work; the wrapper should ultimately be proved using a sound
cover-case argument rather than this cover-free admission. No claim is made that
the current wrapper has a sound completed proof.

## Second reading by U4

1. Signature preservation: PASS. Compared the entire delivered module with the
   repository using diff, and independently compared the two existing theorem
   signatures byte for byte through `:= by`; both are identical. Existing
   docstrings, visibility and proof bodies are unchanged. The only Lean changes
   are a proved private helper, dispute comments, and removal of a plain proof
   import. No definition, target, public import or change record is delivered.

2. Proof and trust check: PASS as a dispute repair, not a completed cup proof.
   Compiled the module with lcompile.py without errors or warnings. A scratch
   copy with #print axioms confirms that moduleCechComparison_add_kernel uses
   only propext, Classical.choice and Quot.sound. The existing core and wrapper
   additionally use sorryAx. The only textual admission is the whole proof of
   picardScalarCech_externalCup_core; there are no hollow definitions, forbidden
   declarations or hidden new admissions. The original core docstring is not a
   valid complete proof: cancellation requires the missing cover condition.
   This inherited fault is explicitly disputed, rather than certified here.

3. Split statements and small cases: PASS; no statements are split off and no
   new admitted node is delivered. The private helper is simply add_comp applied
   to the defining equation: its zero-perturbation case is the original equation,
   and zero coefficients or empty families introduce no exceptional step.
   Loogle finds Preadditive.add_comp, already used in the proof; LeanFinder and
   rg searches found no existing project comparison-addition lemma. Checked the
   actual IsModuleCechComparison and IsPicardScalarCechComparison definitions.
   The obstruction respects global-ring linearity, unlike the rejected
   disconnected-point argument. Stacks Tag 01FD explicitly assumes coverings;
   Tag 0G5E gives the stated top-cohomology vanishing for a nonproper variety.
   The report's geometric example remains an informal argument, not a Lean
   counterexample theorem. Its role is to justify statement review.

4. Route and pruning: PASS with no claim of proof progress. The unchanged
   wrapper directly invokes the existing core; that core has no sound completed
   proof here. The removed CechCupPullbackCompat import supplies cover-dependent
   cup compatibility and is unused by both current proofs. The two retained
   public imports are needed by the original signatures. Checked the unit
   sk-prop-av-cube: its realized statement and step lists are empty, and this
   delivery changes none of its records or chapter/unit steps. Every removed
   baseline proof dependency is listed under No longer needed. The deleted
   point module/node were rejected sandbox artifacts absent from the repository
   baseline, so their removal is neither a baseline hole closure nor library
   module pruning. Removing a proof import is not evidence that its module
   disappears from the targets' transitive import closure.

5. DAG agreement: PASS. Both existing node statements and Lean records match
   the unchanged signatures. Their diffs change only proof, proof_deps and
   proof_origin. The wrapper now records its actual dependency on the core;
   the core records the comparison obstruction and explicitly supplies no
   proof. No new nodes, reverse proof edge or point restatement remains.
   Inherited review records do not certify this disputed core; this review does
   not endorse their mathematical verdicts.

Second-reader changes: added this independent review and clarified the baseline
and pruning accounting. No Lean or node edit was necessary. Closed holes: none
(0 of 1); added holes: none; split off: none. Delivery is a statement-dispute
repair and import cleanup, not a completed proof or decomposition.
