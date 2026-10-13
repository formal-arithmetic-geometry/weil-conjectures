## What changed
Proved ModuleCat.polynomial_tor_bound_of_base_tor_bound by induction on n. The zero-variable case is proved using the coefficient-map bijection and the existing localization Tor comparison at the trivial submonoid. The successor case transports hTor through the scalar-restriction composition isomorphism, applies the induction hypothesis, then applies the new one-variable bound.

## Proved and sorry left
Closed the original hole in ModuleCat.polynomial_tor_bound_of_base_tor_bound. Added one hole, ModuleCat.polynomial_successor_tor_bound (lem-pc-polynomial-successor-tor-bound). This is a decomposition, not a sorry-free proof: the one-variable exact-sequence argument remains. The zero-variable case, the induction, and all scalar restriction and arithmetic glue are complete Lean proofs. Net holes closed minus added: zero.

## No longer needed
No original import or original proof-dependency node is removed. The original node had no proof dependencies to prune. The attempted fixed-degree wrapper and zero-variable helper are not delivered. The proof keeps the existing localization comparison as a tool to prove the zero-variable case.

## Where the brief, the DAG or earlier work was wrong
The original DAG proof has no intermediate declarations for its substantial one-variable exact-sequence argument. The new lemma exposes exactly that induction step. It assumes a Tor bound over the ring with n variables, not over A, and is strictly a part of the n-variable induction. The edge cases n=0, d=0, zero rings and zero modules are valid: coefficient comparison uses module coefficients, not a domain hypothesis. The unit realization record has no nodes assigned to this auxiliary step; the parent polynomial route is preserved. No existing statement, definition or public import changes.

## New nodes
lem-pc-polynomial-successor-tor-bound, in Sheaf.RingTheory.PolynomialSuccessorTorBound, states the one-variable step along rename Fin.castSucc. Its docstring gives the two-term induced-module exact sequence, its coefficient proof, the change-of-rings comparison, and the Tor exact segment. The source is Weibel Theorem 4.3.7, pp. 101–102. The source PDF was read at pp. 101–102: the theorem states a global-dimension result, while its two-term induced-module exact sequence supplies this Tor argument. LeanSearch returned Internal Server Error and is recorded as unavailable. The other Mathlib searches found only projective Tor vanishing and dimension interfaces; the local source searches found no general polynomial Tor bound.


## Second reading by T4

1. **Existing interface: PASS.** Diffed both delivered modules against the repository.
   PolynomialTorBound changes only its proof and adds three ordinary imports.
   Compared the original declaration signature byte for byte: it is identical.
   Its original docstring, definitions, visibility and public imports are unchanged.
   PolynomialSuccessorTorBound is a new module, with no existing interface to alter.
   No change record or forced adaptation is needed.
2. **Proof and trust: PASS as a decomposition.** Both files compile locally in import
   order with no errors or warnings. The only delivered sorry is the complete body of
   ModuleCat.polynomial_successor_tor_bound; there is no definition, arbitrary witness
   choice, axiom, unsafe, opaque, implemented_by or extern in the delivered files.
   Scratch #print axioms checks for both declarations show propext, Classical.choice,
   Quot.sound and sorryAx. The localization comparison used in the base case shows only
   the three allowed axioms. Checked the base-case coefficient bijection, trivial
   localization instance, orientation of the scalar-restriction composition isomorphism,
   induction hypothesis on the restricted module, and successor arithmetic.
3. **Split statement: PASS.** Read the successor theorem and its node together with
   Weibel Theorem 4.3.7, pp. 101–102. Its coefficient inclusion adjoins exactly one
   variable. The coefficient argument proves injectivity without a domain assumption;
   descending degree proves the augmentation kernel assertion. Extending a projective
   resolution is exact because the polynomial ring is free over the coefficient ring,
   and tensor associativity computes Tor' in its first variable, as required here.
   Restriction of scalars reflects zero objects, and the Tor exact segment has zero
   ends for i > d+1, including d=0. For n=0 it is the ordinary one-variable case;
   for the zero ring or zero module the conclusion is immediate. The lemma isolates
   one induction step, not the original arbitrary-variable statement under another name.
   Its named sorry, source, complete proof docstring and matching new node are present.
   Independently searched LeanFinder for weak homological dimension via induced-module
   short exact sequences, Loogle for Tor' and isomorphisms, Mathlib grep for flatDimension,
   weakDimension and Hilbert syzygies, and local/upstream Lean sources for polynomial
   Tor bounds. No matching general bound was found; projective-dimension lemmas require
   stronger assumptions and do not close this flat-dimension step in a few minutes.
4. **Route and pruning: PASS.** The proof goes directly by induction, using the existing
   proved localization comparison only for the zero-variable scalar equivalence.
   Every added import is proof-only and ordinary: Equiv supplies isEmptyRingEquiv,
   the successor module supplies the induction step, and TorVanishingLocalizedBase
   supplies the base case. A scratch compile without Equiv fails on the isEmptyRingEquiv
   identifiers, confirming that import is needed. Public imports supply the statement's
   polynomial ring, Tor', ModuleCat structures and restriction of scalars. The old
   proof_deps is empty, so there are no omitted pruned nodes. Read
   dag/units/sk-thm-picard-duality.json: its realized statement and sole step lists are
   empty; this auxiliary reduction bypasses no assigned unit realization.
5. **DAG correspondence: PASS.** Compared the old and new parent JSON: only proof,
   proof_deps and proof_origin differ. The parent records the actual induction and
   both used nodes, with proof_deps equal to the union of step uses. Both Lean statement
   records occur verbatim in their modules. Checked the new node's chapter, unit,
   source, proof, origin, searches, split status, created record, blueprint ancestry
   and Lean attachment. These match the delivered one-variable lemma.

**Changes made by the second reader:** added this review and independently recorded
searches. No repair of the Lean proof or nodes was necessary. The original hole is
closed by a genuine induction reduction, with one strictly smaller hole added; net
hole reduction remains zero, and no module is pruned.
