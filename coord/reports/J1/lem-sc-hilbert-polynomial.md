1. Files written: repaired item `lem-sc-hilbert-polynomial`; repaired `lem-sc-hilbert-difference` and `lem-sc-regular-meromorphic-section-exists`; retained `lem-sc-hilbert-embedded-points`; updated `citations.json`.

2. Attachments: none.

3. WANTED: none.

4. The returned faults were repaired as follows. The item statement is restored verbatim to the repository copy, including “Varieties, Lemma 33.45.1,” and the original source line. The regular meromorphic section is now defined by injectivity of the canonical map `K_X -> K_X(L)`, matching the Stacks definition; the difference lemma uses this definition. The existence node now assumes that the locally Noetherian scheme `X` itself has no embedded points and no longer assumes a coherent sheaf `F`, with `pqf-def-locnoeth` retained in `stmt_deps`. In the support reduction, I explicitly checked that the scheme-theoretic support `Z` has no embedded points: faithfulness of `G` gives a local embedding `O_Z -> G^r`, hence `Ass(O_Z) ⊆ Ass(G)`, and the no-embedded-points hypothesis on `G` with support `Z` makes these points generic. The second step now applies the existence node only after this check. Every citation quote was refreshed against the repaired node statement.

## Not duplicates

`lem-sc-regular-meromorphic-section-exists` vs `lem-sc-line-bundle-rational-section`: the existing node is only for a smooth connected curve over an algebraically closed field and proves an isomorphism with a divisor line bundle; this node is existence on a proper locally Noetherian scheme without embedded points.

`lem-sc-hilbert-difference` vs `lem-sc-deg-pullback-finite`: the existing node concerns leading coefficients under a finite morphism; this node gives regular-section cokernels and the Euler-characteristic forward-difference identity.

`lem-sc-regular-meromorphic-section-exists` vs `lem-sc-invertible-module-generic-stalk`: the existing node describes generic stalks on an integral scheme; this node asserts existence of a regular meromorphic section on a scheme without embedded points.

## Review by J1

I read the repository item, the blueprint proof text, and the source references for Varieties Tag 0BEM, Divisors Tag 02OZ, and Divisors Tag 02P2. I checked the stronger induction step and added the missing associated-point argument after the scheme-theoretic-support and closed-immersion reductions. The cited nodes state the quotient/support reduction, Euler additivity, support immersion, coherent equivalence, cohomology comparison, regular-section existence, and typed difference identity used by the corresponding steps; `citations.json` contains verbatim excerpts for each use. I verified that the existence node's hypotheses are exactly scheme-level no embedded points plus local Noetherianity, and that the difference node uses injectivity `K_X -> K_X(L)` rather than the weaker generic-point wording. I also checked the restored item statement character-for-character against the repository node, including its source line.

5. What I could not finish: none.

## Second reading by J1

- Item statement: checked against Varieties, Tag 0BEM (Lemma 33.45.1), including the field, properness, dimension, ample invertible module, and numerical-polynomial conclusion; verdict: the repository item is the advertised specialization obtained by taking the coherent sheaf to be $\\mathcal O_X$ and one invertible module.
- Step 1: checked against the statements of `lem-sc-hilbert-embedded-points`, `lem-pc-euler-additive`, the scheme-theoretic-support, coherent-equivalence, and closed-immersion-cohomology nodes; verdict: each cited statement supplies the quoted reduction, and the associated-point argument is written out rather than hidden behind “similarly”.
- Step 2: checked against Divisors, Tags 02OZ and 02P2 and the exact statements of the regular-section, difference, and Euler-additivity nodes; verdict: the sign in the forward-difference identity is equivalent to the source display, and the denominator ideal and meromorphic-section notation are now defined in the node statement.
- Step 3: checked against the zero-dimensional Euler-characteristic node and the finite-difference argument in Tag 0BEM; verdict: the base case, summation step, and specialization to $\\mathcal O_X$ are explicit.
- `lem-sc-hilbert-polynomial`: statement-only item node; source and blueprint fields retained, and its four small cases (empty scheme, field, zero-dimensional scheme, and $g=0$) are consistent.
- `lem-sc-regular-meromorphic-section-exists`: statement-only node; Tag 02OZ case (3) checked hypothesis by hypothesis, with the stronger proper finite-dimensional hypotheses harmless; empty scheme and a field satisfy the conclusion vacuously or by a nonzero one-dimensional section.
- `lem-sc-hilbert-difference`: statement-only node; Tag 02P2 checked for both injections, lower-dimensional cokernels, and Euler identity; all previously implicit notions $K_X$, $K_X(\\mathcal L)$, and the denominator ideal are now defined.
- `lem-sc-hilbert-embedded-points`: statement-only node; Tag 02OL checked for coherent kernel, unchanged support, no embedded associated points in the quotient, and strict support-dimension drop.
- Duplicate and Mathlib searches: searched existing nodes by all three Stacks tags and by the key terms; no duplicate or sorry-free Mathlib declaration states these results. The recorded searches and citation quotes were rechecked against the repaired statements.

Changes made: repaired `lem-sc-hilbert-difference` to define its meromorphic-section and denominator-ideal notation, and added this itemized second-reading record. No target statement was weakened.
