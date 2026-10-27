# Stage 1 report: lem-route-inverse-image-constant-comparison

1. Files written:

- `dag/nodes/sec-zeta-weil/lem-route-inverse-image-constant-comparison.json` — statement, split proof, four Mathlib searches; no new nodes.
- `citations.json` — verbatim quotations for the three cited DAG statements.

2. Attachments: none. No sorry-free declaration in the live `WeilConjectures/` source states this abstract item. No prior abandoned directory for this item was present.

3. WANTED: none.

4. Problems checked and corrected: the imported item had an empty proof and `status: unsplit`. I retained its statement and dependencies, filled the proof origin and blueprint realization, recorded the searches actually run on 2026-10-28, and added the generic left-adjoint-colimits theorem as the one declared off-unit tool use. The item is more general than the existing étale fixed-ring comparison node: it allows arbitrary small sites, an arbitrary ring-sheaf functor, and a whole natural family of coefficient rings, so that node is not a duplicate. The proof does not assume a final object in either site. The coproduct description of a constant sheaf is derived from the sheafification universal property and the constant-sheaf characterization in Tag 0H7J; the empty set is included.

## Review by NC

I read the live item, the `sk-thm-rationality` unit, the `sec-zeta-weil` chapter record, and the source passages for Stacks Tags 0H7J and 00YV. I also read the statements of `def-weil-pbc-constant-sheaf`, `def-weil-pbc-sheafification`, and `lem-weil-pbc-left-adjoint-preserves-colimits`; the quotations used by the proof are copied verbatim into `citations.json`.

Step 1 uses the sheafification universal property to identify the constant sheaf on a set E with the coproduct of E copies of the terminal sheaf, by matching maps out of either object with E-indexed families of global sections. The argument is natural in maps of sets and works for E empty. The constant-sheaf and sheafification hypotheses are exactly those in the cited definition nodes.

Step 2 applies the cited left-adjoint-colimits statement to this E-indexed coproduct. The item hypothesis that L preserves finite limits supplies the terminal comparison; combining it with the coproduct comparison and the two coprojection characterizations gives the canonical set-sheaf comparison kappa_E. I checked that the stated common-universe condition is enough for the indexed coproduct and that no site terminal object was smuggled in.

Step 3 defines the component for a ring A as e_(underline A) inverse followed by kappa_|A|. I checked addition and multiplication by restricting both composites through every pair of coprojections and using naturality of kappa for A times A to A; zero and one are the singleton cases. The assumed operation equations for e_R then make this a ring-sheaf morphism, and invertibility follows from the two isomorphisms.

Step 4 checks a ring homomorphism A to B using e-naturality and kappa-naturality for the underlying set map. Thus the components form the required natural ring-sheaf isomorphism, with exactly the underlying formula required in the item. The zero ring and empty-site/empty-set edge cases remain covered by the same universal-property argument.

5. Nothing remains unfinished. The required pre-report server `check_dag` passed before this report was written.
