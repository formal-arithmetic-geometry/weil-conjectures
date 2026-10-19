## Worker report

Files written:

- `dag/nodes/sec-smooth-purity/lem-fin-radicial-exchange-descent.json` — existing item copied from the repository and marked `split`; its imported seven-step proof and metadata were retained.
- `citations.json` — 25 step/node entries (21 unique nodes), each with a verbatim quote from the cited DAG statement.

No new DAG node was created: every non-elementary ingredient in the imported proof is already represented by an existing DAG node. No attachment is claimed; no sorry-free declaration in `weil-src-slopmaster2/WeilConjectures` states this item. WANTED: none.

There was no statement correction and no source error found. The item statement agrees with the source node and the archived blueprint. The expanded proof follows the blueprint's universal-homeomorphism invariance and exchange-composition route, while spelling out the canonical module-valued exchange, constructibility descent, and the Noetherian test-base argument.

## Review by NW

I read the item node, the chapter `sec-smooth-purity`, the unit `sk-prop-sf-cbc`, and the source passage `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-fin-radicial-exchange-descent.md`. I also searched the read-only source checkout for the item tag and declaration; no matching project declaration was present, so the item is not an attachment. The source statement's finite, surjective, radicial hypotheses, open immersion, finite coefficient sheaf, bounded-constructibility conclusion, and universal Noetherian base-change conclusion are all retained.

For Step 1 I opened `pqf-lem-finite-integral-lft`, `lem-pc-integral-radicial-surjective-universal-homeomorphism`, and `lem-weil-pbc-universal-homeomorphism-base-change`. They say respectively that finite morphisms are integral, that integral universally injective surjections are universal homeomorphisms, and that all pullbacks remain universal homeomorphisms; these are exactly the facts used to identify `u`, `a`, `b`, and later pullbacks.

For Step 2 I read the statements of the universal-homeomorphism topos invariance node, the inverse-image module exactness node, both exact-functor derived-factorization/derived-functor nodes, the exact-functor cohomology node, `sbc-def-base-change-map`, and the mate-isomorphism node. They supply the sheaf and module equivalences, exactness, derived functors, cohomology comparison, the canonical exchange map, and the criterion making its mate an isomorphism. Thus the step proves the canonical exchange isomorphism rather than merely an abstract object isomorphism.

For Step 3 I checked `def-weil-pbc-etale-constructible-sheaf`, `def-weil-constructible-subset`, `lemma-weil-pbc-universal-homeomorphism-site-equivalence`, the universal-homeomorphism invariance theorem, `lemma-constructible-pullback-constant`, and `lem-weil-pbc-reduction-universal-homeomorphism`. These statements justify the finite reduced stratification, preservation of constructible subsets under the underlying homeomorphism, descent of etale covers and constant module models, and the reduced-stratum comparison. The hypotheses needed here are only the universal-homeomorphism and finite coefficient assumptions already in force.

For Step 4 I read `def-weil-pbc-constructible-complexes`. Together with Step 2's cohomology comparison and Step 3's sheaf descent, its statement gives bounded constructibility of `Rj_*F` with the same cohomological interval. I checked that the step uses the definition only after the interval and each cohomology sheaf have been established.

For Step 5 I read `def-weil-finite-integral-morphism`, `lem-weil-pbc-fibre-product-affine-spectra`, and `lem-weil-pbc-finite-type-over-noetherian`. Their statements give the affine tensor-product description of `T'`, finite module generators for the pulled-back finite map, and Noetherianity of a finite-type scheme over a Noetherian base. This verifies that `q` is finite and that `T'` is Noetherian, so `r:T'\to S'` is an admissible test morphism; no Noetherian hypothesis on `S` or `S'` is smuggled in.

For Step 6 I read `sbc-def-base-change-map`, `lem-weil-pbc-inverse-image-composition`, `prop-weil-pbc-inverse-image-modules-exact`, and `lem-weil-pbc-mate-pasting`. Their statements give the canonical exchange definition, the direct- and inverse-image composition comparisons, the unique module structures and underlying compatibility, and the mate pasting formula. These are precisely the inputs to the displayed canonical exchange composition identity for the two factorizations of `T'\to S`.

For Step 7 I checked `lem-weil-mate-iso-along-equivalences` and reused the universal-homeomorphism equivalence established in Step 2. The right-hand exchange factors are isomorphisms by the hypothesis and Step 2; the `q`-exchange is an isomorphism by the same mate argument; cancellation and conservativity of `q_Y^{-1}` then give the exchange over `S`. I verified that the argument quantifies over every Noetherian `T` and concludes both universal formation and the bounded-constructibility assertion.

I checked all cited-node statements against the 25 citation entries, including the three long proof steps (Steps 2, 3, and 6). Each long step is one continuous equivalence, stratification, or coherence argument with all non-elementary inputs cited; I found no hidden independent lemma requiring a new node. I tested the edge cases in the statement and proof informally (identity universal homeomorphism, empty/open strata, zero-dimensional cohomology interval, and arbitrary Noetherian test base). The required server `check_dag` preflight passed with no findings.
