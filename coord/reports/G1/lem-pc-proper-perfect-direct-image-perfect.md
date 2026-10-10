# Stage-1 report

1. Files written:
   - `dag/nodes/sec-picard-framework/lem-pc-proper-perfect-direct-image-perfect.json`: split item, no Mathlib match.
   - `dag/nodes/sec-picard-framework/lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect.json`: statement-only unsplit node, no Mathlib match.
2. Attachments: none.
3. WANTED: none.
4. The source declaration is not present in slopmaster2. The Stacks proof of Tag 0B6G explicitly invokes the broader criterion Tag 08EV, so I added that criterion as the only supporting node instead of restating the target.
5. Nothing remains unfinished.

## Not duplicates

`lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect` vs `lem-pc-proper-support-perfect-direct-image`: the new node assumes bounded coherent cohomology, proper supports, and finite Tor dimension for one complex; the existing node concerns a finite-presentation morphism and a tensor product with a termwise flat bounded complex and additionally asserts arbitrary base change.

## Review by G1

I read Stacks More on Morphisms, Lemma 37.61.13 (Tag 0B6G), including its proof, and the cited Derived Categories of Schemes Lemma 36.27.1 (Tag 08EV). The target statement agrees with Tag 0B6G: S is Noetherian, f is perfect and proper, and P is perfect. Step 1 checks the criterion's hypotheses: properness supplies the finite-type morphism and proper support of X; Noetherianity and perfectness supply bounded coherent cohomology; and the definition of a perfect morphism supplies finite Tor dimension of O_X, which passes to a bounded strictly perfect representative of P. Step 2 quotes the exact conclusion of the new criterion and applies it with E=P. I opened every cited node and verified each quote is literal; no existing node states Tag 08EV, and the duplicate search covered the 0B6G/08EV tags and key phrases. The target and auxiliary statements were tested on the identity morphism and on P=O_X; both reduce to the expected perfect object.

## Second reading by G1

I checked the target against More on Morphisms, Lemma 37.61.13 (Tag 0B6G), and the auxiliary node against Derived Categories of Schemes, Lemma 36.27.1 (Tag 08EV), at the cited source text. The target now uses one base variable Y throughout, states that Y is Noetherian, and explicitly places finite Tor dimension over f^{-1}O_Y; these agree with Tag 0B6G hypothesis by hypothesis. The auxiliary node now states the exact 08EV hypotheses E in D^b_Coh, proper support of every cohomology sheaf, and finite Tor dimension, rather than incorrectly requiring E perfect.

Step 1 was checked against the definition of proper morphism and the definition of perfect complex: properness gives locally finite type and properness of closed supports by composition, while a locally bounded strictly perfect representative gives bounded coherent cohomology and finite Tor dimension of P from finite Tor dimension of O_X. Step 2 was checked against the complete statement of the auxiliary node; its hypotheses are exactly those established in step 1. No step uses a node's proof, and no step is marked elementary.

The auxiliary node is statement-only, self-contained, uses TeX once, cites all notions it introduces, and records the Mathlib searches already run with their actual no-match or unavailable results. Grep found no existing node for Tag 08EV. Small cases checked: identity morphism, empty scheme, and P=O_X. Changes made: corrected the auxiliary theorem to the source's bounded-coherent criterion; corrected Y/S notation and the relative Tor-dimension object in the target; corrected the target's created-item metadata; and updated the verbatim citation quote.
