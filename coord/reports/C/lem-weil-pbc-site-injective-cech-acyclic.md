# Worker report

1. Files written: `dag/nodes/sec-proper-base-change/lem-weil-pbc-site-injective-cech-acyclic.json` (statement node; Mathlib searches found no matching Cech-acyclicity theorem). No new nodes.
2. Attachments: none.
3. WANTED: none.
4. The imported node had no proof. I split it using the general-site argument of Stacks Tags 03AW, 03F6, 03AS, 03AT, 03AU and 03AN: exact sheafification transfers injectivity to presheaves; the free Cech complex is contractible in positive degrees; Yoneda identifies its Hom complex with Cech cochains; and the sheaf equalizer gives degree zero.
5. Nothing remains unfinished. No Lean was written or compiled.

## Review by C

I checked the statement against Stacks Project Tag 03AW and its cited lemmas. The proof is genuinely site-level: it uses only the site fibre products and sheaf condition, rather than the small-etale-only nodes. The presheaf injectivity step correctly applies the exact sheafification adjunction; the decomposition of the free Cech complex by maps to the covering target gives the stated contracting homotopy; Yoneda and direct sums produce exactly the Cech differential; and factorization through the image of a differential proves positive-degree exactness. The degree-zero claim is the equalizer condition. `proof_deps` is exactly the union of the step uses, with the generic sheafification result recorded as a tool use. `python3 tools/review_split.py lem-weil-pbc-site-injective-cech-acyclic` and `python3 tools/check_dag.py --cycles` pass.
