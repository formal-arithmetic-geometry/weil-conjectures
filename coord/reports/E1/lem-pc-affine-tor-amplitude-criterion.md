1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-affine-tor-amplitude-criterion.json` — split statement, two proof steps, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-module-tor-amplitude-flat-model.json` — statement-only unsplit node, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-module-bounded-above-free-resolution.json` — statement-only unsplit node, no Mathlib match.

2. Attachments: none.

3. WANTED: none; `/home/ubuntu/c1-stacks-review/perfect.tex` supplied Tag 08E9.

4. The imported item had no proof. I checked the exact Tag 08E9 statement and proof. The forward step uses the ring bounded-flat-model criterion, the affine derived equivalence, the affine associated-sheaf K-flat lemma, and the derived tensor comparison; the cited statements provide precisely those facts. The converse uses the bounded-above free-resolution statement, the same tensor comparison, and exactness/conservativity of the affine associated-sheaf equivalence. I searched the whole DAG and blueprint before creating both auxiliary nodes; neither statement already existed. Mathlib searches were run for both nodes and recorded, with LeanSearch unavailable.

## Review by E1

I read Tag 08E9 in `perfect.tex` (the full proof around the lemma, including the bounded flat replacement and the bounded-above free resolution). I verified the item hypotheses against the source: affine `Spec(A)`, a complex of modules corresponding to an object of `D_QCoh`, and the same interval `[a,b]`. Step 1 cites the exact bounded-flat-model statement, then the existing affine equivalence, K-flat associated-sheaf statement, and affine derived tensor comparison; these establish ordinary tensor concentration in the stated interval. Step 2 first obtains bounded-above cohomology from the test against `O_X`, then cites the bounded-above free-resolution node; the affine tensor comparison and exact faithful associated-sheaf functor give module cohomology vanishing. I checked each cited node's statement directly and copied the relevant sentences into `citations.json`. Small cases checked were the zero complex, `a=b`, and `A` a field, where both sides reduce to the same degree-support condition. No source or statement correction was needed.

5. Nothing remains unfinished.

## Not duplicates

lem-pc-module-bounded-above-free-resolution vs lem-pc-affine-tor-amplitude-criterion: the new node is a ring-level existence lemma for a bounded-above free resolution, while the existing item is an equivalence between sheaf and module Tor amplitude on an affine scheme.

lem-pc-module-tor-amplitude-flat-model vs lem-weil-derived-tensor-resolution-independent: the new node characterizes module Tor amplitude by bounded flat representatives in a specified degree interval, while the existing node only states independence of derived tensor from the chosen K-flat resolution for pro-etale sheaves.

## Second reading by E1

- Item statement: checked against Stacks `perfect.tex`, Tag 08E9 / `lemma-tor-dimension-affine`; affine `Spec(A)`, corresponding derived object, and interval `[a,b]` agree hypothesis by hypothesis.
- Step 1: checked the bounded-flat replacement, affine equivalence, and K-flat associated-sheaf statements; removed the narrower affine tensor-comparison citation and wrote the K-flat computation for arbitrary sheaves explicitly.
- Step 2: checked the bounded-above free-resolution node, affine tensor comparison (part (3)), and affine equivalence; each cited statement supplies the claimed translation.
- `lem-pc-module-tor-amplitude-flat-model`: checked against More on Algebra Tag 064L; self-contained statement-only node, tested on zero, a field, and `a=b`.
- `lem-pc-module-bounded-above-free-resolution`: checked against the free-resolution sentence in Tag 08E9; bounded-above hypothesis is explicit and the node is statement-only.
- Existing-node search: searched the DAG for the item tag, Tor-amplitude phrases, bounded-flat replacements, and free resolutions; no duplicate substantive node was found.
- Edge cases checked: zero complex, field rings, `a=b`, and the explicit `a\le b` boundary.

Changes made: corrected `created.item` to this item; repaired Step 1 for arbitrary sheaves and removed the stale citation. No statement or source correction was required.
