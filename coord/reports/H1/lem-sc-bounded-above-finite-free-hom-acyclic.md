Files written:

- `dag/nodes/sec-picard-framework/lem-sc-bounded-above-finite-free-hom-acyclic.json`: split item, no Mathlib leaf.
- `dag/nodes/sec-picard-framework/lem-sc-finite-free-internal-hom-exact.json`: statement-only supporting node, no Mathlib match.
- `citations.json`: verbatim quotes for both proof steps.

Attachments: none. No sorry-free declaration in `WeilConjectures/` states the item or the supporting node.

WANTED: none.

The imported item had no proof steps. I kept its statement and added the missing cochain-complex statement dependency. The proof is split into the finite-free internal-Hom exactness input and the descending construction of a primitive for every total Hom cocycle. The supporting node is strictly smaller than the item: it is a degreewise short-exactness statement, not the acyclicity conclusion. The whole-DAG and blueprint searches found no duplicate of that supporting statement.

## Review by H1

I read the item source reference, Stacks Tag 0GM8 (Lemma 20.51.4, case (2)), and the imported parent route through `lem-sc-derived-hom-finite-free-model`. The target hypotheses are unchanged: the first complex is bounded above with finite-rank free terms, the second is bounded below and acyclic, and the conclusion is acyclicity of the total sheaf Hom complex. I also read the blueprint ancestor `thm-sc-p1-duality`; the split realizes its parenthetical bounded-above locally free Hom calculation.

Step 1 cites `lem-sc-finite-free-internal-hom-exact`, whose statement explicitly supplies exactness of internal Hom from a module identified with `\\mathcal O_U^{\\oplus r}` and the coordinate identification with a finite direct sum. This is exactly the degreewise fact used for the short exact sequences of cycles and boundaries in `A^\\bullet`; it does not assert acyclicity of a complex. Step 2 cites the same statement for each descending lift. I checked the indices: the upper bound on `E` and lower bound on `A` give a largest nonzero component of a fixed-degree cocycle, while the recursion then proceeds downward; the cocycle equation makes each next obstruction a cycle, and acyclicity makes it a boundary. The resulting family has the required total degree and gives `d(h)=z`. This checks both boundedness orientations and avoids any unsupported claim that an infinite product of sheaves is exact.

The supporting node is sourced to the finite locally free Hom calculation in Tag 0GM8. Its statement is self-contained, introduces the ringed site, the chosen finite-free presentation, and the short exact sequence, and has no proof sketch because it is intentionally statement-only. I tested the rank-zero case (`E=0`, all Hom sheaves zero) and rank-one case (`E=\\mathcal O_U`, the sequence is unchanged); both agree with the statement. Mathlib searches for the item and supporting node were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and is recorded as such, while the other searches found no ringed-site sheaf theorem. Existing DAG searches for finite-free Hom, exact Hom, and the Stacks tag found no duplicate supporting node.

## Not duplicates

- `lem-sc-finite-free-internal-hom-exact` vs `lem-weil-pbc-module-hom-left-exact`: the existing node is a ring-module contravariant Hom exactness and finite-free coordinate lemma; the new node is covariant internal Hom of sheaves on a ringed site and states exactness for a chosen finite-free sheaf.
- `lem-sc-finite-free-internal-hom-exact` vs `lem-sc-ext-tensor-exact`: the existing node concerns tensoring by finite locally free sheaves on schemes; the new node concerns internal Hom from a finite-free sheaf on a ringed site, with no tensor identification assumed.
- `lem-sc-finite-free-internal-hom-exact` vs `lem-sc-bounded-above-finite-free-hom-acyclic`: the existing item is the total-complex acyclicity theorem for a bounded-above complex and a bounded-below acyclic complex; the new node is only the degreewise short-exactness calculation for one finite-free term.
- `lem-sc-finite-free-internal-hom-exact` vs `lem-sc-derived-internal-hom-stalk-localization`: the existing node compares derived internal Hom with stalkwise derived Hom under pseudo-coherence hypotheses; the new node is an underived exactness statement for finite-free internal Hom and has no stalk comparison.
- `lem-sc-finite-free-internal-hom-exact` vs `lem-sc-ext-stalk-localization`: the existing node identifies Ext sheaves with local Ext groups; the new node is the finite-free degreewise Hom exactness used in a total-complex argument.
- `lem-sc-finite-free-internal-hom-exact` vs `lem-sc-derived-hom-finite-free-model`: the existing node says a finite-free Hom complex represents derived internal Hom after an injective replacement; the new node only states exactness of internal Hom on a short exact sequence and does not mention derived categories or replacements.

Nothing remains unfinished.

## Second reading by H1

- Item statement: checked against Stacks Tag 0GM8, Lemma 20.51.4 case (2), with bounded-above finite-free source, bounded-below acyclic target, and total sheaf Hom conclusion; zero and rank-one cases are consistent.
- Step 1: checked that the cited finite-free internal-Hom statement supplies exactness on short exact cycle/boundary sequences and finite-direct-sum coordinates; the step does not use a stronger conclusion.
- Step 2: checked the descending obstruction argument against the Hom-complex differential and the two boundedness hypotheses; the product totalization is the one defined by `def-pur-hom-complex`, so the infinite downward family is a valid element.
- Supporting node `lem-sc-finite-free-internal-hom-exact`: checked self-contained ringed-site, finite-free, and short-exact-sequence hypotheses, source tag, statement-only form, and rank-zero/rank-one edge cases; searches for an existing DAG or Mathlib declaration found no duplicate.
- Changed the item dependency list to cite `def-pc-acyclic-complex-modules`, because “acyclic” is used in the item statement.
- Corrected the item node's `created.item` to the delivered item; it incorrectly named its parent and would fail ownership preflight.
