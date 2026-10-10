1. Files written

- `dag/nodes/sec-picard-framework/lem-sc-affine-truncation-kernel-finite-locally-free.json`: split item, three source-based proof steps.
- `dag/nodes/sec-picard-framework/lem-sc-affine-truncation-kernel-flat.json`: statement-only auxiliary for the Stacks last-one-flat lemma; Mathlib searches found no match.
- `citations.json`: verbatim node quotes for every cited step.

2. Attachments

None. I found no sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` stating the item or the auxiliary node, including searches by the item id and by truncation/kernel terminology.

3. WANTED:

- `literature/stacks-project/perfect.tex`, Tag 08ED, is absent from this checkout. I read the synchronized copy `/home/ubuntu/c1-stacks-review/perfect.tex` at the complete proof of `lemma-lift-perfect-complex-plus-locally-free`.

4. Problems found and corrections

The imported item had no proof. The source writes `Ker(P^r -> P^{r+1}) = Im(P^{r-1} -> P^r)` as A-modules, which is false in general away from U; the split states K as the image and proves the equality only after restriction to U using the Tor-amplitude vanishing. The source's non-elementary flatness invocation had no DAG node, so I created `lem-sc-affine-truncation-kernel-flat` as a strict subclaim rather than moving the whole item into a child node. The finite-locally-free conclusion is then obtained from flatness and finite presentation using the existing definition node.

## Review by F1

I read the full Tag 08ED proof in `/home/ubuntu/c1-stacks-review/perfect.tex` and compared each item hypothesis with the imported statement: X is affine, U is quasi-compact, P is bounded above and finite free, r is below the Tor-amplitude lower bound, and K is the image in degree r. Step 1 uses the existing affine Tor-amplitude criterion, whose statement explicitly gives equivalence of the sheaf and module Tor-amplitude formulations. Step 2 is elementary from the definition of cohomology and exactness below the amplitude range; it carefully limits the kernel/image equality to U. Step 3 uses the new flat truncation-kernel statement exactly for its flatness conclusion and the existing finite-locally-free definition for the final implication from flatness plus finite presentation.

For the new node I checked the same Tag 08ED paragraph and stated only the last-one-flat conclusion, with all affine, quasi-compact, bounded-above finite-free, and Tor-amplitude hypotheses introduced in the statement. I searched the whole DAG and blueprint for the Stacks label, last-one-flat terminology, and truncation-kernel keywords; no duplicate or blueprint equivalent exists. I ran LeanFinder, Loogle, and Mathlib grep searches for both the item and the new node, including a second phrasing; results were generic flatness/Tor declarations or no hits, so neither is a Mathlib leaf. I tested the corrected restriction claim on the zero complex and on a one-term finite-free complex: both give K=0 and the asserted restricted kernel equality and finite local freeness.

5. Unfinished work

The new auxiliary node remains statement-only by stage-1 policy. No Lean files were changed or compiled.

## Not duplicates

lem-sc-affine-truncation-kernel-flat vs lem-sc-affine-truncation-kernel-finite-locally-free: the auxiliary states only flatness of the restricted image kernel, while the item also identifies the restricted kernel and concludes finite local freeness from finite presentation.
lem-sc-affine-truncation-kernel-flat vs lem-sc-affine-perfect-plus-locally-free: the auxiliary is the flat-and-finitely-presented truncation-kernel subclaim for a chosen index; the existing node is the full Tag 08ED extension theorem, including the perfect summand, triangle, and vanishing argument.

## Second reading by F1

- Item statement: checked against Tag 08ED (Lemma `lemma-lift-perfect-complex-plus-locally-free`), including affine X, quasi-compact U, bounded-above finite-free P, Tor-amplitude bounds, and the restricted image/kernel conclusion; verdict: agrees after restricting the equality to U.
- Item step 1: checked against the first proof paragraph of Tag 08ED and node `lem-pc-affine-tor-amplitude-criterion`; verdict: uses the given P and the cited sheaf/module Tor-amplitude equivalence.
- Item step 2: checked against the K definition and exactness paragraph of Tag 08ED; verdict: elementary from cohomology vanishing below a, with equality asserted only on U.
- Item step 3: checked against the last-one-flat and finite-locally-free paragraphs of Tag 08ED and the cited definition; verdict: the auxiliary node now supplies both flatness and finite presentation, so all non-elementary facts are cited.
- New node `lem-sc-affine-truncation-kernel-flat`: checked against the Cohomology last-one-flat invocation and the following Properties lemma in Tag 08ED; verdict: self-contained statement, strict subclaim, correct hypotheses, and source-backed flat plus finite-presentation conclusion.
- New-node searches: checked whole DAG and blueprint for truncation-kernel/last-one-flat duplicates and reran the recorded LeanFinder, Loogle, and grep searches; verdict: no existing node or Mathlib declaration states the auxiliary fact.
- Small cases: zero complex and one-term finite-free complex give K=0, satisfying the restricted flat, finite-presentation, and finite-locally-free conclusions.

Changes made: corrected the auxiliary node to include the finite-presentation conclusion needed by Step 3; replaced Step 1's unsupported choice of a new P with use of the given P; updated the verbatim citation and duplicate distinction accordingly.
