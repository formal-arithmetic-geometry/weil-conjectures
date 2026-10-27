## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-projective-local-fibre-assassin-specialization.json` (item, statement unchanged, five-step split), and `citations.json` (one verbatim statement quote for each of the seven step citations). No new node files and no new Mathlib leaves.

Attachments: none. Searches of `lean/WeilConjectures/` for the exact item id, associated-prime terminology, homothety, universal injectivity/localization, and Tag 05FV found no declaration stating this item. The associated-prime height and localization declarations do not have this conclusion.

WANTED: none.

The imported node had no proof. Its statement agrees with Stacks `flat.tex`, Tag 05FV, `lemma-explain-why-pure`, including the closed-fibre finiteness hypotheses and the absence of finite generation over the local base. No statement dispute or correction was needed. The proof follows that source; instead of creating a node for Tag 05FR it applies the already existing Tag 05FQ criterion to scalar multiplication. It does not need the general localization/tensor comparison: scalar injectivity already makes the annihilator prime disjoint from the denominator set.

Nothing mathematical remains unfinished at this one-level split. Dependencies are existing nodes, with their own status unaffected.

## Searches and blueprint

Read `GOAL.md`, the three-level rule in `SETUP.md`, stage 1, the worker brief and delivery-errors B–E. Read the chapter and unit records. Read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability.proof.md`, especially its proper/open direct-image and compactification paragraph. This item belongs to the inherited alteration/flattening prerequisite chain recorded in its original `blueprint.from.place`. `tools/blueprint_refs.py ancestor lem-sfb-projective-local-fibre-assassin-specialization` returns `None`; preserve that existing ancestry rather than invent an imported blueprint node. Whole-blueprint searches for homothety, 05FR, 05FQ, universal injectivity, associated primes, and fibre-associated terminology found no exact statement. DAG searches by 05FV, homothety-spectrum, invert-universally-injective, universally-injective-local, associated-prime regular elements, and projective-flatness located all the existing inputs used here.

Six N5 searches were run using the required msearch command and recorded in `searches.jsonl`: LeanFinder, Loogle, two LeanSearch phrasings, and two Mathlib greps. Loogle rejected `Module.associatedPrimes` as an unknown identifier; this is recorded as an unsuccessful query, not evidence of absence. The semantic hits give associated-prime localization, projectivity localization, support specialization, and projective-flatness. Read `Mathlib/RingTheory/Ideal/AssociatedPrime/Localization.lean` lines 36–77, `Mathlib/RingTheory/LocalProperties/Projective.lean` lines 40–78, `Mathlib/RingTheory/Flat/Basic.lean` lines 217–233, and `Mathlib/RingTheory/Spectrum/Prime/Topology.lean` lines 345–378. None proves the entire item by one-line specialization. The projective-flat and spectrum-range declarations already have DAG leaves, reused here. The item's previous Q12 search records are retained.

## New nodes

None. In particular no new node repeats either the item or one of its clauses. Tag 05DE already has `lem-sfb-fibre-regular-localization-spectrum`, and Tag 05FQ already has `lem-trf-local-universal-injective-residue`. A separate Tag 05FR node would be unnecessary for this proof: its scalar-map application is already a direct application of the latter, with a written check of all hypotheses.

## Not duplicates

No new nodes; no new/existing node pairs require justification. Existing spectrum, projective-flatness, local universal-injectivity and exact-annihilator nodes are cited directly.

## Review by N5

I read the item against the actual statement and proof of `flat.tex` Tag 05FV (`lemma-explain-why-pure`, lines 4314–4343), the full statements and proof of Tag 05DE (`lemma-homothety-spectrum`, lines 1782–1818), Tag 05FR (`lemma-invert-universally-injective`, lines 1975–1991), and Tag 05FQ (`lemma-universally-injective-local`, lines 1945–1973). There are no new-node sources to audit. The item uses element-annihilator associated primes, as in 05FV; it does not confuse these with weakly associated primes.

Step 1 uses exactly the statement of `lem-weil-pbc-projective-module-flat`: a projective module over any commutative ring is flat, including infinitely generated modules. The multiplicativity of Sigma is written as the composition of injective scalar maps. No finiteness over R is introduced.

Step 2 uses exactly `lem-trf-local-universal-injective-residue`: source P projective, target P flat by step 1, the same local base R, and residue scalar multiplication injective by membership in Sigma. That node's statement explicitly gives injectivity after tensoring with every R-module. The existing tensor-product definition gives the universal property and generation by pure tensors; I wrote the inverse flip maps and their conjugation on pure tensors to account for its tensor-factor order. No flatness of C, localness of C, finite presentation, or Noetherianity of R or C is assumed. This is a generic off-unit algebra tool, declared in `split_report.tool_uses` for the maintainer to review; no top-level maintainer field was added. It implements the source's 05FR argument without replacing the geometric unit route.

Step 3 uses only `def-weil-pbc-annihilator-associated-primes`, whose statement explicitly supplies an element z with exact annihilator q. Properness forces z nonzero. A denominator in q would kill z, contradicting step 2. This elementary argument needs neither an associated-prime base-change theorem nor an associated-prime invariance theorem.

Step 4 reads the exact statements of both spectrum nodes. `lem-weil-pbc-localization-spectrum-embedding` says the contraction image is precisely primes disjoint from the multiplicative subset. This supplies an actual localized prime over q. `lem-sfb-fibre-regular-localization-spectrum` says that contractions are precisely primes contained in a member of Ass of the closed-fibre module. Its hypotheses are verified with A=R, B=C, N=P; the Noetherian ring is C/mC, not C, and finiteness is over that quotient. These statements give exactly q contained in q-prime, which is all this step takes from them; no use is made of their proofs or of an unasserted choice of maximal ideal.

Step 5 again reads the exact-annihilator definition. All elements of m act as zero on P/mP, so the generated ideal mC kills its annihilator witness. The two inclusions give q+mC contained in the proper prime q-prime. This is elementary ideal arithmetic and quotient action, not a new theorem.

For B1–B7, there are no new nodes to leave with hidden proof sketches, undefined objects, wrong tags or unverified Mathlib matches. The item introduces all its objects and retains its six notion dependencies. All TeX is encoded once. For C1/C4 every non-elementary application has the node statement just described; `citations.json` copies a verbatim statement for every `uses` entry, including elementary steps. For D1–D5 the proof carries the argument and creates no proxy for its conclusion. For E1–E7 I checked the tensor-factor order and scalar action explicitly and kept closed-fibre finiteness distinct from base-ring finiteness. All steps are below 2000 characters, and total assembly text is 2488 characters.

Boundary checks: if P=0 there can be no associated prime of its fibre. If P/mP=0 then Sigma=C includes 0; step 2 forces the fibre to vanish, so again the assumed q cannot exist, consistently with the empty spectrum in the existing 05DE node. If R is a field then m=0 and the conclusion reduces to properness of q, also covered by the argument. If C/mC is the zero ring, the same zero-closed-fibre argument applies; the proof does not assume a nonempty set of maximal ideals. Infinite projective modules remain permitted throughout. No statement was changed during this review.
