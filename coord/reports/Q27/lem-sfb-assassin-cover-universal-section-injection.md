# Delivery report: lem-sfb-assassin-cover-universal-section-injection

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-assassin-cover-universal-section-injection.json` — item, statement, two proof steps, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-assassin-cover-universal-section-injection-local.json` — new statement-only node for Stacks Tag 05DG, no Mathlib match.
- `citations.json` — verbatim statement excerpts for both proof-step citations.

Attachments: none. No sorry-free declaration with the item tag or exact statement was found in `lean/WeilConjectures/` or the slopmaster2 checkout.

WANTED: none.

The imported item had the correct 05DH statement and hypotheses but no proof. Its source proof is not a direct application of a single existing theorem: it first invokes the general localization criterion (05CL), then invokes the local theorem 05DG. I created one supporting node for 05DG rather than restating a clause of the parent. The new node is not a duplicate of `lem-sfb-fibre-regular-localization-spectrum` (05DE), which only describes the regular-element localization spectrum, nor of `lem-trf-universal-injective-check-stalks` (05CL), which is the global localization criterion. The parent retains the original no-faithful-flatness conclusion.

## Review by Q27

I read the item statement and its imported source metadata, then read the complete proof of Stacks `flat.tex` Tag 05DH (lines around the `lemma-base-change-universally-flat` declaration). I also read the complete local lemma 05DG immediately preceding it and the existing DAG statement of the generic 05CL localization criterion. The first parent step uses exactly 05CL's assertion that an A-linear map is universally injective over the base iff every localization at a prime of A is universally injective over the corresponding localized base; its hypotheses match with A=C, source P, target P⊗_C D, and base R. The second parent step localizes at q over p, checks localness, essential finite presentation, finite presentation of P_q, flatness over R_p, and flatness of D_q over C_q, and applies the new 05DG statement. The fibre module and its element-annihilator associated-prime condition are the corresponding localizations of the parent fibre condition, exactly as the 05DH proof says when it passes to R_p→S_q→S'_q. The new node's statement reproduces 05DG's local hypotheses and universal tensor-injectivity conclusion, with the quotient fibre and tensor convention made explicit.

I checked the edge cases N=0 (the associated-prime condition is empty and the map is injective), S'=S (the map is the identity), and a field base (the local condition reduces to the ordinary fibre associated-prime coverage). I checked that the parent proof dependencies are exactly the union of the step uses. I ran LeanFinder, Loogle, grep, and LeanSearch searches for both the parent and the new node, including a second semantic phrasing for each; the returned results contain only flatness, localization, or faithfully-flat ingredients and no exact theorem. The server-side `check_dag` preflight passed before this report was written.

What I corrected: replaced the imported empty proof with the two source-faithful assembly steps and introduced the missing local 05DG statement node. No statement hypotheses were added or removed, and no SGA source was used.

What remains unfinished: the new 05DG node is intentionally statement-only and joins the later proof queue, as required for a one-level stage-1 split.

The local step was checked and corrected before delivery: only R_p→C_q is a local homomorphism, while C_q→D_q is the flat localized map. The associated-prime/fibre condition is used exactly in the source’s reduction from 05DH to 05DG.
