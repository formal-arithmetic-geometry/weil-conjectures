# Stage-1 report: lem-sfb-nonrational-localizing-lower-shriek-composition

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-nonrational-localizing-lower-shriek-composition.json` — statement, split proof in seven steps, no new node and no Mathlib leaf.
- `citations.json` — 35 entries, one verbatim statement quote for every cited node in every proof step.

## Attachments

None. I searched the slopmaster2 project for the item tag and for the lower-shriek composition declarations; no sorry-free declaration under `WeilConjectures/` states this finite/integral localizing-category result exactly.

## WANTED

None.

## Problems found and corrected

The imported item was unsplit and had no proof. Its statement agrees with clause (1) of `sk-thm-sf-comp-composition` for the finite and integral coefficients `A`, `Z_ell`, and `O_E`; I retained all hypotheses and the ordinary unbounded module-object category. I found no statement error, duplicate node, or Mathlib match. The proof is the existing compactification/interchange route, specialized only by replacing the rational admissibility sentence with the stated finite/integral coefficient range. No SGA source is used.

## Review by Q92

I read the item node, `sk-lem-sf-mate` unit and the `sec-six-functors-basics` chapter, the main-20261015 proposition `sk-thm-sf-comp-composition` and its complete proof, and the current statements of all 20 proof dependencies. I also checked the slopmaster2 source tree for the item tag and lower-shriek composition names; only declarations with sorry or differently typed results occur, so there is no attachment.

Step 1 uses `sk-thm-nagata-compactification` for dense compactifications, `lem-weil-pbc-proper-fp-permanence` for separated/finite-type and proper composition, `sk-def-nagata-sketch-data` for the compactification data, and `sk-def-sfb-dc-setting` for the standing schemes. I checked that the intermediate schemes and the composite open/proper factor have the required hypotheses and that scheme-theoretic density is preserved by the two open immersions.

Step 2 uses the exact module extension-by-zero and adjunction in `sk-def-sfb-module-lower-shriek`, exact coefficient pullback from `sk-prop-sfb-cartesian-coefficients`, and the unbounded derived-category conventions in `sk-def-sfb-derived-categories`. The cited module pushforward/pullback, derived ringed-topos pushforward composition, K-injective preservation, and underived module pushforward composition nodes provide exactly the reassociation and restriction facts used. I explicitly checked that all actions remain over the pulled-back `Lambda_T` rings.

Step 3 uses `det-proper-image-localizing-open` to put `j_!K` in the localizing closure, `det-sf-comp-composition-interchange` for the unique restriction-normalized interchange map and its invertibility, and `det-sf-comp-coherence-single` for the localizing codomains. I checked the hypotheses for `Lambda` in `{A, Z_ell, O_E}`, the proper map `p`, the quasi-compact open `i`, and the dense auxiliary compactification, and verified the displayed natural isomorphism has the claimed source and target.

Step 4 uses the refinement morphism, refinement comparison, common dense refinement, and coherence cocycle statements. I checked that both maps compared have the same restriction-normalization, that the auxiliary refinement is proper, and that the cocycle gives independence of the auxiliary compactification.

Step 5 checks refinement of the compactification of `f`: `det-nagata-refinement-morphisms` supplies properness and the inverse-image condition, Nagata supplies the compactification of `uh`, and the interchange/coherence nodes identify the two maps by their common restriction. I included `det-proper-image-localizing-open` at the point where `j'_!K` is used, so the localizing-domain hypothesis is explicit.

Step 6 performs the analogous refinement check for `g`; I verified the constructed model for `i'p`, properness of the composite, and the restriction-normalized uniqueness argument. Step 7 uses `det-nagata-refinement-common-dense` and `det-sf-comp-coherence-cocycle` to descend from dense auxiliary choices to arbitrary chosen compactifications and establish compatibility with every comparison.

I tested the statement on identity and proper maps, two successive open immersions, an empty source, zero objects, and shifts; the construction reduces to the identity or the corresponding evident zero map in each case. I ran the required LeanFinder, Loogle, Mathlib grep, and LeanSearch queries; they returned only generic pushforward composition or topological compact-support declarations, so the item is not a Mathlib leaf. The server `check_dag` request was submitted before this report; it was queued by the server's worktree-capacity limit, with no mathematical error returned.

## Second reading by Q92

I opened the blueprint source `sk-thm-sf-comp-composition` (`_section.md` and `sk-thm-sf-comp-composition.proof.md`) and the item node. The finite/integral coefficient statement retains the standing characteristic, separated finite-type scheme, ordinary unbounded module-object, localizing-closure, and compactification hypotheses clause by clause; identity, proper, empty, zero-object, and shift cases reduce as claimed.

- Step 1 was checked against `sk-thm-nagata-compactification`, `lem-weil-pbc-proper-fp-permanence`, `sk-def-nagata-sketch-data`, and `sk-def-sfb-dc-setting`; the compactification and density hypotheses type-check, and the density argument now explicitly composes the two structure-sheaf injections for every composite open.
- Step 2 was checked against all nine cited module, derived-category, coefficient, K-injective, and pushforward-composition statements; the adjunction, reassociation, restriction, and coefficient-action claims use exactly those statements.
- Step 3 was checked against `det-proper-image-localizing-open`, `det-sf-comp-composition-interchange`, and `det-sf-comp-coherence-single`; the admissible coefficient set, localizing domain, normalized restriction, and codomain are correctly typed.
- Step 4 was checked against the refinement, interchange, common-dense, cocycle, and refinement-morphism statements; both auxiliary choices are compared by the stated normalized restriction and cocycle.
- Step 5 was checked against the refinement morphism, properness permanence, Nagata, interchange, coherence, and open-localizing statements; the refined first compactification and all maps are typed, with the separated/finite-type argument written explicitly.
- Step 6 was checked against Nagata, properness permanence, refinement coherence, interchange, and refinement morphisms; the refined second compactification and its restriction normalization are typed, with the separated/finite-type argument written explicitly.
- Step 7 was checked against `det-nagata-refinement-common-dense` and `det-sf-comp-coherence-cocycle`; the descent to arbitrary compactifications and compatibility with each comparison follow from the displayed formula and cocycle.

There are no new nodes: all 20 proof dependencies are existing DAG nodes, and `citations.json` contains an exact statement quote for every cited dependency in each step. Searches in the worker split and a fresh DAG grep found no duplicate node; LeanFinder/Loogle/LeanSearch hits are generic pushforward or topological support declarations and do not state this compactification-defined result. I changed the item metadata to the Q92 item, added the missing pulled-back-coefficient and module-object definition citations to its statement dependencies, and changed Steps 1, 5, and 6 to replace prohibited “same argument” shorthand with explicit density and finite-type composition arguments.
