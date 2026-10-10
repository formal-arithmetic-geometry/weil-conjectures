Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-torsor-h1-ext-pushforward.json` — statement, split; no Mathlib match.
- `citations.json` — verbatim statement excerpts for every cited node and step.

Attachments:

- None.

WANTED:

- None; the Stacks source paths are recorded in the item and the cited existing nodes.

What was wrong or incomplete:

- The imported item had no proof and was marked `unsplit`. I supplied the missing argument. No statement change was needed, and no new node was required because exact direct-image preservation is already stated by `lem-sc-closed-immersion-pushforward-exact` and the remaining fibre identification is a sectionwise calculation.

What could not be finished:

- Nothing.

## Review by J1

I read the item and its neighboring route in `lem-sc-torsor-h1-functoriality.json`, along with the existing statements of `lem-sc-closed-immersion-pushforward-exact`, `def-weil-closed-immersion`, `def-sc-zariski-site`, `def-sc-topological-abelian-cohomology`, and `def-sc-gm-torsor`. The item statement agrees with the direct-image and fibre constructions attributed to Stacks Lemmas 01AX, 02UV, and 02FQ, including the hypotheses that i is a closed immersion, the sheaves are on the small Zariski sites, and the sequence is short exact.

Step 1 uses the exactness assertion of `lem-sc-closed-immersion-pushforward-exact`, whose statement explicitly says that i_* preserves short exact sequences, and uses the topological-sheaf setting to interpret the sequence. The pullback along u is then the stated fibre-product construction. Step 2 uses the closed-immersion section formula and the Zariski sheaf definitions: on each open U, the pullback fibre consists exactly of sections e on U intersection Z with p(e) equal to the restriction of 1, which is T(U intersection Z). The restriction maps and translation action are preserved pointwise, giving the torsor isomorphism. I marked this calculation elementary because it is direct unpacking of the definitions cited in the step.

I tested the calculation in the edge cases i equal to the identity (where P and T are unchanged) and Z empty (where both sides are the terminal torsor). I also checked that every node named in a proof step exists, that each citation quote is copied verbatim into `citations.json`, that the blueprint ancestor and proof route are unchanged, and that no existing Lean declaration carries this item’s blueprint tag.
