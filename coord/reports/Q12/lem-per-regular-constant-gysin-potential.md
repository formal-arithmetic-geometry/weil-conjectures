# Stage-1 report: lem-per-regular-constant-gysin-potential

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-constant-gysin-potential.json`: split proof, existing dependencies only; no new nodes.
- `citations.json`: verbatim statement excerpts for every cited node at every proof step.
- `report.md`: this report and the Q12 review.

Attachments: none. No declaration in `WeilConjectures/` carries the blueprint tag `(blueprint: lem-per-regular-constant-gysin-potential)` or states the item exactly without `sorry`.

WANTED: none. The ILO PDF is in `literature/`, with a saved text extraction under the sandbox’s `source/`.

The item statement was retained verbatim. The previous draft had a complete eight-step proof but no report or citation manifest; those required delivery artifacts are now supplied. No new node was created: each non-elementary ingredient is already stated by an existing DAG node, and the blueprint search found no duplicate blueprint node for this exact F_ell result. The Mathlib searches recorded in the item are the searches actually run on 2026-10-18; their hits are generic sheaf or scheme declarations and do not state the absolute-purity pinning theorem.

## Review by Q12

I read the item statement and its source at ILO Exposé XVII, Propositions 2.4.1.1, 2.4.2.1(a), 2.4.3.3, Lemma 2.4.3.4 and Proposition 2.4.4.1 (pp. 265–268), together with the twist/shift discussion used in Lemma 4.3.1.1. I also read every statement cited by the eight proof steps in the DAG, rather than relying on the imported dependency names.

Step 1 compares the n=1 prime-power definitions with the F_ell definition, using the two potential-dualizing definition nodes. I checked that both definitions use the same supported-kernel costalks, Tate twists, strict-local normalization, and normalized trait transition. Step 2 uses the regular/normal component decomposition, excellent-ring definition, geometric-immediate catenary lemma, and the dimension-function clause of the potential-dualizing definition. I checked the saturated-prime-chain argument and that it is applied componentwise, including the disconnected and empty cases.

Step 3 uses regular-local localization, excellence under localization, absolute-purity Gysin, the regular Gysin calculus, and the potential-dualizing definition. I checked that the local closed-point immersion is finite between regular affine schemes, that the Gysin virtual dimension is `-c_T(x)`, that the inverse class gives the pinning, and that the generic-point class is the identity. Step 4 uses strict-henselization regularity and dimension, the localization lemma, finite-detection, codimension-one costalk reduction, and excellence of the normalization algebra. I checked that the immediate specialization gives the one-dimensional reduced closure, that normalization is a finite strictly henselian DVR trait, and that the finite-detection square can be tested before potentiality is known.

Step 5 uses absolute-purity Gysin and finite-detection. I checked the Gysin composition square at both trait points, including the residue-field finite map and the inverse-Gysin induced pinning; the virtual dimension is `1-d`, so the shifted pinning has the required values at the generic and closed points. Step 6 uses the trait Gysin-residue statement, finite twist pullback, strict-henselian etale sections, and the potential-dualizing definition. I checked the sign in `sp = Cl(1)[2]`, the cancellation with the inverse Gysin pinning, and that trivializing the rank-one twist commutes with averaging, evaluation, normalization, and the even shift.

Step 7 applies finite-surjective potential detection and the potential-dualizing definition. I checked that it reflects the trait compatibility from the normalization back to the original immediate specialization, with no hidden pullback assumption. Step 8 uses finite twist pullback, the potential-dualizing definition, and strict-henselian sections. I checked the supported-kernel costalk identification after local trivialization, the basis-change invariance of the residue square, the even shift, and preservation of the dimension-function equation under addition of `m`.

I retained the earlier attempt’s logged Mathlib searches recorded in the node (grep, LeanSearch, Loogle, and LeanFinder), and read their saved hit lists; these concern ordinary sheaf and scheme operations, not the Gysin pinnings or residue compatibility. I ran the server-side `review_split` check; it returned `PASS; 0 new nodes`. I have not edited Lean or run a compiler or Lake build, in accordance with the stage-1 restriction.

The first full dry delivery passed at `abe3dd35a1` (not pushed). I then replaced introductory citation excerpts with longer verbatim excerpts containing the assertions actually used. The final dry run validates this citation manifest. Every step is shorter than 2000 characters (maximum 1333). No new-node duplicate or small-case review is applicable; the item was checked on a field, an excellent trait, disconnected regular schemes, and the empty scheme.
