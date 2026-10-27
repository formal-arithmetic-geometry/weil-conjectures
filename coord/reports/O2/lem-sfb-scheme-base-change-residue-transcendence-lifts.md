# Stage-1 report: lem-sfb-scheme-base-change-residue-transcendence-lifts

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-base-change-residue-transcendence-lifts.json — statement, split; no exact Mathlib match after the logged semantic, pattern and source searches. Seven proof steps, using only existing nodes.
- citations.json — one verbatim statement quotation for every step/node citation (17 entries).
- report.md — this report.

New nodes: 0. New Mathlib leaves: 0. The sandbox initially contained only dispatcher marker files, with no earlier proof, report or search log to reuse. The helper write_split.py is sandbox-local and is not part of the delivery.

## Attachments

None. Searched the project WeilConjectures source for the exact blueprint tag and for residue/transcendence terminology. The hits concern support bounds, local dimension formulas, or unrelated residue constructions; no declaration states both conclusions of this item. No Lean was written, no compiler or build was run.

## Wanted literature

None. The proof follows the available Stacks sources.

## Problems found and corrected

The item was unsplit. Its mathematical hypotheses and both conclusions agree with morphisms.tex Tag 02FY (2),(3); no statement dispute is required. Its imported TeX was overescaped (literal doubled backslashes) and used an unsuperscripted prime command: the delivered statement normalizes these to ordinary TeX and primed names, without altering meaning.

The blueprint ancestor command returns None: created.item reaches an imported record without the marker the script uses for a blueprint node. The inherited blueprint.from.node is already null. I retained it and its detailed from.place/via chain, recorded this limitation in split_report, and read the actual current source at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.md. It identifies det-thm-sf-ctf-stability-direct-images and direct-image preservation. This item is a commutative-algebra prerequisite on its recorded proper-support flattening branch, not the unit key node. No unit or chapter file was changed.

The current unit record and chapter record were read. The six-functor route is preserved. The three off-unit non-Mathlib statement tools (fibre-ring residue fields, invariance of dimension at a point, and the local-ring/transcendence-degree formula) are explicitly declared in split_report.tool_uses. No six-functor step is replaced by another route.

## Unfinished work

None in the mathematical split. Existing dependencies remain their own items; no new node is being split recursively.

## Not duplicates

No new nodes. Searched all DAG statements for transcendence degree with field extension/base change and tensor products, searched the tag 02FY and the algebra source label/Tag 0CWE, and searched the blueprint using blueprint_refs.py for 0CWE, inequalities-under-field-extension, transcendence degree, residue, and dimension at a point. In particular lem-sc-fibre-dimension-after-base-change supplies 02FY (1), not this item's two transcendence-degree clauses. The needed 00P4 and 00P1 statements already have nodes, and were reused. The full 0CWE theorem was not made a new node: its argument is expanded here, preventing an affine restatement from becoming the entire split.

## Review by O2

I read morphisms.tex Tag 02FY, including its proof citing Algebra 0CWE, and algebra.tex Tag 0CWE in full. I also read its actual dimension inputs: 00P4 (dimension at a point after field extension), 00P1 (dimension equals local-ring dimension plus residue transcendence degree), and 00ON (dimension formula under going down, hence for flat maps). The affine residue calculation was checked against 00E6 and 0H9M, and the faithful-flatness/surjectivity inputs against 00HI and 00HQ. There are no new nodes requiring separate source reviews.

For step 1 I opened the statements of def-weil-residue-field, def-weil-finite-type-morphism, lem-weil-pbc-cartesian-square-pasting and lem-weil-pbc-fibre-product-affine-spectra. They give respectively the field map, finite-type affine charts, the Cartesian pasting and the spectrum/tensor identification with both projections. The chart on B' is chosen inside g^{-1}(V), which is open; it does not assume that g itself is affine. W is one finite-type affine chart through u, which is sufficient even if f is not quasi-compact. For a prescribed u' its two images lie in the chosen opens, so it lies in their fibre product.

For step 2 I read both clauses of lem-weil-pbc-fibre-ring-primes-residue-fields. They give a bijection of primes AND an isomorphism of residue fields, with the explicit map b tensor lambda mapping to b-bar times lambda-bar. That full statement, rather than the primes-only Mathlib leaf, is needed here. Applied to R to S and R' to C, it identifies the residue fields over the right base fields. The tensor associativity maps and inverses are written out; their compatibility with the inverse kernels verifies contraction to the required original point, not merely existence of an abstract field isomorphism.

For step 3 I opened def-weil-pbc-finite-type-algebra, lem-wf-affine-noetherian-components, lem-weil-pbc-field-extension-base-change-faithfully-flat and def-weil-pbc-faithfully-flat-ring-map. The generator argument makes A finite type over k and T finite type over K. Thus it is these two affine fibre rings that are Noetherian. The original base rings need not be Noetherian. The faithful-flatness leaf applies to any algebra A and any field extension K/k, and the definition explicitly includes flatness; none of these facts is taken merely from a definition of flatness without the theorem supplying it.

For step 4 I read the complete statements of lem-weil-pbc-dimension-at-point-field-extension, lem-weil-pbc-dimension-at-point-local-ring-trdeg and lem-weil-pbc-flat-height-formula. The first requires precisely the finite-type algebra A and an arbitrary field extension; the second applies separately over k and K and explicitly gives finiteness, needed for cancellation; the last applies because A and T are Noetherian and A to T is flat. Its stated quotient-height formulation gives h'=h+height(P/pT). That height is nonnegative because P/pT is a prime, with a length-zero chain. Step 5 is only finite-integer substitution and cancellation from those identities, so it is elementary and introduces no theorem hidden behind a tag.

For step 6 I read lem-weil-pbc-faithfully-flat-surjective-spectrum and lem-weil-pbc-prime-contains-minimal-prime. The first gives an initial P_0 over p. The second applies to the ideal pT contained in P_0, and gives P minimal over that ideal inside P_0. Both inclusions in the contraction equality are written. Minimality then gives height(P/pT)=0 directly from prime chains, as defined in the cited flat-height statement. This avoids assuming that an arbitrary lift or arbitrary minimal prime has the desired contraction. The step-4 equations then give equality of the finite transcendence degrees.

For step 7 I rechecked the same fibre-ring statement: its prime bijection and scalar-compatible residue identification give an actual point of the chart in U' over both prescribed points. The empty cases are quantified correctly: existence is demanded only for compatible pairs. No surjectivity of g is used.

Small cases checked: for A=k and any K/k the only prime of T=K has all dimensions and transcendence degrees zero. For A=k[t], p=(0), K=k(a) with a transcendental, the prime (t-a) of K[t] has r'=0<1=r and e=1, whereas the minimal prime (0) attains r'=r=1. This verifies both the inequality's direction and why equality needs a special lift. For A=k[t]/(t^2), p=(t), the minimal prime remains valid and both transcendence degrees are zero, so reducedness is not being used. Closed original points have r=0 and every lift has r'=0. An arbitrary non-Noetherian base such as an infinite-variable polynomial ring is harmless, since the Noetherian argument only begins after passing to the field fibres. Empty schemes were checked as in step 7.

Against delivery-errors B: no new nodes, no unsplit proof sketches, no invented notions or Mathlib matches; existing definitions are cited for exactly their meanings. Against C: every used non-elementary theorem is an existing cited node, every cited statement was opened, every quote is verbatim, and the generic off-unit tools are declared. The proof never uses a cited node's internal proof or a hidden definition. Against D: the item contains the algebra calculation and the minimal-prime construction itself, not a new-node restatement of its clauses. Against E: both base fields and both affine fibre rings are distinguished throughout, the Noetherian and flat hypotheses are proved exactly where needed, and the tensor/residue compatibilities are explicit. Every step is under 2000 characters; there is no long hidden lemma to extract. No forbidden SGA source is used.

The Mathlib queries in searches.jsonl were executed through msearch.py and their actual hits read. Two semantic phrasings and two grep patterns found residue-field constructions, the trdeg tower identity, and quasi-finite/integral special cases, all insufficient for the present arbitrary locally finite type morphism and arbitrary g. Existing search history on the imported node was retained; this run's records were appended verbatim in query text and tool name.

Final self-review correction: expanded the open-chart universal property in step 1 and cited def-pc-fibre-product. The fact that restriction preserves residue fields is justified there by the cofinal neighbourhoods defining the stalk. These are short elementary arguments, not new nodes. Read the current unit source and the Noetherian-components source/proof under literature/blueprint/latest, and the actual affine-product source 01I4/01JQ plus minimal-prime source 00E0 (4). The first dry run passed; the amended split is submitted to a fresh dry run before pushing.
