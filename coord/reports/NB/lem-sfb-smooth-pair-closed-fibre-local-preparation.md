## Worker report

Item: lem-sfb-smooth-pair-closed-fibre-local-preparation. Group NB, stage 1, 2026-10-24.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-pair-closed-fibre-local-preparation.json: unchanged statement, eight-step split, all dependencies reused; no new nodes and no new Mathlib leaves.
- citations.json: 29 step/node entries with verbatim statements, including every clause used.
- report.md and searches.jsonl: this report and the actual required-search log.

### Attachments

None. Searched the live WeilConjectures source by the exact item id and by closed-fibre local preparation, smooth stalks and closed specialization. No declaration under WeilConjectures states the whole item. Mathlib's formallySmooth_stalkMap_iff at AlgebraicGeometry/Morphisms/Smooth.lean:246 concerns the formal smoothness of a stalk map; it does not give the specialization, fibre prime or dimension clauses. Thus it is neither an attachment nor a Mathlib match for this item. Existing DAG nodes already carry the ingredients and were reused.

### Literature

WANTED: EGA IV4, Proposition 21.14.3(ii), final proof paragraph, and 17.5.3/17.5.8, for lem-sfb-smooth-pair-closed-fibre-local-preparation. The repository has EGA IV1–IV3 but no IV4 PDF at the inherited path. I read the English translation at https://jcreinhold.github.io/ega/iv/34-ch4-21-divisors.html, retaining the consulted page in the sandbox. This delivery has agent proof origin: the actual proof is the explicit assembly of the existing cited Stacks lemmas, not an assertion that the missing PDF was read.

The local Stacks sources read were algebra.tex: Tags 00FN (lemma-Noetherian-permanence), 00FV (theorem-nullstellensatz), 00ES (lemma-irreducible), 00E3 (lemma-spec-localization), 00NP (lemma-regular-domain), 00TT (lemma-characterize-smooth-over-field), 00ON (lemma-dimension-base-fibre-equals-total), 04EG (lemma-localization-formally-etale); schemes.tex: 0HA1 (lemma-local-ring-fibre); varieties.tex: 0478 (lemma-locally-finite-type-Jacobson); morphisms.tex: 01V6 (lemma-smooth-characterize); more-morphisms.tex: 02H6 (lemma-smooth-formally-smooth). Tags were checked against stacks-project/tags/tags. The finite-type, localization, component and residue-field steps below use precisely the statements read there, through their existing DAG nodes.

### What changed and what was wrong

The imported node had no proof. No statement defect was found, and no hypothesis or conclusion was changed. In particular, closedness is only required for the chosen y in V_s, and the bound at z uses both the generic-fibre codimension assumption and the non-generic base case. Finite residue extension is asserted at y, never at arbitrary z. Normality of A_0 is retained, although the local preparation itself needs only its being a Noetherian domain. No excellence or normality of a completion is inferred here.

The online translation's final paragraph has inconsistent x/y/eta notation and even displays a dimension-at-least-one phrase followed by a dimension-at-least-two conclusion. The proof here replaces those ambiguous phrases with the correct explicit cases: s != eta contributes a chain of length one in the base and another in the fibre; s = eta uses the stated generic codimension hypothesis. This clarifies the source's argument without correcting the node's statement.

I read SETUP's fixed chapter/followed unit/free node levels and the current latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and proof. The live unit record still points at an older location/title, while the current unit uses compactification and open direct images; this local algebra node lies below the existing affine-boundary/Ramanujam–Samuel branch serving that proof. No chapter or unit route is changed. blueprint_refs.py ancestor prints null for the item's inherited chain; that metadata is preserved and from.place is made explicit rather than inventing an imported ancestor. Whole-blueprint searches for 'smooth local', 'closed fibre', 'dimension formula' and 'regular local' found no node stating this whole item. The existing regular-local-domain blueprint node and the existing flat-height formula were reused. No new-node duplicate question arises.

### Remaining work

None for this one-level split. Reused unsplit nodes retain their independent obligations; this delivery does not claim those proofs were completed. No Lean was written and no compiler, Lake or build command was run.

## New nodes

None. General local algebra and scheme tools already exist in the DAG. In particular, do not create clause-restatement nodes for closed-specialization preparation, prime fibre ideals, or dimension two: the argument is carried by the eight proof steps.

## Not duplicates

No new nodes. Whole-DAG statement searches reused the existing nodes for smooth stalk formal smoothness, smooth fibres, Jacobson density, Zariski's lemma, fibre stalk quotients, regular local domains, flat height formula, Noetherianity, and prime localization.

## Review by NB

I reviewed delivery-errors B–E with the item, every cited statement and the sources open. The unchanged statement agrees with the preparation in EGA IV4 21.14.3(ii), final paragraph, with the generic-base case made unambiguous. All objects in it are introduced and its definition dependencies are retained. There are zero new nodes, so no new statement-only, missing-definition, same-tag-duplicate or fabricated-search issue. I ran msearch.py for the item in two semantic phrasings as well as Loogle, LeanSearch and two source greps, read the hits, and retained the actual log. The hits give smooth charts, smooth loci, a formally smooth stalk criterion and finite residue fields under quasi-finiteness; none supplies this conjunction under the closed-pair hypotheses. No recorded search was invented.

Step 1 uses the affine smooth/ring-smooth equivalence exactly on Spec B_0 -> Spec A_0; the smooth-ring definition supplies a finite presentation, so the finite-type Noetherian lemma really applies. The affine fibre-product lemma explicitly identifies the tensor coordinate ring and its projections. The smooth-fibre node explicitly gives both base-changed smoothness and regularity of all its prime localizations. The scheme-fibre definition supplies the topological fibre identification. These tools do not assert local finite presentation of the stalk map, and the proof does not need that false assertion.

Step 2 uses the Jacobson node's statement about closed points of the ambient fibre being dense in every closed subset. Applying it to the nonempty closure of z gives a y closed in the whole fibre, not merely in the closed subset as an abstract space. That closure is inside Z_s because Z_s is closed. Zariski's lemma is applied to the field C/M, whose finite algebra generators are the images of a finite generating list of C. The fibre-stalk quotient node really gives the actual map with kernel m_A B, so it identifies fibre and total residue fields compatibly with the base field. No algebraic-closure hypothesis is used.

Step 3 uses the germ-compatible affine-stalk localization node, then the Noetherian-localization node on A_0 and the already Noetherian B_0. The definition of flat scheme morphisms explicitly mentions the locality of actual stalk maps; this is used only for locality, not as evidence of flatness. The same-unit smooth-stalk node states square-zero lifting for all maps into D/J. Restricting that quantifier to maps killing a maximal-ideal power is precisely the stated adic formal-smoothness definition. No completion theorem or extra local-algebra hypothesis is being smuggled in.

Step 4 uses the fibre-stalk quotient at y and the regularity already obtained in step 1. The regular-local-domain node states nonzeroness as well as absence of zero divisors. This justifies primeness of p=m_A B directly by the kernel test. Smoothness of the fibre alone would not make its entire coordinate ring a domain; the argument correctly takes the local ring at y.

Step 5 opens the component/minimal-prime node: it states that the fibre components are V(N) for minimal primes N of C. Thus if P_w were minimal, the closed Z_s would contain that entire component. The separate minimal-prime-existence node gives N_w strictly below the resulting nonminimal P_w. The localization node supplies contraction as inverse to extension; this proves strictness survives localization. The dimension conclusion is a displayed prime chain, using the definition, and is not confused with topological dimension at a nonclosed point.

Step 6 uses flatness of the smooth coordinate-ring map, not flatness of a map to a quotient. Both coordinate rings are Noetherian before applying the flat-height formula. The formula's equivalently clause is exactly the local-dimension equality used here. The Noetherian-local finite-dimension node ensures dim A is finite, so adding a positive fibre dimension gives a strict inequality. The fibre-stalk quotient is already established in step 4. No universal catenarity is required by the formula.

Step 7 writes out the prime and map: q_z=Q_z(B_0)_{Q_y}, with Q_z subset Q_y. The localization correspondence gives primeness and contraction, so containment of m_A B is legitimate. If equality held, the localized P_z would be zero in C_M. But N_z strictly below P_z also lies under M and stays strictly smaller after localization; zero cannot have such a prime below it. Hence containment is strict. Iterated localization is exactly clause (1) of the reused node, and its fraction formula followed by the germ-compatible affine-stalk isomorphism makes B_(q_z) -> O_(V,z) canonical. This establishes the actual identification, not just equality of dimensions of unrelated rings.

Step 8 is a real case split. Because A_0 is a domain, a nongeneric prime sigma is nonzero; the localization correspondence preserves (0) < sigma and gives dim A >= 1. The dimension equality at z and positive fibre-local dimension then give >=2. At the generic point the base stalk is the fraction field, its maximal ideal is zero and the fibre-stalk quotient identifies the total stalk with the generic-fibre stalk; the hypothesis now gives >=2. This avoids applying the generic codimension hypothesis on a nongeneric fibre.

Small cases checked: Z empty makes the assertion vacuous; a zero-dimensional smooth fibre cannot meet Z because every point is a component; for a field base the entire argument lands in the generic case and requires the given codimension-two bound; for a DVR base, a nongeneric non-component fibre point gives the expected minimum total dimension two. An example A_0=k[t], B_0=A_0[u], Z=V(t,u) has y=z, p=(t) properly below q_z=(t,u), dim B=2>dim A=1, and empty generic Z. Thus neither z!=y nor nonempty generic Z was inadvertently required. For A_0=k, B_0=k[u,v], Z=V(u,v), p=0 is properly below q_z and dim B=2. Disconnected smooth fibres cause no issue: regular-local-domain is used only after localization. The finite field extension at y may be inseparable; no separability was added.

All eight steps are below 2000 characters; none hides an uncited long comparison. The non-elementary tools are existing cited nodes and the short kernel, prime-chain, fraction and case arguments are written in the item's steps. citations.json quotes each whole cited statement verbatim, covering the exact clauses described above. There is no new lemma that restates an item clause, no proof moved into a surrogate node, no SGA citation, and no statement weakening. The off-unit comparison tools are lem-weil-pbc-smooth-ring-map-iff-smooth-affine (specified smoothness versus coordinate smoothness), lem-weil-pbc-smooth-fibre-regular-local (regularity of arbitrary smooth affine fibres), and lem-sbc-scheme-fibre-stalk-quotient (actual stalk quotient). They are generic tools absent from this unit; split_report.tool_uses declares these uses for maintainer judgment and no maintainer-owned tool_uses field was written.

A fourth generic off-unit tool is lem-weil-pbc-localization-prime-residue-field-iso: its prime correspondence preserves the strict chains in steps 5, 7 and 8. I declared it alongside the other comparison tools in split_report.tool_uses. The separate server checks completed with review_split PASS and check_dag OK.
