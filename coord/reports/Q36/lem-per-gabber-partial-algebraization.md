# Q36: lem-per-gabber-partial-algebraization

## Files written

All node files are under dag/nodes/sec-deligne-laumon-a1/.

- lem-per-gabber-partial-algebraization.json: statement, split into seven proof steps; original statement retained. No Mathlib match.
- lem-per-cohen-gabber-finite-presentations.json: new statement-only lemma, unsplit; no Mathlib match. The equal- and mixed-characteristic power-series presentations, including the special-fibre etale open.
- lem-per-weierstrass-henselian-cylinder.json: new statement-only lemma, unsplit; no Mathlib match. Coordinate change, distinguished polynomial, henselian cylinder and its two completions.
- lem-per-elkik-finite-etale-away-completion.json: new statement-only lemma, unsplit; no Mathlib match. Elkik's equivalence for finite algebras etale off the completion ideal.
- lem-per-finite-henselian-algebra-local-model.json: new statement-only lemma, unsplit; no Mathlib match. Descent to a finite-type strict local model.
- citations.json: one verbatim statement quotation for every step/node citation.
- report.md: this report.

The earlier sandbox nodes, search results and searches.jsonl were retained and read. The report was missing on resumption; no deliver.py or srvcheck.py for this item was active. The current repository still has the item unsplit and has none of these four children. Only proof, proof dependencies, proof origin, status, blueprint place and split report differ from the current item. No Lean or unit/chapter files were written.

## Attachments

None. Searches under /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the item tag, partial algebraization, Cohen–Gabber, Elkik, Weierstrass and henselization found no declaration proving the item or any child exactly. General henselian and etale declarations do not supply these statements. The upstream master was not treated as completed proof evidence.

## Wanted literature

None. The ILO volume and the relevant Stacks .tex sources are available locally.

## Issues found and changes made

The original node was an unsplit geometric partial-algebraization interface used in Step 4 of lem-per-gabber-local-duality-general. The current blueprint ancestor's Step 1 uses arbitrary-field Verdier duality, reached through the finite-coefficient duality construction. The seven steps supply this algebraic input without replacing the unit route. There is no blueprint_update on the touched item or its ancestor, and this is not the unit's key node.

ILO V 3.1.3 states a stronger prime-to-ell cover in mixed characteristic, but this item's statement requires only a finite surjection. IV 4.2.2 supplies the needed normal finite cover with an etale open meeting the special fibre, followed by V 1.1–1.2 and the descent argument of V 2.2.7. No prime-to-ell assertion is inferred from IV 4.2.2. Equal characteristic keeps the identity cover, as V 3.1.4 requires.

The saved proof had already corrected the lying-over citation to the injective version and added the integral-prime-over-maximal lemma to Step 5. On this resumption I retained those corrections and made the restriction of the etale map in Step 2 explicit: open immersion, etale composition, and cancellation, citing the existing Mathlib leaf lem-weil-pbc-etale-composition-cancellation. This avoids silently using etale stability under localization. Completion is kept as Spec of the completed ring, as in ILO, rather than a formal scheme.

Mathlib searches recorded in the four new files are exactly the saved queries in searches.jsonl, with actual saved outputs. Each child has two semantic phrasings, Loogle, grep and LeanSearch. The Weierstrass search finds PowerSeries.exists_isWeierstrassFactorization at Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean:811; I read that declaration. It supplies ordinary one-variable preparation but neither the coordinate change nor the henselian cylinder's distinguished-polynomial completion, so the combined cylinder statement is not a one-line specialization. The Elkik hits are etale finite-presentation/descent or ordinary henselian-root infrastructure, not an equivalence for possibly ramified finite algebras. The local-model searches likewise do not identify a henselized finite algebra with a finite-type strict localization. The complete-local excellence statement already exists as lem-per-complete-local-excellence, so no new excellence node was created.

## Unfinished work

No gap is left in the item's seven-step argument. The four new supporting results intentionally remain statement-only nodes for subsequent stage-1 work. There are no new Mathlib leaves.

## Not duplicates

Searched the whole DAG by the names/concepts Cohen–Gabber, Elkik, Weierstrass, finite henselian models, and by Stacks Tags 05WP and 04GH; also ran blueprint_refs.py search for Cohen, Elkik, Weierstrass and henselization, and its ancestor command. No blueprint node states any proposed child. Ordinary Cohen structure theorems produce a power-series surjection, not a finite generically etale inclusion.

lem-per-finite-henselian-algebra-local-model vs lem-sbc-finite-strict-henselian-algebra-etale-section: the latter splits surjective etale covers of finite algebras; it does not descend a finite algebra over a henselization to a finite-type strict local model (shared Tag 04GH).

lem-per-finite-henselian-algebra-local-model vs lem-real-henselian-residue-galois-action: the latter constructs an action on residue-field constants over a finite field, not a finite-type model (shared Tag 04GH).

lem-per-finite-henselian-algebra-local-model vs lem-trf-finite-base-strict-localization: the latter identifies strict localizations after an already given finite morphism and its base changes; it does not construct a finite-type model for an arbitrary finite algebra over a henselization (shared Tag 04GH).

lem-per-finite-henselian-algebra-local-model vs lem-weil-pbc-finite-over-henselian-local-product: the latter gives henselian factors and finite residue extensions, without descent to a finite-type strict local model (shared Tag 04GH).

lem-per-finite-henselian-algebra-local-model vs lem-weil-pbc-finite-local-henselian: the latter proves henselianity for a finite local algebra, not model descent or identification with a strict localization (shared Tag 04GH).

lem-per-finite-henselian-algebra-local-model vs lem-trf-strict-henselization-quasi-finite-ring: the latter concerns a given finite-type quasi-finite ring map and its strict henselizations; the new statement starts with a finite algebra over the henselization and asserts existence of a finite-type model. Neither statement includes the other's existence assertion.

lem-per-weierstrass-henselian-cylinder vs lem-weil-pbc-henselization-noetherian-completion: the latter handles the completion of a pair and its henselization, without a Weierstrass coordinate change or identifying the distinguished-polynomial completion with the maximal-ideal completion.

lem-per-cohen-gabber-finite-presentations vs lem-weil-pbc-cohen-structure-power-series-surjection: the existing node is a surjection from a Cohen power-series ring, with neither module-finite injection nor etaleness on a special-fibre-dense open.

## Review by Q36

I read ILO IV 2.1.1–2.1.2 and IV 4.2.2–4.2.5 for the presentation child; V 1.1.1, 1.1.3 and 1.2.3 for the cylinder; V 1.2.4 for Elkik's exact category equivalence; V 2.2.7 and XVII, the final paragraph of 6.5, for finite-type descent and the strict-local form. I read V 3.1.3–3.1.4 and XVII 6.5 for the item itself. For the local-model child I additionally read Stacks algebra.tex Tag 05WP (lemma-quasi-finite-henselization) and Tag 04GH (lemma-finite-over-henselian). The child packages the genuine descent and local henselization identification, not the item's partial algebraization. Its future proof descends a finite presentation and monic integrality relations along etale neighbourhoods, selects the point under the local algebra, and identifies its henselization using 05WP; the finite purely inseparable residue extension of a separably closed field makes it strict.

For Step 1, I opened every cited node: the presentation provides the normal finite injection and the regular bases with their dimensions; finite-over-complete-local-product explicitly includes the domain case, so its completeness and locality conclusion applies to A'. The finite-morphism definition, finite-integral lemma, and injective lying-over lemma provide a finite surjection, with injectivity actually supplied. The complete normal local input is a domain. The base has dimension d-1 in both characteristic cases. The residue characteristic differs from ell, hence ell is a unit in the local base.

For Step 2, the cylinder is applied to ft_r, which remains nonzero modulo the coefficient maximal ideal and is a nonunit. It supplies a positive-degree distinguished polynomial, a Noetherian henselian H, the pair (H,gH), and both completion identifications. The inverse coordinate automorphism re-expresses the finite presentation over R. I checked the additional etale-composition-cancellation node gives exactly the open-immersion, composition and cancellation clauses used to restrict the map to D(ft_r). This node is a Mathlib leaf. The construction works for r=1 without any coordinate changes; in particular mixed dimension d=2 is covered.

For Step 3, I checked the Elkik node assumes a Noetherian henselian pair, not smoothness everywhere. Step 2 supplies exactly that pair; A' is finite over its completion R and is etale outside g. The conclusion gives a finite H-algebra C with R tensor_H C isomorphic to A' as an R-algebra. No assertion about the ramification over V(g) is needed.

For Step 4, I checked each hypothesis of the local-model child: D is Noetherian; D[T] is finite type; q=(m_D,T) is maximal with separably closed residue field; H is its local henselization. The completed tensor is A', a nonzero local domain. Its conclusion gives C itself as the strict localization of a finite-type D-scheme at a geometric point over q, not merely a ring with an abstractly isomorphic completion.

For Step 5, I opened completion-finite-extension, finite-algebra-local-radical, finite-integral, and integral-prime-over-maximal-maximal. The completion theorem supplies the canonical C-algebra comparison as a product over primes over m_H. The last two prime facts show those primes are maximal, and locality makes exactly one; the finite-algebra-local-radical statement shows that C's maximal ideal does lie over m_H. Thus the product is the maximal-ideal completion of C. The resulting A' isomorphism is compatible with the completion map, which is needed for the regularity assertion later.

For Step 6, complete-local-excellence applies to D; finite-type-localization-excellent applies to F over D. The regular-strict-local-model statement explicitly makes both strict localizations excellent, so applying it to the identity of Z gives excellence of C. I checked its statement rather than borrowing a property from its proof. The excellent-ring definition gives the G-ring hypothesis, and g-ring-completion-regular gives flatness and geometrically regular fibres for the actual canonical completion morphism. Step 7 uses the universal-catenarity clause of the excellent-ring definition and exactly the local-existence clause of local-dimension-function-calculus. The statement dependencies were also opened and checked for their named notions.

I checked B–E of delivery-errors point by point. The four children have self-contained statements, introduce their objects, cite the relevant definitions and retain empty proofs. They are substantive algebraic inputs rather than individual clauses of the item. The split itself constructs S, Z, the cover and the completion comparison and verifies excellence, regularity and the dimension function. No non-elementary input is supplied only by a prose source citation. Off-unit generic commutative-algebra tools are declared in split_report.tool_uses. No stage-2/3 or SGA route is used. All seven steps are shorter than 2000 characters.

Small-case checks included equal-characteristic dimension two (D a one-variable power-series ring), mixed-characteristic dimension two (D the coefficient DVR, r=1), ramification allowed along V(g), the nonzero-local hypothesis that excludes the zero algebra and multiple components, and imperfect separably closed residue fields, where a finite purely inseparable residue extension is still separably closed. For the cylinder, the nonzero reduction and nonunit hypotheses ensure n>0; no claim is made for a constant unit. The identity cover in equal characteristic and canonical completion-map compatibility are retained. No statement dispute was found.

The saved citation file was checked against current node statements, then extended for the explicit etale restriction argument. A preliminary server review_split returned PASS. The required full dry run and delivery are the final checks.
