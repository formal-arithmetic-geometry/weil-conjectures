## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-compatible-regular-local-field-presentations.json — statement item, now split into eight steps; no Mathlib match for the whole assertion.
- citations.json — 25 step/node pairs, each quoting the cited statement verbatim.
- report.md and searches.jsonl — review and actual search records.

New nodes: none. New Mathlib leaves: none. Existing Mathlib leaves supply all the non-elementary algebra.

Attachments: none. No project declaration states the item. Searches for the exact blueprint tag and the concepts under lean/WeilConjectures found complete-local presentation theorems instead. In particular RingHom.exists_complete_local_map_regular_presentation in RingTheory/CompleteLocalMapRegularPresentation.lean assumes complete Noetherian local rings; it does not establish this item, even though its own assembly proof is present. No compiler was run.

WANTED: none.

The item statement is unchanged. Its original source describes a construction rather than a named theorem, so proof_origin is honestly agent. The split spells out that construction rather than treating Tag 00QM (a definition) as an existence theorem. No false statement or source error was found. The inherited null blueprint ancestor is retained: blueprint_refs.py ancestor prints None. This node is a commutative-algebra supporting input under the local-CI comparison, not a new claim about the six-functor theorem itself. The chapter, unit and latest blueprint direct-images proof (3) were read, and the inherited route is preserved.

Searches: the pre-existing five item search records were retained. Five fresh queries were actually run with msearch.py, covering LeanSearch, Loogle, grep and two LeanFinder phrasings. Their returned results were read. The first semantic results concern smoothness/localization; the second gives IsLocalization.liftAlgHom and related localization constructions. These are useful elementary operations, not a one-line proof of the simultaneous surjective presentations with all three regular-local conclusions. Loogle and the specific regular-presentation grep returned no hits. Whole-DAG searches included 00QM, 00OQ, polynomial/localization/regularity and finite-type presentations. Whole imported-blueprint searches included polynomial, compatible polynomial, polynomial regular, regular local, 00QM and 00OQ. There is no equivalent blueprint statement.

## Not duplicates

No node is created. The existing lem-trf-compatible-polynomial-fraction-presentations compares two surjections onto one algebra, without local rings, and supplies neither this local-map square nor its flatness and regular fibre. The existing field-polynomial regularity, free flatness, localization flatness, composition and prime-local quotient statements are cited directly instead of being recreated. No other node is edited.

## Review by Q50

I read algebra.tex Tag 00QM (definition-essentially-finite-p-t), 00F3 (definition-finite-type), 00OQ (proposition-finite-gl-dim-polynomial-ring), 00CT (proposition-localize-quotient, including its fraction maps), 00HT (lemma-flat-localization), 00HC (lemma-composition-flat), and the opening of the proof of 051G (lemma-local-artinian-characterize-flat) which explicitly states free/projective flatness. The last use is the unconditional opening sentence, not the Artinian converse. I checked the tag/label mapping in tags/tags. There are no new-node sources to audit. The item takes the construction specified in its source and justifies each part with these existing statements.

Step 1 uses the actual definitions of essentially finite type and finite type to choose C, W and finitely many generators; the polynomial node gives evaluation, and the prime-localization node gives the fraction relation and the maximal ideal. I checked that C need not embed into A: lifting both numerator and denominator from C is enough. No unjustified identification of A with C localized at a prime is made. The resulting polynomial-local map is surjective because every original W-denominator is outside the inverse image of the maximal ideal. Its locality follows from its explicit formula.

Step 2 uses those same four definitions for B and for the simultaneous evaluation b:k[X,Y] to B. The Y variables alone represent every original numerator and denominator of B. Thus no finite-type assumption on the map f is needed and no lift of f to a polynomial ring is assumed. The inverse image Q of the maximal ideal is a proper prime, so S is a nonzero local ring.

Step 3 cites the prime-localization statement for both maximal ideals. I checked both directions of f inverse(m_B)=m_A: the assumed localness supplies one, and preservation of units supplies the reverse. This proves Q intersect P=p, which is what allows every P-denominator to enter S and proves u local. The fraction equation proves the actual requested equality vu=fq, including coefficients and inverted denominators; it is not just an equality on selected generators.

Step 4 cites lem-weil-pbc-polynomial-ring-field-regular-ring, whose statement explicitly gives regularity at EVERY prime, not just maximal polynomial primes. This proves regular locality of P_p and D_Q even for nonclosed points. The essentially-finite-type definition applies directly to these finite polynomial algebras. No completeness or residue-field separability enters.

Step 5 writes the common-denominator description of R[Y] and both inverse fraction maps identifying D_Q with E_(Q_E); it cites polynomial monomial expansions and the prime-localization fraction definition. This is an elementary localization calculation, not a hidden general comparison lemma. Q_E is prime as the inverse image of QS and membership h/t in Q_E is equivalent to h in Q, since t is outside Q. The formulas verify both existence and inverse identities.

Step 6 uses the monomial definition to exhibit E as a free R-module. The cited projective-module-flat node explicitly includes every free module, so no finite-rank hypothesis is needed. The localization-flat node applies to E at the complement of Q_E; the flat-composition node then gives flatness of u. These are precisely the three cited statements, not consequences inferred from the flatness definition alone.

Step 7 uses the prime-localization node's residue FIELD, not the scheme-only residue-field definition. Coefficient reduction identifies E/m_R E with K[Y]: a zero polynomial is detected coefficientwise. The prime-local quotient node states the exact quotient-of-localization isomorphism used for F; its ideal is contained in Q_E because u is local. The field-polynomial regularity node applies to K even when K/k is inseparable. This proves regular locality and nonzeroness, since the localization prime is proper.

Step 8 applies that same prime-local quotient node to D and pD, which is contained in Q by Step 3. I checked m_R S=pS, so it is the same F, not a different fibre. The finite-type definition shows D/pD is generated by the finitely many classes of X,Y; the essentially-finite-type definition then applies to its prime localization. This avoids an invalid claim that the field K itself is a finite-type k-algebra. All maps in these identifications respect k by their formulas.

Small cases checked: empty X and Y variable lists; A=B=k with identity map (R=S=F=k can be chosen); A=k and B=k(t) (a nonclosed polynomial prime and F=k(t)); the nonflat quotient k[x]_(x) to k (R=k[x]_(x), S can equal R, u identity, F=k); nonreduced A=k[e]/(e^2); and an inseparable residue extension in characteristic p. The construction only uses unit preservation and localness of f, not flatness, reducedness, completeness or separability. A local ring here has a proper maximal ideal, so the zero ring is outside the hypotheses and cannot produce a spurious empty fibre.

B1–B10: no new nodes; all existing metadata retained, TeX escapes checked, all search records correspond to actual queries, and blueprint identity/ancestry preserved. C1–C8: opened every cited statement; the 25 quotes are complete verbatim statements; every non-elementary use is an existing leaf, with no off-route open theorem or new cycle. D1–D5: the proof carries the actual evaluation, denominator, contraction, flatness and fibre calculations, rather than moving clauses into new nodes. E1–E7: checked the hypotheses and small cases described above. All proof steps are below 1000 characters; no long non-elementary step hides a lemma.

Corrections during self-review: I gave F a second quotient-localization description over k to verify its essential finite type directly, and made the prime contraction and commuting square explicit. No statement correction was necessary. Nothing remains unfinished; the required remote dry run and delivery results will be recorded below after they finish.

Validation: the required server review_split check passed. The full deliver.py --no-push process exited successfully with OK (not pushed), commit e033e1fdaeb, and preflight passed, including check_dag and review_split. This is the direct-delivery brief: Q50 performed the substantive self-review above, and the maintainer independently reviews the pushed delivery.
