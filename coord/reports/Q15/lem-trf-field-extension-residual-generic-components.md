# Q15 stage-1 delivery: lem-trf-field-extension-residual-generic-components

## Files written

- dag/nodes/sec-trace-formula/lem-trf-field-extension-residual-generic-components.json: existing statement node, now split into six proof steps; no full Mathlib match.
- citations.json: sixteen entries, one for every step/node citation, quoting verbatim the statement of that existing DAG node.
- searches.jsonl: unmodified search-command log; six searches run in this attempt and their actual results retained.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The proof uses existing Mathlib leaves for its non-elementary facts. The statement and its statement dependencies are unchanged.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and residual-generic/field-extension terminology, then for genericPoints, minimalPrimes and IsGenericPoint in AlgebraicGeometry. The returned project declarations concern other generic-fibre or curve statements and do not state every clause here. A declaration in Mathlib or an upstream declaration still containing sorry is not an attachment.

## WANTED

None. All source passages used are present in literature/stacks-project/.

## Issues in the imported node and source

The item had a statement and searches but no proof. Tags 0GSI and 05DC explain why its component bookkeeping is needed, but they do not directly prove this unrestricted statement: 05DC is about associated points and assumes locally finite type. I did not apply that theorem after dropping its hypothesis. Instead the proof uses the residual-fibre universal property displayed in its proof, flat going-down (00HS), and the existing affine-spectrum component theorem (00ES). The statement itself is correct, so no STATEMENT-DISPUTED correction is needed. No additional algebraicity, separability, finite type, Noetherianity or reducedness assumption is introduced.

The chapter and unit records were read. This item is a small tool below the semistable-alteration branch of lem-trf-local-term-locality, not the unit's key node; no chapter/unit edit is needed. The inherited blueprint ancestor and exact proof place are retained; whole-blueprint searches for residual generic, generic component, minimal primes, going down, generic points and field extension found no blueprint node giving this statement. Existing finite-scalar-extension generic-point results require a finite extension and include additional finite-degree conclusions; they cannot replace this arbitrary-extension residual-fibre criterion.

## Unfinished work

None in stage 1. This delivery supplies the complete natural-language split only, as authorized; no Lean file was written and no compiler or build tool was run.

## Not duplicates

No new node was created, so there are no new/existing same-tag pairs. In particular the existing lem-sc-flat-going-down is cited directly, rather than recreated, and the narrower existing lem-sfb-finite-scalar-extension-generic-points is not duplicated.

## Review by Q15

I read the actual statements of every cited node and compared their claims with the use in the proof. I also read Stacks more-morphisms.tex at lemma-associated-point-specializes (0GSI), divisors.tex at lemma-base-change-relative-assassin (05DC), algebra.tex at lemma-flat-going-down (00HS), lemma-spec-localization (00E3), lemma-spec-closed (00E5), and lemma-irreducible (00ES), and morphisms.tex at lemma-base-change-flat (01U9). The crucial distinction is that 05DC's associated-point theorem needs finite type whereas its displayed residual-fibre construction does not. Our proof does not use associated points at all. There are no new nodes whose source or small cases require separate checking.

Step 1 uses def-sc-generic-point and def-weil-irreducible-components exactly for closure and maximality, def-weil-affine-spectrum for primes with the Zariski topology, and lem-weil-pbc-spec-irreducible-components-minimal-primes for the component/minimal-prime correspondence. I checked that the latter has no Noetherian or reducedness hypothesis. The open-locality argument is explicit: intersect a larger irreducible closed subset with the neighbourhood, and use density to show the inclusion remains strict; conversely take closure in the ambient scheme. The spectrum closure formula follows directly from Zariski closed sets. Thus the no-proper-generalization criterion is proved here, not hidden behind a nonexistent generic-point comparison lemma.

Step 2 uses def-pc-scheme-fibre, whose statement explicitly includes the homeomorphism onto the subspace p^{-1}(z), def-pc-fibre-product for its universal property, and lem-weil-pbc-fibre-product-affine-spectra for Spec of the tensor product of the two fields. Both schemes in the affine lemma are affine and over the same Spec k; no finite-generation hypothesis appears. The reassociation is checked by describing maps into both products and the mutually inverse projection-preserving maps. The subspace closure equality is then elementary. It is unnecessary to assert that the fibre inclusion is a closed or locally closed immersion, which can fail for an arbitrary non-closed point.

Step 3 uses lem-weil-pbc-open-fibre-product to identify the inverse image of the affine open U, and lem-weil-pbc-fibre-product-affine-spectra to identify its ring and both projections. lem-pc-field-extension-flat states exactly that Spec L to Spec k is flat for a field extension; lem-weil-pbc-flat-morphism-base-change then applies to this map and U to Spec k. Finally lem-weil-pbc-flat-ring-map-iff-flat-affine applies to the resulting morphism of affine schemes. Its statement explicitly supplies the required ring flatness, so this step does not mistake a definition of flatness for a base-change theorem. All five nodes are existing Mathlib leaves; no off-route unsplit theorem is used.

Step 4 uses only lem-sc-flat-going-down beyond steps already established. Its statement gives a prime q_0 contained in q above every smaller prime p_0 of A, exactly with the flat A to B and q over p obtained in step 3. Minimality of q forces equality and hence the contradiction in contractions. For the second forward conclusion, generalization in the fibre is generalization in the ambient scheme by step 2, so minimality via step 1 suffices; it does not require that the field tensor ring have dimension zero. The latter would be false for transcendental extensions.

Step 5 is elementary from steps 1 and 2: continuity sends a generalization of w to a generalization of z; maximality of z forces the same image; the fibre criterion then forces equality. The open-set argument giving the continuity assertion is included. This proves the reverse implication for arbitrary schemes without an extra prime-correspondence comparison lemma.

Step 6 uses def-weil-closed-immersion, whose actual statement says homeomorphism onto a closed subspace, and the same closure/maximality definitions as step 1. The image contains w and is closed, hence contains all of E; subspace closure gives precisely E. A larger irreducible subset in T would give a larger one in Z_L. This verifies both clauses for arbitrary closed subschemes, including nonreduced ones, without using a scheme-theoretic factorization assertion based solely on support.

I tested the identity extension L=k (the residual fibre is Spec kappa(z)), a split finite separable extension (multiple components are allowed), a purely inseparable extension of an imperfect field (nilpotents in the tensor ring are harmless), and the transcendental situation kappa(z)=k(t), L=k(u) (the residual tensor ring can have non-generic primes, so the fibre-generic condition is essential). For nonreduced Z or T all arguments concern prime spectra and topology, so nilpotents impose no extra assumption. For an empty scheme no point w exists and the quantified assertion is vacuous. At non-closed z the fibre is used only with its subspace topology, not as an assumed closed subscheme.

Against delivery-errors B--E: no new node or clause-restatement node is introduced; every non-elementary fact is a cited existing statement; the quotes in citations.json were copied from those statements without alteration; all used hypotheses have been checked above; no citation to the parent or a descendant creates a cycle. All six proof steps are below 2000 characters. The original seven inherited search records are preserved, and the six searches actually run here are appended with their actual queries and results. The two semantic phrasings return residue-field constructions or flat going-down/localization ingredients, not this whole statement. The search candidates RingHom.Flat.generalizingMap_comap and Ideal.exists_minimalPrimes_comap_eq were read in Mathlib source; neither includes the residual-fibre iff or closed-immersion clause. Therefore the item is a split rather than a Mathlib leaf. No SGA source is used.
