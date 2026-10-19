# Q99 stage-1 delivery: lem-per-prime-to-ell-equivariant-cohen-presentation

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-prime-to-ell-equivariant-cohen-presentation.json`: original statement retained; ten proof steps assemble the input constructions and check all conclusions.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-tame-equivariant-cohen-gabber.json`: statement-only input for reduced equidimensional characteristic-p rings with a tame action; Mathlib no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-galois-epp-reduced-fibre-cover.json`: statement-only Galois Epp preparation, without a formal presentation or a chosen prime ell; Mathlib no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-equivariant-cohen-coefficient-lift.json`: statement-only coefficient extension and equivariant lift for a specified residue section; Mathlib no match.
- `citations.json`: every use in every step has a verbatim quotation from its node's statement.

The previous split and report are retained in the sandbox as `prior-attempt.json` and `prior-report.md`. Its logged searches and citations were read and retained; the repaired citations are renumbered for the ten-step proof. The live repository still has the same unsplit statement. No live project file, Lean file, compiler or launcher was changed or run.

## Attachments

None. I searched the exact item id and Cohen/Gabber/Epp and coefficient-ring terminology in the read-only slopmaster2 and master project sources. No project declaration states the formal presentation input. The earlier exact-tag searches likewise found none. General Artin–Gabber/perverse declarations and upstream sorry declarations do not attach this item or the new inputs.

## WANTED

None. I read the supplied ILO PDF, not an external substitute.

## What needed correction

The previous sandbox's required dry run failed because steps 1 and 2 were non-elementary and cited no nodes. They merely invoked ILO IV 4.3.1 and invariant-ring assertions by source number. This was a substantive missing split, not an elementary-marking problem. I replaced those applications with three genuine preparatory inputs and retained the previously useful power-series argument and invariant normality argument. The statement was not changed and no statement dispute is asserted.

The earlier report attributed the invariant DVR assertion to V 3.2.1–3.2.4 too broadly. Those paragraphs use the fixed formal base in an algebraization argument; they are not themselves a proof of complete DVR descent. Step 9 now writes out the valuation and completeness argument. I also made explicit how the prime-to-ell degree is obtained, rather than quoting the whole conclusion of IV 4.3.1 as a new node.

The three new nodes are strictly auxiliary: Galois Epp removes special-fibre multiplicities and has no formal map or chosen ell; positive-characteristic Cohen–Gabber handles arbitrary tame actions on reduced rings and supplies the special-fibre parameters; the coefficient-lift lemma handles a given section into an arbitrary complete local W-algebra and has no finite formal presentation. The main item still constructs and verifies that presentation, its dense etale open, and its quotient degree. None of the new statements restates the whole item or simply packages its final regular-base clause.

## Review by Q99

I read the standing brief, stages/1-dag.md, the three blueprint levels in SETUP.md, GOAL.md, coord/dag-sync.md, and all of delivery-errors B–E. I read the chapter and unit records and the ancestor lem-per-artin-gabber-affine-curve. This item is a supporting commutative-algebra input beneath the ancestor's Gabber finiteness branch; it does not realize the Fourier unit's key statement, so its unit's existing realized record is not changed.

For the item I read ILO IV 2.1.1–2.1.12, 2.2.2–2.2.6, 4.2.3–4.2.5, 4.3.1–4.3.7, and V 3.2.1–3.2.4 in the supplied PDF. For the new characteristic-p input, IV 2.2.2 is the equivariant statement, and its proof 2.2.4–2.2.6 is the source of the parameter choice; restricting to reduced equidimensional rings gives the injective/torsion-free form. The optional perfect subfield compatibility follows because two lifts of each compatible p-power-root sequence differ by elements of arbitrarily high maximal-ideal powers. For the Galois Epp input I read IV 4.3.3–4.3.5 and 4.3.7 together with the reduced-fibre construction in 4.2.3–4.2.4. The new node retains the actual Galois action before choosing a Sylow and asserts no power-series map. For the coefficient input I read the Cohen-ring construction in IV 4.3.5, the lifting torsor in Lemma 4.3.6, and the formally smooth extension in 4.2.5. Its hypotheses include the perfect coefficient residue field, invertible group order, compatible semilinear actions, and a specified equivariant section. Its conclusion deliberately does not claim that the coefficient map into a general C is injective; the main item's domain hypothesis proves that separately.

Step 1 opens and uses all six existing power-series/dimension statements and the regular-local definition. Their statements give Noetherianity, the unit criterion, completeness for the specified coefficient-plus-variable ideal, the quotient by an initial string of variables, the domain property, and the dimension bound by generators. I checked every hypothesis with a field and with an arbitrary complete DVR, including a ramified DVR. The lower-bound prime chain uses the quotient by variables first and appends the coefficient uniformizer last; it does not assume a quotient-coefficient theorem that was not cited.

Step 2 uses the new characteristic-p input with the trivial group and the existing finite-algebra-etale-near-field-or-dvr statement at the zero prime. Its statement explicitly supplies torsion freeness and the separable generic algebra, so alternative (ii) applies; no separably closed residue field is assumed.

Step 3 uses the existing complete-local-domain-finite-over-regular statement exactly for its finite local coefficient presentation, finite-algebra-is-integral and integral-injective-dimension-equal to count parameters, finite-domain-fraction-degree and char-zero-field-extension-separable for the generic field, and the etale-neighbourhood statement at zero. I checked the source of the Cohen presentation (Stacks 032D, algebra.tex, lemma-complete-local-Noetherian-domain-finite-over-regular). A Cohen DVR cannot occur when the residue characteristic is zero. I wrote out why the finite generic domain is its fraction field.

Step 4 uses the new Epp preparation and the existing Sylow-subgroup-prime-index statement. The latter actually gives both an ell-group and prime-to-ell index. Since ell is a unit in A, its residue characteristic p differs from ell; this verifies every averaging-order hypothesis. The action preserves the ideal of the uniformizer, not necessarily the uniformizer itself.

Step 5 applies the new characteristic-p input to B/pi B, whose reducedness, equidimensionality and dimension d−1 came from Step 4. It then applies the new coefficient input with the actual H-equivariant k0-section just constructed. The DVR unit-times-uniformizer-power statement proves injectivity of its coefficient map into the domain B. Averaging arbitrary lifts of the fixed parameters is written as a formula and preserves their reductions and maximal-ideal membership.

Step 6 uses power-series-universal-property-complete for the evaluation map and parameter-ideal-formal-normalization case (b) for injectivity, finiteness, locality and residue fields. I verified its dimension, coefficient inclusion and radical hypotheses, rather than citing its proof. Equivariance is checked using the evaluation formula, and reduction modulo pi is coefficientwise.

Step 7 uses power-series-domain, regular-principal-prime-localization-dvr, and finite-algebra-etale-near-field-or-dvr. I checked that the actual prime is pi R, its quotient is k'[[T]], and its localization satisfies the cited DVR statement. The actual fibre algebra is the generic algebra of the special fibre, and Step 5 supplies precisely alternative (ii). Thus f is outside pi R, not merely nonzero in R.

Step 8 uses the existing Noetherian-submodule-finitely-presented statement for finiteness of B^H over A, finite-field-action-fixed-degree for both G and H, and field-degree-multiplicativity for the quotient degree. The preparatory Galois assertion identifies the full group G. Its restriction to H is faithful. I wrote out the norm-denominator identification Frac(B^H)=Frac(B)^H, the inverse-of-a-fixed-unit locality argument, and integrally closedness. Therefore none of these conclusions is taken from a definition-only node or from a cited node's proof.

Step 9 uses the DVR factorization statement and the definitions of DVR and adic completeness. It constructs the discrete restricted value group, proves every nonzero invariant ideal principal by its least valuation, and proves completeness with the explicit equality Lambda cap pi^n V = a^{ceil(n/q)} Lambda. The norm of pi supplies a nonzero positive invariant value, so the invariant ring is not a field. This calculation also covers a trivial action and a nonfaithful coefficient action.

Step 10 is coefficientwise equality of series, invariance of inverses, and application of Step 1. In equal characteristic H is trivial. In mixed characteristic V has residue characteristic p different from ell. This checks the final unit assertion without incorrectly deducing invertibility of ell solely from invertibility of |H| when H might be trivial.

I tested d=2 (so the mixed special fibre has e=1), j=0, the trivial group, nonfaithful coefficient actions, and a ramified coefficient DVR. All are included in the stated arguments. No proof step exceeds 2000 characters. The new nodes have no proof sketches inside their statements, no proof dependencies and no proof steps. Their definitions are cited or explained inline. I searched the entire DAG and blueprint before writing them, and searched the source Lean tree. Mathlib searches use only msearch.py and are recorded with their exact tool/query strings and the actual outcomes; the item retains its existing searches. Searches returned standard-etale, invariant, ramification and ordinary lifting declarations but no match for the three new constructions. The square-zero derivation-lift equivalence is a useful future ingredient, but does not supply a coefficient ring with an H-action or an equivariant section lift. No SGA source is used.

Generic off-unit commutative-algebra inputs are declared in split_report.tool_uses, for the maintainer to review; the maintainer-owned tool_uses field is not set.

## Not duplicates

lem-per-tame-equivariant-cohen-gabber vs lem-per-cohen-gabber-finite-presentations: the existing node assumes a separably closed residue field and gives a nonequivariant presentation; this input treats arbitrary residue fields and a prescribed tame action on a reduced equidimensional ring, needed for the special fibre.
lem-per-tame-equivariant-cohen-gabber vs lem-per-coefficient-field-generic-differential-basis: the latter supplies a nonequivariant differential basis, not an equivariant coefficient section and fixed parameters.
lem-per-galois-epp-reduced-fibre-cover vs lem-per-mixed-reduced-special-fibre-cover: the existing statement has no group action or Galois generic extension, so it cannot support the Sylow argument.
lem-per-equivariant-cohen-coefficient-lift vs lem-per-perfect-residue-coefficient-dvr: the existing statement supplies an ordinary formally smooth coefficient extension and lift, without a prescribed group action or equivariance.
lem-per-equivariant-cohen-coefficient-lift vs lem-weil-pbc-fs-adic-lift-into-complete: the latter lifts from a supplied formally smooth source but constructs no Cohen coefficient ring and asserts no equivariance.

## Unfinished work

No unresolved obligation in this one-level split. The three new statements remain unsplit for later workers. Stage 2 and Lean proofs are outside this delivery.

## Repair validation notes

The second dry run found that grouped notion citations in two new statements were not parsed as individual node links. I changed all grouped new-node references to individual `[id]` links, retained the statement meanings, and regenerated the quotations. I also cited `lem-weil-pbc-finite-galois-fixed-field` explicitly in Step 8 to identify the base fixed field, rather than leaving the fundamental Galois fact implicit. The five logged item searches from the original sandbox now appear alongside its inherited searches; no search was invented or repeated.
