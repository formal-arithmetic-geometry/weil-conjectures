# Q52: lem-per-finite-flat-regular-divisor-purity-descent

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-finite-flat-regular-divisor-purity-descent.json: item, split into five proof steps; original statement unchanged.
- dag/nodes/sec-deligne-laumon-a1/lem-per-divisor-purity-strict-local-criterion.json: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep. This is ILO XVI Proposition 3.4.2, not a descent theorem.
- citations.json: one exact statement quotation for every step/node pair.

## Attachments

None. Searched the project Lean source for the blueprint tag and finite-flat/divisor/purity terminology. The hits in divisor-sequence and coherent Serre-duality files do not state etale divisor purity or its descent; the item has no finished declaration. Upstream master is reference only.

## WANTED

None. The ILO PDF and the Stacks source used here are present locally.

## Corrections and source audit

The item is ILO XVI Proposition 3.4.3, printed p.246. Its statement is correct, including the absence of a generic-etaleness assumption. The imported punctual-purity vocabulary is unused context but was retained to leave the statement unchanged. The original node had no proof.

The proof follows the complement-vanishing argument of Proposition 3.4.3 using Proposition 3.4.2 (p.245) and the splitting stated in Lemma 3.4.4 (p.246). The trace is supplied by the already existing general weighted-trace node, not the finite-etale-only trace nodes. Only ILO and Stacks are cited as sources of this delivery. No forbidden source was read or added. The weighted-trace node is reused for its finite locally free rank identity as a black box, independently of its own existing provenance.

It is unnecessary to select a component of degree prime to ell, as the source does: the trace on the entire finite cover has scalar d. We retain all strict-local components and take their finite product of zero cohomology groups. This is the same trace-and-complement argument, not a replacement of the unit route. No absolute-purity theorem is cited, which would be circular through this item.

## Not duplicates

lem-per-divisor-purity-strict-local-criterion vs lem-per-monomial-boundary-purity-criterion: the latter characterizes punctual purity of a specified monomial trait scheme by purity of its coordinate divisors; it does not characterize arbitrary regular divisor purity by strict-local complement cohomology.

lem-per-divisor-purity-strict-local-criterion vs lem-per-kummer-root-regular-divisor-purity: the latter compares purity across a degree-ell root cover and proves geometric regularity; it gives no complement vanishing criterion.

lem-per-divisor-purity-strict-local-criterion vs lem-per-finite-flat-regular-divisor-purity-descent: the new lemma is a local cohomological characterization for a single pair and has no finite map or degree condition. The item's steps prove descent by using it twice with an independent trace injection.

lem-per-divisor-purity-strict-local-criterion vs lem-per-punctual-purity-etale-locality: the latter compares closed-point purity of localizations across etale morphisms, not a divisor purity map with all higher cohomology of its strict-local complement.

Searched the entire DAG for Proposition 3.4.2, divisor/complement/vanishing/purity terminology and the blueprint with blueprint_refs.py search for finite flat, divisor, complement and strict local complement. No existing node states the new criterion. The numerous bare 3.4.2 hits elsewhere concern other documents. The new source has no Stacks tag shared with existing nodes. The ancestor is lem-per-artin-gabber-affine-curve and the full created-item via chain is retained. No current-blueprint node states the criterion in another form.

## Review by Q52

I read ILO XVI pp.244–248, especially the complete statements and proofs of 3.4.2–3.4.4, and the existing statement of every node used in the item. The new lemma is exactly the criterion of 3.4.2; I wrote its effective-Cartier and regularity hypotheses explicitly and used the same Kummer class normalization as the existing class-calculus node. It remains statement-only: it does not hide the finite-flat descent argument.

Step 1 takes precisely the vanishing equivalence from the new criterion. The closed-immersion strict-localization node explicitly identifies the fibre product with the strict-local divisor. Its hypotheses allow any closed immersion, so they hold here.

Step 2 takes the displayed coproduct isomorphism from lem-trf-finite-base-strict-localization, not just a henselian-ring definition. Its finite-map hypothesis holds for f. The strict henselizations are Noetherian and regular by the two cited statements, with no excellence hypothesis. I checked Stacks 03QP (the finite strict-local decomposition), 05WR and 05WS (strict henselization and quotient), 06LJ (Noetherianity) and 06LN (regularity), as well as 02KD for finite-locally-free base change. The closed-immersion comparison applies to D' in Y. There is no assertion that reduction commutes with arbitrary base change: only equality of underlying closed subsets is needed to identify the open complement. The tensor-algebra fibre-product formula and finite free basis in lem-pc-flf-properties show directly that the finite map retains rank d after base change and open restriction; lem-weil-pbc-finite-flat-rank-iso explicitly states the rank equality. I corrected an initially overcompressed step by naming the regularity/Noetherianity nodes and writing this basis argument.

Step 3 applies the criterion on the ORIGINAL pair (Y,D') at each geometric point over the chosen point of D. The assumed purity is therefore available exactly where it is used. It does not infer purity at all points of the base-changed pair from an unstated locality result. I wrote out why a finite disjoint union has the product of the component cohomology groups: the sheaf category, injectives and sections are componentwise and a finite product of vector spaces is exact. This is elementary category bookkeeping, not an omitted cohomological lemma.

Step 4 uses the final sentence of lem-pur-quasifinite-flat-weighted-trace, which explicitly treats finite locally free maps and states trace after unit equals rank times the identity. It does not assume separability; ramification multiplicities are included. U and V are Noetherian opens of finite unions of strict localizations, so its Noetherian hypotheses hold. The module-valued finite-pushforward derived-sections node explicitly supplies RΓ(U,g_*M)=RΓ(V,M), avoiding an abelian-sheaf-only comparison. Multiplying the trace by the inverse of d in F_ell is an actual left inverse; applying RΓ and H^q preserves that equation. A retract of the zero group is zero. This establishes the cohomology injection for all q without any comparison of Gysin classes across the ramified map.

Step 5 applies the converse of the criterion to the vanishing proved for every point. All citations have exact statement quotations in citations.json. I declared the generic statements from other units as tool uses, with reasons; none replaces the ILO route. No proof step exceeds 2000 characters.

Small cases: if D is empty the conclusion is the unique map of zero objects and the criterion is vacuous. If f is the identity, the trace scalar is 1 and the proof reduces to the same criterion. If f is disconnected, the full degree d, not an arbitrarily chosen component degree, controls the splitting. A purely inseparable finite flat map is permitted; weighted fibre lengths, not the number of geometric sheets, give d. If ell divides d the trace no longer has the asserted inverse, which is exactly why that case is excluded. No assumption on excellence, finite dimension of the original scheme, or an algebraically closed residue field was added.

I checked delivery-errors B–E: the new node is self-contained and statement-only; every substantive input is a cited statement; definitions are not cited as theorems; the new lemma is not an item clause or a duplicate; the descent argument remains in the item; there is no upward absolute-purity citation. Statements and coefficients stay ordinary small-etale F_ell throughout, with no adic/pro-etale substitution. No Lean, compiler, Lake, or live-repository write was performed.

## Unfinished work

None within the one-level split. The new complement criterion is deliberately unsplit and joins the next-stage-1 queue. Server review_split passes. Final delivery validation is run after this report.
