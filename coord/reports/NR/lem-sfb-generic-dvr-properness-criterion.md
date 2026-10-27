# Stage-1 report: lem-sfb-generic-dvr-properness-criterion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-generic-dvr-properness-criterion.json: statement, split into eight steps; not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-local-domain-same-field-dvr.json: new statement-only node, unsplit, no Mathlib match. Source: Stacks 00PH, algebra-lemma-exists-dvr, identity field extension.
- citations.json: one entry per step/node pair, quoting the cited statement verbatim.

The other sandbox files are the report, the search command's searches.jsonl, and the preparation script. No repository, launcher, or Lean file was written; no git, compiler, Lake, or build command was run.

## Attachments

None. Searched the live lean/WeilConjectures source for the exact blueprint tag and the notions valuative, generic DVR, and discrete valuation. There is no declaration of the project stating this refined properness criterion. In particular, Mathlib's AlgebraicGeometry.IsProper.of_valuativeCriterion quantifies over all valuation rings, so it does not finish this node.

A relevant upstream declaration was inspected: IsLocalRing.exists_isDiscreteValuationRing, WeilConjectures/RingTheory/DiscreteValuationRing/Dominating.lean:250. Its conclusion is an injective local map to a DVR. It does not assert that the DVR has the original fraction field. The dimension-one variant at line 167 also omits that identification in its statement. These are not attachments for the new node. Their proofs are not being used as statements.

## WANTED

None. All sources used here are in literature/stacks-project/.

## Corrections and issues

The item statement is unchanged and agrees with Tag 0208 (1) iff (4), specialized to an integral source and with separatedness already assumed. The original stmt_deps omitted def-weil-finite-type-morphism although the statement explicitly cites it; this dependency was added. There was no existing proof to retain or repair. The blueprint ancestry is inherited exactly: blueprint_refs.py ancestor reports None for this replacement-route descendant. Its nonempty from.place is retained and refined for the new node. No chapter or unit file was changed. This is not the unit's key node.

A care needed beyond a loose paraphrase of the source: Chow's lemma gives an envelope with a dense open isomorphism, not an assertion that every component of an arbitrary envelope dominates the integral source. Step 2 takes the reduced closure of the unique generic preimage; its proper image contains the dense open and hence is all of R. The argument therefore tests only the original function field, as required.

## Not duplicates

lem-sfb-local-domain-same-field-dvr vs lemma-nagata-local-domain-valuation-dominates: the latter gives an arbitrary valuation ring dominating a local subring, with no discreteness; the new lemma assumes Noetherianity and nonfieldness and gives a DVR in the fixed fraction field.

lem-sfb-local-domain-same-field-dvr vs lem-sbc-noetherian-specialization-trait: the latter traces a strict specialization by some trait without prescribing its fraction field. The new lemma preserves the fraction field, which is essential to apply this item's hypothesis.

lem-sfb-local-domain-same-field-dvr vs lem-sc-normal-dim1-dvr and lem-weil-pbc-z-localizations-dvr: those show that rings already normal of dimension one, or specified localizations of such rings, are themselves DVRs. Here B can have larger dimension and need not be normal; the conclusion is existence of a dominating overring with the same fraction field.

Whole-DAG searches for 00PH, algebra-lemma-exists-dvr, Noetherian local domains and domination found no matching node. Blueprint searches for 00PH, dominating discrete, discrete valuation, generic function field and valuative were read. The general properness and valuation-extension blueprint nodes do not state the item's DVR refinement. No existing node has the new node's source tag. The existing Chow, reduced-induced-closed-subscheme, function-field, localization and properness nodes were reused instead of creating specializations.

## Searches

All added Mathlib searches were run through the prescribed msearch.py command for NR and this item; their exact tool/query pairs and returned summaries are recorded in searches.jsonl and in the applicable node's mathlib_searches. The original item's earlier recorded searches were preserved. For the item, LeanFinder and LeanSearch find the ordinary valuative criterion, Loogle with ValuativeCriterion and IsDiscreteValuationRing gives no hits, and grep locates Mathlib/AlgebraicGeometry/ValuativeCriterion.lean:29-31 explicitly listing the Noetherian DVR reduction as future work. I read the actual ordinary-criterion statement at line 341.

For the new node, two LeanFinder phrasings, LeanSearch, Loogle and two grep searches were run. The returned TFAE, Dedekind-localization and valuation-subring equivalence declarations assume hypotheses not available on B or classify a ring already known to be a valuation ring. I read DiscreteValuationRing/TFAE.lean and Valuation/LocalSubring.lean:251: the latter constructs an arbitrary dominating valuation ring, without discreteness. This is not a one-line specialization of the new statement. All services answered; no unavailable answer was converted to a negative search.

## Review by NR

I read Stacks limits.tex, Tag 0208, lemma-Noetherian-dvr-valuative-proper, its statement and entire proof. The item's forward direction follows its Chow-envelope/boundary-DVR route. I read coherent.tex Tag 0200, lemma-chow-Noetherian (statement and beginning of proof); algebra.tex Tag 00PH, lemma-exists-dvr (statement and complete proof); and schemes.tex Tags 01J3 and 01IQ (reduced closed structures and an immersion with closed image). The new node is precisely the identity-field-extension specialization of 00PH, with locality written as contraction of maximal ideals. Its proof is deliberately not split in this delivery. For the converse and uniqueness I checked the existing API statements against the ordinary valuative criteria, Tags 0BX5, 01KF and 01L0. No SGA source is used.

I opened every node cited in the proof, read its statement, and checked what the step takes from it. citations.json uses those exact statements, including definition statements. In detail:

1. The locally Noetherian definition supplies the chosen affine cover with Noetherian coordinate rings; the proof now chooses that cover explicitly, without invoking the stronger equivalence for every affine open. The separated/finite-type base-change node explicitly gives both properties under an arbitrary base change. The integral-scheme and function-field definitions justify passing to a nonempty open with the same generic field. Universal closedness is defined by closedness after every base change; the step writes the open-cover argument out instead of assuming a locality theorem. The extension factors through the inverse-image open because its composite to S factors through V. The empty restriction is handled separately. This is an elementary argument from the cited statements.
2. The finite-type-over-Noetherian node applies because the chosen base is affine Noetherian. The Chow node explicitly supplies an immersion, proper surjection and dense open isomorphism. The reduced-induced-closed-subscheme node supplies a reduced closed scheme on the generic-point closure and uniqueness over the integral open. Reduced plus irreducible is exactly the integral-scheme definition. The permanence node explicitly gives properness of closed immersions, composition, and composition of immersions. The image of the resulting proper map is closed by the properness definition and contains U; thus it is surjective. No unproved generic-field assertion about a vertical component is used.
3. The same reduced-closed-subscheme node identifies Y with an open of its reduced closure Z by uniqueness on the open O in the immersion factorization. The factorization is the definition of immersion. Irreducibility and the shared integral open give the same function field. The projective-space node states properness over every S, not just fields. Its composition with the closed immersion makes Z proper by the permanence node; it is therefore finite type over the affine Noetherian base, meeting the Noetherian-scheme lemma's hypotheses.
4. The locally Noetherian definition gives a covering by Noetherian affine charts, so one can choose such a chart at z. The integral-function-field node states that its coordinate domain has fraction field L. The point z is not generic, hence its prime is nonzero. The localization node gives the local ring C_p and its maximal ideal; the localization-Noetherian node applies to C and its prime complement. In a domain the nonzero prime remains nonzero on localization (a nonzero element cannot be killed by a nonzero denominator), so C_p is not a field. Every L-fraction of C is also a fraction of C_p and C_p embeds in L, giving its fraction field L. The new 00PH node therefore applies with exactly its hypotheses. Its maximal-ideal contraction makes the resulting Spec A map send the closed point to z; the identity embedding into L fixes the generic morphism. The affine-spectrum definition supplies these contravariant maps.
5. The assumed criterion applies because the bottom morphism has exactly the canonical generic composite, not merely the same generic image point. Valuative existence applies to the proper map Y to R with bottom morphism r and generic map to Y; the square commutes because pi is the identity over U. The DVR definition includes its valuation-ring equivalence. Properness of projective space implies separatedness, and the uniqueness node states equality of two S-maps with equal generic restrictions. It applies to jh and a with this same bottom b. Their closed-point images give the contradiction; no lifting from set-theoretic image containment is asserted.
6. The closed-image immersion node states exactly that the now closed immersion image makes j a closed immersion. The permanence and projective-space nodes then give properness of Y to S.
7. The surjective-base-change node explicitly applies to arbitrary T to S. Taking an inverse image of a closed set is ordinary topology, and surjectivity gives equality of the two images in T. Proper base change is provided by the permanence node. This proves universal closedness rather than assuming a proper-descent theorem; the original hypotheses finish properness by its definition. The local-to-global argument was already written in Step 1.
8. The existing valuative-existence node supplies the required extension for a proper morphism and any valuation ring. The existing uniqueness node assumes only separatedness, which was an original hypothesis throughout. Thus it also proves uniqueness before the forward implication is finished.

I checked the statements and steps against delivery-errors B to E. The only new node has a self-contained statement with all ring hypotheses and definitions, no proof text or proof dependencies, the correct Stacks tag, and actual logged searches. It is neither elementary nor a clause of the properness criterion: 00PH is an independent commutative-algebra existence theorem. All non-elementary geometric inputs are existing cited statements; the integral-envelope and reduced-closure identifications are short applications of the explicitly cited uniqueness theorem. No step exceeds 2000 characters. There is no cycle: the new node depends only on definition leaves, while all reused results predate and do not depend on this criterion.

Small cases checked: a dimension-one DVR B can be taken as its own dominating ring; higher-dimensional B is allowed and is not being claimed to be a DVR; a field B is expressly excluded from the new lemma. Empty inverse-image affine opens require no generic-point argument. A zero-dimensional integral source causes no boundary argument unless a nongeneric boundary point exists; such a boundary point forces a nonzero prime, exactly where 00PH needs nonfieldness. A proper R has extensions by the ordinary criterion. For a nonproper example, R = Spec k[t,t^{-1}] over k fails the test at A = k[t]_(t), whose fraction field is k(t): t cannot be invertible at the closed point. No normality, excellence, regularity, finite residue extension, or quasi-compactness of the original base is assumed or used.

## Unfinished work

None in the one-level split. The new 00PH node is intentionally statement-only and joins the stage-1 queue. There are no statement disputes and no route changes.
