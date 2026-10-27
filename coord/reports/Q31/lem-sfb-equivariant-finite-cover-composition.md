# Stage-1 report: lem-sfb-equivariant-finite-cover-composition

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-finite-cover-composition.json: statement; split into six steps using six existing Mathlib leaves; no new node and no new Mathlib leaf.
- citations.json: six verbatim statement quotations, one for every step/node citation.
- searches.jsonl: actual msearch output for the item, retained verbatim in the additional mathlib_searches entries.

## Attachments

None. Searches of lean/WeilConjectures by the blueprint tag, equivariant covers, generically etale geometry and kernel fixed fields found no declaration stating all the clauses. General normal-extension fixed-field declarations do not prove this assertion for arbitrary, possibly nonfaithful actions and the two specified kernel equalities.

## Wanted literature

WANTED: de Jong, Families of curves and alterations (1997), Remarks 2.3(iii), Situation 5.3 and Lemma 5.7, for lem-sfb-equivariant-finite-cover-composition. The named local PDF is absent. I read the publisher's primary scan at https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf (pp.602, 613, 615); no download was written to the shared repository. The proof is marked agent-written because it supplies the argument and the exact-kernel strengthening rather than treating the remark as a black-box theorem.

## Findings and corrections

The imported item has a sound statement but no proof. I preserved its statement, hypotheses and statement dependencies. In particular I did not replace the exact fixed-field equality by a purely inseparable extension, and did not assume faithful actions. Neither normality nor projectivity is needed in the composition argument; they remain hypotheses and properties of the unchanged terminal scheme.

The inherited blueprint ancestor tool returns `blueprint.from.node = None`. I preserved that metadata and the inherited via chain, whose precise from.place identifies det-thm-sf-ctf-stability-direct-images proof (3), parent proof steps 9 and 10, and de Jong's induction. I read the current blueprint direct-image proof and chapter, plus the unit record. Blueprint searches for finite morphisms, generically etale, generically, equivariant finite, kernel, fixed field and incomparability found no node stating this full composition assertion. The incomparability search did find the existing Mathlib leaf, which is used instead of creating a duplicate. The proof stays on the existing finite equivariant alteration route.

The only substantial geometric point is that a finite surjective map between integral schemes has no nongeneric point over the target generic point. The proof now states the affine reduction and applies integral incomparability explicitly. It then removes the closed image of the bad locus, ensuring etaleness over an entire inverse image, not merely on a dense open upstairs.

## Not duplicates

No new nodes were created. The six existing cited leaves were opened and reused. In particular pqf-lem-incomparability and lem-weil-pbc-integral-incomparability overlap, so I cited the existing blueprint leaf rather than introducing a third copy.

## Review by Q31

I read de Jong Remarks 2.3(iii) for composition, Situation 5.3 for the equivariant alteration setting, and the end of Lemma 5.7 for the repeated finite generically etale covers. The exact composite-kernel equality is the item's agent strengthening; I checked it directly from its hypotheses instead of attributing it to the paper. There are no new-node sources to review. For the geometric ingredients I opened Stacks morphisms.tex at lemma-composition-finite (01WK), lemma-finite-integral (01WJ), lemma-finite-proper (01WN), lemma-composition-etale (02GN), and lemma-base-change-etale (02GO). I also read Stacks 00GT, lemma-integral-no-inclusion, at its primary tag page and the existing incomparability node/Mathlib declaration. The local algebra.tex snapshot does not expose that label at the old node's recorded line; I used the live primary tag to verify the statement.

Step 1 cites the exact finite-composition statement of lem-weil-pbc-finite-composition. Its surjectivity assertion is the explicit two-choice argument, and the two dense opens are hypotheses. Step 2 uses pqf-lem-finite-integral-lft only to infer integrality of the affine ring map, and pqf-lem-incomparability only for comparable primes with equal contractions; I opened both statements. The domains come from integrality of the schemes, finiteness makes the affine inverse image affine, and surjectivity supplies the generic-point image by the closed inverse-image argument written there. Thus no flatness, normality, or affine-intersection assumption enters. Step 3 uses precisely the closed-map clause of lem-weil-pbc-finite-closed-map-finite-fibres; its finite-fibre clause is not needed. The generic point is outside the bad image by step 2, so the target open is nonempty and dense. Step 4 uses exactly arbitrary etale base change from lem-weil-pbc-etale-scheme-base-change and the composition clause (2) of lem-weil-pbc-etale-composition-cancellation. The displayed inverse-image domains make both base-change squares valid. All six cited statements are quoted literally and in full in citations.json (the first dry run rejected a short, otherwise verbatim finite-composition excerpt, so I expanded every quotation to the complete statement); no proof of a cited node is being used as an interface.

Steps 5 and 6 are elementary calculations from the stipulated equivariance and the two fixed-field equalities. I checked that taking germs in the equivariance squares makes the action on F restrict through tau on M and through sigma tau on K. For the first fixed-field inclusion, ker(tau) is contained in ker(sigma tau), then every member of ker(sigma) has a lift in ker(sigma tau) because tau is surjective. For the reverse inclusion every l in the composite kernel acts on K through tau(l) in ker(sigma). Both inclusions are written explicitly. No faithfulness or Galois identification is used.

Small cases checked: all groups trivial forces K=M=F and the invariant computation is tautological; tau an isomorphism and sigma an isomorphism each reduce to the remaining assumed equality; nonfaithful actions retain the same elementwise calculation; zero-dimensional integral schemes (spectra of finite field extensions) have the generic point as their whole space, so the bad image is empty; empty bad locus makes U=V_0. Empty integral schemes and disconnected sources are excluded by the hypotheses and were not silently used. For each step I checked C1 and C4, and checked B1-B10, D1-D5 and E1-E7 against the files: no new or circular lemma, no source route replacement, no statement weakening, and no implicit non-elementary subclaim. Each step is below 2000 characters and the total assembly proof is below 3000 characters.

## Unfinished work

None in this split. Future stage-2/3 work is outside this delivery's authorization.
