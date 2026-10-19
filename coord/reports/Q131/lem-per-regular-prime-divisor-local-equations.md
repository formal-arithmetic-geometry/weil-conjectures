## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-prime-divisor-local-equations.json`: statement, split into eight steps; unchanged statement; no exact Mathlib match.
- `citations.json`: 25 step/node entries, each quoting the cited statement verbatim.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file changed.

## Attachments

None for the item. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for its blueprint tag, prime divisors, Cartier divisors, and regular UFDs did not find a declaration covering all its clauses. `IsRegularLocalRing.uniqueFactorizationMonoid` at `WeilConjectures/RingTheory/RegularLocalRing/UniqueFactorization.lean:132` assumes additionally `IsRegularRing R` and proves only the UFD assertion; it is not an attachment for this scheme-level item. The existing DAG UFD theorem is used instead.

## WANTED

None. All mathematical sources needed here were present in the Stacks checkout.

## Audit of the imported item and route

The statement is correct and was preserved verbatim, as were its statement dependencies and creation/blueprint ancestry. Its proof was empty. It is a created auxiliary node of the surface-resolution input under `lem-per-artin-gabber-affine-curve`, not the unit's key node; no realization fields need changing. I read the chapter and unit records and the current main-20261015 ancestor text. The algebraic input continues to serve the inherited embedded-resolution route, without replacing a unit step.

I read Divisors Tags 0AGA (`lemma-weil-divisor-is-cartier-UFD`), 0AG8 (`lemma-effective-Cartier-in-points`), 0AG9 (`lemma-integral-effective-Cartier-divisor-dvr`), and the second and final proof paragraphs of 0AGB (`lemma-codim-1-part`). I also read More on Algebra 0AG0 (`lemma-regular-local-UFD`), Algebra 0AFT (`lemma-characterize-UFD-height-1`), and Algebra 00PD (`lemma-characterize-dvr`). These sources support precisely the prime equations, their spreading, the localization, and the DVR assertion used here. The generic DVR conclusion needs only a regular local ring of dimension one, so the proof does not apply 0AG9's globally Noetherian statement directly to the merely locally Noetherian X.

One existing source metadata issue is outside the files I own: `lem-sc-regular-dim1-dvr` cites external Tag 00DV, whereas the needed regular-local-dimension-one equivalence is Algebra Tag 00PD, condition (3). Its actual statement says exactly the fact needed. My proof sources cite 00PD and the report flags the metadata issue without editing that node.

## Searches and reuse

I searched the whole DAG by tags 0AGA, 0AG9, 0AGB, 0AG8 and by regular local UFD, height-one principal primes, stalk localization, and locally principal ideals. Blueprint searches included `regular local`, `Cartier`, `localization`, `height.one`, `locally principal`, `prime divisor`, and `factorization`; the ancestor command confirms `lem-per-artin-gabber-affine-curve`. No blueprint statement duplicates the full item. I reused `lem-trf-regular-local-ufd-boundary-factorization`, `lem-trf-ufd-height-one`, the affine and module stalk localization nodes, and `lem-sc-regular-dim1-dvr`. No new auxiliary statement was needed.

The five additional Mathlib searches were all executed through msearch.py under Q131 and read before recording. Both semantic phrasings miss scheme-level Cartier principality; the second returns DVR results under Dedekind hypotheses, which cannot be applied to the arbitrary higher-dimensional local rings A. Loogle finds no AlgebraicGeometry/Cartier declaration and the Mathlib AlgebraicGeometry grep finds none. LeanSearch returns generic-point and prime-ideal results, not the conjunction of conclusions here. The existing item's previous Q48 search records were retained; the Q131 queries and actual hits were appended, with the new command log kept intact. All five services/commands returned successfully; none was recorded as unavailable.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. The UFD and generic-DVR assertions occur as tools within the split rather than being recreated as nodes. The pointwise-to-open denominator argument is an elementary step of the item's proof, not a new version of its Cartier clause.

## Review by Q131

I reviewed the written statement against the listed Stacks labels, with the node files open. The integral closed subscheme hypothesis makes R/J a domain, rather than merely reduced; the dimension hypothesis belongs to the ambient stalk at the generic point, not to O_D,xi. Every x in D has a neighborhood containing xi. Regularity gives both the Noetherian affine neighborhood and regularity of all the local rings used below. No separatedness, excellence, global Noetherianity, finite dimension bound on X, or extra purity assumption was inserted.

1. Step 1 uses `def-weil-regular-scheme` for a Noetherian affine neighborhood; `def-pc-integral-scheme` for R and R/J being domains; `def-weil-closed-immersion` and `def-sbc-closed-immersion-ideal-sheaf` for Spec(R/J) and the sheaf associated to J. `def-sc-generic-point` says the closure is D, which implies xi belongs to this open. The two cited stalk lemmas explicitly give the localizations of the structure sheaf and of the associated module J. Thus they give I_D,x=J R_q, not just a statement about the underlying support. The quotient fraction calculation establishes primality.
2. Step 2 cites the fraction definition of prime localization. It writes both directions of the double-localization isomorphism and checks the denominators using J contained in q. This makes the isomorphism the canonical generization homomorphism, not merely some abstract identification. No extra comparison theorem is hidden here: both sides are rings of the same fractions, and the displayed formulas compose to the identity.
3. Step 3 uses the same fraction definition and the prime-chain definition of Krull dimension. Extension and contraction are given explicitly, so the one-dimensional generic stalk yields the exact nonzero/no-intermediate-prime height-one hypothesis in `lem-trf-ufd-height-one`. This avoids confusing the maximal ideal of A with the divisor prime p.
4. Step 4 uses the regular-scheme definition to obtain a regular local Noetherian ring A, the parameter definition to choose its finite maximal-ideal generating list, and the UFD node with r=0. I read that node's statement: it permits the empty selected sublist and states the UFD conclusion without any boundary hypothesis. `lem-trf-ufd-height-one` applies to a Noetherian domain, already established, and its conclusion is principality of p. Nonzeroness, nonunitness, and the divisibility characterization are then direct properties of this proper nonzero prime ideal. This step is marked non-elementary.
5. Step 5 cites the Noetherian-ring definition, which explicitly says all ideals are finitely generated, and the fraction relation in the prime-localization definition. For every generator the equality in R_q is cleared using its own annihilating factor u_i; taking the finite product h keeps x in U_h. The reverse ideal inclusion follows from a belonging to J. I checked that the affine-open lemma really includes part (0): U_h is affine with ring R_h. The ideal-sheaf definition identifies its sections with the localized ideal. Since R is a domain and a is nonzero, injectivity of multiplication by a follows immediately from fractions. This is the finite-list calculation from 0AG8 written out, not an uncited general spreading or flatness theorem.
6. Step 6 uses the kernel definition of the ideal sheaf off D and the stated definition of an effective Cartier ideal. The equations from Step 5 together with 1 off D form the required cover. It agrees also with the stronger current blueprint wording of that definition (an affine open at each point).
7. Step 7 addresses every generator g, not just f selected earlier: its ideal remains the same proper nonzero prime. The prime-localization definition explicitly states its maximal ideal is p A_p; consequently it is generated by g. This proves the claimed localization for the arbitrary equation appearing in the item's statement.
8. Step 8 uses `def-weil-regular-scheme` at xi and the entire statement of `lem-sc-regular-dim1-dvr`. Both hypotheses (regular local and dimension one) hold directly, so no assertion about codimension in a noncatenary scheme is needed. `def-sc-discrete-valuation-ring` defines a uniformizer as a maximal-ideal generator, exactly what Step 7 supplies. This step is marked non-elementary.

I checked B1–B9 and C1–C8: there are no unsplit new nodes, no renamed clauses, no new definitions, no use of another node's proof, and no dependency cited merely for a suggestive title. The two off-unit non-Mathlib tools are declared in `split_report.tool_uses`, with their limited algebraic purposes. All citations quote actual statements. Other supporting nodes are definitions or Mathlib leaves. No proof step exceeds 2000 characters; the longest is Step 1 at 933 characters. The prime correspondence and finite-generator calculation are explicit elementary arguments in this particular affine setup, not unnamed general theorem interfaces.

For section E I tested X=Spec(k[t]) and D=(t), with x the divisor point; X=Spec(k[u,v]) and D=(u), with x=(u,v), where the divisor prime is strictly smaller than the maximal ideal; x=xi, when the generization localization is just the identity of the already localized ring; points outside D, with ideal (1); and replacing f by a unit multiple. The zero-dimensional field case cannot satisfy the ambient dimension-one hypothesis. Nonreduced thickened divisors such as (t^2) fail integrality, which is precisely why prime elements and uniformizers are asserted only for integral D. The empty selected parameter list r=0 does not require dim A=0: the node explicitly allows selecting zero positions of any full regular parameter system.

There was no prior delivery or return to repair. The main corrections to the initially empty proof were to expose canonical localization maps, account for annihilators when clearing fractions, prove the assertion for every generator, and avoid using a globally Noetherian source with insufficient hypotheses. No statement dispute remains.

## Unfinished work

None in this one-level split. The existing cited DAG results retain their own independent statuses. This delivery asserts a stage-1 proof plan, not a compiled Lean proof.
