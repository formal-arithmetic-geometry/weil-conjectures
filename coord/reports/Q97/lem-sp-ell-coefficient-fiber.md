# Worker report: lem-sp-ell-coefficient-fiber

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-ell-coefficient-fiber.json`: statement item, now split into eight proof steps; Mathlib verdict: no match for the whole statement.
- `citations.json`: seventeen literal excerpts, one for each step/node citation.
- `report.md`: this report.

No new DAG nodes and no Mathlib leaves. The sandbox also holds the mandatory search log, a local text extraction of Bhatt–Scholze, and the script that writes the item. These are working files, not additions to the library.

## Attachments

None. I searched the project source for the exact blueprint tag and for the coefficient, uniformizer and Koszul notions. `WeilConjectures/SixFunctors/ProEtale/CompletedIntegral.lean` defines the inverse-limit coefficients, finite projections and scalar restrictions, but does not prove the complete item, especially its augmented quotient fiber and power transition formula. Existing individual scalar/divisibility results are cited through their existing DAG nodes; their existence does not attach this conjunction.

## WANTED

None for this split. The coefficient DVR and finite-quotient facts already have nodes; their existing source records mention the previously wanted Serre reference. I use their statements as algebraic tools and introduce no new external theorem.

## Corrections and limitations

The item statement is unchanged. No STATEMENT-DISPUTED finding was needed. The statement already distinguishes the completed ring from the discrete constant ring, and the shifted fiber from the two-term coefficient tensor complex.

The source proof only sketches the coefficient calculation. In particular, Bhatt–Scholze Lemmas 3.5.4–3.5.7 concern compatible systems and pro-isomorphisms; they do not state this precise chain-coordinate fiber map. I read §3.5, including Definition 3.5.2 and the proof of Lemma 3.5.4, and kept `proof_origin.by = agent` for the explicit expansion. The blueprint first paragraph is the item's route: no purity, trace, SGA, or alternative reconstruction argument is introduced.

The K-flat statement for a bounded-above flat complex in `lem-pc-bounded-above-flat-kflat` is stated for a ringed space. I did not apply that statement to an arbitrary pro-etale ringed site. Instead step 4 uses the existing ringed-site tensor/cone lemma, whose hypotheses match exactly.

Nothing mathematical remains unfinished in the requested one-level split. The cited unsplit statements retain their own ownership and work queues.

## Not duplicates

No new nodes were created. Whole-DAG searches and blueprint searches for coefficient, projection divisibility, K-flat, regular completed and Koszul found the existing reusable ingredients, but no blueprint node states the complete item. The item remains the coefficient-fiber subargument of `sk-lem-sp-tower`.

## Review by Q97

I read `coord/delivery-errors.md` B–E in full, the stage-1 brief, the three blueprint levels in SETUP, GOAL, the smooth-purity chapter record and the `sk-lem-sp-tower` unit record. I read the current blueprint proof at `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/sk-lem-sp-tower.proof.md` and the extracted Bhatt–Scholze §3.5 text. There are no new nodes whose sources require a separate audit. I opened the statement of every cited existing node and checked its actual quantifiers, rather than relying on its title or its proof.

Step 1 uses `lem-weil-l-adic-extension-integers-dvr` for the DVR, residue field and uniformizer factorization and `lem-weil-valued-dvr-finite-quotients` for finiteness. The latter needs a nonarchimedean valued field, a DVR valuation ring and a finite residue field, all supplied for this E. The exponent of ell is positive because the absolute value restricts to the ell-adic absolute value. Cofinality and conversion of ell-power quotients to uniformizer-power quotients are written out, not hidden in another node.

Step 2 uses clause (3) of `det-prop-sfb-qlbar-colimit-x-integral-limit` to match the pulled-back ring with the genuine inverse limit and `sk-def-sp-coefficient-towers` for the named coefficient projections. `lem-pod-completed-integral-scalar-regular` explicitly allows every scheme T and site object U; its name does not restrict it to a geometric point. Its uniformizer-power injectivity gives ell-power injectivity by multiplication by a unit. This checks the object match needed before using cancellation later.

Step 3 uses `lem-sp-completed-integral-projection-divisibility` with index j-1, which is nonnegative because j is positive. This theorem states divisibility of sections in the kernel of the actual projection, precisely what is used. The constant-sheaf definition and `lem-weil-pbc-site-sheafification-sections-local` supply local representatives for target sections; lifting a representative a to all compatible residues supplies the local preimage. Kernel equality plus this local lifting proves the sheaf quotient comparison. The proof does not confuse the notation R/ell^n stipulated in a definition with a theorem about its actual quotient. Compatibility follows from the common projections, not an unspecified transport.

Step 4 uses the explicit cohomology/cone definitions in `def-weil-abstract-derived-category`, the tensor convention in `def-pc-tensor-complex-sheaves`, and `lem-pc-kflat-tensor-cone-two-out-of-three`. I read Stacks `sites-cohomology.tex`, Tag 07A3, label `lemma-K-flat-two-out-of-three`, and Definition 06YN. The tensor lemma is for a site and an arbitrary acyclic complex, so it applies with this completed ring. Tensoring with R[0] is the identity, and the two-term scalar complex is its cone. This proves K-flatness using the cited definition, rather than silently deducing it from finite freeness without a theorem.

Step 5 uses the tensor definition to compute P and constructs the B_n-linear map from B_m by local lifts. Independence of the representative is the equality ell^(n-m)ell^m=ell^n. Step 6 uses only the already established quotient/regularity results and the cohomology definition: local lifts and explicit cancellation prove both the kernel and cokernel assertions. Sheaf quotient lifts are only local, and the proof explicitly permits further covers when an element lies in an image ideal. No surjectivity on sections of arbitrary quotients is assumed.

Step 7 uses the cone and shift formula of `def-weil-abstract-derived-category`, which I compared with `derived.tex`, label `definition-cone`. The shifted cone has B_n, B_n, B_m in degrees -1,0,1 and differentials ell^m and minus reduction. The degree -1 coordinate in the item is therefore a chain map with the stated sign; direct cohomology checks show it is a quasi-isomorphism of B_n-complexes.

Step 8 uses the same cone formula to define the strict reduction map in all three degrees. I verified the chain-level equality on a local lift: reduction of ell^(n'-m)x equals ell^(n-m)ell^(n'-n)x modulo ell^n. This is the actual transition, not a claim that two unidentified isomorphisms commute. For comparison across different coefficient levels, both maps are read after restriction to B_n'. The identity transition n'=n and n=m both work; for n=m the contractible complementary summand has differential -1.

For edge cases I checked empty T (zero sheaves), E=Q_ell, arbitrary ramification e, m=n=1, n=m, n'=n and n'-n at least m. The last case gives zero on B_m as required for the later pro-zero argument. A finite arithmetic check tested 36 combinations t=p^e with p=2,3, e=1,2, 1<=m<=3 and m<=n<=4, and every n<=n'<=5: kernel=image of a, injectivity of a, the augmentation kernel, and the transition equality all passed. This is a check of the local arithmetic formulas, not a substitute for the sheaf proof.

All steps are below 2000 characters. Steps 5–8 are elementary calculations from the preceding proved assertions and the displayed definitions, so they remain steps rather than generating duplicate or clause-only nodes. Every other non-elementary ingredient has a cited node. Seven generic off-unit tools are declared with their precise purpose in `split_report.tool_uses`; none replaces the unit's reconstruction route. The twelve proof dependencies are exactly the union of the eight `uses` lists. The statement dependencies are unchanged and cover all its named notions. Literal excerpts in `citations.json` were checked against the current node statements. Search records preserve the imported searches and add only the five searches actually run by Q97, using two distinct semantic phrasings; no service failure was reported as a no-match. The grep hit is a future-work comment at Mathlib/Algebra/Homology/LocalCohomology.lean:45, not a theorem.

## Validation

Server `srvcheck.py ... check_dag` passed: no finding introduced by the sandbox or on its nodes. The required `deliver.py Q97 lem-sp-ell-coefficient-fiber --no-push` exited 0 and printed `OK (not pushed) deliver/Q97/lem-sp-ell-coefficient-fiber at d31de0575bc: preflight passed`. Only this validation paragraph was updated after that dry run; the delivery push runs preflight again. No Lean file was written and no compiler or build tool was run.
