# Worker report

## Files written

- `dag/nodes/sec-purity-real-sheaves/prop-wf-open-curve-h1-no-frobenius-fixed.json`: statement, split into four steps; searched Mathlib, no match. No new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotations for all four step citations.
- `searches.jsonl`: actual searches made through msearch.py; retained unchanged.

## Attachments

None. I searched the project Lean source by the exact blueprint id and by open-curve/Frobenius/cohomology terminology. `AlgebraicGeometry.Scheme.EtaleTorsor.exists_section_of_isIsomorphic_mapIso`, in `WeilConjectures/AlgebraicGeometry/FundamentalGroup/Frobenius.lean:607`, is related but states a torsor result with smooth-relative-dimension-one, geometric-point and fundamental-group data. It does not literally state the item's normal-curve derived-cohomology assertion. Its downstream comparison theorem `exists_picTorsionPairing` has `sorry` at line 281, and the local residue extension input has `sorry` at line 382. I therefore make no exact closed attachment claim. The item's existing audit state is none and is preserved.

## WANTED

None. The master blueprint contains the complete proof used here. The main-20261015 file has the identical statement, with no proof body. This delivery uses the existing auxiliary nodes, not an additional external theorem or an SGA source.

## Corrections and scope

The item statement is unchanged. The imported second paragraph used injectivity, exactness, coefficient compatibility and Frobenius equivariance from the residue lemma but cited only the proper-curve lemma. Step 3 now explicitly cites the residue statement and writes both commuting calculations. It proves invariance under Phi_q itself, so step 4 applies the proper-curve result with its parameter Q equal to q, avoiding an unnecessary finite-field base change. The positive power is still used on boundary residues. This retains the unit's open-to-proper route.

Added existing statement dependencies for etale cohomology and constant sheaves. The original scheme and Frobenius conventions are retained; ell is the prime of those conventions. No switch of coefficient category or identification with rational cohomology occurs: every tuple here uses finite constant Z/ell^n coefficients and their ordinary inverse limit.

## Searches and duplicates

Read all hits from two LeanFinder phrasings, LeanSearch, two Loogle queries, and two source greps. The first Loogle query gave an unknown-identifier diagnostic, so it is not evidence of absence; the corrected query `"cohomology", "frobenius"` ran with no hits. The semantic hits concern arithmetic Frobenius at primes, field automorphisms, Witt-vector isocrystals, group Hilbert 90 and function-field class numbers. None is an etale H1 fixed-class theorem. The first source grep finds cotangent-complex H1, not this cohomology; the AlgebraicGeometry-specific grep finds none. These actual outcomes are recorded without an invented service failure or match.

Searched the entire imported blueprint with blueprint_refs.py for Frobenius-fixed and compatible class, and the DAG for open normal curve and fixed-compatible terminology. The only equal blueprint statement is the item itself. The proper-curve result is a genuinely different existing hypothesis case and is cited. No new lemma is needed for the few-line uniqueness calculations.

## Review by Q78

I read the chapter record sec-purity-real-sheaves, the unit record sk-p-real-rankone (especially its third, open-curve step), the master item file including both proof paragraphs, and the current main-20261015 item and residue statements. I opened the complete JSON of each of the three theorem dependencies and read their statements independently of their proofs. The main statement agrees with the imported item hypothesis by hypothesis: normal, geometrically connected, separated, finite type, pure dimension one, and prime ell invertible in F_q. The unit's assertion concerns rank-one purity, so this auxiliary proposition is not its key statement and no unit realization file is changed.

For step 1, lem-wf-curve-normal-smooth-compactification states exactly the smooth projective geometrically connected C_0, dense open j_0, and finite reduced complement required. All its input assumptions are the item's assumptions; no quasi-projectivity hypothesis is added. We use its statement, not the normalization or smoothness argument inside its proof.

For step 2, lem-wf-open-curve-residue-sequence explicitly states the Frobenius-equivariant exact sequence, reduction compatibility, and vanishing of the fixed subgroup of the inverse-limit boundary term for one positive power. The compactification meets its C_0 and D_0 hypotheses. Residues are compatible by its transition clause, and invariant under Phi_q by equivariance. Iterating an equality m times is elementary. Here the phrase 'no fixed element' in the auxiliary statement is read as the displayed fixed subgroup being zero: the zero element of course is fixed. I do not infer that all finite-level residue fixed subgroups vanish, which would be false in general.

For step 3, I checked that the residue statement really starts with zero, so it supplies injectivity as well as existence of lifts from vanishing residues. The two displayed equalities compare the images of the reduction and of Phi_q with those of x_n; injectivity gives the required equalities. This is elementary reasoning from the cited exact compatible sequences, so it remains a step and is marked elementary rather than generating another node. We do not assert inverse limits preserve arbitrary surjections or invoke a derived-limit comparison. This corrects the original paragraph's missing citation and its unnecessary restriction to Phi_Q-fixed lifts.

For step 4, lem-wf-proper-curve-compatible-h1-no-fixed states exactly vanishing for compatible finite-coefficient H1 tuples on a smooth projective geometrically connected curve, for any finite prime-power field and ell prime to its order. With its Q=q, every hypothesis holds by step 1 and the original ell condition. Step 3 supplies exactly the fixed tuple, and zero on all coordinates implies zero of the inverse-limit tuple. No Tate-module pairing, duality, Frobenius base-change comparison, or finiteness theorem is smuggled into this step: those belong below the existing proper-curve lemma.

I checked B through E of delivery-errors.md against these files. There are no new nodes, hence no duplicate helper, self-restatement or unsplit-node proof to audit. All proof citations have their entire literal statement in citations.json. The non-elementary content is precisely in the three cited theorem statements; the remaining work is coordinatewise group algebra and uniqueness. No step exceeds 2000 characters. The cross-unit compactification citation is the unit's explicitly prescribed sk-i-real-compactification route, not a replacement tool argument. No SGA source is cited.

Edge cases: empty boundary reduces at once to the proper case; a non-rational boundary is handled by the supplied positive Frobenius power, without claiming it is pointwise fixed by Phi_q. P1 and A1 have trivial H1 here. For G_m the boundary Z_ell(-1) can have nonzero finite-level invariants when ell divides q-1, but the compatible fixed subgroup is still zero; the proof uses exactly that inverse-limit assertion. Proper curves of positive genus use the existing proper lemma. Geometric connectedness excludes the empty scheme under the project's connectedness convention. No hypothesis on boundary rationality, ell not dividing q-1, nonempty boundary, genus or affineness was introduced.

## Unfinished work

No unresolved step remains in this one-level split. The three cited auxiliary results remain their own DAG items; this delivery does not claim to prove their descendants in Lean. Delivery validation is performed only by the authorized server dry run, never by local check_dag.py/review_split.py or a Lean build.
