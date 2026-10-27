# Stage-1 delivery: lem-per-finite-normalization-codimension-one-purity

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-finite-normalization-codimension-one-purity.json — statement unchanged; five-step split, existing Mathlib searches preserved and actual Q41 searches appended.
- dag/nodes/sec-deligne-laumon-a1/lem-per-local-quasi-finite-branch-purity.json — statement, unsplit, no Mathlib match; Stacks Tag 0BMB in its general local scheme form.
- citations.json — 23 verbatim statement quotations for the 23 step citations.

One new node, zero new Mathlib leaves. The sandbox started without a node or report. Nothing in the shared repository, Lean project, or launcher was changed, and nothing was compiled.

## Attachments

None. Searched lean/WeilConjectures for the item id, its blueprint docstring tag, finite-normalization/codimension-one wording, branch-locus purity and the prospective new local-purity statement. No project declaration proves the item or the new statement. The existing regular-codimension-two extension theorem was read as an alternative tool; it constructs another extension and does not itself identify the given normalization with it, so it was not cited as if it did.

## WANTED

None. All sources used are in literature/stacks-project. No SGA source is used.

## What changed and what was wrong

The item was statement-only. Its hypotheses and conclusion agree with the finite-normalization application of 0BMB, so no statement correction or dispute is needed. The real missing arguments were: normality of the base as a domain, equality of local dimensions for each chosen prime (not just equality of global dimensions), conversion of the differential hypothesis to unramifiedness at height-one source points, and separate treatment of the generic point because 0BMB assumes positive dimension. These are now explicit steps.

The parent blueprint reference is inherited from the earlier uniformization expansion of lem-per-artin-gabber-affine-curve, through the parameter-root quotient and punctured-torsor splitting. I read the chapter and unit records and the latest blueprint chapter, unit and ancestor proof. The latest ancestor's actual three steps are Artin–Gabber amplitude/duality arguments, rather than a literal parameter-root argument; this is historical ancestry of the already-created item, not permission to replace its assigned statement. The split keeps the item, chapter, unit and the inherited purity route. Its blueprint place and split_report explain this provenance rather than pretending the newest ancestor says 0BMB verbatim.

## Mathlib and duplicate searches

All new recorded searches were executed with msearch.py and their outputs read. Both semantic services returned results; no service failure was reported as absence. Two semantic phrasings distinguish the finite normalization item from the local quasi-finite theorem. Loogle patterns used IsEtale with IsRegular and with IsNormal. Grep searched branch-locus/codimension terminology in all Mathlib and purity terminology in AlgebraicGeometry. Hits give Etale/IsEtale definitions, the etale locus and its localization criterion, a separable-field theorem, and normality of integral closure. I read Mathlib/AlgebraicGeometry/Morphisms/Etale.lean and RingTheory/Etale/{Locus,Field}.lean; none states purity. The extra single-file grep output has malformed file metadata because rg suppresses the filename for a single file; it is recorded exactly as returned and is not a claimed declaration match.

Whole-DAG searches included the tag 0BMB, lemma-purity, branch locus, regular-normal, integral-closure normality, going down, incomparability, localization dimensions and the stalk-unramified criterion. Whole imported blueprint searches included purity, branch locus, purity of branch locus, 0BMB, quasi-finite normal, quasi-finite, and normal regular, and ancestor was run for the item. The returned branch-locus blueprint nodes concern generically etale curve maps, not the local theorem. No existing node states general 0BMB.

## Not duplicates

lem-per-local-quasi-finite-branch-purity vs lem-per-finite-normalization-codimension-one-purity: the new statement concerns an arbitrary locally quasi-finite morphism at one point, with explicit local normality, regularity, dimension equality and source-generalization unramifiedness hypotheses. The item concerns a concrete integral closure finite over a global domain, assumes only differential vanishing over height-one BASE primes, and concludes global finite etaleness, including dimension zero. Steps 1–4 verify the additional hypotheses and generic case; the new node does not restate that application.

lem-per-local-quasi-finite-branch-purity vs lem-per-snc-root-punctured-torsor-splitting: that node splits a finite group torsor after simultaneous roots over a strictly henselian regular local ring. It neither states local branch-locus purity nor applies without its parameter/torsor hypotheses.

lem-per-local-quasi-finite-branch-purity vs lem-per-snc-parameter-root-quotient: that node constructs parameter-root invariant quotient charts for a normalization with boundary. It has no general local-purity assertion; purity is only an input to its proof.

lem-per-local-quasi-finite-branch-purity vs lem-sbc-regular-local-punctured-etale-purity: that node extends finite etale covers of a punctured regular local spectrum of dimension at least two to a new finite etale model. It does not assert that a supplied normal quasi-finite morphism is etale at a specified point.

lem-per-local-quasi-finite-branch-purity vs lem-sbc-regular-codimension-two-etale-extension: that node extends a cover over an open subset to some finite etale cover; no identification with an arbitrary given quasi-finite source is in its statement. The local 0BMB theorem has a different conclusion and handles source normality explicitly.

lem-per-local-quasi-finite-branch-purity vs lem-sbc-finite-normal-trait-purity: that node assumes a smooth family over a normal local base of dimension at most one, a specified dense etale restriction and a special-fibre etale neighbourhood. The new node concerns an arbitrary quasi-finite map over a regular target, at arbitrary positive local dimension.

## Review by Q41

I read Stacks pione.tex Tag 0BMB, label pione-lemma-purity, including all five hypotheses and the proof's dimension-one and higher-dimensional cases. The new statement has exactly those hypotheses: both schemes locally Noetherian; normal source stalk, regular target stalk, quasi-finiteness at the chosen point, equal positive local dimensions, and unramifiedness at all one-dimensional generalizations of that point. The source's arrow x' leads to x is spelled out as x in the closure of {x'}, to avoid reversing specialization. The new node is statement-only and does not copy the proof into its statement. I read the statements of every node in the item's uses lists and copied the corresponding portions verbatim into citations.json.

Step 1 uses the definition of finite morphism for module finiteness; pqf-lem-finite-qf states precisely finite implies quasi-finite. The finite-algebra Noetherian statement takes exactly the given finite A-module and Noetherian A. The existing finite-extension integral-closure lemma provides a normal domain and fraction field L; the normal-localization node provides normal C_q. The regular-ring-normal node provides local normality of A, and the local-normal-to-normal-domain node supplies the global normal DOMAIN needed for going down; this distinction is not skipped. The regular-ring definition gives every A_p regular local. I checked these against Algebra 00FN, 034L, 00GY, 0567, 030B and Morphisms 02NU, reading the labels, not just their titles.

Step 2 cites actual going down (00H8), actual incomparability (00GT), and the localization-dimension/chains-below-prime node (00KF and 00E3). Their statements provide exactly the lifting, strict contraction and height identification used. The argument never claims C_q is integral or finite over A_p: that localized map need not be finite. Instead it contracts chains in C and lifts chains in A starting from the specified top prime. This gives equality for EACH q, including all height-one generalizations needed later. This is an elementary short chain argument after those citations, so it is a step, not an unnecessary new lemma.

Step 3 applies the item's differential hypothesis only after Step 2 proves the contraction really has height one. Algebra 00UO says vanishing of these actual local-ring differentials is equivalent to formal unramifiedness of that local-ring map. The stalk-neighbourhood node is stated for locally finite type morphisms and formal unramifiedness of that exact stalk map; Step 1 supplies finite type. Its conclusion is a formally unramified neighbourhood, and the further cited locally-finite-type formal-unramified lemma (02HE, read in more-morphisms.tex) supplies unramifiedness. I did not silently identify formal unramifiedness with unramifiedness or cite a global affine criterion for an arbitrary local map.

Step 4 is necessary even when the base has positive dimension, since every integral source has its generic point. I read Algebra 00FP, 00RT(1),(2), 090W and 08WD and Morphisms 02GU. The finite-type Noetherian node supplies finite presentation because module generators also generate the algebra. The existing field-flatness node supplies flatness of L/K and the separable-field differential node supplies Omega(L/K)=0. Differential localization gives Omega(L/A), not automatically Omega(L/K); the text proves the base change of derivation constants by D(b^-1)=-b^-2 D(b), then uses the stated universal property to identify the differential modules. The cited etale-at-prime criterion explicitly uses S_q flat over R_p and localized Omega(S/R)=0, which are precisely the two conditions proved, and explicitly gives an etale neighbourhood. No extra base-change compatibility theorem is being assumed.

Step 5 supplies every hypothesis of the new local purity node from Steps 1–3 for each nonzero source prime. A nonzero prime in a domain has positive height because (0) is prime. Step 4 covers the remaining prime. The etale neighbourhoods form a source open cover, giving etaleness by the local definition, and finiteness is already known. None of the five steps exceeds 2000 characters; the longest is under 900. There is no hidden induction, no use of a cited node's proof instead of its statement, and no self-dependent subclaim.

Small cases: if A is a field, no height-one condition exists, C=L, and Step 4 is the finite separable field case. If L=K, the integral closure is A because Step 1 proved A normal, and the result is the identity map. In dimension one the hypothesis includes every nonzero source prime after the height comparison. For a ramified DVR example A=k[t], L=k(u), t=u^e with e>1 prime to char(k), Omega at (u) is nonzero (dt=e u^(e-1)du), so the hypothesis correctly excludes it. A purely inseparable field extension would make the height-one hypothesis vacuous but is excluded by separability; Step 4 is exactly where that assumption is used. Empty schemes are permitted by the new local theorem only vacuously, since it specifies a point x. The item uses integral domains, hence nonzero rings. No excellence, henselianity, completeness, global finite dimension, or catenarity is used.

The new node is the independent local purity theorem with its own five hypotheses, not one of the item's clauses moved to another name: three substantive reductions and the separate zero-dimensional case remain in the item. Generic algebraic tools from other units are declared in split_report.tool_uses; none replaces a Fourier/perverse unit step. I checked reachability of those tool dependencies to rule out a dependency back to this item. Preliminary server check_dag and review_split both passed. I corrected one source tag during review: finite implies quasi-finite is 02NU (lemma-finite-quasi-finite), not section tag 01WG.

## Unfinished work

No part of the assigned one-level split remains. The new 0BMB node deliberately remains unsplit for a later worker. The maintainer's independent review is still required after delivery.
