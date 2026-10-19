# Q32 stage-1 delivery: lem-sfb-module-mapmod-pullback-kflat

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-module-mapmod-pullback-kflat.json: item, split into four proof steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-kflat-stalk-criterion.json: statement-only lemma, Stacks 0DEN; unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-proetale-enough-points.json: statement-only lemma, Stacks 0992; unsplit, no Mathlib match.
- citations.json: ten verbatim statement excerpts, one for every step/node citation.
- report.md: this report. searches.jsonl is the original msearch log. write_split.py is sandbox-only drafting machinery, not a delivery file.

Two new nodes, zero Mathlib leaves. No Lean was written, no compiler or Lake was run, and no live repository or launcher file was modified.

## Attachments

None. Searches of WeilConjectures in the provided slopmaster2 checkout found neither the blueprint tag nor the asserted CondensedRing declaration. The recorded module path is absent from that checkout. I also searched its ProEtale/KFlat files and the general sites/point and monoidal KFlat files: the available results concern flat-resolution complexes or flat objects, not arbitrary K-flat module-object complexes. The exact archived master instance is at WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperLowerStar.lean:176-177 and is explicitly `:= sorry`; it is not an attachment.

## WANTED

None. All sources needed for the proof and the new statements are available locally.

## Findings and corrections

The imported statement is mathematically unchanged. Its two nonexistent umbrella references, sk-def-sfb-finite-pushforward-pullback and sk-prop-sfb-module-category, were replaced by the existing precise definitions def-sfb-finite-upper-star-monoidal and def-sfb-modobj-relative-tensor; statement dependencies now also name the coefficient and module notions used.

The imported proof does not justify its key claim. Stacks sites-cohomology lemma-pullback-K-flat (0G7E) explicitly assumes the K-flat complex has flat terms; the item does not. Exactness, strong monoidality and commuting with colimits by themselves only test tensors against pulled-back complexes. The vague final reduction to functorial flat resolutions does not resolve arbitrary test complexes, nor does a quasi-isomorphism alone preserve K-flatness of an arbitrary complex. I replaced that paragraph with the pointwise proof of 0DEP: forward K-flat stalk criterion on Y, composite topos points, reverse criterion on X. Stacks 0992 supplies enough points for every X. This changes the proof below its unit, not the unit statement or route. There is no statement dispute or additional flat-term, finiteness, boundedness or separation assumption.

The general points used here must not be confused with ordinary scheme-geometric points. I read the warning in lem-cbc-proetale-stalk-conservative: ordinary geometric stalks do not detect arbitrary pro-etale sheaves. The new 0992 statement expressly says topos points, and step 3 composes those geometric morphisms; it does not invoke ordinary geometric stalk conservativity.

## Searches and blueprint ancestry

I searched the entire DAG and imported blueprint by K-flat, pullback, stalk, enough points and Tags 0DEN, 0DEP, 0992, using rg and tools/blueprint_refs.py. The ancestor command gives the item itself. Each new node records this ancestor, its precise service to the arbitrary-acyclic-complex test, and no intervening nodes. No equivalent imported blueprint node was found. The unit is sk-prop-sfb-module-derived-factorization: its clause (2), explicitly realized by this item and prop-sfb-module-left-derived-upper-star-iso, remains intact. This is not the unit's key node, so no unit record is changed.

Each of the item and the two new nodes has logged leanfinder, loogle, grep and leansearch queries, plus a second semantic phrasing. The search services all answered successfully. The recorded query strings and result summaries are copied from searches.jsonl, including subdirectory metadata. Hits give ordinary flat modules, sheaf pullback definitions, K-projective/K-injective notions, and etale/topological points, not the statements here. I inspected Mathlib/AlgebraicGeometry/Sites/EtalePoint.lean:129-162 and Mathlib/Topology/Sheaves/Points.lean:54-69: the enough-points instances are for small etale and open-set sites, not the small pro-etale site. No KFlat/IsKFlat/kFlat hit exists in the logged whole-Mathlib grep; the homology grep also found none. No candidate qualifies as a one-line specialization.

## Not duplicates

lem-sfb-ringed-site-kflat-stalk-criterion vs lem-pc-kflat-stalk-criterion: the existing statement is for ringed topological spaces and their ordinary topological stalks; the new statement covers arbitrary ringed sites, arbitrary topos points, and the converse for a specified conservative family.
lem-sfb-ringed-site-kflat-stalk-criterion vs lem-sfb-etale-derived-tensor-stalk: the existing 0DEN citation proves a derived tensor/stalk comparison for constant coefficients on the small etale site; it does not state K-flatness of arbitrary ring-sheaf complexes at arbitrary topos points or the conservative-family converse.
lem-sfb-ringed-site-kflat-stalk-criterion vs det-ctf-finite-proper-tor: that item's 0DEN references use the preceding constant-coefficient derived-stalk comparison to prove a finite proper Tor-amplitude assertion; they do not state the new criterion.
lem-sfb-ringed-site-kflat-stalk-criterion vs lem-kun-geometric-point-derived-constants: that item's 0DEN references concern derived constant sheaves over an algebraically closed geometric point; they do not state the general ringed-site criterion.
lem-sfb-proetale-enough-points vs lem-trf-finitary-site-enough-points: the existing generic criterion requires finite limits and finite cover refinements; applying it to a general scheme's small pro-etale site requires the affine-site comparison/localization from the proof of 0992, rather than a direct specialization to the whole site. The new statement records exactly the geometric conclusion, leaving that source argument to its future split.
lem-sfb-proetale-enough-points vs lem-cbc-proetale-stalk-conservative: the existing finite-discrete-coefficient statement gives covering and basis detection, and ordinary geometric-stalk detection only on etale-origin complexes; its warning explicitly excludes ordinary geometric stalk conservativity on all pro-etale sheaves. The new statement is about a general family of topos points.

## Review by Q32

I read the item's current main-20261015 statement and imported proof, its chapter and unit, the master source instance, and the exact Stacks sources. For 0DEN I read the full statement and proof in sites-cohomology.tex:3767-3830. Its forward direction applies without enough points and without flat terms; its reverse direction uses only conservativity, exact stalks and compatibility of stalks with tensor and direct sums, so a set-indexed conservative family suffices. For 0992 I read proetale.tex:3553-3580: it explicitly includes the small pro-etale site of every scheme, via affine site comparison and Deligne's criterion. I also read the statement and proof of 0G7E and the statement/proof of 0DEP to diagnose the imported gap and check the replacement.

For step 1, I opened sk-def-sfb-sheaf-tensor and lem-pe-internal-section-tensor-comparison. The former really supplies the sheafified objectwise tensor structure, not a cartesian structure; the latter explicitly states exactness, identification of total tensor complexes, and preservation/reflection of K-flatness for arbitrary commutative internal ring objects. Thus it applies to both Lambda_Y and its transported ring S, not only to finite coefficients or constant sheaves. All sites use the compatible small/coefficient-universe convention. I do not merely use the comparison node's proof or a derived-Hom conclusion.

For step 2, I opened def-weil-proetale-inverse-image, def-sfb-finite-upper-star-monoidal and sk-def-sfb-transport. They give the same sheafified inverse image and its ring lift, the strong monoidal comparison and exactly the action F(gamma) after the tensor comparison. The step writes out the action identification on local pure tensors, the induced ring multiplication and unit, and the compatibility of all differentials. This is an elementary substitution of the three displayed constructions, not a new opaque transport theorem. No direct-image tensor projection formula or preservation of arbitrary K-flatness by general strong monoidal functors is used.

For step 3, I opened def-trf-geometric-morphism: it expressly gives the composite inverse-image formula. At each arbitrary point p of X, the point q=u composed with p of Y therefore has q^{-1}=p^{-1}u^{-1}. The forward clause of the new 0DEN node says exactly that the K-flat source stalk at q is K-flat. The two stalk rings and module actions are identical under this formula, so no flat ring-map hypothesis, stalk base-change theorem, or unproved extension-of-scalars input is hidden here. The chain identifications follow termwise with the same differentials.

For step 4, I checked that the new 0992 node gives a conservative set-indexed family on X without any quasi-compactness or Noetherian assumption. The new criterion's reverse clause applies precisely to that family and tests arbitrary acyclic complexes on X. The final reflection statement is explicitly in the existing comparison node. All ten step/node citations have a verbatim excerpt in citations.json; non-elementary facts are node statements. The only elementary step is the explicit definitional action comparison. No step is longer than 2000 characters.

I checked small cases: X empty (the zero sheaf category, where all tests vanish); f the identity (q=p and the action comparison is the identity); the zero condensed ring and zero complex; a nonflat module A/I in degree zero, where the criterion does not incorrectly claim K-flatness; a contractible two-term complex of nonflat modules, which is K-flat and is allowed by the statement; and unbounded complexes (direct-sum total tensor and the full unbounded 0DEN statement are used, with no bounded spectral sequence). The pro-etale-over-an-algebraically-closed-point case illustrates why arbitrary topos points are retained. I checked the new nodes are not elementary restatements or clauses of the item: one is an intrinsic sitewise criterion, the other a geometric existence theorem independent of Lambda, P and f. Neither asserts transport preserves K-flatness.

Against delivery-errors B-E: both new nodes are self-contained statements only, have definition dependencies, correct Stacks tag/label sources, standard TeX, actual logged searches, explicit ancestry and duplicate comparisons; the proof uses the cited statements with their hypotheses in force, has no dependency back from either new node to the item, and does not move the conclusion into a child. No SGA source is used.

## Unfinished work

None in the requested one-level split. The two new nodes are deliberately unsplit and will enter the stage-1 queue.

## Validation

The first required server dry run completed successfully: deliver.py --no-push printed OK at 84a0beeb98, preflight passed. After finalizing this report and replacing the first sheaf-tensor citation excerpt with the explicit tensor definition and monoidal assertion, I rerun the same dry run before the push. All validation runs are on the server through the authorized delivery tool, with one deliver.py invocation active at a time.
