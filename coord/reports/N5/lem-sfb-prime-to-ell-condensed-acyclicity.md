## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-prime-to-ell-condensed-acyclicity.json`: item, statement unchanged, six proof steps, status split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-normed-scalar-profinite-hom-acyclic.json`: new statement-only analytic input, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-prime-to-ell-cochain-finite-quotient-descent.json`: new statement-only analytic input, no Mathlib match.
- `citations.json`: verbatim statement witnesses for every step citation.

Attachments: none. Searching `lean/WeilConjectures/` for the exact blueprint tag, prime-to-ell acyclicity, and condensed acyclicity found no project declaration for the item. The continuous-cohomology files under `WeilConjectures/RepresentationTheory/` handle discrete modules; they do not attach this item. No Lean was written and no compiler or build command was run.

WANTED: an ordinary internal condensed-module reference proving the canonical derived internal-function comparison for norm-topological algebraic ell-adic scalars, including noncomplete Omega, for lem-sfb-normed-scalar-profinite-hom-acyclic.

WANTED: an all-continuous, profinite-parameter-compatible comparison of finite-quotient cochains with continuous trivial-scalar cochains for pro-prime-to-ell groups, retaining the noncomplete norm topology, for lem-sfb-prime-to-ell-cochain-finite-quotient-descent.

The source paragraph (3) in the current blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md` is contextual: it factors a direct image through an open immersion and a proper map. It contains no proof of the analytic scalar assertion in this item. I read that paragraph and the chapter and unit records. The imported node already labels this assertion an agent-formulated WANTED input. I retain its statement and mark the proof as agent-written. In particular, I do not attribute either new analytic assertion to that paragraph or to a Stacks tag that states only the discrete analogue.

I also read Bhatt--Scholze, *The pro-etale topology for schemes*, section 4.3, Lemmas 4.3.8--4.3.12, in the available PDF. Lemma 4.3.9 provides useful comparison conditions for discrete coefficients and suitable limits and colimits. It does not itself verify the two analytic assertions here for norm-topological Omega. This is why they remain explicit unsplit nodes. A check of Kedlaya's online *Condensed Mathematics*, section 8.1, https://kskedlaya.org/condensed/sec_cohomology.html, likewise supplied a solid-coefficient acyclicity statement, not the required noncomplete ordinary-module assertion. No external document was downloaded.

The item is split by a computation plus a calculation: the existing derived bar model, a column computation with no group in its statement, the comparison between two explicit function complexes, and a finite averaging calculation written in the item. This does not complete the analytic subproblems. Those are the two new unsplit nodes, which carry no proof, proof dependencies, or disguised proof sketch. In particular the second node compares complexes; it does not assert the augmentation from the scalar module to derived invariants. The item still has to calculate the finite-quotient complex and check which augmentation the comparisons give.

## Searches and reuse

There was no earlier item copy, report, or search log in this sandbox. I retained the item's existing search records and added actual searches made through the prescribed msearch.py command. Each new node records LeanFinder (two phrasings), Loogle, LeanSearch, and Mathlib grep searches exactly as logged in searches.jsonl. All these services answered. No failure was recorded as absence.

The relevant hits were `Condensed.profiniteFree`, `Condensed.profiniteSolid`, `CondensedMod.IsSolid.isIso_solidification_map`, `LightCondensed.ihomPoints` and the internal-projectivity criteria, and `continuousCohomology` with its functoriality and degree-zero results. I read `Mathlib/Condensed/Light/InternallyProjective.lean` and `Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean`. The former is for light condensed modules over a fixed ordinary ring and gives evaluation and a criterion, not derived acyclicity for the internal function ring. The latter defines topological cochains, with no finite-quotient comparison or ordinary condensed derived-invariant theorem. The standard resolution quasi-isomorphism hits concern abstract representations. None is a one-line specialization to either new node. Thus there are zero Mathlib leaves.

Whole-DAG concept searches included prime-to-ell, Haar/averaging, condensed bars, continuous cochains, profinite parameters, and derived internal Hom. I searched the entire imported blueprint with blueprint_refs.py for `condensed acyclicity`, `Haar`, `prime-to`, `continuous cohomology`, `profinite hom`, `cochain finite`, `locally constant cochain`, and `bar`. The focused comparisons found no equivalent blueprint assertion. The nearest-ancestor tool returns None; the inherited null ancestor and via chain are preserved, and the new nodes prepend this item to that chain. No unit or chapter record was modified.

I reused `lem-sfb-condensed-derived-invariant-bar` and `lem-sc-first-quadrant-column-augmentation`. The latter is a generic tool from the Picard unit; it is declared in split_report.tool_uses, with no maintainer-owned top-level tool_uses field. It supplies the finite-diagonal homological argument without changing the unit's geometric route.

## Not duplicates

lem-sfb-normed-scalar-profinite-hom-acyclic vs lem-sfb-profinite-constant-derived-functions: the existing node identifies relative geometric derived functions with derived internal Hom and explicitly retains that derived object; the new node compares underived continuous functions to that derived internal Hom on the condensed point.

lem-sfb-normed-scalar-profinite-hom-acyclic vs lem-sfb-root-tower-boundary-acyclicity: the existing node computes a geometric root-tower term as derived internal Hom and does not assert that it is concentrated in degree zero for an arbitrary profinite parameter.

lem-sfb-normed-scalar-profinite-hom-acyclic vs lem-sfb-derived-internal-hom-sections-model: the existing node describes a derived Hom using a K-injective representative and global morphisms; it does not replace that resolution by continuous functions or assert its acyclicity.

lem-sfb-normed-scalar-profinite-hom-acyclic vs lem-sfb-condensed-derived-invariant-bar: the existing theorem retains derived internal Hom in every nerve degree, rather than computing a single profinite parameter's derived functions.

lem-sfb-prime-to-ell-cochain-finite-quotient-descent vs lem-sfb-condensed-derived-invariant-bar: the existing theorem computes derived invariants as a derived-function total; it makes no comparison of the two explicit underived continuous-function complexes of the new node.

lem-sfb-prime-to-ell-cochain-finite-quotient-descent vs lem-sfb-prime-to-ell-derived-invariants-reduction: the existing node removes a finite-image profinite factor by the item's scalar augmentation; it does not state the finite-quotient-to-continuous cochain comparison used below that augmentation.

No new node cites a Stacks tag also carried by an existing node. The analytical sources are WANTED; no tag was invented.

## Review by N5

I read the item, its entire source paragraph (3), the unit and chapter records, and the statements of each node used in its six steps. The supplied remote-worker brief overrides the older general worker/lead second-reader convention, so this is the required direct-delivery worker review. No other agents were started.

Step 1 uses the statement of `lem-sfb-condensed-derived-invariant-bar`, specifically the isomorphism to the total of derived internal functions, the nonnegative-resolution clause, and the invariant-inclusion normalization. Its ring is precisely C_F and its equivariant input is the trivial regular module. I did not use a statement about discrete representations in its place.

Step 2 uses the first new statement's derived isomorphism for P=K^n and its contravariant naturality in continuous parameter maps. Those hypotheses cover all products and every inhomogeneous nerve map; the coefficient action is trivial. It then uses the existing column-augmentation statement: a first-quadrant double complex, a nonnegative cochain complex, commuting augmentations, zero next resolution differential, and column quasi-isomorphisms give a total quasi-isomorphism. I checked these against the bar-resolution model explicitly. This generic totalization result is cited, not passed off as elementary. The formula for internal Hom sections is part of the new node itself; no general fully-faithful Yoneda statement is used as a substitute for an evaluation statement.

Step 3 uses exactly the second new statement's specified inclusion and its quasi-isomorphism assertion. Both complexes are complexes of internal C_F-modules, and the prime-to-ell finite quotient hypothesis is identical. Their term in degree zero is C_F, with identity inclusion; no change of the topology of Omega occurs here. This is an unresolved analytic input, not a conclusion claimed from Bhatt--Scholze's discrete comparison.

Step 4 uses only the second node's definition of the finite-quotient subcomplex and the elementary finite sum displayed in the step. I expanded the differential computation, including the sign (-1)^n and the reindexing h to g_n h. No finite-group vanishing theorem or Haar measure is hidden in this step. A section of a sheafification is represented locally; zero differential can be checked after a further cover. Common refinements of the finitely many finite quotients are given by intersection of open normal subgroups. Thus the proof obtains local primitives, which is exactly what exactness of sheaves requires. The inverse of m=|K/U| is a constant scalar for both fields. The stronger ell-unit property is needed by the analytic comparison input, although the finite sum itself needs only invertibility of m.

Step 5 uses the local primitives of step 4, the degree-zero differential for a trivial action, and the localization clause in `sk-def-sfb-derived-categories`. There are no negative terms. Therefore the augmentation is a quasi-isomorphism; no uncited unbounded spectral-sequence convergence is asserted.

Step 6 uses the degree-zero normalization from the existing derived bar statement and the canonical comparison maps fixed in the two new nodes. The resulting composite is the invariant-inclusion augmentation in the original statement, not merely an unspecified isomorphism of source and target objects. This finishes the item conditional only on its named DAG inputs, as a stage-1 split must do.

I checked small cases for each new statement. For the profinite-parameter node P empty gives the zero object on both sides and P finite gives a finite power of C_F, so internal Hom is exact in this case. For the cochain-comparison node K finite has U=1, making the inclusion an equality; K=1 has identical cochain complexes and identity augmentation. Empty S gives zero sections. For a nontrivial infinite check K=Z_r, r different from ell, continuous additive characters into either F vanish: a compact additive image is bounded, and each discrete quotient modulo ell^n of a bounded lattice has ell-primary torsion, so its finite pro-r image is zero; intersecting these kernels gives zero. This checks degree one; I have not claimed it proves higher-degree comparison. For K=Z_ell the excluded hypothesis fails and nonzero additive characters exist, explaining why one must not remove the prime-to-ell condition from the comparison input.

I also checked the noncomplete edge explicitly: a compact subset of Omega need not lie in a finite extension (take elements of increasing degrees scaled to converge to zero). Therefore no step replaces all-continuous functions by finite-extension-valued functions. Nor do the finite averages extend by an asserted Omega-valued infinite Haar integral. The missing analysis is visible exactly in the two new nodes and in the WANTED lines above. No contradiction to the imported statement was established, so no statement correction or STATEMENT-DISPUTED claim is made.

Against delivery-errors B--E: both new statements introduce every object and have only statement dependencies; both derived comparisons are stated as derived isomorphisms, not solely as per-degree consequences. I opened the close existing nodes listed above and recorded the distinctions. All non-elementary facts in the item have node citations, and the citations.json witnesses are copied verbatim from those statements. The two elementary calculations are left in the item. I checked all proof-step lengths: none exceeds 2000 characters, and there is no deferred hidden sublemma in a long paragraph. The source's absent analytic proof is recorded instead of being reconstructed as an unsupported citation. No SGA route, geometric alternate route, or target change is involved.

## Validation

The server single-item review_split check passed. The first full dry run stopped before push because the column-augmentation citation quote was under the tool's 40-character minimum. I replaced that quote with the full verbatim statement, including all hypotheses and its conclusion, and reran the dry run. The full delivery dry run then exited successfully: OK (not pushed), preflight passed at 3036d46f691. The final report records that result; it is revalidated before the authorized push.
