# Stage-1 delivery: lem-zl-classical-weil-filtration-heart-transport

## Files written

- dag/nodes/sec-deligne-laumon-general/lem-zl-classical-weil-filtration-heart-transport.json — statement preserved, split into eleven proof steps using eighteen existing nodes. No new nodes and no new Mathlib leaves.
- citations.json — thirty entries, one for every step/node citation, copied verbatim from the cited statements.
- searches.jsonl — the search command's original log. The item's pre-existing searches were retained; six actual new searches were added to mathlib_searches with their returned hits and verdicts.

The local write_split.py is a sandbox drafting aid, not part of the DAG delivery. The report and citations accompany the item. No repository, launcher, literature or Lean file was edited, and no compiler or build tool was run.

## Attachments

None. Searched lean/WeilConjectures for the exact item id and blueprint tag, classical Weil filtration names, lisse/rational realization, and filtration/heart terminology. No declaration there states the full item, including classical systems, exact heart quotients, normalized iterated point transport and common finite stages. Existing general comparison declarations are tools, not an attachment of this item.

## WANTED

None. All sources actually needed were available locally.

## Corrections and scope

There was no earlier item/report in the sandbox. I copied the current unsplit repository node, retained its statement, source, blueprint ancestry and searches, and supplied its proof. There is no statement dispute. The item is an auxiliary node, not the unit's key theorem, so no unit record is changed.

The imported reference to lem-tw-lisse-rational-realization does not by itself identify a classical inverse system with an ordinary lisse module: it is an equivalence between the raw-heart lisse subcategory and ordinary pro-etale modules. The split explicitly composes it with the existing lem-per-lisse-completed-system-comparison, rather than assuming it is a theorem about classical systems. This also avoids inventing a new duplicate comparison node. Exactness is not inferred merely from full faithfulness, nor from exactness of arbitrary integral representatives.

The proof follows the blueprint unit's actual-filtration route. It does not construct geometric constituents, prove purity by curves, or substitute a different route for those arguments. It realizes the particular given filtration. Generic comparison and exactness tools outside the unit are declared in split_report.tool_uses for the maintainer's review; no tool_uses field was set directly.

## Unfinished work

None in this one-level split. Existing cited statements may still have their own open Lean obligations; none is reported as a newly completed Lean proof.

## Not duplicates

No new nodes. Before deciding this, I searched the whole DAG for classical/lisse, exact adic fibres, completed reduction systems, rational realization, and finite diagrams; and ran tools/blueprint_refs.py ancestor for this item and search for “lisse rational realization”, “filtration”, “lisse”, “classical Weil filtration” and “completed lisse”. In particular the existing completed-system comparison, normalized-fibre exactness, constructible-fibre exactness, sf/PBC comparison, stable-lattice and common-stage calculus nodes supply the needed facts. There are no new/existing same-tag pairs.

## Mathlib searches

The pre-existing item searches were read and retained. The six new logged searches were:

- leanfinder: “Transport a finite filtration of classical lisse adic Weil sheaves to an exact constructible heart filtration with normalized Frobenius fibres”. Eight hits, concerning ordinary module/ideal filtrations and local cohomology; none states the item.
- loogle: “CategoryTheory.ShortComplex.ShortExact, CategoryTheory.Equivalence”. No hits.
- grep: “WeilSheaf|lisse.*realization|classical.*adic”. Eighteen returned hits, all unrelated ordinary Classical/padic algebra code. These actual results, despite being unhelpful, were recorded as returned.
- leansearch: “A fully faithful realization of lisse adic sheaves respects geometric fibres and Frobenius structures”. Eight hits about locally constant condensed functors and abstract sheaf/Spec full faithfulness, with no classical adic Weil comparison.
- leanfinder, second phrasing: “Classical lisse adic inverse systems have fully faithful rational realization with exact geometric fibre functors”. Eight abstract profinite/condensed full-faithfulness hits; none supplies the adic assertion.
- grep: “WeilSheaf”, subdirectory AlgebraicGeometry. No hits.

No service was unavailable. No Mathlib result was rejected merely because it was more general: the abstract fully faithful results do not supply the classical realization, fibre normalization, exactness or Weil comparisons required here. No new node needs a Mathlib search.

## Review by Q109

I read the chapter and unit records, including all four unit steps, the current main-20261015 proof of thm-zl-real-mixed-by-curves, and the full statements of every node cited by this split. For the item I read Bhatt–Scholze §6.8, printed pp. 58–62: Lemma 6.8.2, Definition 6.8.3, Proposition 6.8.4, Corollary 6.8.5, Lemma 6.8.7, Proposition 6.8.14 and Remark 6.8.15. I also read Weil II (1.1.1), (1.1.6)–(1.1.14) and the punctual-purity convention, and Stanford L19 Proposition 1.1.9, especially its stable-lattice and quotient-system bullets. There are no new-node sources to audit. The normalized sf/common-stage assembly is explicitly marked as an agent proof: the external sources do not literally state this entire interface theorem.

Step 1 uses the actual statements of lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type and lem-weil-pbc-noetherian-finitely-many-components. These give Noetherianity, finite dimension, and finite irreducible components. The finite intersection graph argument written in the step then gives clopen connected components. The field is Noetherian, and Y is separated finite type over k, so the comparison hypotheses are satisfied. The step does not assume irreducible components are disjoint.

Step 2 uses the explicit object-pair and Hom-colimit clauses of def-pod-lisse-l-adic-sheaves and the pullback/scalar compatibility in lem-per-lisse-completed-system-comparison. Each object, arrow, inverse and equation is part of a finite list, so composita and eventual equality suffice. In particular inverse identities and Weil-equivariance equations are included, not inferred from an arbitrary representative. No exactness is asserted yet at this stage.

Step 3 uses cor-galois-lisse-representations(2) to obtain the continuous E-representation and its integral counterpart, and lem-pod-profinite-stable-lattice for a finite free stable lattice. The group is profinite and hence compact, the fibre is finite-dimensional, and the correspondence's action is continuous. Connectedness is supplied componentwise by Step 1; Noetherianity, separatedness and invertibility of ell have all been checked. These lattices need not be Weil-stable or make the inclusion sequences integrally exact. This is why no smoothness or geometric-unibranch assumption is added to the item.

Step 4 uses the statement, not the proof, of lem-per-lisse-completed-system-comparison: its normalized finite-free systems have inverse-limit realization, rational full faithfulness, and normalized pullback/scalar comparisons. lem-tw-lisse-rational-realization supplies exactly the sf lisse-heart essential image and full faithfulness. Both realize arrows through specified functors. Lifting maps and their inverses, and then checking composites through a faithful functor, proves the equations. def-weil-weil-sheaf-complex supplies the precise equation for a Weil morphism. The steps do not treat the Weil-pair category as a derived category of Weil sheaves.

Step 5 first checks the sf/PBC passage. lem-fd-rational-coefficient-category-comparison says identity on the common integral category and localized maps; def-weil-constructible-standard-tstructure and prop-weil-localized-tstructure define their rational halves by the same isomorphism-closure formulas. Thus their finite-stage hearts agree. On lisse objects the scalar-realization formulas are the same. The normalized inverse-limit fibre and fractional-map formulas are explicitly in lem-per-adic-normalized-fibre-exactness, and the point-fibre statement of lem-tw-lisse-rational-realization identifies the actual point functor. The completed-system comparison supplies finite coefficient compatibility. This avoids silently applying a PBC fibre theorem to an unidentified sf heart.

Step 6 uses lem-dl-a1-constructible-fibres-exact, whose statement explicitly gives short exactness iff all geometric coefficient fibres are short exact, including after forgetting a Weil structure. The lifted short complex has zero composite by faithfulness, and the hypothesis supplies exactness on EVERY geometric adic fibre, not just at selected closed points. This proves monicity and the prescribed cokernel in the ambient heart. Conjugation by the given top Weil isomorphism makes the filtration end at the actual G. This is an application of exactness detection, not an unsupported assertion that a fully faithful functor preserves short exactness.

Step 7 reuses the finite-stage normalized-fibre criterion after the heart comparison, and lem-weil-field-scalar-extension-exact for extension of vector-space kernels, homology and cokernels. Vanishing reflects along E to Qlbar because a nonzero vector extends to a basis and remains nonzero. Thus exactness at all Qlbar fibres proves exactness of the finite-stage rational fibre sequences and hence the finite-stage heart sequences. I checked that this argument does not require reduction of a short exact rational sequence to be exact for a chosen integral lattice.

Step 8 uses prop-weil-pbc-common-stage-calculus for precisely its finite-diagram/equality assertion, and lem-fd-rational-coefficient-category-comparison to use it on sf data. We retain the already chosen lisse models and enlarge fields for maps and equations; Step 7 establishes exactness there. A common stage includes inverse Weil maps, not just forward maps. The source of every pulled-back map is fixed by the named scalar comparisons.

Step 9 uses the arbitrary-scheme-map and iterated point-transport normalization clauses of lem-tw-lisse-rational-realization, the classical finite-level pullback comparisons of lem-per-lisse-completed-system-comparison, and the actual local operator formula of def-weil-local-frobenius-trace. I checked the three factors individually: iterated restriction/coprojection transport; the comparison for g_Y^n composed with x = x composed with g_s^n; and the pullback of theta^[n]. The last agrees by the displayed recursion. On integral inverse limits equality is checked after each finite projection, then localization gives the rational map. No equality g_Y^n x = x, nor any unspecified scalar multiple of the operator, is used.

Step 10 uses def-weil-punctual-weights only for its exact eigenvalue-modulus definition. The intertwiner in Step 9 and its inverse prove equality of eigenvalues directly on eigenvectors; the residue field and cardinality are the same. This checks purity of each prescribed weight, including its vacuous truth on zero quotients, without incorrectly asserting a unique weight for zero.

Step 11 uses the same normalized pullback and iterate clauses and the local-operator definition. Grouping the written theta factors and point transports proves compatibility with the m-fold structure after any finite constant extension. The Frobenius scheme map need not be k-linear: the comparison statement explicitly allows arbitrary scheme maps. The empty filtration of zero, rank-zero terms, repeated terms, empty base, disconnected base and nonsmooth base were checked. None requires a strict-inclusion or nonzero-rank hypothesis.

Against delivery-errors B–E: every object is introduced in the retained statement; no new unsplit node contains a hidden proof; no new declaration or same-tag duplicate was fabricated. Every non-elementary step cites the existing statement that supplies it, and citations.json was checked by substring against those statements. No step relies on a cited node's proof or a definition for an unstated theorem. The item's proof carries the construction and the compatibility calculations, rather than moving a clause into a new node. All eleven steps are below 2000 characters. There is no SGA route citation; reading Weil II's surrounding historical references did not turn them into proof dependencies. No unit or target statement was changed.

The initial server review_split check passed with zero new nodes and declared generic tool uses. Final delivery validation is recorded by the required deliver.py dry run and push.

The first deliver.py dry run requested longer quotations for five citations (the tool requires 40 characters or the whole statement). I replaced these by the full finiteness statements, the full Weil-iterate recursion and the punctual-purity sentence with its formula. I also made the Step 10 source precise as Weil II (1.2.6), p. 154, which permits real iota-weights. No mathematical statement or proof argument changed.
