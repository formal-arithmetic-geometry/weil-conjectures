## Files written

- dag/nodes/sec-trace-formula/lem-trf-good-truncation-stage-naturality.json: statement item, now split into seven steps; not a Mathlib leaf. Its statement, statement dependencies, provenance, and original searches are retained. Five actual Q89 searches are appended.
- citations.json: one statement quotation for every node cited by every proof step.
- report.md: this report. searches.jsonl is the search command's own log.

No new nodes and no new Mathlib leaves. No Lean files, compiler commands, repository writes, launcher edits, or agents were used.

## Attachments

None. The project search by the exact blueprint tag and by good-truncation, truncLE naturality and stage-comparison terminology found no declaration stating the whole item. CochainComplex.truncLEMapOfLE_naturality in WeilConjectures/FromJoel/Algebra/Homology/Embedding/CochainComplexTrunc.lean:65 only states the raw truncation-inclusion square, not comparisons with supplied cohomological stage models. No attachment is claimed.

## Literature wanted

None.

## Corrections and source assessment

The item had an empty proof. Its statement is correct and unchanged. I read Stacks Tag 0794, derived.tex, proposition-left-derived-exists, especially the diagram after “The problem is that” and the sentence asserting compatibility as n varies. That source motivates this auxiliary statement but does not write out its inverse-cancellation calculation. I therefore mark the expanded argument as agent-written, using the explicit truncation construction and cohomology formula in Tag 0118, homology.tex, section-truncations. In the larger Tag 0794 diagram the displayed arrow labelled alpha has an orientation inconsistent with the preceding displayed alpha; the present item's explicit alpha:X to Y fixes the orientation unambiguously, and all equations below follow that orientation. This does not require a change to the item.

The current blueprint chapter, sk-i-curve-zero unit, and lem-trf-local-term-locality statement/proof were read from literature/blueprint/latest. This is a generic auxiliary homological lemma below the existing long blueprint.from.via chain supporting that ancestor's proof (1)--(2), not a replacement for the chapter or unit route. No SGA argument is used.

## Mathlib and duplicate searches

The five searches in searches.jsonl were actually run with msearch.py: grep for the inclusion-naturality/quasi-isomorphism criteria, Loogle for truncLE and naturality, LeanSearch for naturality in the cutoff degree, and two LeanFinder phrasings of the supplied-stage comparison. Every service answered successfully. I read Mathlib/Algebra/Homology/Embedding/CochainComplex.lean:45–100 and 270–313, Embedding/TruncLE.lean:180–208, and DerivedCategory/Fractions.lean:65–100. These supply cohomology, inclusion naturality and a roof representation; they do not state the item's simultaneous tower formulas and augmentation identities. The simpler inputs already have DAG nodes, so I reuse those rather than creating leaves for them.

I searched the whole imported blueprint with blueprint_refs.py search for “good truncation”, “truncation comparison”, and “truncation”, and searched the DAG for truncation-cohomology and the relevant quasi-isomorphism declaration names. The broader results concern individual truncations, filtered truncation towers, geometric comparisons or extra exact-functor data; no imported blueprint node states the supplied-stage comparison of this item. Its blueprint.same_as remains empty.

## Not duplicates

No new nodes: there are no new/existing same-tag pairs to justify. Existing lem-weil-pbc-truncation-cohomology and lem-weil-pbc-truncation-descends are deliberately cited. In particular, no node for any clause of the item, no repackaging of the entire item, and no node for a short naturality calculation is created.

## Review by Q89

I checked the split against delivery-errors B–E with the item, the three cited node statements and the Stacks sources open. B: the statement remains self-contained, all original notion dependencies are retained, sources use verified tags and labels (0118 = homology-section-truncations; 0794 = derived-proposition-left-derived-exists), and TeX is serialized once. There are no new unsplit nodes or unverified leaf declarations. C: every non-elementary input is the statement of an existing cited node, not information borrowed from its proof. D: the item's own steps carry the construction and all compatibility calculations; the proof is not delegated to a newly named version of the conclusion. E: I checked the degree-n edge and each cancellation with its actual domain and codomain; in particular the proof never treats c_n^X or c_n^Y as an isomorphism.

For Step 1 I read the complete statement of lem-weil-pbc-truncation-descends. It explicitly calls the canonical truncation a functor and the consecutive inclusions natural transformations, and gives the square in the derived category. The remaining two identities for c are proved degree by degree from the displayed kernel construction: at the endpoint the induced kernel map composes with the kernel inclusion to the original component, and above the endpoint the source is zero. This is a direct definition calculation, so the step is elementary relative to the cited input.

For Step 2 I read lem-weil-pbc-truncation-cohomology, which explicitly states that H^j(c_n) is an isomorphism for j <= n and that the truncated cohomology vanishes above n. I use its actual inclusion-induced identification, not merely an unspecified object isomorphism. The hypothesis H^j(S_n)=0 for j>n is applied only to the stage S_n, while H^j(s_n) being invertible is applied only for j<=n. Naturality then proves T_n(s_n) is a quasi-isomorphism in all degrees. The statement of def-weil-abstract-derived-category supplies the definition of quasi-isomorphism, functorial cohomology, and localization inverting quasi-isomorphisms. Thus all inverses used in t_n are justified without termwise boundedness.

Step 3 uses only Steps 1–2 and the assumed equality s_{n+1}w_n=s_n. I checked each line: c_n factors through c_{n+1} using k_n; naturality moves w_n through c_{n+1}; functoriality combines s_{n+1} and w_n; naturality moves s_n through k_n. The final cancellation is of C_n=Q(c_n^{S_n}), whose invertibility Step 2 proved. The same calculation explicitly covers both towers. Step 4 is the c-naturality equation followed by cancellation of the same stage inverse; it stays in the ambient derived category and needs no ambient bound. Neither step imports an additional non-elementary theorem.

For Step 5 I checked clause (a) of lem-weil-pbc-truncation-descends for T_n(alpha), and its final naturality formula for i_q with q=n+1 for the square with k_n. The objects here may be arbitrary complexes, as that node permits. The localization statement of def-weil-abstract-derived-category makes A_n invertible. The other square in Step 5 is Step 1 with f=alpha. Step 6 is the displayed associative calculation using Steps 3–5. All occurrences of (t_n^G)^{-1} and (t_{n+1}^G)^{-1} are inverses of maps proved invertible; no inverse to the transition maps is used. The augmentation equality is obtained by composing actual maps, not by cancelling a map into Y. For Step 7 the stage bounds are hypotheses, the truncation bounds are exactly lem-weil-pbc-truncation-cohomology, and preservation of cohomology under Q is explicitly in def-weil-abstract-derived-category. The quotation for each citation is copied from that cited statement into citations.json.

I tested the zero category/zero complexes (all maps reduce to the unique identity of a zero object), identity alpha and identical stage models (a_n becomes the identity), and the cutoff n=1 with nonzero H^1 and H^2 of the ambient complex (c_1^X is not inverted). To check the absence of termwise bounds I considered an unbounded split acyclic complex with an identity differential on disjoint consecutive pairs of degrees: it has zero cohomology but nonzero terms in arbitrarily high degrees, and the c_n argument still applies. Arbitrary negative-degree tails do not affect any calculation. For a zero-differential unbounded complex with nonzero terms in every degree, the standard stages E_n=G_n=T_nX and alpha=identity yield the ordinary inclusions k_n and the same equations. No cohomological bound on the ambient complex was silently used.

The only off-unit non-leaf tool is lem-weil-pbc-truncation-descends, declared in split_report.tool_uses for maintainer review. Its generic truncation functoriality is absent from the geometric unit itself; this is a tool use, not a route change. Every proof step is shorter than 2000 characters, and I checked that none hides a separate lemma requiring its own hypotheses. No cycle is introduced: none of the three dependencies reaches this item.

## Unfinished work

None in the one-level stage-1 split. The new proof requires the mandated server dry run and delivery before it is submitted for the maintainer's independent review.
