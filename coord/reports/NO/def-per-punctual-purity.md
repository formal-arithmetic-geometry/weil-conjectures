# Worker report: def-per-punctual-purity

## Files written

- dag/nodes/sec-deligne-laumon-a1/def-per-punctual-purity.json: existing definition, now split. Preserves its statement, source, stmt_deps, earlier searches and blueprint provenance. Adds four construction/well-definedness steps, their named dependencies, fresh searches and split_report.
- citations.json: all 14 citations in the four construction steps, with verbatim statement excerpts.
- searches.jsonl: six real msearch queries and their actual results, preserved in the item's Mathlib searches.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record changes, Lean files or compiler invocations.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, IsPunctuallyPureAt and punctualPurityClassMap, and searched the punctual-purity terminology. There is no declaration of this finite-coefficient local cohomological predicate. The hits in RealSheaves and WeilSheaf describe Frobenius eigenvalue weights of Weil sheaves and do not state this definition. The maintenance note explicitly withdrew the deleted local Sheaf module's attachment; it is not used as evidence.

## Literature and searches

Read ILO, Travaux de Gabber, Expose XVI, Definitions 3.2.1 and 3.2.2, printed p.244 (PDF p.250), together with Definition 2.3.1 and Theorem 2.3.2, printed pp.233--234 (PDF pp.239--240). The source defines the local predicate as invertibility of the canonical closed-point Gysin class, then defines the predicate at an arbitrary point by localization, and the global predicate by all points. We specialize only coefficients to F_ell, exactly as the existing item requires. No henselization/completion equivalence, absolute purity theorem, arbitrary-field adic duality or excluded route is asserted or used. SGA references appearing within the surrounding ILO pages are not sources for this split.

Also read all eight statement dependencies, the regular-local generators theorem (Stacks 00NQ, lemma-regular-ring-CM), the Noetherian dimension theorem (00KQ, proposition-dimension), the affine closed-immersion definition, and the strictly full bounded-derived-subcategory definition. The source locations of the two algebra inputs are recorded in their existing nodes; this delivery creates no source aliases.

Ran leanfinder on the punctual-purity predicate and on the more general supported fundamental class. The first returns etale-locus/local-stalk facts, the second scheme-module restrictions and units, not the ordinary etale supported class. Loogle on AlgebraicGeometry.Scheme, CategoryTheory.IsIso returns scheme isomorphisms, not this predicate. LeanSearch returns stalkClosedPointIso, scheme closed-point maps and Kummer field-extension automorphisms. Both greps have been read: the punctual-purity pattern has zero hits; the broader fundamentalClass/Gysin/Kummer-class pattern hits KummerExtension (cyclic field extensions, read its header) and the canonical site topology, neither a supported etale class. Thus a second phrasing does not reveal a match. No searches have been invented or substituted for unavailable services; all six completed successfully.

Searched the entire DAG for the regular-local/regular-sequence obligations and found the existing lem-weil-pbc-regular-local-generators-regular-sequence and lem-weil-pbc-noetherian-local-system-of-parameters. Searched the blueprint using blueprint_refs.py search for punctual purity, closed point and Kummer, and read the current ancestor's proof in literature/blueprint/latest. The punctual-purity matches concern Weil weights and do not define the present notion. Kummer matches concern sequences, coefficient twists or smooth-field purity, not this arbitrary regular-local predicate. No blueprint definition of this notion was found, so same_as remains []. The inherited ancestor remains provenance; Q84 explicitly re-admits this finite interface, without reviving the ancestor's discarded proof route.

## What was wrong or incomplete

The released stage-1 repair note of 2026-10-24 says the definition was intentionally reopened with its old proof graph and Lean attachment withdrawn. I reconstructed the definition from its preserved interfaces, instead of restoring that graph. Its existing sentence saying that the witnesses are not extra hypotheses now has named support: finite dimension and regularity of the closed-point immersion. The actual map is written as G(b^+) composed with the adjunction unit. In particular there is no unspecified choice of a class, no ad hoc support functor, and no unsupported movement of Tate twists through an exceptional functor. The original statement, source and statement dependencies are unchanged. No statement dispute or source error was found.

The four entries in proof are construction and well-definedness explanations for a definition; they do not purport to prove the purity predicate for every scheme. The IsIso test is the predicate being defined. These entries retain proof_deps as their exact union, so the named construction obligations are visible in the DAG without adding unnecessary definition aliases.

## Not duplicates

No new node was needed. The two algebra obligations and every derived-category/class interface are existing nodes. There are therefore no new/existing same-tag pairs to distinguish.

## Unfinished and WANTED

Nothing requested of this stage-1 split remains unfinished. WANTED: none. The existing unsplit class-calculus and closed-support-adjunction interfaces remain independent tasks, as required by one-level splitting. No proof of their statements is claimed here.

## Review by NO

I read the source definitions against the existing item, including the distinction between a scheme's arbitrary point and the closed point of its local spectrum. I checked the Q84 repair note and route decision before writing. The finite coefficient A=F_ell is level 1, and all functors are on ordinary small-etale module derived categories. The twist is the finite tensor power, not an adic coefficient object.

In step 1, def-weil-regular-scheme says the stalk R is regular Noetherian local; the dimension node explicitly says Noetherian local dimension is finite. The regular-local definition gives d generators of the maximal ideal, and the generators node explicitly says they form a regular sequence. Thus the quotient-to-residue-field immersion has codimension d. The residue-field node supplies exactly R/m, the spectrum node supplies the one-point spectrum of that field, and the closed-immersion node supplies the affine surjection criterion. The scheme T has its one affine Noetherian chart; Z is the spectrum of a field. Invertibility of ell passes to stalks and quotients by applying a ring map to its inverse. Nothing here assumes W has finite global Krull dimension, a coefficient field, excellence, or finite type over a field.

In step 2, the finite-twist node actually gives the roots-of-unity tensor power, and the derived-category node gives D and D+; the degree-zero sheaves and their shifts belong to D+ directly. The closed-support definition specifies the fixed adjunction, unit and counit. It is therefore enough to form G(K), with K=A_T(d)[2d]; I do not replace it by G(A_T) tensor A_Z(d), which would require an additional theorem.

In step 3, I re-read the whole class-calculus statement: it supplies the canonical supported class for regular closed immersions of Noetherian schemes, all the hypotheses just verified, and explicitly supplies independence of regular generators and their order. I take the supported direct-image form of that class, at n=1, without tensoring by another coefficient module. Exact direct image and its derived comparison are stated in the closed-support definition. The bounded-derived-subcategory definition says these are strictly full subcategories of D. Hence the direct-image supported morphism with the two bounded-below endpoints has the unique same morphism b^+ in D+. This uses fullness as a defining property, not a general unproved comparison between two exceptional functors.

In step 4, the fixed unit gives the actual formula alpha=G(b^+) composed with u_M. Its inverse transpose is epsilon_K composed with F(alpha); naturality and the adjunction triangle identity reduce that expression to b^+. The shift comparison is explicitly part of the closed-support definition. The remaining expressions are the IsIso predicate and universal quantification over points, exactly ILO XVI 3.2.1--3.2.2. These manipulations are elementary from the specified adjunction data; no separate lemma-node is warranted. All step citations have verbatim entries in citations.json, and the class/adjunction entries quote their full statements to cover every clause used.

I tested the construction on W empty (the global predicate is vacuous), a field with ell invertible (d=0 and the class is the identity), a regular trait at its closed point (one regular parameter and the normalized Cartier Kummer class), and a nonclosed point (the closed-point test is on Spec O_{W,w}, not the closure of w in W). A regular scheme with varying local dimensions uses d_w point by point. Characteristic ell is excluded by the original unit hypothesis. Parameters do not enter the final data; their existence only discharges the immersion witness and class independence removes their possible effect. The two named witness results already existed, so no false new lemma or duplicate clause was introduced. Every step is shorter than 2000 characters.

I checked delivery-errors B--E: self-contained data, unchanged hypotheses and objects, existing definition nodes, actual construction rather than relabelling purity as a lemma, all non-elementary inputs named, and the canonical morphism specified rather than a bare existence choice. The first dry run required a longer quotation for the derived-category citation; I replaced it by the full existing statement. The mathematical construction was unchanged. Final validation is recorded below.

## Validation

The required deliver.py --no-push completed with exit 0 and OK at edbda409591, with the Weil-server preflight passing (including check_dag and review_split). The original statement, source, stmt_deps, blueprint, created and lean_audit were compared with the read repository and are unchanged. The proof_deps list is exactly the union of the four steps' uses. No new nodes or Mathlib leaves were introduced.
