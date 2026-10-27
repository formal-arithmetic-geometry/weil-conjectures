## Worker report

Files written:
- dag/nodes/sec-smooth-purity/lem-pur-line-zero-geometry.json: statement, split into nine steps; no complete Mathlib match.
- citations.json: one verbatim statement excerpt (in this case the whole statement) per node cited in each numbered proof step.
- searches.jsonl: actual searches saved by msearch.py; the five new completed searches were read and added where not already present in the item's inherited records.
- write_split.py: sandbox-only JSON generation helper; not part of the DAG delivery.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. Searching WeilConjectures for the exact blueprint id, Cartier zero sections and projective compactification gives no declaration stating the whole item. The vector-bundle atlas and zero section in AlgebraicGeometry/VectorBundle.lean supply data and closedness only, not this conjunction. No compiler, Lake, Lean-writing tool or git command was run.

WANTED: none. All sources needed for this split are in the read clone.

The imported statement is preserved verbatim, with all hypotheses and every conclusion. It was unsplit and had no proof; its existing Mathlib search records are retained. No statement dispute, unit-route error, target change or unresolved mathematical gap was found. No SGA source is used. The auxiliary affine-line lemma is used for its explicitly stated Noetherianity of the base, not for purity or for any fact hidden in its proof.

The report and split are written by this dispatched worker N9 for direct delivery. No second worker or sub-agent was started. The maintainer's independent reading remains the external mathematical review.

## Sources and route

I read GOAL.md, the three levels in SETUP.md, the worker/stage-1 contract, the complete B--E checklists in delivery-errors.md (both copies), the sec-smooth-purity chapter and sk-prop-an unit records, and the current main-20261015 unit text. This is a geometric prerequisite to the zero-divisor Step 1 in thm-pur-rank-one-thom.proof.md, and to steps 1--2 of lem-pur-line-zero-class-etale-realization. It leaves the vector-bundle route intact. Its nearest blueprint ancestor remains thm-pur-rank-one-thom, via lem-pur-line-zero-class-etale-realization. Whole-blueprint searches by projective bundle, relative Proj, Cartier, dimension drop and zero section found ingredients and higher purity assertions, but no duplicate of this complete geometry statement; same_as is empty.

For the actual geometry I read the local Stacks texts: Constructions 01LX (lemma-spec-properties), 01OB (definition-projective-bundle), 01OE (lemma-projective-space-bundle), and the relative-Proj base-change discussion 01O3; Morphisms 01S7 (lemma-affine-separated), 01V6 (lemma-smooth-characterize), 01T6 (lemma-finite-type-noetherian); Properties 01OW (lemma-locally-Noetherian), 01OX (lemma-immersion-into-noetherian), 01OZ (lemma-Noetherian-topology); Divisors 01WR/01WS (definition-effective-Cartier-divisor/lemma-characterize-effective-Cartier-divisor); Algebra 00KW (lemma-one-equation). I checked the tag-to-label mapping in tags/tags. I corrected an initially inaccurate source label that had called 01WS a definition: 01WR is the definition, 01WS the local-equation characterization.

## Review by N9

I opened every cited node and read its statement, rather than relying on its title or proof. The following checks describe the mathematical use in each step; citations.json reproduces the exact statement used, without manufactured quotations.

1. def-pur-vector-bundle-zero-section explicitly constructs the relative spectrum and gives its affine symmetric-algebra description, augmentation, closedness, and section identity. def-amb-finite-locally-free-module gives Zariski frames, and lem-weil-pbc-symmetric-algebra-free-module-polynomial identifies the generator with the polynomial variable. These give the actual pair Spec R[t], V(t). The overlap equation t'=u t is obtained by applying the same linear generator map to e'=u e. This is compatible with the convention Sym(E), with no dual silently substituted.

2. lem-weil-pbc-affine-morphism-relative-spec explicitly makes the projection affine; lem-weil-pbc-affine-morphism-permanence gives quasi-compactness and separatedness. lem-weil-pbc-lft-pointwise-criterion applies because each point has the affine pair R to R[t], a singly generated algebra. def-weil-finite-type-morphism supplies the conjunction. lem-sfb-finite-type-composition-base-change and clause (e) of lem-weil-pbc-proper-fp-permanence give the two required composition facts. Both factors have the hypotheses. In particular I do not confuse smoothness with separatedness or omit quasi-compactness from finite type.

3. sbc-lem-affine-space-smooth states smoothness with the precise relative dimension for every scheme and every n. lem-weil-pbc-smooth-restrict-open-subschemes includes composing the local projection with the target open immersion and transport under isomorphism; lem-weil-pbc-smooth-local-on-source is exactly the open-cover gluing criterion. def-sbc-smooth-morphisms identifies relative dimension with dimension at a point of the fibre, not the Krull dimension of its stalk. The affine-line fibre has dimension one at all its points in that sense. There is no regularity hypothesis on B.

4. lem-pur-projective-bundle-tautological-geometry gives properness and the frame identification for F=O plus E, of rank two. lemma-nagata-relative-affine-space-open-immersion gives the coordinate t=T1/T0 over any base. The transition equation T1'=u T1, T0'=T0 makes the local open embeddings agree, so lem-weil-pbc-scheme-morphism-gluing applies on the source frame opens and also to their inverses on the corresponding target opens. All overlaps can be refined by affine opens; I never assume their intersections are affine. The displayed transition argument is written out, rather than asserting a hidden comparison lemma. def-weil-compactifications-refinements then recognizes the factorization. No density condition is secretly added to this definition.

5. The coefficient calculation directly proves injectivity of multiplication by t for every ring R. def-pc-divisor-line-bundle defines the needed Cartier notion by a nonzerodivisor equation, so this is an elementary step rather than a new node repeating the item's Cartier clause. The quotient ring is R and the two maps composing to the identity identify D with B. sbc-lem-affine-space-smooth for n=0, def-sbc-affine-space, and the smooth isomorphism transport lemma give relative dimension zero. This concerns D over B, not smoothness over k.

6. lem-pur-affine-line-support-geometry explicitly includes that its base Y is Noetherian when Y is finite type over a field. Take Y=B and the already supplied field k. This is a legitimate use of its statement, not an inference from the fact that the affine line is Noetherian. lem-weil-pbc-finite-type-over-noetherian then applies to pi with its finite-type property from step 2 and gives Noetherianity of E, including quasi-compactness.

7. lem-weil-pbc-affine-open-stalk-localization gives both stalk descriptions. pqf-lem-affine-open-locnoeth and lem-weil-pbc-localization-noetherian make the local ring A Noetherian. I wrote out the fraction argument proving t remains a nonzerodivisor and the evaluation-kernel calculation A/(t)=O_D,x, so no uncited localization-exactness theorem is being used. The point lies in D, hence t belongs to its maximal ideal. All hypotheses of lem-weil-pbc-dimension-quotient-nonzerodivisor are satisfied. This proves the local Krull-dimension formula, including at nonclosed points and for nonreduced or reducible bases; global scheme dimension is not substituted for stalk dimension.

8. lem-weil-pbc-noetherian-open-subscheme-noetherian applies twice, to an affine open V in E and then to V minus D. It gives quasi-compactness of the inverse image of every affine open target. def-weil-finite-type-morphism defines exactly this quasi-compact-morphism condition. This short elementary application needs no new node and does not assume that all affine opens lie inside one chosen frame.

9. def-pc-base-change specifies the section being pulled back. lem-weil-pbc-fibre-product-affine-spectra gives the actual tensor product, with its two structural maps; I give inverse ring maps to R'[t], not an unsupported claim that constructions commute. lem-weil-pbc-closed-immersion-base-change identifies the scheme-theoretic pulled-back closed subscheme. Evaluation has ideal (t), and the coefficient injectivity proof needs neither flatness nor Noetherianity. def-pc-divisor-line-bundle applies on these affine charts. The transition units remain units under a ring homomorphism. These cover arbitrary B', even if B' has no finiteness property.

All non-elementary inputs above are cited nodes. Definitions are used for their actual defining data; none is cited as a surrogate for a permanence theorem. Off-unit generic tools are declared in split_report.tool_uses for maintainer review: relative Spec affineness, affine-space smoothness, the standard projective chart, and finite-type-base Noetherianity. Other tools are existing Mathlib leaves or same-unit nodes. No new unsplit node restates a clause, and no new statement requires a separate small-case audit.

I tested the argument on B empty (all local and point assertions are vacuous and the glued spaces are empty), a field, a nonreduced finite-type ring such as k[epsilon]/(epsilon^2), and reducible finite-type rings. At a zero-section point the coordinate is always in the prime, which is essential to step 7. For arbitrary base change I checked quotients, nonflat maps, and a non-Noetherian target ring: the polynomial coefficient proof still works. A nontrivial line module over B is handled by the units u, so the compactification is not incorrectly replaced by B times P1.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the files: no new nodes, sources and tags explicit, statement unchanged, exact citation coverage, no proof-of-a-node dependency, no hidden finiteness or flatness hypotheses, explicit transition and fraction arguments, no cohomological shortcut. All nine steps are shorter than 2000 characters, and each is a single chart calculation or application of the cited statement. No forbidden source, repository write, compiler invocation or agent delegation occurred. The server review_split check passed before the report was written; the final dry run and push follow.

## Not duplicates

No new nodes. Existing ingredients were reused, including projective-bundle geometry, affine-line support geometry, dimension drop, affine symmetric algebras, and the standard Proj chart. No new/existing Stacks-tag pairs arise.

## Unfinished work

None in the authorized one-level stage-1 split. The existing cited nodes keep their own statuses and proofs; this delivery does not claim to close them in Lean.
