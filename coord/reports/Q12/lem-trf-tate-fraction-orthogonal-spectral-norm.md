# Stage-1 delivery: lem-trf-tate-fraction-orthogonal-spectral-norm

## Files written

- dag/nodes/sec-trace-formula/lem-trf-tate-fraction-orthogonal-spectral-norm.json: item, split with its statement unchanged, five assembly steps.
- dag/nodes/sec-trace-formula/def-trf-stable-nonarchimedean-field.json: new definition, unsplit; no Mathlib definition found.
- dag/nodes/sec-trace-formula/lem-trf-tate-gauss-fraction-stability.json: new statement only, unsplit; no Mathlib match for BGR's Stability Theorem.
- dag/nodes/sec-trace-formula/lem-trf-incomplete-spectral-algebra-norm.json: new Mathlib leaf, spectralAlgNorm and isNonarchimedean_spectralNorm, including the coefficient formula and normalization at 1.
- citations.json: a verbatim statement quotation for each node used in each proof step.
- searches.jsonl: actual wrapper searches. All services answered successfully. The definition and stability theorem each have two semantic phrasings, Loogle and grep; the leaf's semantic candidates were checked directly in the pinned source.

## Attachments

None. Project source searches for the exact blueprint id, orthogonal bases, spectralNorm, stable valued fields, Gauss and Tate notions found no declaration stating this item. General category-theoretic orthogonality and unrelated Tate modules are not matches. No Lean was written or compiled.

## Literature wanted

WANTED: Bosch–Guentzer–Remmert, Non-Archimedean Analysis, Sections 3.6.1, 5.1.2, 5.3.2 and 6.4.1, for this item and the two BGR nodes. The intended archival path literature/bosch-guentzer-remmert-nonarchimedean-analysis.pdf is absent. I read the primary Arizona scan online (query suffix read=1), rendering its pages within this sandbox: PDF p.164 = printed p.156; PDF p.199 = printed p.193; PDF p.219 = printed p.213; PDF pp.257-258 = printed pp.251-252. The scan has no text layer. These are verified places, not inferred section numbers.

WANTED: Bosch, Lectures on Formal and Rigid Geometry, Section 1.4 Lemma 12, printed pp.25-27, for the existing fibre-polynomial comparison used in the assembly. I read the primary Muenster PDF's text online. No source was added to the shared repository.

## Findings and scope

The seeded item is true as stated; no STATEMENT-DISPUTED correction was needed. Its separate claims must concern the same norm, so the proof defines N by the minimal polynomial first and identifies its restriction to C afterwards. F is generally incomplete, so the existing complete-base spectral-norm node alone is insufficient. The original imported search verdict does not distinguish general spectral algebra norm inequalities from normedField; the new leaf records the former without adding a completeness hypothesis.

The current blueprint latest (main-20261024, ef6f9619) ancestor lem-trf-local-term-locality has a contracting-correspondence proof. This node belongs to the already recorded historical analytic auxiliary branch and does not replace any current unit step. The unit and chapter records were read and left untouched. The item is not the unit's key node. There is no released repair note and no earlier sandbox proof/report/search log to preserve.

## Not duplicates

- lem-trf-incomplete-spectral-algebra-norm vs lem-trf-spectral-norm-algebraic-extension: the existing node requires a complete base and concludes multiplicativity; the new leaf works over an arbitrary possibly incomplete valued base and concludes submultiplicativity. The existing theorem cannot be applied to Frac(T).
- lem-trf-incomplete-spectral-algebra-norm vs lem-weil-l-adic-extension-absolute-value: that node treats absolute values on finite extensions of Q_l, not a spectral algebra norm over arbitrary incomplete fields.
- def-trf-stable-nonarchimedean-field vs lem-trf-finite-ultrametric-almost-orthogonal-basis: the latter gives r-almost orthogonal bases for arbitrary finite normed spaces over a complete field; the definition concerns exact orthogonality of spectral norms on every finite field extension, without completeness.
- lem-trf-tate-gauss-fraction-stability vs lem-trf-tate-fraction-orthogonal-spectral-norm: the new node is the independent generic stability theorem, with a stable complete ground field and no affinoid extension C. It has no affinoid restriction or finite-module claim; the item still needs the localization argument and the fibre-polynomial comparison. It is not a relabelled clause for the particular L.
- lem-trf-tate-gauss-fraction-stability vs lem-trf-tate-torsionfree-fibre-polynomial: the latter identifies integral polynomials and their maximal-fibre root values; it asserts no stability or orthogonal bases.
- lem-trf-tate-gauss-fraction-stability vs lem-trf-restricted-series-gauss-completion: completeness and submultiplicativity of a Tate algebra do not assert stability of its fraction field.

Whole-DAG statement/title/source searches included stable fields, cartesian normed fields, orthogonal bases, spectral norms, 3.6.1, 5.3.2 and Mathlib spectralAlgNorm. Blueprint searches (all chapters) for spectral norm, orthogonal basis, cartesian field, stable field, stable valued, Gauss and stability found no blueprint statement of the two new notions/results. Existing affinoid spectral equations and minimal-polynomial fibre results were read and reused instead of creating an affinoid norm-comparison node. No Stacks tag is assigned to a non-Stacks analytic result.

## Review by Q12

I checked BGR 6.4.1/3 in the scan: the domain case passes to Q(A)/Q(T_d), invokes 5.3.2/1, obtains a cartesian vector space for the spectral norm and restricts it to the affinoid supremum. I separately read Definition 3.6.1/1 and the following paragraph: stability means every finite extension with spectral norm is cartesian; algebraically closed fields are stable. I read 5.1.2/1 (Gauss norm is a valuation) and 5.3.2/1 (fraction field stable if ground field stable). These support the new definition and the independent statement-only theorem, with e=0 retained. The two properties in the theorem use the same Gauss valuation, not an unspecified extension norm.

For the Mathlib leaf I read SpectralNorm.lean lines 90-125, 369-435 and 565-690. spectralNorm is the spectralValue of minpoly; the finite coefficient formula is the reindexing j=r-i of spectralValueTerms. spectralAlgNorm at 663-671 has only NormedField, IsUltrametricDist and Algebra.IsAlgebraic, and gives precisely definiteness, negation, scalar homogeneity and the ordinary/submultiplicative inequalities. isNonarchimedean_spectralNorm at 645 supplies the stronger triangle inequality and spectralNorm_one at 577 supplies normalization. CompleteSpace occurs later, so no complete-base theorem is being applied implicitly.

Step 1 quotes the existing finite-algebra-is-integral statement, which supplies a monic equation for each nonzero denominator. I wrote the constant-term nonvanishing and inverse formula, so the finite generating list spans the actual fraction field L, not an auxiliary tensor product that has not been identified. The coefficient t_r is nonzero in T because T maps injectively to the domain C. This establishes finite degree directly and needs no separability or normality.

Step 2 uses the new stability definition and theorem, whose complete-ground-field and stable-ground-field hypotheses are both verified. Stability of algebraically closed K is checked with the one-element basis and linear minimal polynomial, rather than hidden in an additional lemma. The theorem also justifies the fraction absolute value assumed in the item.

Step 3 quotes exactly the incomplete-base spectral-algebra-norm result for norm properties and the stability definition for the orthogonal basis. The finite extension proved in step 1 is the extension used here. No multiplicativity of N is claimed and no completion of L or F is substituted.

Step 4 uses the existing fibre-polynomial statement's monic kernel generator; its finite, injective, affinoid and torsion-free hypotheses hold because C is a domain and T embeds. The proof explicitly clears all polynomial denominators to show that this polynomial remains the generator over F, hence is the very minimal polynomial that defines N. This identification is not taken from the existing node's proof.

Step 5 uses exactly the existing fibre-polynomial node's finite nonempty fibre equality, and the supremum-calculus node's finite residue fields and Tate equality rho_T=G. Every maximal ideal of C contracts to a maximal ideal: its finite-dimensional residue field contains the image of T, a K-subspace and domain, hence a finite-dimensional K-field. Thus all maximal ideals occur in the fibre suprema. Commuting the finite maximum and continuous positive roots with suprema gives the displayed restriction. Zero coefficients and c=0 give zero and need no division by a spectral value. Both existing statements were reread in full, and the same fibre equality appears in Bosch Lemma 12(ii), with the suprema consequence in (iii).

Small cases checked: e=0 forces F=K and L=K, with basis 1; C=T gives N=G; c=0 has polynomial Z and zero norm. In characteristic p, the map K<U> into K<X> given by U=X^p has finite purely inseparable fraction extension and basis 1,X,...,X^(p-1), with the maximum Gauss equality, so no separability is required. Stability is exact orthogonality and is not inferred from the existing almost-orthogonal-basis theorem. All new nodes introduce their fields and valuations and either cite their notions or define them inline. The only new theorem left for later splitting is the independent BGR stability theorem; the definition and Mathlib leaf contain no hidden proof. Every assembly step is under 2000 characters (491, 328, 367, 427, 751), and every non-elementary input has a cited statement with a verbatim entry in citations.json. No source error, circular norm-lifting argument, new SGA route, or unsolved item clause was found.

## Unfinished work

No assembly clause remains. The new stability theorem is deliberately statement-only for the next stage-1 item, as required. The server dry run and direct push follow this report.

## Validation

The first server preflight required an explicit numeric mathlib_match.line; the previously supplied source-line detail was in how. Added line=663 after rereading the declaration. The final dry run exited 0 with `OK (not pushed)` at ddde2cee34b, including the required server preflight. No mathematics or statements changed for this repair.
