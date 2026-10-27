# Stage-1 report: lem-trf-sharp-monoid-vertex-cotangent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-sharp-monoid-vertex-cotangent.json: existing statement, now split into six explicit calculation steps; no match for the whole item in Mathlib.
- citations.json: a verbatim statement quote for every dependency in every proof step.
- searches.jsonl: searches run through the required msearch.py command; the original item's searches were retained as inherited records.
- report.md: this report. write_split.py is sandbox scratch work only.

No new nodes, no new Mathlib leaves. No repository, launcher, Lean source, compiler or build was written or invoked.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for sharp monoids, atoms, indecomposables, monoid vertices and cotangent-localization terminology. No declaration gives the whole item. The sorry-free Mathlib theorems finite_addIrreducible and AddSubmonoid.closure_addIrreducible give only the atom clause, and are not project attachments.

## WANTED

None. The ILO PDF and Stacks algebra.tex used here are present.

## What was wrong or missing

The live item was unsplit with no proof. Its statement is correct and was retained verbatim. Its existing blueprint ancestry identifies a historical nearby-duality/alteration branch. I read the current latest chapter, unit, and lem-trf-local-term-locality statement/proof: the current local-term proof uses contracting correspondences, not this historical toric-resolution branch. This delivery retains the recorded supporting lemma and ancestry, does not claim that the latest blueprint contains a toric cotangent lemma, and changes no chapter or unit route.

The source's assertion that the indecomposables generate needs an argument; step 1 supplies the minimal finite generating-set proof without assuming saturation. The source computes the vertex without torus factors. Steps 2--4 provide the Laurent-coordinate augmentation, spanning calculation, and independent coefficient functionals for the product with a torus. Step 5 supplies the actual inverse to the localization map rather than referring to an unstated cotangent-localization theorem. The localization definition is reused for fractions and their equality relation, not cited as a theorem proving that inverse.

## Unfinished work

None for this split. All proof steps are elementary calculations written out from the cited definitions; no auxiliary statement is left for later. The item itself is not claimed Lean-proved.

## Searches and existing-node comparison

The msearch.py log contains LeanFinder, LeanSearch, Loogle and source grep, including a second semantic phrasing. The whole-item searches return presentation cotangent-space bases, ideal cotangent definitions, and localization of H1 cotangent homology. I read Mathlib/RingTheory/Extension/Cotangent/Basic.lean:442--444 and RingTheory/Etale/Kaehler.lean:281 and :385: these describe different modules, not this maximal-ideal quotient basis. The second atom phrasing found finite_addIrreducible and AddSubmonoid.closure_addIrreducible. I read Algebra/AffineMonoid/Irreducible.lean, especially :58 and :71 and their to_additive attributes: they prove precisely the atom clause with cancellativity, finite generation and trivial units. They do not prove the whole item. Because the minimal-generator argument is a short direct calculation, it stays inline and is not repackaged as a new clause node.

Searched the whole DAG and blueprint with blueprint_refs.py search for cotangent, atoms and monoid, and searched node statements and Lean sources for the same notions and declaration names. Read lem-trf-sharp-monoid-ideal-minimal-generators, lem-trf-fine-monoid-unit-generators, lem-trf-positive-monoid-convolution-length, lem-trf-monoidal-local-regularity-criterion, and lem-trf-toric-vertex-dimension-freeness. The ideal-minimal-generator node proves finite monoid-ideal generation; the unit node concerns the unit subgroup; the convolution node assumes a positive weight; the regularity criterion has extra local-ring and saturation hypotheses; the dimension/freeness node assumes this item's cotangent formula. None is an exact attachment or a needed black-box input to the direct computations. No dependency cycle is introduced.

## Not duplicates

No new nodes are created. The atom, augmentation, spanning, independence and localization clauses remain arguments of the item, not duplicate children.

## Review by Q66

I read ILO, Expose VIII, proof of Lemma 3.2.12(ii), printed pp.104--105 (PDF pp.110--111): the source writes the monomial ideal as a direct sum, its square as the direct sum indexed by decomposable exponents, and identifies the quotient with atom monomials. I also read Stacks algebra.tex, the fraction relation and operations immediately before Tag 00CO, label definition-localization, and verified the tag in tags/tags. The minimal-generating-set and Laurent/localization additions are marked agent-written rather than attributed verbatim to ILO. There are no new-node sources to check.

Step 1 cites def-trf-fine-fan-blowup for finite generation, the embedding into the group completion, and sharpness. Its statement actually contains those definitions. Cancellation comes from that embedding. If a putative decomposition of a minimal generator uses that generator, cancellation gives a zero sum and sharpness contradicts a nonzero summand; otherwise the generator is redundant. Conversely an atom has exactly one summand in its generator expression. This proves generation and finiteness without a well-foundedness assumption or saturation.

Step 2 cites that same definition for sharpness and def-trf-monoscheme-toric-realization for the ring of finite formal monomial sums and its multiplication. I read both statements, not their proofs. Sharpness prevents nonzero exponents from multiplying to exponent zero, so the displayed augmentation is multiplicative. The written geometric-series and negative-power identities prove its kernel is exactly the displayed ideal; the constant section proves the residue quotient is k and the ideal maximal.

Step 3 cites only the formal-sum/multiplication definition. Products of two nonzero monomial exponents vanish modulo the square; negative powers of 1+z have linear term -z, so the integer exponent expansion works in arbitrary characteristic. In a kernel element, the sum of the q=0 coefficients is zero. The explicit formula therefore proves spanning, including the torus coordinates, without importing a tensor-product conormal theorem.

Step 4 cites sharpness and formal-sum multiplication. I checked the exact two convolution identities: for the atom coefficient only 0+a and a+0 occur; for the torus derivative the q=0 term requires both exponents zero, and Laurent exponents add. Thus both functionals kill every product in the kernel and all of its square. Their Kronecker values give independence. They use no square-zero-extension construction or hidden universal-property theorem.

Step 5 cites def-weil-pbc-localization-at-prime for the fraction description and equality criterion. The quote in citations.json includes that criterion verbatim. The step supplies its own well-definedness calculation with u(s'x-sx')=0, its own square-ideal vanishing and both inverse identities. Every denominator has nonzero image in k because it lies outside ker epsilon. Multiplication on the global cotangent quotient is by its residue, as proved by (b-epsilon(b))x lying in the square. The statement dependency now explicitly records this localization notion as well. No flatness or exactness theorem is silently used.

Step 6 uses the preceding calculated basis and isomorphism and counts its finite index set. Empty generating sets, empty Laurent families and the zero-dimensional quotient need no separate lemma. Small cases checked: R=0 with t=0 gives k and zero cotangent spaces; R=0 with positive t gives the torus identity basis; R=N and t=0 gives the usual one monomial class; R=N^2 gives two classes; R generated by 2 and 3 inside N has two atoms and two cotangent directions, showing saturation was not slipped into the proof. In characteristic p, a p-th Laurent power has zero linear term as the integer-coefficient formula predicts, while each y_j-1 is still detected with coefficient 1. Nonsharp monoids would make the augmentation fail, which explains exactly where sharpness is necessary. Torsion-freeness is allowed but not needed by these calculations; no stronger hypothesis was added.

Against delivery-errors B--E: statements and existing metadata are retained; all decoded TeX was checked; no source tag is used for meaning; every citation was checked against its statement and quoted; no non-elementary fact is hidden behind a definition citation; no clause was moved to a child; no off-unit theorem or forbidden SGA source is used. Each step is below 2000 characters and contains its actual finite-sum or fraction argument. The only newly named objects in the proof are explicit formulas, not hollow definitions or unproved comparison lemmas. I checked the supplied uses union and every quote before the required server checks.
