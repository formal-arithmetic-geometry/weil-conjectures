## Worker report

Files written, all in the Q54 item sandbox:
- `dag/nodes/sec-deligne-laumon-a1/lem-per-laurent-subalgebra-dimension-bound.json`: item, statement unchanged, split in six steps.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-nilradical-minimal-prime-intersection.json`: statement, Mathlib leaf `Ideal.sInf_minimalPrimes`, `Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean:116`, specialized to the zero ideal.
- `citations.json`: a verbatim statement quotation for every cited node in every step.

Attachments: none. Searching `lean/WeilConjectures/` for the blueprint tag, Laurent subalgebra dimension, and Krull-dimension/subalgebra combinations found no declaration stating the item. Laurent points and deformation spaces are different statements. No Lean was written or compiled.

WANTED: none. All sources are present locally.

The item initially had an empty proof, and the sandbox contained no prior node or report. No released repair note exists. The statement is true without reducedness, catenarity, locality or domain assumptions and was retained verbatim. Its source gives a consequence of Stacks 0BAG rather than an explicit Laurent-subalgebra theorem. This split supplies the consequence; it does not assume that arbitrary subalgebra inclusions preserve dimension inequalities.

Nothing remains unfinished at the level of this split. The one new node is an exact Mathlib leaf. Existing non-leaf tools remain with their own items. The chapter and unit were read; this is not the key statement of the unit, so their realization fields were not edited.

## New nodes

`lem-per-nilradical-minimal-prime-intersection` is general radical/minimal-prime algebra, independent of dimension or Laurent polynomials. It has a statement only, empty proof and empty proof dependencies. It introduces its ring, minimal primes, nilpotent condition and empty-intersection convention inline. Stacks `algebra.tex`, Tag 00E0, `lemma-Zariski-topology` parts (4) and (7), implies it: every prime contains a minimal prime, and the radical is the intersection of primes. I read these assertions and their proofs, then `Ideal.sInf_minimalPrimes` at `MinimalPrime/Basic.lean:116`, with lines 104–126. The zero-ideal specialization is exact, with no Noetherian or nonzero hypothesis.

Searches for prospective rational-function transcendence and algebraic-adjoin nodes found the existing `lem-sfb-algebraic-adjoin-transcendence-bound`; I reused it and created neither proposed node. The explicit polynomial Q(t)Z-P(t) proves algebraicity for each rational function. Fraction embeddings, coefficient reduction and the finite-prime-product argument are elementary steps, not separate nodes.

Every actual Mathlib query is in `searches.jsonl`; the new leaf records the minimal-prime queries exactly. LeanFinder and LeanSearch returned `Ideal.sInf_minimalPrimes`; grep locates line 116. The Loogle query returned related radical-invariance statements, not the exact intersection theorem. Existing Q50 item searches were retained, and current Q54 Laurent-dimension and generic-transcendence searches added. Polynomial dimension hits do not prove a dimension inequality for a subalgebra. Whole-DAG and blueprint searches preceded node creation, including tags, minimal primes, nilradical, Laurent, rational function and transcendence degree.

## Review by Q54

I read the latest blueprint's `lem-per-artin-gabber-affine-curve.md` and `.proof.md`, the Fourier-exactness unit and chapter records, and the parent `lem-per-associated-graded-local-dimension` including its Rees argument. The ancestor chain assigns this algebra tool to the ILO III Corollary 5.4(i) normal-cone comparison used in III Proposition 6.2. I read Stacks `morphisms.tex` Tag 0BAG (`lemma-alteration-dimension-general`, line 13814 onward) and Tag 0BAE (`lemma-dimension-formula-general`, line 13610 onward). Their actual hypotheses are a locally Noetherian base and local finite type, and their generic terms are residue-field transcendence degrees at component generic points. Neither upper bound assumes universal catenarity. I also read Tag 00E0 parts (4),(7) for the new leaf, and `fields.tex` Tag 030F (`lemma-transcendence-degree`), especially the generating-set argument. The existing algebra-adjoin generalization is `Algebra.IsAlgebraic.trdeg_le_cardinalMk` at `TranscendenceBasis.lean:469`, whose statement and proof I read.

Step 1 cites the finite-minimal-primes statement for the finite family, the new intersection statement to exclude an empty family in a nonzero ring, the prime-residue-field algebra statement for fraction fields, and the rational-function definition. I opened each statement; it gives precisely that input. Coefficient reduction preserves finite sums and convolution products. Multiplication by a power of t detects Laurent coefficients in an ordinary polynomial. The kernel is prime because the target is a field, and testing constants proves contraction to R. Only R/p_i, not R, is treated as a domain.

Step 2 uses the new intersection formula. It does not assume a uniform nilpotence exponent for the entire kernel ideal: the finitely many coefficients of a fixed Laurent polynomial give the explicit exponent M=1+sum(e_j-1). The written product-of-elements argument proves that any prime containing the intersection contains one K_i. Its minimality then gives q=K_i. I do not claim the unnecessary converse that every K_i must be minimal. This argument handles nilpotent coefficients and multiple components.

Step 3 uses elementary fraction arithmetic. The embedding is written as a/b mapped to rho(a)/rho(b); cross multiplication proves well-definedness and injectivity, and nonzero denominators stay nonzero. Constants identify Frac(R/p_i) inside both Frac(B/q) and F_i(t) compatibly. No fibre ring is substituted for a residue fraction field.

Step 4 uses the rational-function definition to write P/Q and the existing algebraic-adjoin cardinal bound for the only non-elementary estimate. The target F_i(t) is a nonzero field, its base subalgebra is F_i[t], and every P/Q satisfies the nonzero polynomial Q(t)Z-P(t), whose linear coefficient is nonzero. The generating set is the singleton {t}. The bound passes to E by the explicit polynomial-relation argument and the algebraic-independence definition. These statements were opened and their actual hypotheses checked; the argument works over finite fields and in positive characteristic.

Step 5 uses the lft pointwise criterion with the single affine pair Spec B, Spec R, and the locally-Noetherian definition with the singleton affine cover of Spec R. The component/minimal-prime statement and the point-closure formula identify the generic points. The spectrum field-point statement gives their residue fraction fields. The Spec-map residue-field naturality statement identifies their field maps with the compatible fraction maps of step 3. I read every cited statement, not its proof as a substitute for its assertion. No identification is inferred solely from the definition of residue fields or the fully faithful spectrum functor.

Step 6 uses the ring Krull-dimension definition, which explicitly states equality with topological dimension of Spec, and the existing general Tag 0BAG node with n=1. Step 5 verified every-component generic transcendence bound, local finite type and local Noetherianity. The integers d and 1 are nonnegative. It follows that dim B <= d+1. The generic Tag 0BAG node is in another unit; `split_report.tool_uses` declares it solely as general dimension theory, not replacement of a Fourier/perverse unit step. No top-level maintainer tool-use approval was written.

Small cases checked: B=R (constant fraction fields); B=R[t,t^{-1}] over a field (sharp upper bound); R=k[epsilon]/(epsilon^2) (finite-coefficient nilpotence); R=k x k (two coefficient kernels, with B allowed to have several components); d=0 over finite or positive-characteristic residue fields. For the new leaf, a field has intersection zero, the dual numbers have intersection (epsilon), a product of fields has intersection zero, and the zero ring has empty prime family and whole zero ring on both sides. The zero-ring check is for the leaf only; the item's nonzero hypothesis is preserved.

I checked delivery-errors B–E against the files and sources. The new statement has no proof sketch, defines every object inline, uses single TeX escapes, and names exact declaration/file/line evidence. It is the general minimal-prime intersection theorem, not a dimension clause of the item. All non-elementary inputs are cited nodes, and `citations.json` quotes their statements verbatim. No step takes a construction from the proof of a node. All steps are under 1100 characters, so there is no long-step hidden-lemma issue. Fraction compatibility, coefficient nilpotence and prime selection are explicit. No statement dispute or source correction was needed. I corrected the prospective-node plan by finding and reusing the existing algebraic-adjoin leaf; only one new leaf remains.

## Not duplicates

lem-per-nilradical-minimal-prime-intersection vs lem-wf-smooth-components-disjoint: The existing statement concerns irreducible components of a smooth variety do not meet, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-a1-finite-locally-free-principal-basis-cover: The existing statement concerns principal fixed-rank bases for a finite locally free affine algebra, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-a1-quasi-affine-open-principal-comparison-cover: The existing statement concerns common principal-open comparison cover for an open in a quasi-affine scheme, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-domain-generic-local-fibre-bound: The existing statement concerns generic dimension bounds every local field-fibre dimension of a finite type domain, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-projective-local-flat-family-injectivity: The existing statement concerns projective modules detected by flat local families with injective residue maps, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-completed-maximal-localizations-detect-zero: The existing statement concerns completed maximal localizations are complete local flat tests for zero derived objects, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-normalization-completed-product-comparison: The existing statement concerns recover normalization by intersection with normalized completed branches, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-normalization-completed-branch-lift: The existing statement concerns a closed normalization point lifts to a completed branch, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-locally-principal-supported-kernel: The existing statement concerns locally principal inverse-image complements and supported module kernels, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-smooth-fibre-affine-ring-at-prime: The existing statement concerns a smooth fibre neighbourhood gives smoothness of its affine fibre ring at the kernel prime, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-two-semilocal-rings-intersection-cover: The existing statement concerns two independent semilocal rings give an affine intersection cover, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-reduced-finite-type-field-product-embedding: The existing statement concerns embedding a reduced finite-type algebra into finitely many extension fields, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-fixed-tensor-kernel-stalk-criterion: The existing statement concerns kernel and injectivity of a fixed tensor test at contracted primes, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-two-term-normalization-locality-equivariance: The existing statement concerns localization and equivariance of kernel-normalized determinant maps, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-affine-etale-cover-component-criterion: The existing statement concerns affine split-etale-cover criterion in terms of strictly henselian components, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-normalization-principal-height-one-refinement: The existing statement concerns a prime over a principal ideal in a local normalization contains a height-one prime over it, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-inseparable-prime-localization-identification: The existing statement concerns prime localization after finite purely inseparable scalar extension, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-coprime-generators-mprimary-or-unit: The existing statement concerns coprime generators in a regular local surface are unit or maximal-primary, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-flat-local-component-dimension-difference: The existing statement concerns dimension difference on minimal components of a flat local map, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-reduced-affine-injective-factor-stalk-comparison: The existing statement concerns generic points and selected stalks in a reduced affine injective factorization, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-minimal-primes-dense-spectrum: The existing statement concerns minimal primes are dense in the spectrum, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-etale-ideal-local-factor: The existing statement concerns an etale-local ideal divides an ideal extended from the base, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-reduced-algebra-generic-completion-cover: The existing statement concerns generic localization and completion cover for the reduced projectivity induction, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-codimension-one-neighbourhood-etale-extension: The existing statement concerns finite etale model from boundary source neighbourhoods and codimension-two extension, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-stack-finite-type-smooth-closed-chart: The existing statement concerns closed points in smooth charts representing finite-type stack points, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-reduced-polynomial-module-generic-freeness: The existing statement concerns generic freeness of finite polynomial modules over a reduced ring, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-koszul-closed-immersion-affine-criterion: The existing statement concerns affine and principal neighbourhood criterion for a koszul-regular closed immersion, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-subdirect-product-reductivity: The existing statement concerns reductivity of a smooth connected subdirect product, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-group-local-minimal-prime: The existing statement concerns local irreducibility and the neutral irreducible component of a group scheme, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-lci-local-fitting-smoothing: The existing statement concerns local complete-intersection deformations with a fitting-ideal bound, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-syntomic-smooth-composition: The existing statement concerns syntomic composition and smooth inputs, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-graded-coordinate-polynomial-degree-emptiness: The existing statement concerns degree bound and empty proj criterion for an eventual coordinate polynomial, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-field-extension-immersion-koszul-points: The existing statement concerns pointwise koszul regularity of an immersion after extension of the ground field, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-separated-lqf-affine-finite-set: The existing statement concerns finite sets have affine neighbourhoods over an affine locally quasi-finite target, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-birational-generic-localization: The existing statement concerns generic localization isomorphism for a birational affine ring map, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-fibre-assassin-containment-base-change: The existing statement concerns fibre-assassin containment in an open is invariant under arbitrary base change, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-idempotent-annihilator-generic-retraction: The existing statement concerns continuous retraction onto minimal primes for a reduced ring with idempotent annihilators, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-smooth-pair-closed-fibre-local-preparation: The existing statement concerns closed-fibre specialization and local algebra preparation for a smooth pair, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-polynomial-zero-section-dimension: The existing statement concerns topological dimension at the zero section of a polynomial algebra, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-principalized-maximal-ideal-height-one-prime: The existing statement concerns a height-one prime above a principalized local maximal ideal, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-separable-point-closure-universal-density: The existing statement concerns universal density and geometric reducedness of a separable-point closure, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-bounded-pseudocoherent-stalkwise-perfect: The existing statement concerns bounded-below pseudo-coherent complexes are perfect if all prime localizations are perfect, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-koszul-ideal-faithfully-flat-descent: The existing statement concerns faithfully flat descent of locally koszul-regular ideals, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-faithfully-flat-group-quotient-universal: The existing statement concerns universal property of a faithfully flat affine group quotient, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-space-finite-type-point-characterization: The existing statement concerns finite type points of spaces have locally finite type field representatives, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-groupoid-strict-local-reduced-orbit: The existing statement concerns reduced closed orbits for a stabilizer-preserving etale groupoid map, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-finite-type-noetherian-spectrum: The existing statement concerns finite type algebras preserve noetherian spectra, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-dense-rational-closed-subscheme-descent: The existing statement concerns a reduced closed subscheme with dense rational points descends, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-dense-fixed-local-ideal-jets: The existing statement concerns dense-subgroup fixed ideals and rational finite jets, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-finite-fixed-endomorphism-sheaf: The existing statement concerns common fixed endomorphisms commute with principal localization and affine sheaves, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-nilpotent-tower-monomorphism-rigidity: The existing statement concerns a finite-type monomorphism containing an entire nilpotent tower is an isomorphism, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-integral-element-prime-local-criterion: The existing statement concerns integrality of an algebra element is detected at every base prime, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-t1-finite-hausdorff-affine-cover: The existing statement concerns finite compact hausdorff affine charts for quasi-compact schemes with closed points, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-syntomic-presentation-conormal-fibre-rank: The existing statement concerns finite projective syntomic conormal and its fibre dimension rank, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-supported-complex-ext-completion: The existing statement concerns supported pseudo-coherent ext is unchanged by completing coefficients, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-scheme-algebraic-residue-closed-point: The existing statement concerns algebraic residue extensions over closed base points give closed scheme points, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-finite-maximal-support-localization: The existing statement concerns localization decomposition of a finite module with finite maximal support, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-qcqs-functions-local-comparison: The existing statement concerns localization, stalks and the local coefficient criterion for qcqs regular functions, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-wlocal-directed-limit-topology: The existing statement concerns topology of directed limits of w-local affine spectra, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-etale-dvr-principal-neighbourhood: The existing statement concerns a special-fibre point of an etale dvr algebra has a principal dvr neighbourhood, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-space-generic-line-section-injectivity: The existing statement concerns generic geometric germs detect line-module sections on integral spaces, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-principal-affine-test-universally-open: The existing statement concerns principal-open affine tests suffice for universal openness, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-elementary-contraction-evaluation: The existing statement concerns evaluation under one rational-component contraction, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-affine-free-split-torus-invariants: The existing statement concerns affine quotient of a free split-torus action is the spectrum of invariants, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-fibre-product-spectrum-topology: The existing statement concerns topological spectrum of a ring fibre product along a surjection, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-singleton-stack-flat-lfp-field-cover: The existing statement concerns flat finitely presented field cover of a singleton stack, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-punctured-local-spectrum-closed-points: The existing statement concerns closed points of the punctured spectrum of a noetherian local ring meet its locally closed subsets, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-affine-principal-relative-pseudocoherence-gluing: The existing statement concerns polynomial-chart pseudo-coherence glues on a principal affine cover, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-boundary-affine-local-domain-model: The existing statement concerns affine local domain model of a missing image point, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-equation-count-closed-fibre-localization: The existing statement concerns expected closed-fibre equation count permits localization preserving reduction, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-dense-generic-trait-selection: The existing statement concerns trait selection meeting a prescribed generic open with finite fraction field, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-polynomial-power-lifting-universal-homeomorphism: The existing statement concerns polynomial power lifting for an inclusion gives a universal homeomorphism, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-relative-flat-tensor-charts-sheaf-exact: The existing statement concerns relative-flat tensor chart criterion for sheaf short exactness, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-polynomial-adequacy-nil-base-change: The existing statement concerns polynomial tests for universal power lifting with nil kernel, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sfb-ample-existence-field-extension: The existing statement concerns existence of an ample invertible module descends along field extensions, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sc-affine-totalquotient-minimal-product: The existing statement concerns total quotient ring as a product over minimal primes, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sc-affine-weakass-nonzerodivisors: The existing statement concerns weakly associated primes detect the zero divisors of a ring, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-tame-inertia-surjective-group-trace: The existing statement concerns tame inertia implies a surjective group trace, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-finite-function-subring-residue-test: The existing statement concerns proper ideals in finite function subrings admit residue evaluation tests, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-principal-parameter-conductor-bound: The existing statement concerns a principal parameter has bounded obstruction near its zero fibre, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-g-ring-alteration-closed-fibre-neighbourhood: The existing statement concerns alteration neighbourhoods regular over a j-2 quotient of a g-ring, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-universal-catenarity-minimal-quotients: The existing statement concerns universal catenarity checked on minimal-prime quotients, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-admissible-quotient-affine-integral-charts: The existing statement concerns invariant affine charts of an admissible finite-group scheme quotient, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-a1-smooth-curve-cotangent-generic-isomorphism: The existing statement concerns rank-one cotangent sheaves and generic invertibility on smooth integral curves, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-j2-closed-fibre-regular-locus: The existing statement concerns openness of the ambient regular locus along a j-2 closed fibre, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-one-dimensional-component-conormal: The existing statement concerns conormal torsion for a one-dimensional completed component, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-noetherian-local-domain-open-infinite: The existing statement concerns nonempty opens in a high-dimensional noetherian local domain are infinite, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-adic-noetherian-normalization-finite: The existing statement concerns a noetherian normalization is finite over a complete pair with nagata closed fibre, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-cyclotomic-finite-etale-cover: The existing statement concerns the primitive-root cover after inverting its order, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-qe-formal-regularity-locality: The existing statement concerns regularity and regular morphisms on quasi-excellent formal charts, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-birational-generic-localization: The existing statement concerns generic localization isomorphism for a birational affine map, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-geometric-affinoid-jacobian-unit: The existing statement concerns the continuous jacobian ideal of a geometrically regular affinoid quotient is the unit ideal, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-semilocal-jacobson-completion-product: The existing statement concerns jacobson-radical completion of a noetherian semilocal ring, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-henselian-component-dimension: The existing statement concerns one-dimensional components and strict henselization, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-jacobian-torsion-closed-base-change: The existing statement concerns closed base change preserves completed jacobian torsion, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-completion-component-dimension: The existing statement concerns one-dimensional components and completion, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-formal-completion-reduction-dictionary: The existing statement concerns infinitesimal quotients on arbitrary affine charts of a formal completion, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-per-field-extension-generic-reducedness: The existing statement concerns generic reducedness is invariant under characteristic-zero field extension, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-product-ideal-closed-subscheme-union: The existing statement concerns the closed subscheme cut out by a product of two ideal sheaves has the union as underlying set, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-integral-closure-finite-fibre-choose-g: The existing statement concerns a lift of the fibre idempotent gives the localization isomorphism, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-reduced-induced-closed-subscheme: The existing statement concerns reduced induced closed subscheme structure on a closed subset: existence and uniqueness, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-proj-standard-open-inclusion: The existing statement concerns standard opens of proj: basis, intersections, inclusions and coverings, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-finite-type-domain-dimension-local-ring: The existing statement concerns a finite type domain over a field has the dimension of each of its local rings at maximal ideals, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-zero-locus-eq-iff-radical-eq: The existing node intersects all primes containing an ideal and compares zero loci; it does not state the minimal-prime intersection formula. The new exact Mathlib leaf supplies the missing minimal-prime reduction.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-finite-projective-standard-free-cover: The existing statement concerns a direct summand of a finite free module is finite locally free (standard cover), whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-zero-locus-ideal-intersection: The existing statement concerns the zero locus of an intersection of two ideals is the union of the zero loci, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact: The existing statement concerns principal opens cover spec r iff unit ideal; spec r is quasi-compact, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-finite-type-field-finite-isolated-points: The existing statement concerns a finite type algebra over a field has finitely many isolated spectrum points, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-dimension-zero-local-strictly-henselian: The existing statement concerns a local ring with a single prime ideal and separably closed residue field is strictly henselian, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-span-pow-eq-top: The existing statement concerns powers of generators of the unit ideal generate the unit ideal, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-polynomial-quotient-dimension-lower-bound: The existing statement concerns dimension lower bound for a polynomial quotient over a field, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-proper-ideal-contained-in-maximal: The existing statement concerns every proper ideal is contained in a maximal ideal, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-popescu-smoothing: The existing statement concerns popescu's theorem: regular maps of noetherian rings are filtered colimits of smooth algebras, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-coherent-support-power-ideal-kills: The existing statement concerns a coherent module supported in the zero set of an ideal is killed by a power of it, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-etale-localize-upstairs: The existing statement concerns etale near a closed subset gives an etale principal localization, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-separate-image-closed-from-closed: The existing statement concerns separating v(i) from the closure of the image of v(j) by one element, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-closed-point-dimension-local-ring: The existing statement concerns dimension at a closed point of a finite type algebra over a field is the dimension of the local ring, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-spec-localization-away-basic-open: The existing statement concerns basic opens form a basis of spec a, and spec a_f is homeomorphic to the open d(f), whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-prime-contains-minimal-prime: The existing statement concerns a prime containing an ideal contains a minimal prime over that ideal, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs def-weil-pbc-singular-ideal: The existing statement concerns smoothness at a prime and the singular ideal h_{a/r}, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-minimal-prime-over-proper-ideal: The existing statement concerns a proper ideal has a minimal prime over it, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-local-dimension-zero-henselian: The existing statement concerns local rings of dimension zero are henselian, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-formal-systems-proper-support-serre: The existing statement concerns coherent formal modules with support proper over the base form serre subcategories, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-spec-zero-loci-disjoint-unit-ideal: The existing statement concerns v(a) and v(b) are disjoint iff a + b is the unit ideal, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-reduced-source-factors-through-closed-subscheme: The existing statement concerns a map from a reduced scheme factors through a closed subscheme exactly set-theoretically, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum: The existing statement concerns a finite algebra over a local ring with a single prime has finitely many primes, all maximal and over the maximal ideal, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-scheme-theoretic-union: The existing statement concerns scheme-theoretic union of two closed subschemes, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-exc-closed-cover-extension: The existing statement concerns lifting a covering of a closed fibre, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-pur-parameter-chart-germ-criterion: The existing statement concerns parameter tuples characterize germs of flat quasi-finite affine-space charts, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-generic-separable-algebra-splitting: The existing statement concerns generic finite algebra splits after a finite separable field extension, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-exc-j0-finite-type-domain-descent: The existing statement concerns a nonempty regular open descends along a dominant finite type map of domains, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-pur-coordinate-chart-finite-dimension-witness: The existing statement concerns a finite local-dimension witness in a nonempty coordinate chart, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-fin-generic-curve-model: The existing statement concerns a generic curve model with finite comparison boundary, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-exc-local-curve-principal-total-fractions: The existing statement concerns a parameter in a reduced local curve localizes to the total fraction ring, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-sc-reduced-ideals-zero-intersection: The existing statement concerns ideals covering the spectrum of a reduced ring have zero intersection, whereas the new leaf identifies the intersection of minimal prime ideals with nilpotent elements in an arbitrary ring.

lem-per-nilradical-minimal-prime-intersection vs lem-weil-pbc-noetherian-finitely-many-minimal-primes: the existing node gives finiteness, not the intersection formula; the new leaf has no Noetherian hypothesis.

lem-per-nilradical-minimal-prime-intersection vs lem-trf-reduced-finite-type-field-product-embedding: the existing node embeds reduced finite-type field algebras into products of fields, while the new leaf is an arbitrary-ring ideal identity and allows nilpotent rings.

## Dry-run repairs

The first server preflight found two metadata omissions: the new leaf had no notion citation and its Mathlib match lacked the structured integer line field. I added a citation to the existing radical/zero-locus node for its explicit radical notation, with the equivalent formula sqrt(0), and set mathlib_match.line to 116, already verified in the pinned source. The new leaf does not use the all-primes formula as a substitute for its own minimal-prime conclusion. Updated the verbatim quotations in citations.json. No mathematical statement or proof route changed.
