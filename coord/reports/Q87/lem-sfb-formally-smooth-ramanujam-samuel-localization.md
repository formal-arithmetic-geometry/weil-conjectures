# Q87 stage-1 report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-formally-smooth-ramanujam-samuel-localization.json`: item, split; unchanged statement and statement dependencies.
- `lem-sfb-formally-smooth-normal-power-series-cover`: new statement, unsplit, no Mathlib match.
- `lem-sfb-complete-normal-horizontal-primes-principal`: new statement, unsplit, no Mathlib match.
- `lem-sfb-reflexive-ideal-principal-flat-descent`: new statement, unsplit, no Mathlib match.
- `lem-sfb-principal-divisor-punctured-local-criterion`: new statement, unsplit, no Mathlib match.

All node files are under `dag/nodes/sec-six-functors-basics/`. Also wrote citations.json and retained searches.jsonl. Four new nodes; zero Mathlib leaves.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the exact blueprint tag and for Ramanujam, Samuel, parafactoriality, horizontal primes, reflexive modules and the formal-smooth power-series construction. No declaration states this item or one of the new nodes. Ordinary local-ring Picard triviality is not punctured-spectrum Picard triviality.

## Literature wanted

WANTED: EGA IV, fourth part (1967), Theorem 21.14.1 and Corollary 21.14.2, for lem-sfb-formally-smooth-ramanujam-samuel-localization and the power-series cover and horizontal-prime inputs.
WANTED: EGA IV4, 21.13.8, Corollary 21.13.15 and Remark 21.13.16, for lem-sfb-principal-divisor-punctured-local-criterion.
WANTED: Bourbaki, Algebre commutative, VII §3 no.7 Lemma 3 and no.8 Propositions 5–6; VII §1 no.10 Proposition 15 and no.4 Proposition 5, for the horizontal-prime and flat-descent inputs.

The local literature directory contains IV1–IV3, not IV4. I read the English EGA translation at https://jcreinhold.github.io/ega/iv/34-ch4-21-divisors.html (21.13.8, 21.13.15–16, all of the proof of 21.14.1, and 21.14.2). The node proof is marked agent-written because its document is not locally present and the valuation assembly is explicit work by Q87. No SGA source is used.

## Problems found and corrections

No statement dispute. In particular the finite residue extension and normality of the completion are retained; no excellence or separability assumption has been inserted. The inherited null blueprint ancestor was confirmed by `blueprint_refs.py ancestor`; its via chain and exact inherited EGA location are retained, and every new node adds its lower source location.

The source proves 21.14.2 through 21.14.1 and the (a) ⇒ (b) direction of 21.13.15. The existing `lem-sfb-parafactorial-principal-cycle-extension` gives only (b) ⇒ (a), so citing it for this step would be C4 and circular through the sibling's parent route. I instead state the missing converse criterion. The existing `lem-per-flat-base-change-reflexive-modules` is reused as source material for generic descent rather than duplicated. The source's substantial power-series reduction and horizontal-prime theorem are separate lower inputs; neither states the item's punctured-spectrum conclusion.

## Unfinished work

None in this one-level split. The four new statements remain unsplit as required; they are the next stage-1 items. No Lean was written or compiled.

## Review by Q87

I read the project contract, stage-1 brief, three route levels, GOAL.md, the item's chapter and unit, and both copies of delivery-errors B–E in full. I compared the item to the EGA theorem and corollary just listed. The inherited route is the use of Ramanujam–Samuel in EGA 21.14.3(i), below the recorded affine-boundary argument; no unit or chapter route is changed.

For step 1 I opened the complete statements of the new cover, the existing faithfully flat normality descent (033G), and ideal contraction (05CK). The cover supplies exactly a local faithfully flat map into a normal Noetherian power-series domain and the required contraction of the extended coefficient maximal ideal. Normality descends by 033G, and injectivity by 05CK gives a domain, rather than silently identifying normal rings with domains. The assumption that p is prime, finite residue degree, dimension inequality, and normal completion all appear in the cover statement.

For step 2 I opened `lem-per-divisorial-fractional-module-lattices`. Its statement really gives finite reflexivity, the height-one lattice formula, and the intersection of height-one localizations. These identify its one-prime effective ideal with r: contraction from B_r is r since denominators are outside the prime. Thus the descent input applies to a reflexive ideal, not to an arbitrary codimension-two ideal. The chosen c in r minus p stays outside nD by the cover's contraction equality; every prime containing rD therefore fails containment in nD. The horizontal-prime node supplies actual principality for those primes, with complete normal coefficient domain and arbitrary residue characteristic; the generic descent node then supplies principality back in B. This checks both directions of all subset conditions. The source for the cover is the first paragraph of 21.14.1; the source for horizontal primes is its coordinate-change and Weierstrass paragraphs. The new generic descent statement abstracts its divisorial-ideal and local descent paragraph, and I read Stacks more-algebra.tex, 0EB9 and the 0AVB intersection formulation as recorded in the existing lattice node. Flat base change of arbitrary ideals is not claimed reflexive.

For step 3 I opened the entire statement of `lem-trf-normal-domain-principal-divisor-kernel`, which explicitly gives finite valuation support and the divisor homomorphism. This is what the product computation needs; a definition of the class group alone would not suffice. Each principal height-one ideal (h) gives exactly one at its own DVR and zero at all other height-one primes. Consequently the finite product with integer exponents produces the prescribed divisor, including negative coefficients. This establishes the precise hypothesis of the new converse criterion. For step 4 I read that criterion against 21.13.15(a) ⇒ (b), S={p}, and 21.13.8. A point q is a generization of p precisely when q is contained in p, so the exceptional locus has the correct direction. A globally principal divisor is in particular locally principal, so our stronger global hypothesis implies EGA's (a). Parafactoriality in local dimension at least two gives both the restriction isomorphism and trivial invertible modules on the punctured spectrum, not merely the latter. Verbatim complete statements for every step citation are in citations.json.

Small cases checked: with A a field and B=k[[x,y]], p=(0) and every requested prime of height at least two has the expected punctured Picard triviality. For d=0 in the horizontal-prime input no prime avoids n, so it is vacuous; no false positive-dimensional requirement was added. A nonfactorial complete normal coefficient ring is permitted: its nonprincipal vertical primes lie inside nD and are excluded, so the new input does not assert that D is factorial. For descent, I=R is allowed with no supporting prime, and the reflexivity restriction is essential: a height-two maximal ideal in a two-dimensional regular local ring has no containing height-one primes but need not be principal, so an arbitrary-ideal version would be false. The criterion deliberately requires local dimension at least two: the puncture of a DVR is its fraction field and its section restriction is not an isomorphism. The finite-product argument works for the zero divisor, the empty support, and negative coefficients.

I searched the whole DAG by source place, tags, and notions, and the whole imported blueprint with `blueprint_refs.py` using parafactorial, Ramanujam, power series, faithfully flat, height one, divisor, principal, reflexive, Weierstrass, Cartier and local algebra. I also searched the newest blueprint tree; it contains no Ramanujam–Samuel or parafactorial node. Existing power-series normality does not prove horizontal prime principality, and existing formal-smooth lifts do not assert the specified normal cover. Semantic, Loogle, and source searches are actual msearch.py invocations logged in searches.jsonl. I read their hits: Weierstrass preparation exists in Mathlib but is a lower input to the new prime theorem; the power-series UFD instance assumes a PID coefficient ring; local Picard triviality concerns Spec of the local ring, not its puncture. No new node is a Mathlib specialization. All new statements introduce their objects and define local/reflexive/height-one where needed, cite definition nodes, contain no proof or proof dependencies, and have filled blueprint fields. Every item step is shorter than 2000 characters.

## Not duplicates

lem-sfb-principal-divisor-punctured-local-criterion vs lem-sfb-parafactorial-principal-cycle-extension: the new node gives the converse implication, from divisor principality to punctured local parafactoriality; the existing node assumes punctured Picard triviality and proves divisor extension.
lem-sfb-complete-normal-horizontal-primes-principal vs lem-weil-pbc-power-series-normal-domain: the existing result proves normality of a power-series ring; it gives no principality of horizontal primes.
lem-sfb-formally-smooth-normal-power-series-cover vs lem-sfb-complete-local-smooth-power-series: the existing result assumes a complete local k-algebra setting with prescribed identical residue field; the new cover handles arbitrary characteristic, finite residue extensions and an analytically normal coefficient local ring, and supplies faithful flatness plus the exact contraction p.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-sbc-finite-unramified-principal-quotient: the existing statement (Formal unramifiedness of a finite local model from its principal quotient) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-trf-lift-regular-generators-through-fibre: the existing statement (Lifting generators regular in the target along a generator-space isomorphism) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-trf-fibrewise-zero-kahler-differentials: the existing statement (Vanishing of relative differentials detected on ordinary algebra fibres) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-trf-completion-prefix-kernel-comparison: the existing statement (Completed prefix multiplication kernels and reflection of regular sequences) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-trf-local-finite-module-tensor-nonzero: the existing statement (Nonzero tensor product of finite modules over a local ring) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-sc-regular-dim1-dvr: the existing statement (One-dimensional regular local rings) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-pc-hilb-representable: the existing statement (Hilbert schemes of points are representable) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-sfb-jacobson-marked-free-complex-lift: the existing statement (Lifting a prescribed finite-free derived model modulo a Jacobson ideal) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-sfb-perfect-nilpotent-reduction: the existing statement (Perfectness is reflected by a nilpotent derived reduction) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-sfb-relative-regular-ideal-generation: the existing statement (Relative generation and polynomial multiplication from fibre regularity) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-sc-finite-module-surjective-mod-ideal: the existing statement (Surjectivity detected modulo a Jacobson ideal) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-sc-finite-constant-length-flat: the existing statement (Finite morphisms with constant fibre length are flat) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-per-flat-base-change-reflexive-modules: the existing node gives finite reflexivity after flat tensor product; the new node assumes all supporting height-one primes principal and proves principality and its local descent.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-per-reflexive-height-one-intersection-criterion: the existing statement (Reflexivity and intersection of height-one localizations over a normal domain) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-per-divisorial-fractional-module-lattices: the existing node constructs valuation lattices and their localization; the new node descends principality under a local faithfully flat map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-gabber-upstairs-tensor-coefficients: the existing statement (Gabber upstairs relation with tensor coefficients) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-formal-systems-surjective: the existing statement (Surjectivity of a coherent formal-system map is detected modulo the ideal) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-localized-ideal-conormal-generator-bound: the existing statement (Finite ideal generator bound from localized conormal generators) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-zariski-pair-finite-gabber-polynomial: the existing statement (An element lifting (1,0) in a finite algebra is a root of a monic polynomial reducing to (x-1)x^d) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-popescu-clear-conormal-chart: the existing statement (Clear the polynomial relations on one prescribed conormal chart) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-criterion-flatness-fibre-noetherian: the existing statement (Critere de platitude par fibres, Noetherian case) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-finite-type-lift-nilpotent: the existing statement (Finite type lifts along a nilpotent ideal (ring version)) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-lci-conormal-generators-global-complete-intersection: the existing statement (Conormal module generated by the codimension number of elements gives a global complete intersection nearby) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-nakayama-jacobson: the existing statement (Nakayama's lemma for an ideal in the Jacobson radical) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-zariski-pair-finite-gabber-polynomial-upstairs-relation: the existing statement (Gabber relation in a quotient after faithfully flat base change) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-thickening-lft-cartesian: the existing statement (Locally of finite type lifts along finite order thickenings (cartesian case)) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-nakayama-one-plus-ideal-annihilator: the existing statement (Nakayama: a finite module with IM=M is killed by an element of 1+I) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-coherent-formal-modules-affine: the existing statement (Coherent formal modules on an affine Noetherian scheme are finite modules over the completion) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-popescu-lift-once: the existing statement (Factoring a finitely presented algebra through B/J, B smooth, J in IB (square-zero base)) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-nakayama-nilpotent: the existing statement (Nakayama's lemma for a nilpotent ideal (surjectivity modulo I)) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-local-artinian-basis-when-flat: the existing statement (Bases of flat modules over a local ring with nilpotent maximal ideal) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-nakayama-local-generators: the existing statement (Nakayama: generators of a finite module over a local ring are detected modulo the maximal ideal) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-semilocal-fibre-generators: the existing statement (Finite module generators bounded by fibre dimensions) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-completion-maximal-ideal-generators: the existing statement (The maximal ideals of a Noetherian local ring and of its completion need equally many generators) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-weil-pbc-conormal-span-clearing: the existing statement (Clear a finite ideal from localized conormal spanning) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-pur-local-generating-tuples: the existing statement (Elementary changes between generating tuples over a local ring) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.

lem-sfb-reflexive-ideal-principal-flat-descent vs lem-pod-dvr-complex-amplitude-mod-uniformizer: the existing statement (Cohomological amplitude of a complex over a DVR is detected modulo the uniformizer) does not assert that a reflexive ideal with principal supporting primes becomes principal and descends under a faithfully flat local map.
