# Repair report: integral general-lfp internal Hom inversion

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-general-lfp-hom-inversion.json`: existing item; statement preserved byte-for-byte; three-step assembly, 1634 characters.
- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-general-lfp-sequential-continuity.json`: new statement-only obligation, status unsplit, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-scalar-hom-telescope-evaluation.json`: new statement-only obligation, status unsplit, no Mathlib match.
- `citations.json`: a verbatim statement excerpt for each step-node citation. Searches and their full answers remain in searches.jsonl and search-*.txt.

## Attachments

None. I searched WeilConjectures by the item tag, general-lfp, scalar telescope, and internal-Hom continuity. The matching project theorem in Sheaf/Paper/IntegralGeneralLfpHomInversion.lean ends in sorry, so it cannot close the item.

## WANTED

None; the cited PDFs and Stacks source files are present.

## Return repaired

This is the human-directed re-split of the 4823-character seven-step proof. The sandbox was empty at the start, so I copied the current repository item, which contains that reviewed split and the NX Lean metadata. There was no retained sandbox report or search log to reuse. I changed no statement or Lean metadata and ran no git command in the read clone. The two new statements receive comparable, separate parts of the original work: old steps 1–4 (2297 characters) and old steps 5–7 (2526 characters). The parent now checks hypotheses and applies these two statements. Their proof and proof_deps are empty; the original full argument is retained below as the next workers' brief, rather than compressed or discarded.

The first obligation handles the coefficient-specific passage from arbitrary local presentation matrices to finite constant scalar models, topology, internal continuity, and the scalar-equivariant lower representative. It does not assert a change-of-coefficients theorem. The second is a formal result on any small ringed site; continuity is a hypothesis rather than the coefficient-specific conclusion proved by the first. It handles the formal localization comparison and every representative/leg/evaluation compatibility, rather than re-proving the coefficient-specific bridge. Neither is the original statement, and neither alone proves the item.

The explicit return requests these work units despite the usual instruction to inline short specializations: they deliberately expose two independent proof-development tasks. Existing general results remain their inputs in the full argument below; no input is silently re-proved or replaced by a new axiom.

## Unfinished

No repair point remains intentionally unfinished. The two new nodes are unsplit as explicitly requested. No Lean was written or compiled.

## Review by NZ

I read the current chapter and unit records, the final inverting-ell paragraph of the main-20261015 blueprint proof, Bhatt–Scholze pp. 61–62 (Lemma 6.8.12, Proposition 6.8.14(2) and Remark 6.8.15), and the corresponding statements of all twelve former proof dependencies. Bhatt–Scholze's continuity lemma concerns global Hom and direct sums: I have not presented it as an internal-sheaf continuity theorem. Both extracted nodes retain the agent-extraction attribution. For the first new node I also read Hemo–Richarz–Scholbach Theorems 4.13 and 6.2(2)–(3), and Stacks properties.tex label lemma-Noetherian-topology (01OZ) and homology.tex section-truncations (0118). The HRS heart theorem alone is not the arbitrary-entry lfp-to-constant assertion: that content remains the existing coefficient-specific comparison obligation. For the second new node I read derived.tex lemma-K-injective (070I) and the existing reflection, complex-colimit, K-injective telescope, scalar-adjunction and conditional-localization statements; the auxiliary sheafification/tensor/localization tags are the sources recorded in those statements, not substitute black boxes.

Parent step 1 cites the new continuity statement. I checked every hypothesis: ell is prime, E is finite, X is locally Noetherian and quasi-compact, K has precisely general ring-object bounded constructible cohomology, and L only has a cohomological lower bound. The cited statement explicitly supplies exact filtered colimits, finite local models, the internal sequential continuity map, and a scalar-equivariant representative. In the transferred argument, the minimal-closed-subset node supplies the topological DCC, the lfp comparison supplies (i) implies (ii) allowing arbitrary matrices and torsion models, and the continuity node supplies the evaluation-induced internal map, not only global Hom. The pro-etale site definition fixes the small module universe, and the Grothendieck-abelian node explicitly says filtered colimits are exact. Only finitely many cohomology sheaves occur; their stratifications need not coincide. The quotient lower truncation is quasi-isomorphic because the cohomology below c already vanishes; multiplication by ell descends through its cokernel. These are old steps 1–4, all retained below.

Parent step 2 uses the coefficient node's displayed E_X = O_{E,X}[1/ell] together with its actual repeated-ell description. The formal new statement is applied with scalar ring O_E, sheaf ring B, and t=ell; there is no confusion between a scalar ring and its non-discrete pulled-back ring sheaf. Continuity and exactness are supplied by step 1. The new statement defines chi by the same evaluation transpose, and rho by the normalized restricted scalar adjunction; its statement asserts both isomorphisms and two-variable naturality. This is the original step 5 with its formal-comparison input transferred to the second obligation.

Parent step 3 uses exactly the beta legs, gamma square and final evaluation identity printed in the second new statement. I checked their domains: beta_H lands in UF H_R(K,L), beta_L in UFL, and H_R(K,beta_L) takes the target of gamma to H_R(K,UFL). The gamma leg has Q(j_n) composed after e_L inverse, so it starts at L. The evaluation equality has domain H_R(K,L) tensor K and codomain UFL. Its scalar leg is t^{-n} times eta, matching the stated pairing. The transferred argument uses reflection for exact termwise scalar extension and unit normalization; complex-colimit for every nth leg; K-injective scalar-telescope for the non-R-linear functorial resolution transition, preserving the zeroth leg as well; and the scalar-adjunction statement for the evaluation transpose. None of those identifications is taken from a dependency's proof. These are old steps 6–7, retained in full below.

I checked B–E: new nodes contain statements only and introduce their objects; the statement dependencies name definitions used; TeX is singly escaped; sources distinguish the agent extraction from literal literature results; all recorded searches actually ran through msearch.py and their full output was read. Both semantic phrasings were tried for each node. LeanSearch was rate-limited and is recorded as unavailable, while LeanFinder, Loogle and grep succeeded. The related hits concern finitely presented rings, underived presheaf colimits, condensed-module AB5, or ordinary injective resolutions, and do not state these assertions. A second, more precise grep returned no hits for either statement. Blueprint searches for internal Hom, continuity, telescope, and scalar localization found no identical imported statement; ancestor returns None, so the existing null ancestor is preserved and the full created-node via chain is given. No SGA source is used. All three parent steps are under 2000 characters, and the total is below 3000. The item is not weakened and its proof is not moved into one child. The original argument's coverage is explicitly one-to-one below.

Small-case checks: X empty, K=0 and L=0 give zero comparisons; K=B reduces to scalar localization itself. Integral ell-power-torsion K is allowed; after inversion both relevant Hom localizations vanish by the same scalar action. L may have unbounded terms despite bounded-below cohomology; the quotient truncation gives the required common lower bound without adding a hypothesis. For the formal node, t a unit makes each telescope a constant diagram up to canonical isomorphism and the equations reduce to naturality of evaluation. For t=0 or nilpotent, localization and scalar telescopes are zero, so the asserted derived equations still hold. Arbitrary unbounded C_H is permitted because the complex-colimit statement imposes no bound; I did not apply sequential continuity directly to an unbounded-below C_L. It is first replaced by its lower truncation, and exact filtered colimits carry the quasi-isomorphic scalar towers to the same derived object. No completed coefficient category, finite dimension, ell-invertibility on X, perfectness, or completeness was added.

## Not duplicates

lem-sfb-integral-general-lfp-sequential-continuity vs prop-weil-pbc-integral-tstructure: the existing node states The standard t-structure on the integral category; the new node instead gives internal sheaf-Hom continuity for arbitrary-entry general-lfp integral constructible K, together with its applicability to scalar-equivariant bounded-below representatives. Truncation alone does not supply that continuity.

lem-sfb-integral-general-lfp-sequential-continuity vs prop-weil-pbc-levelwise-truncations: the existing node states Levelwise truncations of the adic tower; the new node instead gives internal sheaf-Hom continuity for arbitrary-entry general-lfp integral constructible K, together with its applicability to scalar-equivariant bounded-below representatives. Truncation alone does not supply that continuity.

lem-sfb-integral-general-lfp-sequential-continuity vs thm-weil-pbc-integral-truncations: the existing node states Truncations of the integral category; the new node instead gives internal sheaf-Hom continuity for arbitrary-entry general-lfp integral constructible K, together with its applicability to scalar-equivariant bounded-below representatives. Truncation alone does not supply that continuity.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-weil-pbc-alternating-unit-resolution: the existing node states Alternating unit resolution of an exact periodic pair; the new node instead gives internal sheaf-Hom continuity for arbitrary-entry general-lfp integral constructible K, together with its applicability to scalar-equivariant bounded-below representatives. Truncation alone does not supply that continuity.

lem-sfb-integral-general-lfp-sequential-continuity vs def-weil-t-structure: the existing node states t-structure; the new node instead gives internal sheaf-Hom continuity for arbitrary-entry general-lfp integral constructible K, together with its applicability to scalar-equivariant bounded-below representatives. Truncation alone does not supply that continuity.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-weil-pbc-regular-quotient-self-cohomology: the existing node states Self-reduction along a regular quotient; the new node instead gives internal sheaf-Hom continuity for arbitrary-entry general-lfp integral constructible K, together with its applicability to scalar-equivariant bounded-below representatives. Truncation alone does not supply that continuity.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-weil-pbc-periodic-quotient-tor: the existing node states Tor from an exact periodic unit pair; the new node instead gives internal sheaf-Hom continuity for arbitrary-entry general-lfp integral constructible K, together with its applicability to scalar-equivariant bounded-below representatives. Truncation alone does not supply that continuity.

lem-sfb-integral-general-lfp-sequential-continuity vs prop-weil-localized-tstructure: the existing node states The rational t-structure; the new node instead gives internal sheaf-Hom continuity for arbitrary-entry general-lfp integral constructible K, together with its applicability to scalar-equivariant bounded-below representatives. Truncation alone does not supply that continuity.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-weil-pbc-principal-adjacent-quotient-tor: the existing node states Residue Tor between adjacent principal quotients; the new node instead gives internal sheaf-Hom continuity for arbitrary-entry general-lfp integral constructible K, together with its applicability to scalar-equivariant bounded-below representatives. Truncation alone does not supply that continuity.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-pc-right-exact-truncge-iso: the existing node states Right exact additive functors commute with canonical lower truncation; the new node instead gives internal sheaf-Hom continuity for arbitrary-entry general-lfp integral constructible K, together with its applicability to scalar-equivariant bounded-below representatives. Truncation alone does not supply that continuity.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-pc-derived-lower-truncation-step-ses: the existing node states Successive lower truncations have a two-term kernel quasi-isomorphic to one cohomology object; the new node instead gives internal sheaf-Hom continuity for arbitrary-entry general-lfp integral constructible K, together with its applicability to scalar-equivariant bounded-below representatives. Truncation alone does not supply that continuity.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-pc-lower-truncation-transition-kernel: the existing node states Kernel geometry and homology of a fixed successive lower truncation transition; the new node instead gives internal sheaf-Hom continuity for arbitrary-entry general-lfp integral constructible K, together with its applicability to scalar-equivariant bounded-below representatives. Truncation alone does not supply that continuity.

lem-sfb-scalar-hom-telescope-evaluation vs lem-sc-module-localization-filtered-colimit: the existing node states Module localization is the filtered colimit over powers; the new node instead compares derived internal Hom, its functorial-resolution and literal scalar telescopes, the two beta identifications and gamma square, and evaluation on every stage under a continuity hypothesis. Ordinary localization alone does not state this.

lem-sfb-scalar-hom-telescope-evaluation vs lem-sc-bounded-free-stalk-model-spread: the existing node states Spreading a given bounded free stalk model; the new node instead compares derived internal Hom, its functorial-resolution and literal scalar telescopes, the two beta identifications and gamma square, and evaluation on every stage under a continuity hypothesis. Ordinary localization alone does not state this.

lem-sfb-scalar-hom-telescope-evaluation vs lem-weil-pbc-scalar-localization-complex-colimit: the existing node states Ordinary scalar-sequence colimit of complexes; the new node instead compares derived internal Hom, its functorial-resolution and literal scalar telescopes, the two beta identifications and gamma square, and evaluation on every stage under a continuity hypothesis. Ordinary localization alone does not state this.

lem-sfb-scalar-hom-telescope-evaluation vs def-weil-pbc-module-localization-away: the existing node states Localization of a module at one element, and the canonical maps M_f -> M_{fg}; the new node instead compares derived internal Hom, its functorial-resolution and literal scalar telescopes, the two beta identifications and gamma square, and evaluation on every stage under a continuity hypothesis. Ordinary localization alone does not state this.

lem-sfb-scalar-hom-telescope-evaluation vs lem-weil-pbc-localization-of-localization: the existing node states A localization of a localization is a localization; the new node instead compares derived internal Hom, its functorial-resolution and literal scalar telescopes, the two beta identifications and gamma square, and evaluation on every stage under a continuity hypothesis. Ordinary localization alone does not state this.

lem-sfb-scalar-hom-telescope-evaluation vs lem-weil-pbc-scalar-localization-module-colimit: the existing node states Scalar localization as an ordinary module-sheaf colimit; the new node instead compares derived internal Hom, its functorial-resolution and literal scalar telescopes, the two beta identifications and gamma square, and evaluation on every stage under a continuity hypothesis. Ordinary localization alone does not state this.

lem-sfb-scalar-hom-telescope-evaluation vs lem-weil-pbc-scalar-localization-regular-colimit: the existing node states The regular module localization colimit; the new node instead compares derived internal Hom, its functorial-resolution and literal scalar telescopes, the two beta identifications and gamma square, and evaluation on every stage under a continuity hypothesis. Ordinary localization alone does not state this.

lem-sfb-scalar-hom-telescope-evaluation vs def-weil-pbc-module-localization: the existing node states Localization of a module at a multiplicative subset; the new node instead compares derived internal Hom, its functorial-resolution and literal scalar telescopes, the two beta identifications and gamma square, and evaluation on every stage under a continuity hypothesis. Ordinary localization alone does not state this.

lem-sfb-scalar-hom-telescope-evaluation vs lem-weil-pbc-generic-fibre-localization-domain-irreducible: the existing node states The generic fibre of a domain over a domain is an irreducible spectrum; the new node instead compares derived internal Hom, its functorial-resolution and literal scalar telescopes, the two beta identifications and gamma square, and evaluation on every stage under a continuity hypothesis. Ordinary localization alone does not state this.

lem-sfb-scalar-hom-telescope-evaluation vs def-weil-pbc-scalar-localization-coefficient-actions: the existing node states Canonical coefficient actions on scalar-localized derived module sheaves; the new node instead compares derived internal Hom, its functorial-resolution and literal scalar telescopes, the two beta identifications and gamma square, and evaluation on every stage under a continuity hypothesis. Ordinary localization alone does not state this.

lem-sfb-scalar-hom-telescope-evaluation vs def-weil-ring-localization-away: the existing node states Localization of a ring at one element; the new node instead compares derived internal Hom, its functorial-resolution and literal scalar telescopes, the two beta identifications and gamma square, and evaluation on every stage under a continuity hypothesis. Ordinary localization alone does not state this.

lem-sfb-scalar-hom-telescope-evaluation vs lem-sc-local-domain-dim-one-principal-localization-fraction-field: the existing node states A principal localization of a one-dimensional local domain is its fraction field; the new node instead compares derived internal Hom, its functorial-resolution and literal scalar telescopes, the two beta identifications and gamma square, and evaluation on every stage under a continuity hypothesis. Ordinary localization alone does not state this.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-sfb-constructible-internal-hom-continuity: the existing statement assumes finite constant local models and topologically Noetherian X; the new statement starts with arbitrary-entry general-lfp cohomology and locally Noetherian quasi-compact X, and supplies the scalar-equivariant lower representative as well. It isolates the original coefficient-specific preparation for the formal localization input.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-weil-pbc-integral-lfp-hom-continuity: the existing statement concerns additive shifted global Hom from a single locally finitely presented degree-zero module; the new statement concerns derived internal sheaf Hom from a bounded stratified complex, plus the lower representative.

lem-sfb-scalar-hom-telescope-evaluation vs lem-sfb-internal-hom-localization-comparison: the existing statement provides invertibility and an abstract restricted continuity identification; it does not state beta_H, beta_L and gamma for every representative, every nth leg, or their evaluation equation. The extracted obligation retains this existing formal comparison as an input, then handles the remaining strict scalar telescope normalization.

lem-sfb-scalar-hom-telescope-evaluation vs lem-sfb-kinjective-hom-scalar-telescope: the existing statement compares the two transitions by homotopy and the two colimits by a leg-preserving derived isomorphism; it supplies neither the scalar-extension beta square nor the evaluation-normalized comparison on L.

lem-sfb-scalar-hom-telescope-evaluation vs lem-pod-condensed-localization-hom: the existing statement is a global Hom localization theorem for two stratified dualizable inputs; the new one is an internal-sheaf theorem with an arbitrary bounded-below second input and explicit representative and evaluation equations.

lem-sfb-integral-general-lfp-sequential-continuity vs def-sp-extended-smart-truncation-tower: the existing statement concerns Extended upper smart truncation tower (an upper cutoff, mapped/totalized truncation, or comparison between two cutoffs). It states no general-lfp-to-constant-model bridge and no sequential internal sheaf-Hom continuity for K. The new node bundles that coefficient-specific continuity preparation with a lower scalar-equivariant representative; it does not assert a CE, decalage or cutoff-tower comparison.

lem-sfb-integral-general-lfp-sequential-continuity vs def-sp-map-good-upper-truncation: the existing statement concerns Left exact functors commute with good upper truncation (an upper cutoff, mapped/totalized truncation, or comparison between two cutoffs). It states no general-lfp-to-constant-model bridge and no sequential internal sheaf-Hom continuity for K. The new node bundles that coefficient-specific continuity preparation with a lower scalar-equivariant representative; it does not assert a CE, decalage or cutoff-tower comparison.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-sp-ce-good-cut-identification: the existing statement concerns Good-cut total represents canonical truncation compatibly with decalage (an upper cutoff, mapped/totalized truncation, or comparison between two cutoffs). It states no general-lfp-to-constant-model bridge and no sequential internal sheaf-Hom continuity for K. The new node bundles that coefficient-specific continuity preparation with a lower scalar-equivariant representative; it does not assert a CE, decalage or cutoff-tower comparison.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-sp-ce-smart-truncation-spectral-object: the existing statement concerns Resolved CE smart cuts compute the derived truncation spectral object (an upper cutoff, mapped/totalized truncation, or comparison between two cutoffs). It states no general-lfp-to-constant-model bridge and no sequential internal sheaf-Hom continuity for K. The new node bundles that coefficient-specific continuity preparation with a lower scalar-equivariant representative; it does not assert a CE, decalage or cutoff-tower comparison.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-sp-derived-upper-truncation-comparison: the existing statement concerns Cochain upper truncations compared coherently with derived truncations (an upper cutoff, mapped/totalized truncation, or comparison between two cutoffs). It states no general-lfp-to-constant-model bridge and no sequential internal sheaf-Hom continuity for K. The new node bundles that coefficient-specific continuity preparation with a lower scalar-equivariant representative; it does not assert a CE, decalage or cutoff-tower comparison.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-sp-double-complex-truncation-decalage: the existing statement concerns Horizontal smart truncation total equals a decalage step (an upper cutoff, mapped/totalized truncation, or comparison between two cutoffs). It states no general-lfp-to-constant-model bridge and no sequential internal sheaf-Hom continuity for K. The new node bundles that coefficient-specific continuity preparation with a lower scalar-equivariant representative; it does not assert a CE, decalage or cutoff-tower comparison.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-sp-extended-smart-truncation-map-iso: the existing statement concerns Left exactness commutes with the extended smart truncation tower (an upper cutoff, mapped/totalized truncation, or comparison between two cutoffs). It states no general-lfp-to-constant-model bridge and no sequential internal sheaf-Hom continuity for K. The new node bundles that coefficient-specific continuity preparation with a lower scalar-equivariant representative; it does not assert a CE, decalage or cutoff-tower comparison.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-sp-mapped-smart-truncation-tower: the existing statement concerns Map the smart cuts before totalizing (an upper cutoff, mapped/totalized truncation, or comparison between two cutoffs). It states no general-lfp-to-constant-model bridge and no sequential internal sheaf-Hom continuity for K. The new node bundles that coefficient-specific continuity preparation with a lower scalar-equivariant representative; it does not assert a CE, decalage or cutoff-tower comparison.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-sp-smart-truncation-decalage-tower: the existing statement concerns Total smart truncations identify naturally with the decalage tower (an upper cutoff, mapped/totalized truncation, or comparison between two cutoffs). It states no general-lfp-to-constant-model bridge and no sequential internal sheaf-Hom continuity for K. The new node bundles that coefficient-specific continuity preparation with a lower scalar-equivariant representative; it does not assert a CE, decalage or cutoff-tower comparison.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-sp-vertical-cutoff-column-quasiiso-equal: the existing statement concerns Nested smart cutoff comparison: equal endpoints (an upper cutoff, mapped/totalized truncation, or comparison between two cutoffs). It states no general-lfp-to-constant-model bridge and no sequential internal sheaf-Hom continuity for K. The new node bundles that coefficient-specific continuity preparation with a lower scalar-equivariant representative; it does not assert a CE, decalage or cutoff-tower comparison.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-sp-vertical-cutoff-column-quasiiso-strict-nonpositive: the existing statement concerns strict cutoff comparison: nonpositive endpoint (an upper cutoff, mapped/totalized truncation, or comparison between two cutoffs). It states no general-lfp-to-constant-model bridge and no sequential internal sheaf-Hom continuity for K. The new node bundles that coefficient-specific continuity preparation with a lower scalar-equivariant representative; it does not assert a CE, decalage or cutoff-tower comparison.

lem-sfb-integral-general-lfp-sequential-continuity vs lem-sp-vertical-cutoff-column-quasiiso-strict-positive: the existing statement concerns strict cutoff comparison: positive endpoint (an upper cutoff, mapped/totalized truncation, or comparison between two cutoffs). It states no general-lfp-to-constant-model bridge and no sequential internal sheaf-Hom continuity for K. The new node bundles that coefficient-specific continuity preparation with a lower scalar-equivariant representative; it does not assert a CE, decalage or cutoff-tower comparison.

## Complete transferred argument for the next workers

These are the seven original steps, without shortening. They are work instructions in this report, not proof steps in either new unsplit node. The first four belong to lem-sfb-integral-general-lfp-sequential-continuity, and the last three belong to lem-sfb-scalar-hom-telescope-evaluation. In the latter use general scalar t on a small ringed site: old step 5's coefficient identification is supplied by the parent, while the formal theorem is independent of it. The first node generalizes the same lower-truncation construction to every applicable L; the second allows arbitrary representatives by the exact-colimit and functorial-resolution compatibilities of old step 6.

### Original step 1 → lem-sfb-integral-general-lfp-sequential-continuity

First check the topological hypothesis needed for internal continuity. Apply [lem-weil-pbc-noetherian-scheme-closed-subsets-minimal] to the given locally Noetherian, quasi-compact scheme $X$. In a descending chain $(Z_n)$ of closed subsets, choose a minimal member $Z_N$ of the nonempty set of its members. For $n\ge N$, $Z_n\subseteq Z_N$, so minimality forces $Z_n=Z_N$. Thus the underlying space of $X$ is Noetherian.

Inputs: lem-weil-pbc-noetherian-scheme-closed-subsets-minimal.

Source: literature/stacks-project/properties.tex, Tag 01OZ, lemma-Noetherian-topology; minimal-closed-subset formulation.

### Original step 2 → lem-sfb-integral-general-lfp-sequential-continuity

For each nonzero cohomology sheaf $H^q(K)$ apply (i)$\Rightarrow$(ii) of [lem-sfb-integral-lfp-constant-model-comparison], with $A=R$. Its input is exactly the finite constructible stratification and the arbitrary-entry local finite presentation in the hypothesis. It gives finite constant scalar local models for $H^q(K)$, allowing a different stratification for each $q$. Since only finitely many $q$ occur, $K$ has bounded constructible cohomology in the finite constant local model sense. No torsion-freeness or completeness of these cohomology sheaves is required.

Inputs: lem-sfb-integral-lfp-constant-model-comparison.

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf, Theorem 6.2(2)–(3), Theorem 4.13; use the existing coefficient-specific general-lfp comparison obligation, not merely the heart characterization.

### Original step 3 → lem-sfb-integral-general-lfp-sequential-continuity

Use the small skeleton of $X_{\mathrm{proet}}$ specified by [def-weil-pbc-proetale-site]. By [lem-pur-ringed-site-grothendieck-abelian], filtered colimits of $B$-module sheaves are exact. Apply [lem-sfb-constructible-internal-hom-continuity] with $\Lambda=\underline R$, using steps 1–2. In particular take any sequential diagram $(M_n^\bullet)$ with a common termwise lower bound; the natural-number category is small and filtered. The evaluation-induced map $\varinjlim_n R\mathcal Hom_B(K,M_n)\to R\mathcal Hom_B(K,\varinjlim_n M_n)$ is an isomorphism. This proves precisely the sequential-continuity hypothesis of the formal localization theorem.

Inputs: def-weil-pbc-proetale-site, lem-pur-ringed-site-grothendieck-abelian, lem-sfb-constructible-internal-hom-continuity.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61–62; agent internal-sheaf localization extraction.

### Original step 4 → lem-sfb-integral-general-lfp-sequential-continuity

Here is an explicit bounded-below representative for the telescope of $L$. Choose $c$ with $H^q(L)=0$ for $q<c$ and any complex $C$ representing $L$ [def-weil-abstract-derived-category]. Define $P^q=0$ for $q<c$, $P^c=\operatorname{coker}(d_C^{c-1})$, and $P^q=C^q$ for $q>c$, with induced differentials. The quotient $C\to P$ induces the identity on cohomology in degrees $q\ge c$, while both sides have zero cohomology below $c$. It is a quasi-isomorphism. Multiplication by $\ell$ descends to $P$, so the repeated-$\ell$ tower has one common termwise lower bound. This construction uses no condition on $L$ beyond the stipulated cohomological lower bound.

Inputs: def-weil-abstract-derived-category.

Source: literature/stacks-project/homology.tex, Tag 0118, section-truncations, canonical lower truncation; direct kernel/image computation.

### Original step 5 → lem-sfb-scalar-hom-telescope-evaluation

By [sk-prop-sfb-qlbar-colimit-x], the actual coefficient map $B\to S$ identifies $S$ with $B[1/\ell]$, with underlying module the repeated-$\ell$ telescope. Apply [lem-sfb-internal-hom-localization-comparison] with ring sheaf $B$, section $s=\ell$, first input $K$, and second input $L$. Smallness, exact filtered colimits and sequential continuity were checked in step 3, and $L$ is cohomologically bounded below. This yields the asserted isomorphism in $D(S)$ for the canonical evaluation-transpose map. The same theorem identifies its restriction to $D(B)$ with the evaluation-induced sequential-continuity isomorphism. It also supplies naturality in both inputs.

Inputs: sk-prop-sfb-qlbar-colimit-x, lem-sfb-internal-hom-localization-comparison.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61–62; agent internal-sheaf localization extraction.

### Original step 6 → lem-sfb-scalar-hom-telescope-evaluation

Pin down the legs of that identification. By [lem-sfb-derived-scalar-localization-reflection], localization is exact termwise extension with unit $x\mapsto1\otimes x$. Apply [lem-weil-pbc-scalar-localization-complex-colimit] with scalar ring $R$, $t=\ell$, sheaf ring $B$, to $P$ and to any complex representing $H=R\mathcal Hom_B(K,L)$. It identifies each scalar telescope with the restricted localization, with $n$th leg $x\mapsto\ell^{-n}(1\otimes x)$. For a functorial K-injective Hom representative the transition obtained from $\ell_P$ need not literally equal multiplication by $\ell$ on the chain level. The leg-compatible isomorphism of [lem-sfb-kinjective-hom-scalar-telescope] identifies those two colimits and preserves every derived leg. Consequently the preceding restricted comparison is the one between the two scalar repeated-$\ell$ telescopes, including at every stage. No lower bound on the complex representing $H$ is needed.

Inputs: lem-sfb-derived-scalar-localization-reflection, lem-weil-pbc-scalar-localization-complex-colimit, lem-sfb-kinjective-hom-scalar-telescope.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61–62; agent internal-sheaf localization extraction.

### Original step 7 → lem-sfb-scalar-hom-telescope-evaluation

The evaluation normalization of [lem-sfb-dc-hom-scalar-adjunction] identifies the restricted target with $R\mathcal Hom_B(K,L_E)$ by precomposing restricted evaluation with $K\to K_E$. On telescope stage $n$, step 6 gives the leg $h\mapsto\ell^{-n}(1\otimes h)$. Pairing it with $k$ therefore gives $\ell^{-n}(1\otimes h(k))$ by scalar linearity of evaluation. This notation means the corresponding composite of evaluation, the scalar unit, and multiplication by $\ell^{-n}$ on representatives. The next-stage representative is $\ell h$, and $\ell^{-(n+1)}(1\otimes(\ell h)(k))=\ell^{-n}(1\otimes h(k))$, so these pairings form the required cocone. The scalar-adjunction normalization shows that its transpose is exactly the map of step 5. Thus the formula characterizes the canonical derived map, and all choices disappear under the representative-independent continuity and localization isomorphisms already used.

Inputs: lem-sfb-dc-hom-scalar-adjunction.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61–62; agent internal-sheaf localization extraction.


## Verification log

Server check_dag and review_split passed before the report was written. The first deliver dry run requested twelve further same-tag truncation comparisons; I opened every listed statement and added the comparisons above. None provides the new continuity assertion.

The second dry run required a longer coefficient-node citation excerpt. I expanded it to include both the ring isomorphism and the repeated-ell module telescope in its statement, preserving the verbatim text.
