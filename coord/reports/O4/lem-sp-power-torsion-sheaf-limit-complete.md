## Worker report

1. Files written: `dag/nodes/sec-smooth-purity/lem-sp-power-torsion-sheaf-limit-complete.json` (statement unchanged; four-step assembly, 2206 characters); three statement-only nodes in the same chapter: `lem-sp-nilpotent-action-koszul-unit` (statement, unsplit, no Mathlib match), `lem-sp-signed-double-roos-tensor-exchange` (statement, unsplit, no Mathlib match), and `lem-sp-koszul-quotient-strict-resolution-bridge` (statement, unsplit, no Mathlib match). `citations.json` supplies literal statement quotes for every citation in every assembly step.
2. Attachments: none. The live `lean/Sheaf/Paper/PowerTorsionSheafLimitComplete.lean:288` states the item but ends in `sorry`. Its `unit_condition` helper is proved; it supplies compatibility of the augmentation, not the full theorem. Searches of `lean/WeilConjectures/` by the item id and by power torsion, nilpotent completion, Koszul and Roos found no exact finished project declaration.
3. WANTED: none.
4. The return asks to distribute the existing 8280-character proof rather than abbreviate it. The sandbox initially contained only dispatcher marker files; no retained report or searches were present. I copied the returned item from the live read-only repository and preserved its statement, source, old searches and maintainer metadata. The substantive repair is three separate, self-contained, general ringed-site statements, of comparable size (1788, 2163 and 2226 characters). None asserts completeness of the inverse limit of a power-torsion tower. No source or statement dispute was found. No Lean was written or compiled and no repository or launcher file was modified.
5. Nothing mathematical remains unfinished in the assembly. The new lemmas are deliberately unsplit for parallel work, as the return requires. Their arguments are preserved verbatim below for their future workers, not installed as proof steps in the new node files.

## Repair of the return

The sole numbered requirement is the re-split. Old steps 2--3 belong to the nilpotent-action node; old steps 4--6 belong to the signed double-Roos/tensor node (the levelwise quasi-isomorphism application in old step 6 is retained in assembly step 2); old steps 7--8 belong to the strict-resolution bridge. Old step 1 remains assembly step 1, and old step 9 remains assembly step 4. Each new statement exposes the corresponding maps, hypotheses and compatibility identities. This preserves the whole argument rather than suppressing it. The item has four steps and 2206 proof-text characters, below 3000, and no non-elementary step over 2000 characters. The new nodes have `status: unsplit`, empty `proof` and `proof_deps`, and null `proof_origin`. The original statement is byte-for-byte unchanged.

The three tasks can be started independently: the first proves a nilpotent-action quotient-tower vanishing calculation; the second constructs signed coordinate isomorphisms for arbitrary complexes without torsion or regularity; the third compares a single K-flat representative's entire Koszul and quotient towers without completeness or torsion. The last task's conclusion is an isomorphism in the derived category, not merely a cohomology calculation.

## Searches

Before creating the nodes I searched the whole DAG statements and metadata for nilpotent Koszul completion, double/iterated Roos, tensor/Roos, regular quotient units, the Stacks tags and the proposed ids. `tools/blueprint_refs.py ancestor` returned `sk-lem-sp-tower`. Whole-blueprint searches included `Roos`, `Koszul`, `nilpotent`, `power-torsion`, `completion unit`, `iterated`, `nilpotent action`, `double Roos`, and `K-flat resolution`; the same-as lists are empty. The generic existing comparisons listed below were read, not inferred from names. Their statements lack the new maps or have different hypotheses.

All three new nodes have five actual `msearch.py` calls: LeanFinder, Loogle, Mathlib grep, LeanSearch, and a second LeanFinder phrasing. Their exact queries and result summaries are in the node records and `searches.jsonl`; full answers are retained as sandbox search text files. All services answered. The first node's searches return generic homology, truncation, resolutions and vanishing derived functors. The second returns total-complex shift/symmetry; I read `Mathlib/Algebra/Homology/TotalComplexSymmetry.lean`, especially `totalFlipIso` and its summand formulas. This is a useful ingredient but does not construct the double-product Roos complex or its tensor/unit normalization: these require coordinate identifications and several chain-map compatibilities. The third returns resolutions, abstract Tor, generic quasi-isomorphisms and ordinary adic completion. Its Mathlib grep only found a comment about Koszul homology in LocalCohomology. No result is an exact or one-line specialization of any new statement. The item's unchanged earlier search results were read and retained; its statement and search question did not change.

## Review by O4

I read the current chapter and unit records, the current `sk-lem-sp-tower.proof.md` completeness and reduction-as-cone sentences, the full returned nine-step argument, and the live Lean theorem and docstring. I also read Bhatt--Scholze Lemma 3.4.12 and Lemma 3.5.7 and the exact Stacks sources 0941 (`sites-cohomology.tex`, `lemma-derived-limit-is-ok`), 012Z (`homology.tex`, `definition-associated-simple-complex`), 014E (`derived.tex`, `definition-cone`), 06YT (`sites-cohomology.tex`, `lemma-derived-tor-quasi-isomorphism-other-side`), 06YY (`lemma-derived-base-change`) and 0A0E (`algebraization.tex`, `lemma-derived-completion-koszul`). The blueprint and Bhatt--Scholze motivate the completeness argument; the signed coordinate and strict augmentation refinements are the agent-written expansions preserved below, not assertions falsely attributed verbatim to those sources. No SGA source is used.

Assembly step 1 uses `lem-weil-proetale-countable-products-exact`, whose statement explicitly includes arbitrary ring sheaves and completed coefficients; `lem-weil-strict-roos-comparison`, whose statement supplies the functor on unbounded tower derived categories, evaluation compatibility and the zero shifted-component augmentation normalization; and the new nilpotent-action lemma, whose statement supplies natural units and levelwise quasi-isomorphisms. The site is chosen small in the module universe, the coefficients are the actual completed ring sheaf R, and the exponent is r_n separately at each level. No common exponent or normalization is introduced.

Assembly step 2 uses `lem-weil-tower-category-levelwise-abelian`, which states exactness of evaluations and levelwise kernels and cokernels, together with the descent-to-derived-functor clause of strict Roos comparison. Thus a levelwise quasi-isomorphism is a quasi-isomorphism of tower complexes and its Roos image is invertible. The new exchange node states both the actual (-1)^{pq} chain isomorphism and gamma, and the precise augmentation-composite identity the step takes from it. I recomputed the sign on all four Roos bidegrees; it is -1 only at (1,1), and is 1 on q=0. For tensor/Roos comparison, use common summands indexed by Roos degree p, complex degree a and Koszul degree b: both differentials are -(1-s_n)+(-1)^p d_Q+(-1)^{p+a}d_L. Only four Roos summands and two Koszul degrees occur per total degree, even when Q is unbounded. Therefore no infinite coproduct/product interchange is hidden. The composite puts q=b=0 and so gives exactly h tensor 1 and zero shifted j-component, not merely some isomorphism to a completion object.

Assembly step 3 uses `lem-sp-ell-coefficient-fiber`, whose statement explicitly supplies injectivity of pi and R/pi^j=(O/pi^j)_T; `lem-pc-kflat-resolution`, which supplies a flat-term K-flat resolution of an arbitrary unbounded complex; and the new strict-resolution bridge, whose statement includes the two levelwise quasi-isomorphisms, the derived-limit span, the identity identifying its unit, and every quotient projection. I checked that only pi-regularity is used here, not in the first two new lemmas. The same P is used for all j. The new bridge does not claim that M is K-flat, or that P tensor B_j is K-flat over R. The acyclicity test uses K-flatness of P and of L_j in the appropriate variables; the signed tensor braiding is accounted for in the retained old step 7. In the comparison equation e=Q(f) points from Q(P) to Q(M), so e^{-1} occurs on the source side of the quotient augmentation, with the correct domains. This is an equality of maps in D(R).

Assembly step 4 uses `lem-weil-pbc-ringed-strict-tower-homotopy-limit`, whose statement supplies the distinguished Roos triangle for the strict quotient tower. The `def-weil-derived-complete` statement explicitly gives the equivalent criterion using an isomorphism whose projection components are the quotient maps; it also spells out the triangle transport. The step performs precisely that transport. It is elementary from these two cited statements. The final completeness terminology is scoped, as in the unchanged item, to its integral coefficient convention; the argument itself works for any T.

For each new node I checked self-contained objects, universes, tensor order, all quantifiers and hypotheses; its notions are cited in `stmt_deps`, not merely supplied by literature tags. The first node states a general short exact sequence and the consequence of nilpotent action on Q; it does not assume the section t itself is nilpotent in R. In degree k the quotient sign (-1)^k is necessary to make the differential on Q[1] be -d_Q. The constant tower has diagonal kernel and a chain section z_1=0, z_j=-sum_{i<j} y_i for 1-s. The quotient tower transitions compose to t^r=0, giving vanishing of its total derived limit. These details are retained for the future worker. The second node is an independent signed exchange/coherence result for arbitrary double strict towers. The third is an independent regular quotient bridge for arbitrary M, and takes any supplied K-flat resolution rather than choosing data from a mere existence assertion.

Small cases checked: Q=0, t=0 in the nilpotent lemma, r=1, a complex concentrated in either degree 0 or -1, and Q=R/(t^r) with nonzero t in R. The latter distinguishes nilpotence on Q from nilpotence in R. In the exchange lemma, identity or zero transitions still give the same four-coordinate sign formula; swapping twice gives (-1)^{2pq}=1, and the q=1 augmentation coordinates vanish. In the bridge, M=0 and M=R[0] recover the usual regular quotient resolution; if t is a unit, all L_j and B_j are acyclic/zero after localization, so the statement still holds. The bridge imposes regularity: no claim is made for a general nonregular quotient. No characteristic, boundedness or global exponent hypothesis was added to the item.

Against B--E: new files carry statements only and no proof sketch in their statements; TeX uses single mathematical backslashes; sources include actual Stacks tags and labels, and all searches were run. New lemmas are separate arguments needed for the assembly, not the whole conclusion moved to a child. There is no dependency back to the item: `created.item` and `blueprint.from.via` record provenance only. Every use in the item has a literal citation quote. I read the full statement of every old node now cited, including the precise quotient clause of `lem-sp-ell-coefficient-fiber`, and checked all relevant hypotheses. The only correction to the previous work is the required distribution of work, with its old argument preserved.

## Not duplicates

lem-sp-koszul-quotient-strict-resolution-bridge vs def-a1-integral-finite-pullback-tower: Defines finite pullback of quotient towers for a scheme map; it asserts no Koszul-to-quotient quasi-isomorphism span or completion-unit identity for an arbitrary representative.

lem-sp-koszul-quotient-strict-resolution-bridge vs new-h4-qcoh-chart-comparison-hom-identification: Identifies a chart tensor-comparison homology map; it has no principal quotient system, Roos limit, or specified completion unit.

lem-sp-koszul-quotient-strict-resolution-bridge vs new-h4-qcoh-tensor-comparison-restriction-naturality: Proves homology naturality under an open restriction for common K-flat tensor comparisons, not the strict Koszul/quotient tower span and completion-unit equation.

lem-sp-koszul-quotient-strict-resolution-bridge vs new-t3-qcoh-tensor-resolution-chart-comparison-naturality: Concerns affine-chart homology comparisons for quasi-coherent modules and projective resolutions, not principal quotient towers or normalized Roos units.

lem-sp-koszul-quotient-strict-resolution-bridge vs new-t3-qcoh-tensor-resolution-coordinate-factorization: Factors an affine-chart coordinate sheaf isomorphism in a fixed cohomology degree, not the full derived-category Koszul/quotient tower comparison and its augmentation.

lem-sp-koszul-quotient-strict-resolution-bridge vs lem-weil-pbc-completed-constant-derived-tensor-tower: States existence and K-flat computation of a universal derived ordinary tensor diagram; it does not provide the regular Koszul augmentation span, an arbitrary M representative comparison or the completion-unit equation.

lem-sp-nilpotent-action-koszul-unit vs def-a1-lisse-section-evaluation: Defines evaluation of global cohomology at a geometric point of a Weil complex, with no nilpotent-action Koszul-unit theorem.

lem-sp-nilpotent-action-koszul-unit vs lem-a1-normalized-roos-shift-comparison: Compares one Roos direction with integer shifts and its derived normalization; it neither proves nilpotent-action completeness nor exchanges two inverse directions and tensor factors.

lem-sp-nilpotent-action-koszul-unit vs lem-a1-quotient-unit-shift-completeness: Assumes a quotient completion unit is invertible and proves shift completeness. The new nilpotent-action result proves its Koszul unit is invertible from termwise nilpotent action, without that assumption or regularity.

lem-sp-signed-double-roos-tensor-exchange vs lem-a1-normalized-roos-shift-comparison: Compares one Roos direction with integer shifts and its derived normalization; it neither proves nilpotent-action completeness nor exchanges two inverse directions and tensor factors.

lem-sp-signed-double-roos-tensor-exchange vs lem-a1-strict-roos-shift-localization: Descends the shift comparison for one Roos direction; it does not construct the double inverse-sequence interchange, tensor comparison or their simultaneous augmentation identity.

lem-sp-signed-double-roos-tensor-exchange vs def-zl-field-weil-shriek-shift-data: Defines shifts and Frobenius exchange on field-coefficient shriek functors; it has no double-Roos/tensor exchange theorem for arbitrary unbounded sheaf complexes.

lem-sp-nilpotent-action-koszul-unit vs lem-sf-completed-tensor-finite-shift: The existing result moves a shift through finite reductions of a tensor of two complexes; it neither proves a nilpotent-action unit nor exchanges Roos directions or compares Koszul and quotient towers.

lem-sp-nilpotent-action-koszul-unit vs def-sf-open-semilinear-tensor-model-data: The existing node defines open semilinear tensor comparison data, and asserts no existence or nilpotent-unit/Roos-comparison theorem.

lem-sp-nilpotent-action-koszul-unit vs def-pc-tensor-complex-sheaves: The existing node defines total tensor and its differential, but asserts none of the new quasi-isomorphism or Roos-coordinate comparison conclusions.

lem-sp-nilpotent-action-koszul-unit vs lem-sc-total-extension-nat-arrow-iso: The existing result concerns extension by zero of natural-number bicomplexes and their arrows, with no strict inverse tower, Koszul unit or quotient resolution comparison.

lem-sp-nilpotent-action-koszul-unit vs lem-sp-bounded-below-second-filtration: The existing result constructs a bounded-below second filtration, with no nilpotent-action, Roos exchange or quotient-unit comparison.

lem-sp-nilpotent-action-koszul-unit vs lem-sp-ce-filtered-total-lifts: The existing result constructs filtered lifts of Cartan--Eilenberg comparisons, with no Koszul tower, Roos coordinate exchange or quotient unit.

lem-sp-nilpotent-action-koszul-unit vs lem-sc-tensor-total-extend-nat: The existing result compares natural-degree tensor totals and extension by zero over a field, rather than arbitrary unbounded sheaf complexes with strict inverse tower maps.

lem-sp-nilpotent-action-koszul-unit vs lem-sc-tensor-total-extension-coordinates: The existing result gives summand formulas for zero extension of natural-degree vector-space tensors, not the sheaf-complex Roos/Koszul identities of the new node.

lem-sp-nilpotent-action-koszul-unit vs def-sp-total-tensor-summand-interface: The existing node names total-tensor summand inclusions and aliases; it asserts no theorem about inverse limits, nilpotence or quotient comparisons.

lem-sp-nilpotent-action-koszul-unit vs def-sbc-strict-projection-tower-data: The existing node defines normalized projection/derived direct-image data but asserts no Koszul-unit quasi-isomorphism or signed exchange theorem.

lem-sp-nilpotent-action-koszul-unit vs lem-sf-open-reduction-adjunction-transport: The existing result assumes reconstruction units invertible and studies open adjunction transport; it supplies none of the new elementary Roos/Koszul comparison constructions.

lem-sp-nilpotent-action-koszul-unit vs lem-coef-derived-tower-counit-projections: The existing result identifies evaluation of the derived constant-tower/limit adjunction counit, not the new nilpotent-unit or chain-coordinate comparison.

lem-sp-signed-double-roos-tensor-exchange vs lem-sf-completed-tensor-finite-shift: The existing result moves a shift through finite reductions of a tensor of two complexes; it neither proves a nilpotent-action unit nor exchanges Roos directions or compares Koszul and quotient towers.

lem-sp-signed-double-roos-tensor-exchange vs def-sf-open-semilinear-tensor-model-data: The existing node defines open semilinear tensor comparison data, and asserts no existence or nilpotent-unit/Roos-comparison theorem.

lem-sp-signed-double-roos-tensor-exchange vs def-pc-tensor-complex-sheaves: The existing node defines total tensor and its differential, but asserts none of the new quasi-isomorphism or Roos-coordinate comparison conclusions.

lem-sp-signed-double-roos-tensor-exchange vs lem-sc-total-extension-nat-arrow-iso: The existing result concerns extension by zero of natural-number bicomplexes and their arrows, with no strict inverse tower, Koszul unit or quotient resolution comparison.

lem-sp-signed-double-roos-tensor-exchange vs lem-sp-bounded-below-second-filtration: The existing result constructs a bounded-below second filtration, with no nilpotent-action, Roos exchange or quotient-unit comparison.

lem-sp-signed-double-roos-tensor-exchange vs lem-sp-ce-filtered-total-lifts: The existing result constructs filtered lifts of Cartan--Eilenberg comparisons, with no Koszul tower, Roos coordinate exchange or quotient unit.

lem-sp-signed-double-roos-tensor-exchange vs lem-sc-tensor-total-extend-nat: The existing result compares natural-degree tensor totals and extension by zero over a field, rather than arbitrary unbounded sheaf complexes with strict inverse tower maps.

lem-sp-signed-double-roos-tensor-exchange vs lem-sc-tensor-total-extension-coordinates: The existing result gives summand formulas for zero extension of natural-degree vector-space tensors, not the sheaf-complex Roos/Koszul identities of the new node.

lem-sp-signed-double-roos-tensor-exchange vs def-sp-total-tensor-summand-interface: The existing node names total-tensor summand inclusions and aliases; it asserts no theorem about inverse limits, nilpotence or quotient comparisons.

lem-sp-signed-double-roos-tensor-exchange vs lem-pe-endomorphism-fibre-double-cone: The existing result compares the fibre of a cone with the cone of fibre maps; it does not exchange two countable-product Roos directions or include the tensor comparison and its augmentation identity.

lem-sp-signed-double-roos-tensor-exchange vs lem-pe-endomorphism-fibre-coordinate-calculus: The existing result supplies a single endomorphism fibre functor, shift signs and single augmentation naturality; it lacks double inverse towers and tensor/Roos exchange.

lem-sp-signed-double-roos-tensor-exchange vs def-weil-signed-mapping-cocone-functor: The existing node defines mapping-cocone maps and shift comparisons without proving the signed double-Roos/tensor interchange.

lem-sp-koszul-quotient-strict-resolution-bridge vs lem-pe-restricted-kflat-tensor-identification: The existing result identifies scalar-first and scalar-last tensor models of one scalar extension and arbitrary linear coefficient maps. It has no regular Koszul resolution, entire tower quasi-isomorphism span or zero-homotopy completion-unit identity.

lem-sp-koszul-quotient-strict-resolution-bridge vs lem-sbc-scalar-extension-counit-properties: The existing result proves properties of universal scalar-extension counits on K-flat complexes, not the regular Koszul/quotient tower span or its units.

lem-sp-koszul-quotient-strict-resolution-bridge vs lem-sf-cochain-tensor-model-rigidity: The existing result is rigidity of models for derived tensor bifunctors, not an explicit principal quotient completion comparison with strict augmentations.

lem-sp-koszul-quotient-strict-resolution-bridge vs lem-sf-ringed-finite-free-tensor-complex: The existing result concerns ordinary change of rings preserving tensor and K-flat complexes, not regular Koszul resolutions and Roos units.

lem-sp-koszul-quotient-strict-resolution-bridge vs def-sf-unrestricted-reduction-complex-constructions: The existing node defines finite quotient reduction complexes and computation maps, with no theorem comparing their whole tower to Koszul completion of an arbitrary representative.

lem-sp-koszul-quotient-strict-resolution-bridge vs lem-sf-ringed-derived-native-tensor: The existing result supplies native derived monoidal tensor comparisons, not a strict regular-Koszul/quotient tower comparison carrying specified Roos units.

lem-sp-koszul-quotient-strict-resolution-bridge vs def-zl-ringed-derived-closed-symmetric-monoidal-data: The existing node defines representative monoidal coherence data and asserts no existence or Koszul/quotient completion comparison.

lem-sp-koszul-quotient-strict-resolution-bridge vs def-zl-derived-change-of-rings-model: The existing node selects the canonical scalar-extension model; it states no strict tower span or completion-unit compatibility theorem.

lem-sp-koszul-quotient-strict-resolution-bridge vs new-t3-qcoh-tensor-resolution-chart-homology-naturality: The existing result concerns affine-chart homology of quasi-coherent tensor resolutions and semilinear restriction, not unbounded ringed-site Koszul/quotient towers.

lem-sp-koszul-quotient-strict-resolution-bridge vs new-j1-qcoh-ordinary-tensor-resolution-coordinates-witness: The existing result constructs projective-resolution coordinate witnesses on affine quasi-coherent charts, not the regular quotient Roos comparison or its units.

lem-sp-koszul-quotient-strict-resolution-bridge vs new-h4-qcoh-tensor-comparison-hom-formula: The existing result gives homology-map formulas for two-resolution tensor comparisons, not an isomorphism of entire strict quotient towers or a specified completion unit.

lem-sp-koszul-quotient-strict-resolution-bridge vs new-g2-existing-qcoh-tensor-resolution-coordinate-naturality: The existing result proves affine-chart homology naturality for comparison witnesses, not a derived strict-tower comparison with quotient units.

lem-sp-nilpotent-action-koszul-unit vs lem-weil-pbc-nilpotent-koszul-completion-unit: The existing result assumes a power of each element vanishes in a constant ring B. The new result assumes only that t acts nilpotently on Q over an arbitrary ring sheaf R; e.g. R=Z_l, Q=R/l works but t=l is not nilpotent in R. It also states the quotient strict-tower sequence and strict naturality.

lem-sp-signed-double-roos-tensor-exchange vs lem-sp-normalized-koszul-roos-models: That node asserts existence of a bundled regular-section model normalized on a scheme pro-etale site; it does not state the signed double-tower interchange beta and its precise augmentation-composite equation for arbitrary complexes. The new node works on an arbitrary small ringed site and does not require regularity.

lem-sp-koszul-quotient-strict-resolution-bridge vs lem-pur-derived-complete-koszul-reconstruction: That node starts with a K-flat representative and compares its Koszul and quotient towers. The new node includes the separate M tensor L <- P tensor L comparison for arbitrary M and an explicit equality between its normalized Roos unit and the actual quotient augmentation via Q(f)^(-1). The existing statement does not supply that additional comparison or equation.

lem-sp-koszul-quotient-strict-resolution-bridge vs lem-sf-regular-roos-koszul-unit: That node compares derived completion objects on a chosen K-flat representative and characterizes completeness. It does not state the strict span including the arbitrary M representative or the explicit Roos chain-unit equation s_f Q(u_M)=Q(v_P)Q(f)^(-1).

lem-sp-koszul-quotient-strict-resolution-bridge vs lem-pur-regular-quotient-completion-unit: That node proves local derived completeness of quotient completion and equivalent criteria; it does not state the two strict tower quasi-isomorphisms connecting arbitrary M tensor L_j to quotient tensors on one P, or the resulting unit comparison equation.

## Full retained argument and task ownership

The following is the full original returned proof, preserved without abbreviation. These are future-proof instructions in the report; the new nodes themselves remain statement-only.

### Original step 1: Assembly step 1

Work throughout in the single category $\mathcal A=\operatorname{Mod}(R)$ on the small pro-etale site of $T$. Countable products in this category are exact by [lem-weil-proetale-countable-products-exact]. Consequently [lem-weil-strict-roos-comparison] computes the total derived limit of every strict tower $X$ by $\mathsf R(X)=\operatorname{Cone}(1-s_X:\prod X_i\to\prod X_i)[-1]$, naturally for strict maps and strict augmentations. Use reordered coordinates $(v,u)$ with differential $(dv,-du-(1-s_X)v)$. Its evaluation is $\mathrm{pr}_i(v)$ and an augmented family $a_i:M\to X_i$ induces $m\mapsto((a_i m)_i,0)$. This fixes both the models and the units; it does not assert that a lift in an abstract triangulated category is unique.

Cited nodes: lem-weil-proetale-countable-products-exact, lem-weil-strict-roos-comparison.

### Original step 2: lem-sp-nilpotent-action-koszul-unit

Fix $n$ and write $Q=Q_n$, $r=r_n$, and $M_j=Q\otimes_R L_j$. The tensor convention [def-pc-tensor-complex-sheaves] gives $M_j^k=Q^k\oplus Q^{k+1}$ and $d(x,y)=(dx+(-1)^{k+1}\pi^j y,dy)$. The degree-zero inclusion $i_j(x)=(x,0)$ is compatible with the transitions $(x,y)\mapsto(x,\pi y)$. Its quotient is $Q[1]$: the quotient identification in degree $k$ sends $y$ to $(-1)^k y$, so its differential is $-d_Q$ and its transition is multiplication by $\pi$. Thus there is a short exact sequence of complexes of strict $j$-towers $0\to\operatorname{const}(Q)\xrightarrow{i}M_\bullet\to Z_\bullet\to0$, where every $Z_j=Q[1]$ and every transition is $\pi$. Exactness is levelwise by [lem-weil-tower-category-levelwise-abelian], and [lem-weil-pbc-complex-ses-triangle] gives its distinguished triangle in the derived category of towers. No splitting as complexes, nor eventual vanishing of the differential on $M_j$, is being assumed.

Cited nodes: def-pc-tensor-complex-sheaves, lem-weil-tower-category-levelwise-abelian, lem-weil-pbc-complex-ses-triangle.

### Original step 3: lem-sp-nilpotent-action-koszul-unit

The composite $Z_{j+r}\to Z_j$ is $\pi^r=0$ on $Q[1]$. The exact total derived-limit functor and its pro-zero criterion in [lem-weil-pbc-ringed-strict-tower-homotopy-limit] therefore give $R\lim_j Z_j=0$ and $R\lim_j\operatorname{const}(Q)\xrightarrow{\sim}R\lim_j M_j$. The diagonal identifies $Q$ with the first limit: on the constant tower $1-s$ has kernel the diagonal, and the chain section solving $z_j-z_{j+1}=y_j$ is $z_1=0$, $z_j=-\sum_{i<j}y_i$. The resulting split product sequence identifies its fibre with $Q$. By the augmentation clause of [lem-weil-strict-roos-comparison], the resulting isomorphism is precisely $u_Q:Q\to\mathsf R_j(Q\otimes L_j)$ with product components $i_j$ and zero shifted component. The inclusions and all these constructions commute with every $R$-linear chain map $Q\to Q'$. Hence $u_{Q_n}$ is a strict natural map of $n$-towers and a quasi-isomorphism at each $n$; the argument used only $r_n$, separately at each level.

Cited nodes: lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-weil-strict-roos-comparison, lem-weil-pbc-complex-ses-triangle.

### Original step 4: lem-sp-signed-double-roos-tensor-exchange

For $X_{n,j}=Q_n\otimes_RL_j$, interchange the two product coordinates $\prod_n\prod_jX_{n,j}^a\cong\prod_j\prod_nX_{n,j}^a$ by $(x_{n,j})\mapsto(x_{n,j})$. In the iterated Roos complexes let $p\in\{0,1\}$ be the outer $n$-Roos degree and $q\in\{0,1\}$ the inner $j$-Roos degree. On the summand of total degree $a+p+q$ multiply this coordinate interchange by $(-1)^{pq}$. The source differential is $-(1-s_n)+(-1)^p(-(1-s_j))+(-1)^{p+q}d_X$, with each term mapping to its corresponding new degree. Under interchange the $n$-term acquires $(-1)^q$ and the $j$-term acquires $(-1)^p$, exactly the signs in the target differential. The internal term has the same sign on both sides. This proves the chain-map identity; the reverse formula is its inverse since $(-1)^{2pq}=1$. There are only four Roos summands in each total degree, so products commute with these finite sums even for unbounded $X$. The formula is natural for both transitions and every strict map. It fixes all terms with $q=0$ and therefore carries the strict $j$-inclusions to the corresponding inclusions after interchange. By step 1 this is the asserted canonical interchange of iterated derived-limit Roos models.

Cited nodes: lem-weil-strict-roos-comparison.

### Original step 5: lem-sp-signed-double-roos-tensor-exchange

Put $H_0=\mathsf R_n(Q_\bullet)$, representing $H$ by step 1. For each $j$, tensoring its two Roos product coordinates with $L_j$ commutes with the products: each degree of $L_j$ is a single copy of $R$ and only the two degrees $-1,0$ occur. Explicitly, for Roos degree $p$, $Q$-degree $a$ and $L_j$-degree $b$, both $H_0\otimes L_j$ and $\mathsf R_n(Q_n\otimes L_j)$ have the product summand $\prod_n(Q_n^a\otimes L_j^b)$ and differential $-(1-s_n)+(-1)^p d_Q+(-1)^{p+a}d_{L_j}$. The coordinate identities therefore give a chain isomorphism $\gamma_j:H_0\otimes L_j\xrightarrow{\sim}\mathsf R_n(Q_n\otimes L_j)$. The components $(\pi,1)$ of $L_{j+1}\to L_j$ commute with this formula, so the $\gamma_j$ form an isomorphism of strict $j$-towers. It sends $h\otimes1$ to the $n$-Roos image of the inclusions $Q_n\to Q_n\otimes L_j$ and preserves the projections to $Q_n\otimes L_j$.

Cited nodes: def-pc-tensor-complex-sheaves, lem-weil-strict-roos-comparison.

### Original step 6: lem-sp-signed-double-roos-tensor-exchange; derived-functor application retained in assembly step 2

Apply $\mathsf R_n$ to the strict natural levelwise quasi-isomorphism $u_{Q_n}$ of step 3. It is a quasi-isomorphism because [lem-weil-tower-category-levelwise-abelian] detects exactness levelwise and [lem-weil-strict-roos-comparison] makes $\mathsf R_n$ a functor on the derived category of strict towers. Compose with the interchange of step 4 and $\mathsf R_j(\gamma_j^{-1})$ from step 5. This gives an isomorphism $H_0\to\mathsf R_j(H_0\otimes L_j)$. To identify this map, the first arrow puts every $j$-Roos degree in $q=0$ and every Koszul degree in $b=0$. The interchange sign there is $(-1)^{p\cdot0}=1$; $\gamma_j^{-1}$ then sends the component to $h\otimes1$. Thus the composite has product component $(h\mapsto h\otimes1)_j$ and zero shifted $j$-product component. It is exactly the specified Koszul completion unit of $H$, and its $j$th projection is the degree-zero inclusion $H_0\to H_0\otimes L_j$. This argument never forms a common exponent for the $Q_n$.

Cited nodes: lem-weil-tower-category-levelwise-abelian, lem-weil-strict-roos-comparison.

### Original step 7: lem-sp-koszul-quotient-strict-resolution-bridge

By [lem-sp-ell-coefficient-fiber], multiplication by $\pi^j$ on $R$ is injective, $R/\pi^jR=(O/\pi^j)_T=:B_j$, and the augmented $L_j\to B_j$ is a finite free K-flat resolution. Choose one flat-term K-flat resolution $f:P\to H_0$ by [lem-pc-kflat-resolution]. The map $P\otimes L_j\to H_0\otimes L_j$ is a quasi-isomorphism by [lem-pur-kflat-tensor-quasiiso-independent]. Also $P\otimes L_j\to P\otimes B_j$ is a quasi-isomorphism: the cone of $L_j\to B_j$ is acyclic by [lem-pur-quasi-iso-cone-acyclic], tensoring it with $P$ is acyclic by [def-pc-kflat-complex], and [lem-pc-tensor-mapping-cone-iso] identifies this with the cone of the tensor map. Here the interchange $x\otimes y\mapsto(-1)^{ab}y\otimes x$ in degrees $(a,b)$ is a chain isomorphism by the differential in [def-pc-tensor-complex-sheaves], so the K-flat test applies with $P$ on either side. Finally [lem-pur-derived-change-of-rings] identifies $P\otimes B_j$ with the scalar extension of $H$, and [def-pc-sheaf-restrict-scalars] regards its underlying complex as an $R$-complex. The span $H_0\otimes L_j\leftarrow P\otimes L_j\to\operatorname{Res}(P\otimes B_j)$ therefore gives the claimed isomorphism with restricted derived reduction for every $j$.

Cited nodes: lem-sp-ell-coefficient-fiber, lem-pc-kflat-resolution, lem-pur-kflat-tensor-quasiiso-independent, lem-pur-quasi-iso-cone-acyclic, def-pc-kflat-complex, lem-pc-tensor-mapping-cone-iso, def-pc-tensor-complex-sheaves, lem-pur-derived-change-of-rings, def-pc-sheaf-restrict-scalars.

### Original step 8: lem-sp-koszul-quotient-strict-resolution-bridge

Use the same $P$ for every $j$. The augmentations $L_j\to B_j$ commute with $(\pi,1)$ and quotient reduction, and both arrows in the span in step 7 commute with them. The two spans are therefore levelwise quasi-isomorphisms of entire strict towers, so [lem-weil-strict-roos-comparison] gives the claimed derived-limit comparison. The square whose top map is $P\to P\otimes L_j$, $p\mapsto p\otimes1$, whose bottom map is $P\to P\otimes B_j$, $p\mapsto p\otimes\overline1$, and whose right map is tensor augmentation commutes literally. Together with $f$, this identifies the $j$th projection of the unit of step 6 with the canonical quotient reduction map, rather than an arbitrary morphism to an isomorphic reduction object. The inclusion and augmentation formulas are those of [def-pur-principal-koszul-quotient-towers], in the right-tensor convention; since $1$ has degree zero its symmetry contributes no sign.

Cited nodes: lem-weil-strict-roos-comparison, def-pur-principal-koszul-quotient-towers.

### Original step 9: Assembly step 4

The strict quotient-reduction tower has its natural distinguished Roos triangle by [lem-weil-pbc-ringed-strict-tower-homotopy-limit]. Transport that triangle along the completion-unit isomorphism of steps 6--8. Its first map is $H\to\prod_j^D\operatorname{Res}(H\otimes_R^LB_j)$ with exactly the quotient-reduction components just identified; the second remains $1-s$. This is the Roos-triangle condition in [def-weil-derived-complete], and proves the final completeness assertion.

Cited nodes: lem-weil-pbc-ringed-strict-tower-homotopy-limit, def-weil-derived-complete.

