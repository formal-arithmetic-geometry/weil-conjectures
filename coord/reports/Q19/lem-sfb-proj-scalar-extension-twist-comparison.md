## Worker report

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-proj-scalar-extension-twist-comparison.json` (statement, split; six proof steps; unchanged statement; no exact Mathlib match); `dag/nodes/sec-six-functors-basics/lem-sfb-graded-module-localization-scalar-extension.json` (statement only, unsplit; no exact Mathlib match). Also `citations.json` and this report. The sandbox search log records all searches actually run. No Lean file was written and no compiler, Lake or build was run. No repository or launcher file was changed.
2. Attachments: none. Searched the project source for the exact blueprint tag and for Proj twist, scalar-extension, graded-module base-change and pullback notions. The existing twist and graded-module files do not state the whole item, including its arbitrary degree, normalized chart formula, unit, multiplication, section and composition clauses. In particular the projective-space twists do not provide a proof for arbitrary graded rings.
3. WANTED: none. All sources used are present locally.
4. What needed work: the item was statement-only. The degree-zero localization node cannot be used as if it also stated the comparison in degree j. The new algebra lemma supplies that missing fact. The source proof of 01N2 says only to inspect standard opens, and 01MZ omits the proof: the six steps spell out the maps, their overlaps and their composites. No statement dispute or source error was found. I preserved the imported statement and the inherited blueprint fields, including its null nearest blueprint ancestor (confirmed by `blueprint_refs.py ancestor`).
5. Outstanding: only the proof of the new statement-only algebra node, which is the intended next level of stage 1. It is strictly an algebraic localized-piece comparison for an arbitrary graded module: it does not state a sheaf pullback, Proj comparison, multiplication, homogeneous global sections or coherence. Thus it is neither a replacement name for this item nor a restatement of its sheaf clauses. No Mathlib leaves were created.

## Review by Q19

I read constructions.tex at the full statements and proofs of 01MY (lemma-morphism-proj), 01MZ (lemma-morphism-proj-transitive), and 01N2 (lemma-base-change-map-proj), and the graded-module section summarized in 01M7 (lemma-proj-sheaves). The normalized map in 01MY is a map of graded algebras, so its degree-j component has precisely the multiplication and unit normalization required here. The base-change assumption of 01N2 is the tensor algebra assumption, not generation in degree one and not flatness. An isomorphic model B is handled by applying beta to each numerator and denominator, with inverse beta inverse. I also read the current latest blueprint's sk-thm-sf-ctf-stability proof: this remains an affine relative-Proj prerequisite in the inherited compactification/direct-image route, rather than a change of that route. Chapter and unit records were read and not changed.

For the new algebra node, I read 01N2's standard-open reduction and algebra.tex's lemma-tensor-localization and lemma-tensor-product-localization proofs. The formulation for arbitrary Z-graded M is my explicit module refinement of that calculation; the node source says so, rather than pretending Stacks states that formulation verbatim. The proof to pursue for this new node is as follows. Represent a finite sum of pure tensors by a common denominator f^m. The numerator then lies in S tensor M_(md+j). Each graded inclusion M_i into M has a projection, so it stays injective after tensoring, independently of flatness. An element of the base-changed localization vanishes exactly when some power of 1 tensor f kills that numerator. By the split graded inclusion this is an equality already in S tensor M_((m+k)d+j), so the tensor of the corresponding transition to the larger denominator is zero. This proves injectivity; every target fraction has a numerator in S tensor M_(md+j), proving surjectivity. The negative degrees are retained throughout; no bounded-below assumption on M is used. This argument belongs to the report, not the statement-only node.

In step 1 I opened and read the scalar-extension Proj lemma: its statement actually supplies the inverse-image charts, their ring maps, the cover and uniqueness, not merely the Cartesian square. The twisting definition supplies the degree-j fractions. The graded-module sheaf theorem (c), applied to A(j) and B(j), supplies quasi-coherence. The pullback-quasi-coherent node supplies it for the source sheaf. The affine-sections node applies with V = D_+(f) and U = D_+(psi(f)), both affine, and its explicit unit formula identifies the source section module. This avoids treating the definition of pullback as an affine-sections theorem.

In step 2 I read the degree-zero localization node and used only its S-algebra isomorphism. The new module lemma supplies every integer degree for M = A. I wrote both directions of the intermediate tensor rearrangement and its balancing relations; then applying beta on fraction representatives gives the stated map for an arbitrary specified model B. No injectivity of R into S, no cancellation of f and no flatness is invoked. Neither node is being cited for its internal proof.

In step 3 I read the affine tilde--Gamma adjunction node, in particular the mapping bijection, isomorphic unit and isomorphic counit for quasi-coherent modules. I read its sources in schemes.tex: 01I7 (lemma-compare-constructions), 01IA (lemma-quasi-coherent-affine), and the pullback description 01I9 (lemma-widetilde-pullback). These statements turn an isomorphism of chart section modules into the specified isomorphism of the actual restricted sheaves; just a module bijection would not suffice.

In step 4 I used the actual restriction statement (a) of the graded-module sheaf theorem and the fraction restrictions in the twist definition. I added a citation of the standard-open-intersection node when checking that U_fg is the overlap. Its statement explicitly includes D_+(f) intersect D_+(g) = D_+(fg). The affine pullback-sections node shows the pulled sections and coefficients generate on that overlap, while affine adjunction detects the equality of sheaf maps there. The formula with g^e = hf checks arbitrary inclusions too. I read sheaves.tex's 04TN (lemma-glue-maps) and the module gluing node (1): that node supplies both existence and uniqueness of the global map. The inverse glues because the inverses of equal isomorphisms are equal. This is a genuine local calculation followed by gluing, not an assertion that the maps 'transport'.

In step 5 I opened the quasi-coherent tensor-product affine-sections node, which explicitly says its sheafification map is bijective on affine opens, and read schemes.tex 01I8 (lemma-widetilde-constructions). This justifies testing the sheaf multiplication diagram on pure chart tensors. I wrote the forward and inverse tensor rearrangements for the canonical pullback--tensor comparison. The common value ce psi(ab) / psi(f)^(m+n) proves multiplicativity. Degree zero and the unit are checked by their formulas, and homogeneous global sections by the twist definition's a/1 formula. The gluing node supplies equality globally. The multiplication maps themselves arise by the elementary bilinear fraction product, which respects each restriction and hence glues; no invertibility of any twist is assumed.

In step 6 the scalar-extension Proj statement's uniqueness and chart description prove the equality of scheme maps. The two ring tensor associators are written explicitly on pure tensors, so the associated graded-algebra map is chi psi. The module pullback definition explicitly includes the composition and identity isomorphisms. On each final chart the affine pullback-sections theorem identifies iterated pullback with triple tensors; the formula c chi(b) chi(psi(a)) / chi(psi(f))^m is the same for both composites. Affine adjunction and gluing uniqueness therefore prove equality as sheaf maps after the stated canonical comparison. The identity case is checked by u tensor c mapping to cu. This fills the omitted computation of 01MZ rather than citing that omission as a proof.

I checked delivery-errors B through E against the files: the new node is self-contained and statement-only, with its localization notion cited and its gradings and scalar action written out; its source names the tag and label and discloses the module refinement. Every mathematical tool used in a proof step is a node citation, with a verbatim quote in citations.json; I read those nodes' statements before using them. The balancing, fraction multiplication and associator formulas are the routine arguments written in the steps. No step is over 2000 characters. The non-elementary localized-piece identification has been extracted into its own algebra node. Off-unit statements used as general affine and sheaf tools are declared in split_report.tool_uses, not in the maintained tool_uses field. No route is replaced and no unit realization is changed.

Small-case checks: S = 0 or a zero graded ring gives empty Proj and zero chart modules; f = 0 or nilpotent gives zero localized modules and an empty standard open, and the formulas still hold. For A = R[x] with deg x = 2 and j odd, the localized degree-j module can be zero; no rank-one argument is used. For negative j, denominators may be increased until the numerator degree is nonnegative when M = A; the module lemma itself permits all negative degrees of M. The nonflat test R = Z, S = Z/2 uses the same killed-by-a-power criterion, not tensor preservation of a kernel. A_0 is allowed to strictly contain R. Taking S = R and then a further scalar extension checks that the specified associator is in the direction required in the statement. These checks found no missing hypothesis.

Searches were made through msearch.py with the actual query strings preserved. I read the returned IsLocalizedModule.rTensor at Mathlib/RingTheory/Localization/BaseChange.lean:244, the ungraded localization tensor equivalence there, and the grading construction in RingTheory/GradedAlgebra/TensorProduct.lean. They are useful inputs for a later proof of the new node, but none identifies the homogeneous localized degree-j pieces in one line. The first and second semantic phrasings and the homogeneous-localization source grep found no exact match. Blueprint searches for homogeneous localization, localized graded, twisting, scalar extension and the three source tags found no matching imported statement; DAG keyword searches were also inspected. The same-tag comparisons are recorded below.

## Not duplicates

lem-sfb-graded-module-localization-scalar-extension vs lem-per-excellent-quasiprojective-normalized-blowup: concerns projectivity of normalized blowups over excellent bases, not a graded-module tensor identity.

lem-sfb-graded-module-localization-scalar-extension vs def-nagata-graded-algebra-pullback-data: defines coefficientwise pullback data on affine base charts; the new node proves an isomorphism after homogeneous module localization.

lem-sfb-graded-module-localization-scalar-extension vs lem-nagata-affine-proj-scalar-extension: constructs the scalar-extension scheme morphism and Cartesian square, with degree-zero chart maps; it does not compare localized module pieces.

lem-sfb-graded-module-localization-scalar-extension vs lem-nagata-homogeneous-localization-scalar-extension: treats only the degree-zero localized R-algebra for M = A; the new node treats arbitrary Z-graded modules and every degree j. I reuse the existing ring case for its algebra structure.

lem-sfb-graded-module-localization-scalar-extension vs lem-nagata-proj-affine-restriction: compares Proj schemes under affine restriction of the base, and says nothing about localized graded-module pieces.

lem-sfb-graded-module-localization-scalar-extension vs prop-nagata-relative-proj-functoriality: states functoriality of relative Proj schemes, not homogeneous localized-module scalar extension.

lem-sfb-graded-module-localization-scalar-extension vs lem-wf-finite-field-curve-quasi-projective: proves quasi-projectivity of curves, not an algebraic localized-module identity.

lem-sfb-graded-module-localization-scalar-extension vs lem-sfb-fermat-finite-chart-cover: gives the two affine charts of a Fermat hypersurface map, finite freeness and base change; it does not concern arbitrary graded modules.

lem-sfb-graded-module-localization-scalar-extension vs lem-sfb-finite-branch-ample-descent: descends an ample line bundle through a finite modification and proves projectivity; it is not a graded-localization lemma.

lem-sfb-graded-module-localization-scalar-extension vs lem-sfb-flat-pullback-blowup-chart-restrictions: requires flatness and concerns Rees blowup charts and centre ideals; it has no arbitrary graded-module localized-degree assertion.

lem-sfb-graded-module-localization-scalar-extension vs lem-sfb-polynomial-quotient-proj-cartesian: identifies polynomial quotient Proj schemes and embeddings under base change, using the image of the pulled ideal; no arbitrary localized graded module appears.

lem-sfb-graded-module-localization-scalar-extension vs lem-sfb-polynomial-quotient-proj-presentation: constructs a projective polynomial quotient with a finite chart cover; it is a geometric presentation result.

lem-sfb-graded-module-localization-scalar-extension vs lem-sfb-proj-scalar-extension-twist-comparison: is the parent sheaf statement; the new lemma is its algebraic input and has no Proj, sheaf pullback, unit/multiplication, global sections or composition clause.

lem-sfb-graded-module-localization-scalar-extension vs lem-sfb-projective-field-coordinate-euler-polynomial: concerns Euler and Hilbert polynomials for projective schemes over a field, not localization and coefficients.

lem-sfb-graded-module-localization-scalar-extension vs lem-sfb-projective-twist-euler-section-uniqueness: concerns eventual cohomology vanishing and uniqueness of Euler polynomials, not a localization comparison.

lem-sfb-graded-module-localization-scalar-extension vs lem-sfb-relative-proj-twists-degree-opens: constructs relative-Proj twists and their degree-generated loci; it uses the parent item for transitions and does not state the algebraic input for general M.

lem-sfb-graded-module-localization-scalar-extension vs lem-pur-projective-bundle-base-change-coherence: concerns rank-n projective-bundle frame models and the degree-one tautological line; the new lemma covers all graded modules and every localized degree.

lem-sfb-graded-module-localization-scalar-extension vs lem-trf-free-projective-bundle-base-change-space: identifies a free symmetric-algebra Proj with base-change projective space; it has no arbitrary graded module.

lem-sfb-graded-module-localization-scalar-extension vs lem-trf-hilbert-samuel-near-normal-cone: concerns Hilbert-Samuel functions and a polynomial normal-cone presentation, not localized-module scalar extension.

lem-sfb-graded-module-localization-scalar-extension vs lem-trf-line-proj-chart-pullback: compares generator loci and maps associated with a line quotient under base change, not homogeneous pieces of an arbitrary localized graded module.

lem-sfb-graded-module-localization-scalar-extension vs lem-trf-local-proj-isomorphism-compatibility: gives scheme isomorphisms for graded algebra isomorphisms over a base and their invariance under degreewise unit rescaling, not coefficient tensor with localized module pieces.

lem-sfb-graded-module-localization-scalar-extension vs lem-trf-relative-proj-invertible-twist: compares projective bundles after tensoring the defining module by a line bundle; it does not state the algebraic localization comparison.

lem-sfb-graded-module-localization-scalar-extension vs lem-trf-symmetric-proj-normalized-descent: constructs the tautological line quotient for a symmetric algebra and its affine-base restrictions; the new lemma is purely algebraic and allows arbitrary graded modules.

Additional close keyword hits were checked: lem-per-finite-graded-module-dehomogenization proves finite generation of degree-zero fractions under finite-generation hypotheses; lem-kun-filtered-tensor-localization concerns filtered derived categories, not homogeneous ring localization. Neither subsumes the new node.

## Validation

The server check_dag reports no finding introduced by the sandbox or on its nodes. Server review_split reports PASS. The required full delivery dry run and push are run after this report is complete.
