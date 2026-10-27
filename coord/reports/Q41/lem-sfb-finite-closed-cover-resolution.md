# Repair of lem-sfb-finite-closed-cover-resolution

## Worker report

Files written: the item JSON and the four new statement-only JSON files below, all under dag/nodes/sec-six-functors-basics/. The item statement, statement dependencies, Lean record, provenance, and existing maintainer fields are preserved. No repository file was written and no git or compiler command was run locally. The sandbox initially contained only dispatcher marker files, so there was no retained report or search log to resume. The complete current repository item was copied as returned-item-baseline.json before editing; its old search records are retained on the item.

- lem-sfb-finite-closed-restriction-detection: statement; unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle, and logged Mathlib grep.
- lem-sfb-closed-intersection-vertex-contraction: statement; unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle, and logged Mathlib grep.
- lem-sfb-closed-restriction-signed-refinements: statement; unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle, and logged Mathlib grep.
- lem-sfb-closed-restriction-total-pullback: statement; unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle, and logged Mathlib grep.

Attachments: none. The project search by blueprint tag and by finite-closed-cover notions found no complete declaration under WeilConjectures/. The existing Sheaf.AlgebraicGeometry.FiniteClosedCoverResolution theorem ends in `by sorry`; its definitions and its proof docstring were read but are not finished proofs. No compiler was run.

WANTED: none. The existing Stacks source and the current blueprint source were available. No SGA source is used.

What was wrong: the returned split placed 8022 characters of proof in one item. This repair spreads its arguments among four independently claimable nodes; it does not alter the statement or replace the route. The existing baseline already has the corrected quasi-compact-morphism hypothesis for complementary opens, and this is retained. There is no new statement dispute. The blueprint ancestor command returns None because the inherited provenance chain has a null ancestor; the existing exact textual place and via chain are retained, with the item prepended for the new nodes, rather than inventing ancestry.

Unfinished mathematical work: the four new nodes deliberately have no proof steps, no proof dependencies, and null proof_origin. They are the next parallel jobs. Nothing required by this stage-1 repair is postponed beyond those statement-only children.

## New nodes and division of work

1. Finite closed restriction detection takes the localization induction of old step 3, the exact-inverse-image and homology input of old step 1, and the homology-detection inference of old step 6. It handles arbitrary coefficient ring sheaves and arbitrary finite closed families, including the empty family, without a Noetherian hypothesis.
2. Vertex contraction takes all affine-local comparison and locality work of old step 4, all the actual-unit comparison and sign-cancellation work of old step 5, and the intersection quasi-compactness/exactness setup of old step 1. It states the actual homotopy, not just vanishing of cohomology; no global exact closed-cover resolution is asserted.
3. Signed refinements takes the full construction, composite-unit identities, and d-squared cancellation of old step 2, and the sorting, duplicate cancellation and augmentation calculation in the refinement part of old step 8. Its result is a chain map with a specified formula, not a quasi-isomorphism theorem. It needs no covering hypothesis.
4. Total pullback takes the remaining pullback and parameter-diagram part of old step 8. The existing Lean docstring makes explicit its intermediate face-compatibility argument: precompose with the epimorphic closed unit. The statement retains this unit normalization, all-intersection comparisons, the diagonal-inclusion characterization, and the augmentation square before localization. It assumes comparisons are supplied, not an unrestricted closed-base-change theorem.

Old step 7 remains the assembly using the already-existing finite-strip row-augmentation node. Derived refinement independence follows by cancelling the two invertible augmentations; this short argument remains in the parent. No argument has been removed by compression.

## Review by Q41

I read proetale.tex Tag 09AH, label lemma-ses-associated-to-open, including the assumption that the complementary OPEN IMMERSION is a quasi-compact MORPHISM and the proof by affine weakly contractible test objects. I also read Tag 09AA, lemma-closed-immersion, and Tag 09BM, lemma-closed-immersion-complement-retrocompact-exact. These supply localization, the invertible closed counit and exact closed direct image, respectively, through the existing ringed-open-closed node. The finite induction, vertex homotopy, and refinement formulas are agent deductions; none is falsely attributed as the literal statement of 09AH. For totalization I read homology.tex Tag 0133, lemma-double-complex-gives-resolution, including its second-variable variant and finite-diagonal hypotheses. The blueprint file det-thm-sf-ctf-stability-direct-images.md, clause (3), is the same open-direct-image finiteness application as before; these nodes are technical support calculations, not a replacement for the unit route.

For parent step 1 I opened signed-refinements: its statement gives the exact alternating differential, the augmented complex, composition of restrictions, and the displayed equation with the actual units. For parent step 2 I opened vertex-contraction: it gives contraction only after restriction to a closed member on an affine chart, vanishing off the support, and the open-locality comparison. Detection then gives acyclicity on each chart, including the degree -1 term; the chart-locality clause gives exactness globally. I checked every complement after base change is the pullback of an original quasi-compact open, and each intersection complement is a finite union of such opens. No closed family is asserted to cover the pro-etale site.

For parent step 3 I opened lem-sc-finite-strip-row-augmentation: its statement asks for a commuting double complex with finitely many columns, the actual column-zero augmentation, and the row quasi-isomorphisms with precisely those components. The construction and preceding row exactness supply all three. The exactness of E_Z is a stated clause of vertex-contraction, so preservation of quasi-isomorphisms follows on homology, and two-out-of-three follows because isomorphisms of each homology object have that property. I opened def-weil-abstract-derived-category: localization at quasi-isomorphisms is exactly the universal property used to descend the two functors and their augmentation. No K-injective resolution, infinite product total, or unmentioned boundedness theorem is used.

For parent step 4 signed-refinements states both the actual chain map and its augmentation equation. In the derived category the formula Q(rho)=Q(alpha_W) Q(alpha_Z)^(-1) proves independence; cancellation is the entire additional argument. It also proves composition. For step 5 total-pullback states the unit-to-face implication, actual diagonal components, the total augmentation square, and its derived normalization. Its parameter-diagram conclusion is an identity of natural transformations on the whole small indexing category, not a claim checked at individual points. The arbitrary pullback g is used only with supplied comparisons; qcqs base change is invoked solely on affine charts in the contraction child.

I checked the new statements with m=1 (and with Z_1 a nonreduced thickening having the same underlying support), m=2, repeated closed members, empty intersections, Z empty, zero coefficient ring, and K=0. For detection with m=0 the covering hypothesis forces Z empty and j is the identity. For contraction at the bottom degree the closed counit is the inverse of the restricted augmentation; at the top degree insertion is zero where appropriate and the remaining deletion-insertion term is the identity. For a refinement with f constant, every positive-degree component is zero, and the only surviving differential terms cancel; sorting signs handle non-monotone f. For total pullback with g the identity and identity comparisons, the diagonal equations give the identity map, and uniqueness follows from the finite biproduct inclusions. No reduction, Noetherianity, constant coefficients, or global qcqs hypothesis is tacitly introduced.

I checked delivery-errors B through E: new nodes contain statements only with explicit data and TeX, definition references are recorded, and sources identify tags and labels while distinguishing deductions. All cited parent statements were read, not their proofs substituted for their statements; citations.json copies their literal text. Whole-DAG searches included 09AH, finite closed covers, closed detection, insertion homotopies, refinements, epimorphic units and totalization; whole-blueprint searches included closed cover, contractible, refinement, alternating, closed restriction, zero detection, totalization and epimorphic unit. The project Lean search and its existing sorry theorem do not close the item. The search services were called through msearch.py only: all actual queries are recorded, and the rate-limited LeanSearch query for total pullback is marked unavailable. I read the pertinent Mathlib sources: AlgebraicTopology/AlternatingFaceMapComplex.lean (finite ordered normalization is not supplied there), ExtraDegeneracy.lean lines 415 onward (requires an already supplied simplicial extra degeneracy), AlgebraicGeometry/Cover/Open.lean zero_of_zero_cover (structure-sheaf sections on OPEN covers), and Algebra/Homology/TotalComplex.lean lines 438 and 452 (total.mapIso and diagonal naturality presuppose the bicomplex map). These are ingredients, not one-line specializations proving the children.

The return had one requirement with several explicit parts. I repaired each: at least two new nodes (four added); comparable independent jobs (induction/detection, affine comparison/contraction, sign/refinement calculus, normalized pullback/totalization); every child is unsplit with no steps; the old item statement is byte-for-byte unchanged; the parent proof is under 3000 characters; and all eight old arguments are preserved verbatim below, with the allocation above. No parent proof step is longer than 2000 characters. There was no fresh reviewer or second worker, as the direct-delivery brief explicitly requests this signed self-review.

### Repair of landing return L (2026-10-22)

The returned delivery was mathematically approved but could not land because side completion had not been promoted to the live DAG. I treated this as a rebase-and-recheck order, not as permission to change maintainer completion flags. I first ran the required dry run of the retained split; it exited successfully at 8376b53947c. I compared returned-item-baseline.json, the retained sandbox item, and the current shared item: the saved baseline and current item are equal in every field; the retained split differs only in proof, proof_deps, and split_report. I rebuilt the item from the current live JSON and restored only those three worker-owned fields. In particular its current Lean record, reviewed_lean, reviewed, statement, statement dependencies and provenance survive byte-for-byte as JSON values. The four child ids are still absent from the live DAG, so they remain new statement-only nodes rather than conflicting edits. Promotion of the side completion remains L's operation.

I re-read both live proof citations in full. lem-sc-finite-strip-row-augmentation still requires an integer-indexed commuting double complex, column bound r, an actual total chain map through column zero, and row quasi-isomorphisms with specified zero components. Step 3 now explicitly specializes r=m, A=E_Z(K), and a_q=alpha_(K^q), and checks that the constructed total augmentation has exactly these components. Its source is now homology.tex Tag 0133's second-variable variant, rather than the unrelated blanket 09AH reference. def-weil-abstract-derived-category still defines localization at all quasi-isomorphisms; its unchanged localization clause is exactly what steps 3 and 4 use. Both live statements equal their retained verbatim citation quotes, so there is no changed cited theorem to accommodate. I nevertheless replaced the overlong full-statement quotations by the relevant verbatim clauses where possible, checking all ten (step,node) pairs against the current statements.

I also re-read the four retained child statements and every live definition or theorem in their statement dependencies. In particular def-weil-finite-type-morphism explicitly defines quasi-compactness of a MORPHISM, def-sfb-proetale-unit-normalized-adjunction fixes the actual unit, and the ringed-open-closed statement supplies exact closed direct image and the localization epimorphism. No child requires constant coefficients. Signed refinements supplies step 1's equations and step 4's chain and augmentation equations; vertex contraction supplies step 2's open-locality and local contractions and step 3's exact E_Z; finite detection supplies the acyclicity test; total pullback supplies step 5's all-intersection, diagonal, augmentation and parameter-diagram identities. Step 2 now states explicitly the finite-cover and quasi-compact-complement hypotheses after affine restriction. All four children still have empty proofs and proof dependencies, with the earlier detailed arguments and worker guidance retained below.

I re-read the local Stacks sources 09AA, 09BM, 09AH and 0133, as well as the current Lean theorem's docstring and final sorry. The fresh project-source search finds no exact finished WeilConjectures declaration: the topology finite-closed-cover theorem is a different cohomological-vanishing statement. I reused and read every recorded Mathlib search result, including the unavailable rate-limited query; no question or child statement changed, so there was no reason to fabricate or repeat a search. I checked the same edge cases again: m=1, empty support, repeated members, zero modules, and identity pullback. The r=m specialization includes m=1 without a bound or sign exception. The assembly remains below 3000 characters and every step below 2000. This repairs the return with explicit current-DAG proof and citation adjustments; it is not an unchanged re-push. On resumption, the required dry run found that step 3's 29-character exactness quote was below the delivery tool's 40-character minimum. I expanded it verbatim with the adjoining open-restriction sentence and verified all ten quotes against their current cited statements; the proof and node statements need no change.

### Current rebase and citation recheck (2026-10-22, resumed delivery)

The retained dry run completed normally at b35a3362ec4 with preflight passed. I compared all JSON fields of the saved returned baseline against the current shared item: there are no differences. I then reconstructed the sandbox item from the current JSON and restored only proof, proof_deps and split_report. All four child ids remain absent from the current shared DAG. Thus the delivery tool will build this retained work on its freshly fetched current base; no completion or review flag is being altered to bypass the side-to-live promotion that L owns.

I opened every current statement used by the five assembly steps: the four child statements, lem-sc-finite-strip-row-augmentation, and def-weil-abstract-derived-category. Their text still contains each retained quote verbatim; all ten step/node pairs are present. I also opened the current statement dependencies, especially the actual unit normalization, inverse-image coefficients, quasi-compact morphism definition, and ringed open/closed sequence. There is no changed cited statement requiring a substitution. The recorded searches and their logged result lists were read and retained, including the unavailable LeanSearch response; neither the four statement-only jobs nor their search questions changed.

The additional proof repair is in step 5. The pullback lemma's derived normalization requires invertible augmentations. The assembly now applies the earlier row and total argument to the pulled-back closed covering to obtain alpha', then uses the actual square tau g*(alpha)=alpha' c_Z. Because tau and c_Z are chain isomorphisms, two-out-of-three gives that g*(alpha) is a quasi-isomorphism. This supplies the normalization hypothesis explicitly and avoids silently treating a chain-map comparison as an already justified derived inverse. The cover and quasi-compact complementary immersions persist under pullback; no new Noetherianity, constant coefficient or global qcqs assumption is introduced. Identity pullback and the singleton cover give the identity square, including the zero complex. This change stays within the approved construction and changes no target or child statement.

I re-read the local source lemmas 09AA, 09BM and 09AH and homology Tag 0133's second-variable variant, the current blueprint direct-image statement, and the current Lean theorem ending in sorry. The fresh exact blueprint-tag search in WeilConjectures gives no attachment; its finite-closed-cover cohomology-vanishing theorem is about vanishing on topological spaces, not the present augmented complex and its naturality. The assembly and every step remain within the required length limits. This is a current-base recheck with an explicit proof correction, not an unchanged re-push.

## Retained complete proof and worker guidance

The following is the complete pre-repair eight-step argument, copied verbatim from the current returned item before modification. It is retained here as worker guidance, not embedded in any unsplit child statement or proof. The allocation to children is above; the existing totalization result already carries old step 7's independent homological-algebra work.

### Old step 1

Write $E_T(M)=i_{T,*}i_T^*M$ for a closed subscheme $T$ among $Z$ and its intersections. The complement of $Z_J$ is the finite union of the complements of its members. A finite union of quasi-compact open immersions is quasi-compact: over an affine test open it is a finite union of quasi-compact inverse images. Base change preserves closed immersions and quasi-compactness. Thus the cited closed/open localization sequence and exact closed direct image apply to every intersection and every open restriction used below. Geometric inverse image with the inverse-image coefficient ring is exact, so every $E_T$ is exact. The module category is abelian; kernels are sectionwise and cokernels are sheafified sectionwise cokernels. In particular homology may be checked after exact inverse image.

Cited nodes: lem-weil-pbc-closed-immersion-base-change, lem-pc-quasi-compact-base-change, lem-weil-pbc-proetale-ringed-open-closed, lem-trf-geometric-inverse-image-exact, def-weil-sheaf-of-modules-category, lem-sp-exact-functor-preserves-homology.

### Old step 2

For a module $M$, put $C^p(M)=\bigoplus_{|J|=p+1}E_{Z_J}(M)$ for $0\le p<m$, and put $C^{-1}(M)=E_Z(M)$. For $J\subset L$ the component $r_{J,L}$ is the unit for $Z_L\hookrightarrow Z_J$ pushed to $X$, using the inverse-image composition comparison. Define $r_{Z,J}$ the same way. The composite-adjunction unit formula gives $r_{L,H}r_{J,L}=r_{J,H}$ and $r_{Z,J}\eta_i=\eta_{i_J}$. For an increasing tuple $L=(a_0,\ldots,a_{p+1})$, define $(dc)_L=\sum_t(-1)^t r_{L\setminus\{a_t\},L}c_{L\setminus\{a_t\}}$; the augmentation is $(r_{Z,\{a\}})_a$. Every term of $d^2$ occurs twice, with opposite signs and the same composite restriction; the augmented composite is likewise zero. This defines the actual augmented complex, natural in $M$, and already proves its asserted equation after composition with $M\to E_Z(M)$.

Cited nodes: def-weil-pbc-composite-adjunction, def-weil-proetale-inverse-image, lem-weil-pbc-left-exact-site-inverse-image-tensor.

### Old step 3

The following zero detection is proved by induction on the number of closed members, allowing zero members in this induction. Suppose $N$ restricts to zero on $X\setminus Z$ and on every $Z_a$. For zero members, $Z$ is empty, so the first restriction is $N$ itself. For a nonempty family let $V=X\setminus Z_1$. Localization for $Z_1$ and $i_1^*N=0$ give $N\cong j_{V,!}j_V^*N$. In $V$ the closed subscheme $Z\times_XV$ is covered by $Z_a\times_XV$ for $a>1$. Their complements are base changes of the original complementary opens, hence quasi-compact. The restriction of $j_V^*N$ to each is the further inverse image of $i_a^*N=0$, by inverse-image composition; it also vanishes off $Z\times_XV$. The induction hypothesis in $V$ gives $j_V^*N=0$, hence $N=0$. This argument uses actual open and closed restrictions, without asserting that the closed family covers the pro-etale site.

Cited nodes: lem-weil-pbc-proetale-ringed-open-closed, lem-pc-quasi-compact-base-change, lem-weil-pbc-closed-immersion-base-change, def-weil-proetale-inverse-image, lem-weil-pbc-left-exact-site-inverse-image-tensor.

### Old step 4

We can test exactness of the augmented complex Zariski locally on $X$. Indeed restriction to an open is exact; on an object $W\to X$ its restriction evaluates on $W\times_XV$, so direct image by a closed immersion commutes with this restriction by the defining formula $i_*G(W)=G(W\times_XT)$. Inverse-image compositions agree by the adjunction comparison, compatibly with units. These identifications are linear for the inverse-image rings, since all actions are restricted through the same ring maps. A sheaf vanishing on an affine open cover vanishes: pull the cover back to each $W$, and apply the separatedness part of the sheaf axiom to every section. Applying this to the homology sheaves reduces to affine $X$. There $X$, each closed $Z_J$, and each $Z_a$ are qcqs. Consequently the existing arbitrary-ring-sheaf closed base-change theorem applies to $g=i_a:Z_a\to X$ and $i_J$, with all its qcqs and quasi-compact-complement hypotheses verified. Its operations are the same module actions and adjunctions as ours.

Cited nodes: def-weil-proetale-inverse-image, lem-weil-pbc-left-exact-site-inverse-image-tensor, lem-trf-geometric-inverse-image-exact, lem-sp-exact-functor-preserves-homology, def-weil-pbc-proetale-site, lem-sf-ring-sheaf-base-change-mates, def-sf-proetale-ring-sheaf-operations.

### Old step 5

Fix $a$ on the affine base. Closed base change identifies $i_a^*E_{Z_J}(M)$ with the closed direct image on $Z_a$ from $Z_{J\cup\{a\}}$ of the restriction of $M_a=i_a^*M$; it identifies $i_a^*E_Z(M)$ with $M_a$. The beta transpose equation in the cited base-change theorem, together with the composite-adjunction unit formula, identifies each restricted $r_{J,L}$ with the actual restriction between these intersections: its transpose is the same inverse-image compositor followed by the same counit. When $a\notin J$, the arrow from $J$ to $J\cup\{a\}$ is therefore an isomorphism after restriction, because both intersections are identical and the identity-adjunction unit is the identity. Define $h$ from degree $p$ to degree $p-1$ by the component from $J\cup\{a\}$ to $J$ with sign $(-1)^{\#\{b\in J:b<a\}}$ and the inverse of that isomorphism when $a\notin J$, and zero when $a\in J$. For $J=\varnothing$ this is the singleton-$a$ component followed by the closed counit, with target $M_a$ in degree $-1$. In $dh+hd$, the insert/delete-$a$ term is the identity. Every other term appears twice: deleting $b<a$ changes the insertion position by one, and deleting $b>a$ changes its deletion position by one, so the signs are opposite; commutativity of restrictions makes the two maps equal. Thus $dh+hd=1$ in all degrees, including $-1$ and the top degree. The restricted augmented complex is contractible, hence exact.

Cited nodes: lem-sf-ring-sheaf-base-change-mates, def-weil-pbc-composite-adjunction, lem-weil-pbc-proetale-ringed-open-closed.

### Old step 6

On $X\setminus Z$, every term of the augmented complex vanishes: in the direct-image evaluation formula its closed fibre is empty, whose module sections are zero. For every homology sheaf $H$ of the augmented complex, exactness of inverse images and preservation of homology give $H|_{X\setminus Z}=0$ and $i_a^*H=0$ by the preceding contraction. Step 3 therefore gives $H=0$. This proves exactness of $0\to E_Z(M)\to C^0(M)\to\cdots\to C^{m-1}(M)\to0$, for every module $M$. Equivalently its canonical map $E_Z(M)[0]\to C^{\geq0}(M)$ is a quasi-isomorphism.

Cited nodes: def-weil-proetale-inverse-image, lem-trf-geometric-inverse-image-exact, lem-sp-exact-functor-preserves-homology.

### Old step 7

Apply the construction to every term $K^q$. Naturality of all units makes the horizontal differentials commute with $d_K$. Form the finite-strip total with summands $C^{p}(K^q)$, $p+q=n$, and differential $d_C+(-1)^p d_K$; its augmentation from $E_Z(K)$ has components in column zero. There are only $m$ columns, so every diagonal is finite. Step 6 supplies exactly the row quasi-isomorphisms, with their specified zero components, required by the finite-strip row-augmentation lemma. That lemma proves that the augmentation of total complexes is a quasi-isomorphism. This works in particular for the stipulated bounded-below $K$. Because $E_Z$ is exact, it preserves quasi-isomorphisms. The natural augmentation square and two-out-of-three then show that the total functor also preserves quasi-isomorphisms. The definition of the derived category as localization therefore gives the claimed natural isomorphism in the ordinary derived category.

Cited nodes: lem-sc-finite-strip-row-augmentation, lem-weil-pbc-proetale-ringed-open-closed, lem-trf-geometric-inverse-image-exact, lem-sp-exact-functor-preserves-homology, def-weil-abstract-derived-category.

### Old step 8

A refinement means a finer ordered closed family $W_b$ together with a function $f$ and factorizations $W_b\to Z_{f(b)}$ over $Z$. For an increasing tuple $(b_0,\ldots,b_p)$, the component of the refinement map is the restriction from the tuple $(f(b_0),\ldots,f(b_p))$: it is zero if an index repeats, and otherwise is the sign of its sorting permutation times restriction from its underlying intersection. If there are no repetitions, deleting an index gives precisely the same sign on both sides of the chain-map equation. If there are repetitions, terms with still-repeated indices vanish; the only possible remaining two terms delete one of a duplicated pair and cancel with opposite signs. Thus refinement is a chain map. Its composite with the augmentation is the finer augmentation, by the composite-unit formula. Both augmentations are invertible in the derived category, so this identity also characterizes the derived refinement map uniquely; it proves independence of the refinement function and compatibility with iterated refinements. For any supplied pullback comparisons identifying closed restrictions and their units, exact inverse image commutes with the finite sums and the two differentials, so componentwise the augmentation square commutes. The same is true for maps of $K$. These are identities of natural transformations on the whole diagram, hence also after applying the constructions to a parameterized diagram. In particular automorphisms, including families of them, preserve the derived identification; no passage to individual parameter points occurs.

Cited nodes: def-weil-pbc-composite-adjunction, lem-trf-geometric-inverse-image-exact, def-weil-abstract-derived-category.

### Pullback normalization detail retained from the existing Lean docstring

For each face E_T -> E_S, compare c_S g*(r) with r' c_T. Precompose both with g*(eta_T). The composite-unit formula r eta_T = eta_S and the given unit equations make both composites eta'_S. The closed unit eta_T is epic by the localization short exact sequence, and exact g* preserves that epimorphism. Hence the two face maps agree. Finite sums of c_J therefore form the row chain isomorphism sigma, with augmentation square given by c_Z. Exact inverse image preserves every finite diagonal sum. The induced total chain map tau has on each g*(iota_{p,q}) precisely iota'_{p,q} sigma^p_{K^q}; these inclusions jointly determine it. The differential d_D+(-1)^p d_K commutes because sigma is both a horizontal chain map and natural in K^q. Totalizing the augmentation square and then localizing yields the displayed normalization of Q(tau). All equations are natural in compatible diagrams, so this is also the proof for parameterized automorphisms.

## Not duplicates

lem-sfb-finite-closed-restriction-detection vs det-lem-formal-closed-support-sheaves: existing node is 'Sections with support: the sheaf-level adjunction'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs det-prop-closed-adjoint-constructible-support: existing node is 'Sections with support of a constructible complex are constructible'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs det-sf-comp-coherence-refinement: existing node is 'The refinement map on the localizing category'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs det-sf-comp-composition-base-change: existing node is 'Base change for $Rf_!$ on the localizing category'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs det-sf-comp-composition-interchange: existing node is 'Interchanging proper direct image and extension by zero'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sf-finite-immersion-constructibility-interval: existing node is 'Finite constructibility partitions and unchanged intervals for immersion restriction and closed direct image'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sf-open-finite-constructibility-interval: existing node is 'Open extension preserves finite constructibility and its cohomological interval'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sf-proetale-open-closed-sequence: existing node is 'Open-closed short exact sequence on the pro-etale site'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sf-ring-sheaf-closed-localization: existing node is 'Closed localization for arbitrary pro-etale ring-sheaf module objects'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sf-ringed-closed-kernel-adjoint: existing node is 'The support-kernel adjoint for an arbitrary pro-etale ring sheaf'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sf-ringed-open-roos-preservation: existing node is 'Ringed pro-etale open extension preserves products and Roos triangles'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-adic-stratum-cover-conservativity: existing node is 'Algebraic inverse images on stratum covering slices jointly reflect derived isomorphisms'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-closed-supported-scalar-comparison: existing node is 'Supported closed-unit construction and normalization of scalar comparison'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-condensed-support-derived-localization: existing node is 'Open/closed localization for ordinary derived condensed module objects'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-condensed-support-projection-formula: existing node is 'Natural support tensor projection formulas on unbounded condensed modules'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-exact-open-closed-unbounded-calculus: existing node is 'Unbounded support calculus from exact abelian open/closed localization data'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-finite-closed-cover-resolution: existing node is 'Finite closed-cover resolution with its actual adjunction augmentation'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-integral-bounded-stratum-base-change: existing node is 'Bounded ambient base change for integral stratum extension'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-internal-open-extension-disjoint-vanishing: existing node is 'Disjoint pullback of internal module extension by zero vanishes'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-locally-closed-extension-coherence: existing node is 'Restriction and composition for locally closed extension by zero'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-locally-closed-module-extension-coherence: existing node is 'Normalized locally closed extension on module sheaves'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-open-closed-flatness: existing node is 'Flatness detected on a complementary open and closed pair'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-open-filtration-successor: existing node is 'Natural quotient for two nested open module pieces'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-proetale-fixed-scalar-zero-detection: existing node is 'Complementary restrictions detect zero fixed-scalar pro-etale sheaves'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-proetale-identified-open-closed: existing node is 'Exact open and closed extensions with identified inverse-image coefficients'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-proetale-identified-supported-reconstruction: existing node is 'Normalized supported reconstruction for actual tensor pullbacks'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-proetale-locally-closed-extension: existing node is 'Pointwise exact locally closed extension'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-proetale-open-disjoint-direct-image: existing node is 'Direct image restricts to zero on a disjoint pro-etale open'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-proetale-supported-reconstruction: existing node is 'Normalized reconstruction from two successive support conditions'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-weil-pbc-closed-immersion-scalar-change: existing node is 'Ordinary closed scalar change with transported coefficients'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-weil-pbc-condensed-open-closed-recollement: existing node is 'Open/closed recollement for condensed coefficient modules'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-weil-pbc-continuous-constructible-supported: existing node is 'Constructibility of supported continuous modules'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-weil-pbc-continuous-module-localization: existing node is 'Localization for the actual continuous module functors'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-weil-pbc-integral-model-open-closed-pieces: existing node is 'Integral open and closed pieces remain constructible and rationalize to the localization sequence'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-weil-pbc-localization-equivalence-transport: existing node is 'Localization transports across equivalent supported categories'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-weil-pbc-noetherian-stratum-detection: existing node is 'Finite stratified restrictions detect pro-etale sheaves'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-weil-pbc-proetale-abelian-closed-support: existing node is 'Closed support for abelian pro-etale sheaves'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-weil-pbc-proetale-closed-underived-projection: existing node is 'Underived tensor projection for closed pro-etale immersions with arbitrary ring coefficients'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-weil-pbc-proetale-ringed-localization-sequence: existing node is 'Ringed local open-closed short exact sequence'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-weil-pbc-proetale-ringed-open-closed: existing node is 'Ringed pro-etale open-closed localization'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs lem-weil-pbc-wcontractible-closed-localization: existing node is 'Closed localization of a w-contractible ring'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs new-lem-weil-pbc-condensed-finite-model-immersion-restriction: existing node is 'finite model on immersion range'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs new-lem-weil-pbc-condensed-surjective-closed-equivalence: existing node is 'condensedSurjectiveClosedPullback isEquivalence'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-finite-closed-restriction-detection vs new-lem-weil-pbc-condensed-surjective-closed-local-presentation: existing node is 'lfp lowerStar of surjective closed'; this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance.

lem-sfb-closed-intersection-vertex-contraction vs def-sfb-proetale-unit-normalized-adjunction: existing node is 'Unit-normalized adjunction for pro-etale module inverse image'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs det-formal-closed-support-ii-left-exact: existing node is 'Left $t$-exactness of sections with closed support'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs det-formal-closed-support-ii-limits: existing node is 'Closed support commutes with derived limits of sequences'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs det-lem-formal-closed-support-sheaves: existing node is 'Sections with support: the sheaf-level adjunction'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs det-lem-int-ext-bound: existing node is 'Uniform vanishing of Ext between integral constructible sheaves'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs det-prop-closed-adjoint-constructible-support: existing node is 'Sections with support of a constructible complex are constructible'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs det-proper-heart-bound-lattice: existing node is 'The lattice bound $2d+1$'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs det-sf-comp-coherence-refinement: existing node is 'The refinement map on the localizing category'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs det-sf-comp-composition-base-change: existing node is 'Base change for $Rf_!$ on the localizing category'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs det-sf-comp-composition-interchange: existing node is 'Interchanging proper direct image and extension by zero'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs det-sfb-dc-restricted-functors-closed-image: existing node is 'Extension by zero and closed direct image preserve integral constructible complexes'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs det-uniform-constructible-ext-integral: existing node is 'The integral stratum bound'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-cbc-extension-zero-stratified-perfect: existing node is 'Extension by zero preserves stratified perfect local models'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-formal-closed-pullback-derived-products: existing node is 'Closed coefficient-compatible pullback preserves derived products'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-pur-closed-support-exceptional-comparison: existing node is 'Comparison of closed support with the transported finite exceptional value'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sf-finite-immersion-constructibility-interval: existing node is 'Finite constructibility partitions and unchanged intervals for immersion restriction and closed direct image'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sf-open-finite-constructibility-interval: existing node is 'Open extension preserves finite constructibility and its cohomological interval'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sf-proetale-open-closed-sequence: existing node is 'Open-closed short exact sequence on the pro-etale site'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sf-ring-sheaf-closed-localization: existing node is 'Closed localization for arbitrary pro-etale ring-sheaf module objects'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sf-ringed-closed-kernel-adjoint: existing node is 'The support-kernel adjoint for an arbitrary pro-etale ring sheaf'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sf-ringed-open-roos-preservation: existing node is 'Ringed pro-etale open extension preserves products and Roos triangles'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-adic-stratum-cover-conservativity: existing node is 'Algebraic inverse images on stratum covering slices jointly reflect derived isomorphisms'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-closed-support-bounded-continuity: existing node is 'Bounded-below continuity for open direct image and closed support'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-closed-supported-scalar-comparison: existing node is 'Supported closed-unit construction and normalization of scalar comparison'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-condensed-support-derived-localization: existing node is 'Open/closed localization for ordinary derived condensed module objects'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-condensed-support-projection-formula: existing node is 'Natural support tensor projection formulas on unbounded condensed modules'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-exact-open-closed-unbounded-calculus: existing node is 'Unbounded support calculus from exact abelian open/closed localization data'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-finite-closed-cover-resolution: existing node is 'Finite closed-cover resolution with its actual adjunction augmentation'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-integral-bounded-stratum-base-change: existing node is 'Bounded ambient base change for integral stratum extension'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-internal-open-extension-disjoint-vanishing: existing node is 'Disjoint pullback of internal module extension by zero vanishes'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-local-integral-perfect-model-cohomology: existing node is 'Cohomology of a local integral perfect scalar model'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-locally-closed-extension-coherence: existing node is 'Restriction and composition for locally closed extension by zero'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-locally-closed-module-extension-coherence: existing node is 'Normalized locally closed extension on module sheaves'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-normalized-immersion-comparison-coherence: existing node is 'Coherence of comparison maps normalized on an immersion image'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-open-closed-flatness: existing node is 'Flatness detected on a complementary open and closed pair'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-open-filtration-successor: existing node is 'Natural quotient for two nested open module pieces'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-proetale-fixed-scalar-zero-detection: existing node is 'Complementary restrictions detect zero fixed-scalar pro-etale sheaves'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-proetale-identified-open-closed: existing node is 'Exact open and closed extensions with identified inverse-image coefficients'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-proetale-identified-supported-reconstruction: existing node is 'Normalized supported reconstruction for actual tensor pullbacks'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-proetale-locally-closed-extension: existing node is 'Pointwise exact locally closed extension'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-proetale-open-disjoint-direct-image: existing node is 'Direct image restricts to zero on a disjoint pro-etale open'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-proetale-supported-reconstruction: existing node is 'Normalized reconstruction from two successive support conditions'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-closed-immersion-scalar-change: existing node is 'Ordinary closed scalar change with transported coefficients'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-condensed-open-closed-recollement: existing node is 'Open/closed recollement for condensed coefficient modules'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-continuous-constructible-supported: existing node is 'Constructibility of supported continuous modules'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-continuous-module-localization: existing node is 'Localization for the actual continuous module functors'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-integral-model-open-closed-pieces: existing node is 'Integral open and closed pieces remain constructible and rationalize to the localization sequence'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-localization-equivalence-transport: existing node is 'Localization transports across equivalent supported categories'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-noetherian-stratum-detection: existing node is 'Finite stratified restrictions detect pro-etale sheaves'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-proetale-abelian-closed-counit: existing node is 'The closed counit on abelian pro-etale sheaves'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-proetale-abelian-closed-support: existing node is 'Closed support for abelian pro-etale sheaves'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-proetale-closed-underived-projection: existing node is 'Underived tensor projection for closed pro-etale immersions with arbitrary ring coefficients'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-proetale-immersion-limit-preservation: existing node is 'Inverse images along immersions preserve pro-etale limits'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-proetale-inverse-image-limits-zariski-local: existing node is 'Zariski locality of preservation of pro-etale inverse-image limits'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-proetale-restriction-preserves-limits: existing node is 'Limits preserved by weakly etale pro-etale restriction'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-proetale-ringed-closed-counit: existing node is 'Closed ringed counit is invertible'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-proetale-ringed-localization-sequence: existing node is 'Ringed local open-closed short exact sequence'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-proetale-ringed-open-closed: existing node is 'Ringed pro-etale open-closed localization'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs lem-weil-pbc-wcontractible-closed-localization: existing node is 'Closed localization of a w-contractible ring'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs new-lem-weil-pbc-condensed-finite-model-immersion-restriction: existing node is 'finite model on immersion range'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs new-lem-weil-pbc-condensed-surjective-closed-equivalence: existing node is 'condensedSurjectiveClosedPullback isEquivalence'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs new-lem-weil-pbc-condensed-surjective-closed-local-presentation: existing node is 'lfp lowerStar of surjective closed'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs sk-lem-formal-closed-support-ii: existing node is 'Closed support, truncation and derived limits'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs sk-lem-int-ext: existing node is 'Continuity and boundedness of Ext'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs sk-lem-int-tensor: existing node is 'Inverse image and tensor product'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs sk-lem-proper-heart-bound: existing node is 'A uniform bound for proper direct image'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-intersection-vertex-contraction vs sk-lem-uniform-constructible-ext: existing node is 'Uniform Ext bound'; this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison.

lem-sfb-closed-restriction-signed-refinements vs det-lem-formal-closed-support-sheaves: existing node is 'Sections with support: the sheaf-level adjunction'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs det-prop-closed-adjoint-constructible-support: existing node is 'Sections with support of a constructible complex are constructible'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs det-sf-comp-coherence-refinement: existing node is 'The refinement map on the localizing category'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs det-sf-comp-composition-base-change: existing node is 'Base change for $Rf_!$ on the localizing category'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs det-sf-comp-composition-interchange: existing node is 'Interchanging proper direct image and extension by zero'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sf-finite-immersion-constructibility-interval: existing node is 'Finite constructibility partitions and unchanged intervals for immersion restriction and closed direct image'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sf-open-finite-constructibility-interval: existing node is 'Open extension preserves finite constructibility and its cohomological interval'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sf-proetale-open-closed-sequence: existing node is 'Open-closed short exact sequence on the pro-etale site'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sf-ring-sheaf-closed-localization: existing node is 'Closed localization for arbitrary pro-etale ring-sheaf module objects'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sf-ringed-closed-kernel-adjoint: existing node is 'The support-kernel adjoint for an arbitrary pro-etale ring sheaf'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sf-ringed-open-roos-preservation: existing node is 'Ringed pro-etale open extension preserves products and Roos triangles'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-adic-stratum-cover-conservativity: existing node is 'Algebraic inverse images on stratum covering slices jointly reflect derived isomorphisms'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-closed-supported-scalar-comparison: existing node is 'Supported closed-unit construction and normalization of scalar comparison'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-condensed-support-derived-localization: existing node is 'Open/closed localization for ordinary derived condensed module objects'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-condensed-support-projection-formula: existing node is 'Natural support tensor projection formulas on unbounded condensed modules'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-exact-open-closed-unbounded-calculus: existing node is 'Unbounded support calculus from exact abelian open/closed localization data'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-finite-closed-cover-resolution: existing node is 'Finite closed-cover resolution with its actual adjunction augmentation'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-integral-bounded-stratum-base-change: existing node is 'Bounded ambient base change for integral stratum extension'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-internal-open-extension-disjoint-vanishing: existing node is 'Disjoint pullback of internal module extension by zero vanishes'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-locally-closed-extension-coherence: existing node is 'Restriction and composition for locally closed extension by zero'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-locally-closed-module-extension-coherence: existing node is 'Normalized locally closed extension on module sheaves'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-open-closed-flatness: existing node is 'Flatness detected on a complementary open and closed pair'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-open-filtration-successor: existing node is 'Natural quotient for two nested open module pieces'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-proetale-fixed-scalar-zero-detection: existing node is 'Complementary restrictions detect zero fixed-scalar pro-etale sheaves'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-proetale-identified-open-closed: existing node is 'Exact open and closed extensions with identified inverse-image coefficients'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-proetale-identified-supported-reconstruction: existing node is 'Normalized supported reconstruction for actual tensor pullbacks'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-proetale-locally-closed-extension: existing node is 'Pointwise exact locally closed extension'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-proetale-open-disjoint-direct-image: existing node is 'Direct image restricts to zero on a disjoint pro-etale open'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-sfb-proetale-supported-reconstruction: existing node is 'Normalized reconstruction from two successive support conditions'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-weil-pbc-closed-immersion-scalar-change: existing node is 'Ordinary closed scalar change with transported coefficients'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-weil-pbc-condensed-open-closed-recollement: existing node is 'Open/closed recollement for condensed coefficient modules'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-weil-pbc-continuous-constructible-supported: existing node is 'Constructibility of supported continuous modules'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-weil-pbc-continuous-module-localization: existing node is 'Localization for the actual continuous module functors'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-weil-pbc-integral-model-open-closed-pieces: existing node is 'Integral open and closed pieces remain constructible and rationalize to the localization sequence'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-weil-pbc-localization-equivalence-transport: existing node is 'Localization transports across equivalent supported categories'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-weil-pbc-noetherian-stratum-detection: existing node is 'Finite stratified restrictions detect pro-etale sheaves'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-weil-pbc-proetale-abelian-closed-support: existing node is 'Closed support for abelian pro-etale sheaves'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-weil-pbc-proetale-closed-underived-projection: existing node is 'Underived tensor projection for closed pro-etale immersions with arbitrary ring coefficients'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-weil-pbc-proetale-ringed-localization-sequence: existing node is 'Ringed local open-closed short exact sequence'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-weil-pbc-proetale-ringed-open-closed: existing node is 'Ringed pro-etale open-closed localization'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs lem-weil-pbc-wcontractible-closed-localization: existing node is 'Closed localization of a w-contractible ring'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs new-lem-weil-pbc-condensed-finite-model-immersion-restriction: existing node is 'finite model on immersion range'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs new-lem-weil-pbc-condensed-surjective-closed-equivalence: existing node is 'condensedSurjectiveClosedPullback isEquivalence'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-signed-refinements vs new-lem-weil-pbc-condensed-surjective-closed-local-presentation: existing node is 'lfp lowerStar of surjective closed'; this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution.

lem-sfb-closed-restriction-total-pullback vs def-sc-finite-strip-cone-graded-map: existing node is 'Canonical surviving diagonal map into the graded cone'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs def-weil-pbc-etale-filtered-step-cohomology-iso: existing node is 'Canonical filtered-step derived-cohomology comparison'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs def-weil-pbc-etale-restricted-augmentation: existing node is 'Explicit restricted augmented-total map'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs def-weil-pbc-etale-restricted-sections-lift: existing node is 'Canonical lift through the monic filtered-step inclusion'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs def-weil-pbc-etale-restricted-total-construction: existing node is 'Concrete restricted CE total and sections inclusion'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs det-lem-formal-closed-support-sheaves: existing node is 'Sections with support: the sheaf-level adjunction'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs det-prop-closed-adjoint-constructible-support: existing node is 'Sections with support of a constructible complex are constructible'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs det-sf-comp-coherence-refinement: existing node is 'The refinement map on the localizing category'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs det-sf-comp-composition-base-change: existing node is 'Base change for $Rf_!$ on the localizing category'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs det-sf-comp-composition-interchange: existing node is 'Interchanging proper direct image and extension by zero'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-pbc-additive-cech-beta-quasi-iso: existing node is 'Fixed affine additive coefficient augmentation quasi-isomorphism'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-pc-abelian-cech-alpha-quasi-iso: existing node is 'The explicit abelian Čech section augmentation is a quasi-isomorphism'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sc-finite-strip-cone-filtration: existing node is 'Finite-strip augmentation cone filtration and row-cone graded homology'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sc-finite-strip-cone-filtration-graded: existing node is 'Finite-strip cone graded homology comparison'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sc-finite-strip-cone-filtration-graded-point: existing node is 'Finite-strip cone diagonal three-term comparison'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sc-finite-strip-cone-filtration-steps: existing node is 'Finite-strip cone filtration steps'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sc-finite-strip-cone-graded-map-differential: existing node is 'Differential commutation of the surviving diagonal map'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sc-finite-strip-cone-graded-map-epi: existing node is 'Finite-strip graded map is epi'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sc-finite-strip-cone-graded-map-isIso: existing node is 'Invertibility of the surviving diagonal map'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sc-finite-strip-cone-graded-map-mono: existing node is 'Finite-strip graded map is mono'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sc-finite-strip-cone-graded-map-split-epi: existing node is 'Finite-strip row map is epic onto the filtration step'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sc-finite-strip-row-augmentation: existing node is 'Finite horizontal strip row augmentation induces a total quasi-isomorphism'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sc-first-quadrant-column-augmentation: existing node is 'A first-quadrant resolution-column augmentation induces a total quasi-isomorphism'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sc-first-quadrant-total-column-comparison: existing node is 'Columnwise quasi-isomorphisms induce first-quadrant total quasi-isomorphisms'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sf-finite-immersion-constructibility-interval: existing node is 'Finite constructibility partitions and unchanged intervals for immersion restriction and closed direct image'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sf-open-finite-constructibility-interval: existing node is 'Open extension preserves finite constructibility and its cohomological interval'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sf-proetale-open-closed-sequence: existing node is 'Open-closed short exact sequence on the pro-etale site'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sf-ring-sheaf-closed-localization: existing node is 'Closed localization for arbitrary pro-etale ring-sheaf module objects'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sf-ringed-closed-kernel-adjoint: existing node is 'The support-kernel adjoint for an arbitrary pro-etale ring sheaf'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sf-ringed-open-roos-preservation: existing node is 'Ringed pro-etale open extension preserves products and Roos triangles'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-adic-stratum-cover-conservativity: existing node is 'Algebraic inverse images on stratum covering slices jointly reflect derived isomorphisms'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-closed-supported-scalar-comparison: existing node is 'Supported closed-unit construction and normalization of scalar comparison'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-condensed-support-derived-localization: existing node is 'Open/closed localization for ordinary derived condensed module objects'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-condensed-support-projection-formula: existing node is 'Natural support tensor projection formulas on unbounded condensed modules'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-exact-open-closed-unbounded-calculus: existing node is 'Unbounded support calculus from exact abelian open/closed localization data'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-finite-closed-cover-resolution: existing node is 'Finite closed-cover resolution with its actual adjunction augmentation'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-integral-bounded-stratum-base-change: existing node is 'Bounded ambient base change for integral stratum extension'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-internal-open-extension-disjoint-vanishing: existing node is 'Disjoint pullback of internal module extension by zero vanishes'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-locally-closed-extension-coherence: existing node is 'Restriction and composition for locally closed extension by zero'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-locally-closed-module-extension-coherence: existing node is 'Normalized locally closed extension on module sheaves'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-open-closed-flatness: existing node is 'Flatness detected on a complementary open and closed pair'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-open-filtration-successor: existing node is 'Natural quotient for two nested open module pieces'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-proetale-fixed-scalar-zero-detection: existing node is 'Complementary restrictions detect zero fixed-scalar pro-etale sheaves'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-proetale-identified-open-closed: existing node is 'Exact open and closed extensions with identified inverse-image coefficients'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-proetale-identified-supported-reconstruction: existing node is 'Normalized supported reconstruction for actual tensor pullbacks'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-proetale-locally-closed-extension: existing node is 'Pointwise exact locally closed extension'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-proetale-open-disjoint-direct-image: existing node is 'Direct image restricts to zero on a disjoint pro-etale open'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-proetale-supported-reconstruction: existing node is 'Normalized reconstruction from two successive support conditions'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-cartan-eilenberg-augmentation-quasi-iso: existing node is 'Exact augmented resolution columns give a quasi-isomorphism to the total'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-cartan-eilenberg-cone-filtration: existing node is 'Pinned complex-degree filtration and column-cone graded cohomology'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-cartan-eilenberg-cone-filtration-data: existing node is 'Construction of pinned cone filtration steps'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-cartan-eilenberg-cone-filtration-data-steps: existing node is 'Explicit cone steps are antitone and differential-stable'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-cartan-eilenberg-cone-filtration-properties: existing node is 'Bounds and graded pieces of pinned cone filtration'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-cartan-eilenberg-cone-graded-augmentation-representative: existing node is 'Graded differential on retained augmentation representatives'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-cartan-eilenberg-cone-graded-hom-ext: existing node is 'Retained-column generators detect maps from the graded piece'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-cartan-eilenberg-cone-graded-normalized-differential: existing node is 'Adjacent differential compatibility of normalized column-cone maps'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-cartan-eilenberg-cone-graded-normalized-iso: existing node is 'Normalized degreewise quotient comparison for the augmented cone'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-cartan-eilenberg-cone-graded-resolution-representative: existing node is 'Graded differential on retained resolution representatives'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-cartan-eilenberg-cone-graded-short-complex-iso: existing node is 'Short-complex comparison for the graded augmented cone'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-cartan-eilenberg-cone-graded-split-injection: existing node is 'Normalized retained-column split injection'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-cartan-eilenberg-total-resolution: existing node is 'The augmented bounded-below injective bicomplex total is a K-injective resolution'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-sp-ce-total-injective-terms: existing node is 'First-quadrant finite-diagonal totals have injective terms'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-bounded-below-row-augmentation: existing node is 'Comparison of a row augmentation with a bounded-below total complex'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-bounded-below-total-column-comparison: existing node is 'Column and row comparison for uniformly bounded-below integer bicomplexes'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-closed-immersion-scalar-change: existing node is 'Ordinary closed scalar change with transported coefficients'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-condensed-open-closed-recollement: existing node is 'Open/closed recollement for condensed coefficient modules'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-continuous-constructible-supported: existing node is 'Constructibility of supported continuous modules'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-continuous-module-localization: existing node is 'Localization for the actual continuous module functors'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-etale-filtered-step-cohomology: existing node is 'Cohomology of a filtered CE step computes the fixed stupid truncation'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-etale-filtered-step-cohomology-compatibility: existing node is 'Compatibility of filtered-step cohomology isomorphism'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-etale-filtered-step-cohomology-iso: existing node is 'Existence of filtered-step cohomology isomorphism'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-etale-restricted-augmentation-comm: existing node is 'Restricted augmentation commutes with the differential'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-etale-restricted-augmentation-inclusion: existing node is 'Augmentation commutes with restricted total inclusion'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-etale-restricted-sections-comparison-map: existing node is 'Sections of the restricted resolution comparison'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-etale-restricted-sections-factors: existing node is 'Restricted sections inclusion factors through the filtered step'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-etale-restricted-sections-lift-component-isIso: existing node is 'Componentwise isomorphism of the restricted sections lift'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-etale-restricted-sections-lift-isIso: existing node is 'Canonical sections lift is invertible'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-etale-restricted-total-resolution: existing node is 'Restricted augmentation is a K-injective resolution'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-integral-model-open-closed-pieces: existing node is 'Integral open and closed pieces remain constructible and rationalize to the localization sequence'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-localization-equivalence-transport: existing node is 'Localization transports across equivalent supported categories'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-noetherian-stratum-detection: existing node is 'Finite stratified restrictions detect pro-etale sheaves'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-proetale-abelian-closed-support: existing node is 'Closed support for abelian pro-etale sheaves'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-proetale-closed-underived-projection: existing node is 'Underived tensor projection for closed pro-etale immersions with arbitrary ring coefficients'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-proetale-ringed-localization-sequence: existing node is 'Ringed local open-closed short exact sequence'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-proetale-ringed-open-closed: existing node is 'Ringed pro-etale open-closed localization'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs lem-weil-pbc-wcontractible-closed-localization: existing node is 'Closed localization of a w-contractible ring'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs new-lem-weil-pbc-condensed-finite-model-immersion-restriction: existing node is 'finite model on immersion range'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs new-lem-weil-pbc-condensed-surjective-closed-equivalence: existing node is 'condensedSurjectiveClosedPullback isEquivalence'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-closed-restriction-total-pullback vs new-lem-weil-pbc-condensed-surjective-closed-local-presentation: existing node is 'lfp lowerStar of surjective closed'; this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness.

lem-sfb-finite-closed-restriction-detection vs lem-exc-open-closed-detection: this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance; the existing statement has a different domain or conclusion and does not give this assertion by specialization.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-proetale-fixed-scalar-zero-detection: this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance; the existing statement has a different domain or conclusion and does not give this assertion by specialization.

lem-sfb-finite-closed-restriction-detection vs lem-weil-pbc-noetherian-stratum-detection: this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance; the existing statement has a different domain or conclusion and does not give this assertion by specialization.

lem-sfb-finite-closed-restriction-detection vs lem-sfb-adic-stratum-cover-conservativity: this child is finite-family conservativity/acyclicity for arbitrary ring sheaves on arbitrary schemes, including m=0; it is not two-piece localization, reconstruction, constructibility, or topological invariance; the existing statement has a different domain or conclusion and does not give this assertion by specialization.

lem-sfb-closed-intersection-vertex-contraction vs lem-sf-ring-sheaf-base-change-mates: this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison; the existing statement has a different domain or conclusion and does not give this assertion by specialization.

lem-sfb-closed-intersection-vertex-contraction vs lem-sfb-cech-localization-unit-totalization: this child supplies affine all-intersection base-change identifications with actual faces and an explicit insertion contracting homotopy, not a localization sequence or scalar comparison; the existing statement has a different domain or conclusion and does not give this assertion by specialization.

lem-sfb-closed-restriction-signed-refinements vs lem-pc-affine-cech-complex: this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution; the existing statement has a different domain or conclusion and does not give this assertion by specialization.

lem-sfb-closed-restriction-signed-refinements vs lem-weil-pbc-cech-criterion: this child supplies the finite strictly-increasing closed-intersection complex and sorting-sign refinement maps without assuming row exactness; it is not localization, derived finiteness, or the completed resolution; the existing statement has a different domain or conclusion and does not give this assertion by specialization.

lem-sfb-closed-restriction-total-pullback vs lem-sc-finite-strip-row-augmentation: this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness; the existing statement has a different domain or conclusion and does not give this assertion by specialization.

lem-sfb-closed-restriction-total-pullback vs lem-sfb-cech-localization-unit-totalization: this child assumes all closed comparison isomorphisms and proves their face, augmentation and finite-total normalization; it neither supplies base change itself nor proves row exactness; the existing statement has a different domain or conclusion and does not give this assertion by specialization.


### Landing return L: final current-DAG repair and bound check (2026-10-22)

The resumed retained-work dry run exited successfully at b10e47cd55d. I then compared the returned baseline with the current shared item field by field: no fields changed; all four child ids remain absent from the current DAG. I reconstructed the delivered item from that current JSON, restoring only the worker proof, proof_deps and split_report. This preserves every live statement, Lean record, review field and provenance value; deliver.py performs the actual rebase in its own fresh worktree.

I reread all six statements cited by the assembly, every statement dependency of the item and children, and the retained search log results. None of these citations changed relative to the retained split. In step 3 I made the horizontal vanishing hypotheses explicit: the nonnegative row complex is zero for p<0 and for p>=m. Thus the finite-strip theorem applies with r=m, including m=1, to exactly the column-zero augmentation already specified. This is a proof adjustment on the rebased delivery, not an unchanged re-push. Detection still applies on affine charts, refinements still preserve the actual augmentation, and step 5 still derives invertibility of the pulled-back augmentation from its actual comparison square before invoking the derived identity. All ten citation quotes remain verbatim and cover exactly the ten cited step/node pairs; the parent proof is 2467 characters, with no step over 2000.

For sources I reread proetale.tex at labels lemma-closed-immersion (09AA), lemma-closed-immersion-complement-retrocompact-exact (09BM), and lemma-ses-associated-to-open (09AH), and homology.tex lemma-double-complex-gives-resolution (0133), including the second-variable variant. I also read the current main-20261015 direct-images proof, paragraph (3), and the existing finite_closed_cover_resolution Lean docstring and final sorry. The project-source search gives no exact finished attachment. The four unchanged child statements retain their logged searches, including the unavailable LeanSearch request; no query was invented or repeated. Edge checks remain m=1, empty support, repeated members, empty intersections, zero coefficients, and identity pullback. No new hypothesis is imposed on the item, no completed flag is changed, and side-to-live promotion remains the maintainer's operation.


### Landing return L: current-base repair signed 2026-10-23

The required first retained-work dry run completed successfully at 17e62e97349. I compared returned-item-baseline.json with the current shared item field by field: no differences. The retained item differed only in proof, proof_deps and split_report. I rebuilt the delivery item from the current JSON, retaining those worker fields and all current maintainer, statement, Lean and provenance fields. The four child ids are still absent from the current shared DAG. The delivery tool performs the rebase onto its freshly fetched server base; no local git command was used.

I reread every assembly citation: signed-refinements gives the actual differential and augmentation, vertex-contraction gives affine-local contraction and locality, finite detection supplies acyclicity, finite-strip row augmentation supplies precisely the finite-column total map, the derived-category definition supplies localization, and total-pullback supplies the actual augmentation square and diagonal normalization. I also reread all current statement dependencies of the item and children. No cited statement changed. All ten citation quotes remain verbatim and cover every cited step/node pair. The retained searches.jsonl results were read and reused, including the unavailable rate-limited LeanSearch query; no child statement or search question changed.

The concrete adjustment is in step 5: before applying steps 1–3 on the pulled-back configuration it now explicitly checks preservation of the closed covering and quasi-compact complementary immersions by base change. This discharges those hypotheses at their use, together with the already explicit invertibility argument from the actual augmentation square. Step 3 still uses r=m, vanishing for p<0 and p>=m, and the actual column-zero map. I rechecked singleton and empty-support covers, repeated members, empty intersections, zero modules and identity pullback. No hypothesis is added to the item. Four statement-only children remain independent jobs and the complete old arguments remain retained above.

For sources I reread the local Stacks statements and proofs at 09AA, 09BM, 09AH and 0133 (including the second-variable variant), the current main-20261015 direct-image proof, and the existing Lean theorem's docstring and final sorry. The project-source search again gives no finished attachment. The general Mathlib total.mapIso and extra-degeneracy results require data that the children construct, so they do not replace these statements by one-line specialization. This satisfies delivery-errors B–E without another worker, Lean writing or compilation. The live completion promotion remains the maintainer's operation; this delivery does not alter any completion flag.
