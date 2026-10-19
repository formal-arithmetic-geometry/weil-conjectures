1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-refined-quasi-finite-polynomial-pure-transcendental.json`: repaired split, eight proof steps; statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-refined-noether-normalization-prime.json`: retained statement-only Stacks 051P child; statement and logged searches unchanged; completed its ancestry via this item.
- `dag/nodes/sec-trace-formula/lem-trf-quasi-finite-composition.json`: new statement-only Stacks 00PO node, unsplit. Mathlib has a composition candidate, requiring a separate bridge between its fibrewise module-finite predicate and the DAG's isolated-fibre predicate (B8).
- `citations.json`: 45 verbatim step/node statement quotes. The delivery script validates this local file but packages only node files and report.md, so the complete citation evidence is also included in this report's appendix.

2. Attachments: none. Searches in WeilConjectures/ for the item tag, refined normalization, refined quasi-finite charts and the composition notion found no declaration stating this item or either new node exactly. The upstream master remains reference material, not evidence of a finished proof.

3. WANTED: none.

4. Returned faults repaired:

1. Composition (C1): added `lem-trf-quasi-finite-composition`, the statement of Stacks Algebra 00PO, and cited it in Step 5 only after both maps are quasi-finite everywhere.
2. Scheme and dimension translation (C1): Step 1 cites the affine fibre-product isomorphism, the fibre-prime correspondence and the definition of topological dimension at a point before using 00QE. Step 7 cites the scheme quasi-finite definition and the local-quasi-finite plus quasi-compact and finite-fibre equivalences. It checks quasi-compactness on basic opens using affine-scheme quasi-compactness, and identifies finite discrete scheme fibres using the affine fibre formula.
3. Localization (C1/E5): Step 5 cites the principal-localization theorem twice and explicitly first inverts f in B=A_g as well as in R[t]. The final ring is T=(A_g)_f[1/alpha_f(h)], abbreviated A_{gfh}; writing alpha_f(h)=a/(gf)^N realizes it as the genuine principal localization A_{gfa}. All g,f,a avoid the source prime, and f is a unit in T, so the source open lies over S_0=Spec(R_f).
4. Residue fields (E4): Step 2 uses kappa(Q)=kappa(q') for the original polynomial-image prime q', not kappa(q_A). It defines r using Q, so the proof needs no equality or finite-extension argument involving the source residue field. In general kappa(q_A) is only finite over kappa(q'), as the returned review correctly observes; the former equality was removed.
5. Final image (E3/E5): Step 6 tests membership of every polynomial F under the lifted-coordinate square and the fibre-prime correspondence, obtaining P=(p R_f,x_{r+1},...,x_n) by the vanishing of its surviving coefficients modulo p. The localization prime-correspondence theorem identifies P with the actual contraction of the surviving source prime. Step 8 uses the fibre-prime residue comparison at P and I, not at Q, to obtain kappa(t)=k(x_1,...,x_r). Steps 6 and 8 are not marked elementary.

The additional report issues are repaired as well: the off-unit tool lemmas are declared in split_report.tool_uses, and the citation evidence travels in the report appendix. The initial dry run of the retained repair passed at 6c5e890c83; further source review produced the eight-step version here, including explicit tensor-fibre maps and corrected Mathlib candidate descriptions, so a fresh final dry run is required.

5. Unfinished work: both children are intentionally statement-only; no proof obligation of the item is deferred into an unstated fact. No Lean files, compilers or Lake tools were used.

## Review by Q69

I read Algebra 0520 (algebra.tex:31211 onward) and its scheme translation 052E (more-morphisms.tex:13382 onward), and checked the child statements against the full statements and proofs of 051P (algebra.tex:28074 onward) and 00PO (algebra.tex:30342 onward). The route is precisely 00QE, refined normalization, lifted finite special fibre, 00QA, localization and 00PO, followed by the prescribed prime calculation. The main item statement remains correct and unchanged. The new composition result is strictly smaller and useful independently; the retained normalization result is the exact 051P statement.

For Step 1 I opened the affine fibre-product statement (isomorphism with Spec of the tensor product and its projections), the fibre-prime statement (the prime is the kernel of the canonical map to the source residue field), and the dimension definition (minimum over open neighbourhoods). Those are the exact objects in the 00QE statement. The source ring map goes R to A, correcting the old reversed arrow. The localization prime theorem supplies q_B and its contraction. No local-ring dimension is substituted for topological dimension at a point.

For Step 2 I checked that the contraction q' lies over p and that the polynomial scalar-extension theorem identifies its fibre ring with k[t]. The fibre-prime/residue-field node says precisely kappa(Q)=kappa(q'), and 051P applies to that Q with its own r. The old source-residue equality is absent. There is no need to prove transcendence-degree invariance under a finite extension in this version.

For Step 3 the finite set of polynomial coefficients gives a product denominator f outside p, including f=1 when the list is empty. The polynomial universal property constructs psi, and the variables t_j supply its finite-type generators. The localization theorem and fibre-prime correspondence verify the primes and their contractions. For Step 4 I checked the two tensor maps on pure tensors, their balancing relations and inverse compositions. The residue-field isomorphism is C-linear, so the fibre comparison has the asserted base action. Tensoring the finite module generators of the normalization gives a finite algebra over kappa(I). The finite-ring-map node says every prime is isolated in this fibre; the ring quasi-finite definition therefore applies to psi. The 00QA statement then supplies h outside the correct prime, with quasi-finiteness at every prime after localization. These are a routine tensor-generator calculation and application of cited statements, not a hidden generic comparison lemma.

For Step 5 the principal-localization statement allows both applications with its target element equal to 1. Its source elements are respectively f and h; every prime under consideration avoids them. The old composition with A_g before inverting f is removed. I verified T=A_{gfa} by writing the image of h as a fraction, so this really is a single principal affine open of the original source. The 00PO child says exactly that the composite is finite type and quasi-finite at every prime.

For Step 6 I checked both directions of F in P: the lifted map reduces to the normalized map, the latter has comap I, and the coefficient map R_f to k has kernel p R_f. The contraction to C is therefore the stated coordinate prime. For Step 7 the ring condition gives local quasi-finiteness using the whole affine pair; inverse images of basic opens are principal localizations and hence affine quasi-compact, which verifies the quasi-compactness hypothesis of pqf-lem-qf-locqf-qc. The finite-fibre criterion and affine fibre formula give precisely finite discrete fibres. For Step 8 the residue-field comparison is applied to R_f to C, the prime P and its fibre prime I. The quotient k[x]/I is the polynomial domain in the first r variables, whose localization at zero is its rational function field. The localization residue theorem preserves the base field. Thus the final image residue extension is purely transcendental.

I tested n=0 (empty coordinate list, r=0), r=n (Q=0), and Q=(t^2-2) over the rationals with the finite map x maps to t^2-2. In the last example the final image has residue field Q while Q has residue field Q(sqrt(2)); the repaired Steps 6 and 8 keep these separate. Composition with an identity and finite maps satisfies 00PO, and empty spectra cause no failure of its universally quantified prime conditions. No reducedness, Noetherianity, separatedness or injectivity of any ring map is assumed. I inspected all eight step lengths: none exceeds 2000 characters. I reread B--E of delivery-errors against the final files: self-contained statement-only children, genuine smaller tools, complete citation union, no illicit route change, no SGA source, and unchanged item statement. All cited statements were read in full; the appendix records their exact text.

The existing search log was retained. For 00PO I used LeanFinder, Loogle, grep, LeanSearch and a second semantic phrasing. Reading actual Mathlib source corrected the search service's inaccurate prose gloss: Algebra.QuasiFinite means finite-dimensional residue-field fibres, not a module-finite algebra over the base. RingHom.QuasiFinite.comp is a candidate, but translating the DAG predicate requires the separate fibre-isolated/finite-fibre equivalence; it is not a one-line specialization, consistent with delivery-errors B8. This reason is recorded in mathlib_candidate and the exact queries remain in searches.jsonl.

## Not duplicates

The current whole-DAG tag searches for 051P/refined-Noether-normalization and 00PO/lemma-quasi-finite-composition returned no nodes; whole-blueprint searches for quasi-finite, composition and normalization gave no equivalent statements. The nearest tools do not state either child:

- lem-trf-quasi-finite-composition vs lem-weil-pbc-quasi-finite-at-prime-permanence: 00PO composes two quasi-finite maps; permanence 0C6H deduces quasi-finiteness of the second map from that of a composite, a different implication.
- lem-trf-quasi-finite-composition vs lem-weil-pbc-quasi-finite-at-prime-principal-localization: 077H preserves pointwise quasi-finiteness under paired localizations; it does not compose arbitrary maps.
- lem-trf-refined-noether-normalization-prime vs lem-weil-pbc-noether-normalization-field: ordinary normalization gives a finite map with a dimension-indexed source; it does not prescribe the comap of a selected prime under a finite map between two n-variable polynomial rings.
- lem-trf-refined-noether-normalization-prime vs lem-weil-pbc-quasi-finite-over-polynomial-algebra: 00QE gives a local quasi-finite chart over an arbitrary base, not the finite field-polynomial coordinate change with prescribed prime of 051P.

## Citation evidence

The following is the complete citations.json validated by deliver.py, included here because that script packages report.md and the node JSON files but does not package the separate local citations.json.

```json
[
 {
  "step": 1,
  "node": "lem-weil-pbc-fibre-product-affine-spectra",
  "quote": "Let $R$ be a commutative ring and $A,B$ commutative $R$-algebras, and let $\\operatorname{Spec}A\\to\\operatorname{Spec}R$, $\\operatorname{Spec}B\\to\\operatorname{Spec}R$ be the morphisms induced by the structure maps [def-weil-affine-spectrum]. Then there is an isomorphism $\\operatorname{Spec}A\\times_{\\operatorname{Spec}R}\\operatorname{Spec}B\\cong\\operatorname{Spec}(A\\otimes_RB)$ [def-pc-fibre-product] under which the two projections become $\\operatorname{Spec}$ of the ring maps $A\\to A\\otimes_RB$, $a\\mapsto a\\otimes1$, and $B\\to A\\otimes_RB$, $b\\mapsto1\\otimes b$. In particular the fibre product is affine with ring of global sections $A\\otimes_RB$."
 },
 {
  "step": 1,
  "node": "lem-weil-pbc-fibre-ring-primes-residue-fields",
  "quote": "Let $\\varphi:A\\to B$ be a homomorphism of commutative rings, $\\mathfrak p\\subset A$ a prime ideal with residue field $\\kappa(\\mathfrak p)=A_{\\mathfrak p}/\\mathfrak pA_{\\mathfrak p}$ [def-weil-pbc-localization-at-prime], $C=B\\otimes_A\\kappa(\\mathfrak p)$ the fibre ring and $j:B\\to C$, $b\\mapsto b\\otimes1$. For a prime $\\mathfrak q\\subset B$ with $\\varphi^{-1}(\\mathfrak q)=\\mathfrak p$ let $\\kappa(\\mathfrak q)=B_{\\mathfrak q}/\\mathfrak qB_{\\mathfrak q}$ and let $\\psi_{\\mathfrak q}:C\\to\\kappa(\\mathfrak q)$ be the ring map $b\\otimes\\lambda\\mapsto\\bar b\\,\\bar\\lambda$, where $\\bar b$ is the image of $b$ and $\\bar\\lambda$ the image of $\\lambda$ under the map $\\kappa(\\mathfrak p)\\to\\kappa(\\mathfrak q)$ induced by $\\varphi$. Then (1) the map $\\mathfrak Q\\mapsto j^{-1}(\\mathfrak Q)$ is a bijection from the set of prime ideals of $C$ onto the set of prime ideals $\\mathfrak q\\subset B$ with $\\varphi^{-1}(\\mathfrak q)=\\mathfrak p$, with inverse $\\mathfrak q\\mapsto\\ker\\psi_{\\mathfrak q}$, and it preserves and reflects inclusions; (2) for each such $\\mathfrak q$, with $\\mathfrak Q=\\ker\\psi_{\\mathfrak q}$, the map $\\psi_{\\mathfrak q}$ induces an isomorphism of fields $\\kappa(\\mathfrak Q)=C_{\\mathfrak Q}/\\mathfrak QC_{\\mathfrak Q}\\xrightarrow{\\sim}\\kappa(\\mathfrak q)$; in other words $\\psi_{\\mathfrak q}$ is the composite of $C\\to\\kappa(\\mathfrak Q)$ with this isomorphism. (Residue fields as in [def-weil-residue-field] at the points of $\\operatorname{Spec}$ [def-weil-affine-spectrum].)"
 },
 {
  "step": 1,
  "node": "def-kun-topological-dimension-at-point",
  "quote": "Let $X$ be a topological space and $x\\in X$. The *Krull dimension of $X$ at $x$* is\n\n$$\n\\dim_x X=\\min\\{\\dim U: x\\in U\\subseteq X\\text{ open}\\},\n$$\n\nthe minimum, over the open neighbourhoods [def-kun-open-neighbourhood] $U$ of $x$ in $X$, of the Krull dimension [def-kun-topological-krull-dimension] of $U$ with the subspace topology [def-kun-subspace-topology] (an element of $\\{0,1,2,\\ldots,\\infty\\}$, since every such $U$ contains $x$ and so is nonempty; the minimum exists because every nonempty family in $\\{-\\infty,0,1,\\ldots,\\infty\\}$ has a least element [lem-kun-extended-naturals-minimum])."
 },
 {
  "step": 1,
  "node": "lem-weil-pbc-quasi-finite-over-polynomial-algebra",
  "quote": "Let $R\\to S$ be a homomorphism of commutative rings of finite type [def-weil-pbc-finite-type-algebra], let $\\mathfrak q\\subset S$ be prime, and let $\\mathfrak p\\subset R$ be its inverse image. Write $F=S\\otimes_R\\kappa(\\mathfrak p)$ for the fibre ring [def-weil-pbc-localization-at-prime], and $\\mathfrak Q=\\ker(F\\to\\kappa(\\mathfrak q))$ for the corresponding prime. Suppose the Krull dimension of $\\operatorname{Spec}F$ [def-weil-affine-spectrum] at $\\mathfrak Q$ [def-kun-topological-dimension-at-point] is an integer $n\\ge0$. Then there are $g\\in S\\setminus\\mathfrak q$ and an $R$-algebra homomorphism $R[t_1,\\dots,t_n]\\to S_g$ [def-weil-pbc-mv-polynomial-ring, def-weil-ring-localization-away] which is quasi-finite: it is of finite type and quasi-finite at every prime of $S_g$ in the sense of [def-weil-pbc-ring-map-quasi-finite-at-prime]."
 },
 {
  "step": 1,
  "node": "lem-weil-pbc-localization-prime-residue-field-iso",
  "quote": "Let $A$ be a commutative ring, $W\\subseteq A$ a multiplicative subset and $\\lambda:A\\to A'$ a homomorphism of commutative rings which is a localization of $A$ at $W$: (a) $\\lambda(w)$ is a unit for every $w\\in W$; (b) every element of $A'$ is $\\lambda(a)\\lambda(w)^{-1}$ with $a\\in A$, $w\\in W$; (c) $\\lambda(a)=0$ implies $wa=0$ for some $w\\in W$ (for instance $A'=W^{-1}A$ with $a\\mapsto a/1$). Let $\\mathfrak q'\\subset A'$ be a prime ideal and $\\mathfrak q=\\lambda^{-1}(\\mathfrak q')$. Then: (1) $\\mathfrak q$ is a prime ideal of $A$ with $\\mathfrak q\\cap W=\\emptyset$; conversely, for every prime ideal $\\mathfrak p\\subset A$ with $\\mathfrak p\\cap W=\\emptyset$ the ideal $\\mathfrak pA'$ generated by $\\lambda(\\mathfrak p)$ is a prime ideal of $A'$ with $\\lambda^{-1}(\\mathfrak pA')=\\mathfrak p$, and $\\lambda(\\lambda^{-1}(\\mathfrak q'))A'=\\mathfrak q'$, so $\\mathfrak q'\\mapsto\\lambda^{-1}(\\mathfrak q')$ is a bijection from the primes of $A'$ onto the primes of $A$ disjoint from $W$, with inverse $\\mathfrak p\\mapsto\\mathfrak pA'$; (2) the composite $A\\xrightarrow{\\lambda}A'\\to A'_{\\mathfrak q'}$ is a localization of $A$ at $A\\setminus\\mathfrak q$ (in the sense of (a)-(c) with $W$ replaced by $A\\setminus\\mathfrak q$), so the ring map $A_{\\mathfrak q}\\to A'_{\\mathfrak q'}$, $a/s\\mapsto\\lambda(a)/\\lambda(s)$, is an isomorphism of $A$-algebras [def-weil-pbc-localization-at-prime]; (3) this isomorphism carries $\\mathfrak qA_{\\mathfrak q}$ onto $\\mathfrak q'A'_{\\mathfrak q'}$ and induces an isomorphism of fields and of $A$-algebras $\\sigma:\\kappa(\\mathfrak q)=A_{\\mathfrak q}/\\mathfrak qA_{\\mathfrak q}\\xrightarrow{\\sim}\\kappa(\\mathfrak q')=A'_{\\mathfrak q'}/\\mathfrak q'A'_{\\mathfrak q'}$, where $\\kappa(\\mathfrak q')$ is an $A$-algebra via $A\\to A'\\to\\kappa(\\mathfrak q')$."
 },
 {
  "step": 1,
  "node": "def-weil-finite-type-morphism",
  "quote": "A morphism of schemes $f:X\\to Y$ is *locally of finite type* if, for every\naffine open $V=\\operatorname{Spec}A$ of $Y$, the preimage $f^{-1}(V)$ has an\naffine open cover by $\\operatorname{Spec}B$ with $B$ a finitely generated\n$A$-algebra. It is *quasi-compact* if every such preimage is quasi-compact.\nIt is *of finite type* if both conditions hold; equivalently, the affine\ncover of each $f^{-1}(V)$ can be chosen finite. For a scheme over a field,\nfinite type refers to its structure morphism. See\n[Stacks Project, Section 29.15](https://stacks.math.columbia.edu/tag/01T0)."
 },
 {
  "step": 2,
  "node": "lem-weil-pbc-polynomial-scalar-extension",
  "quote": "Let $A\\to R$ be a homomorphism of commutative rings and $J$ a set. The map $R\\otimes_AA[U_j:j\\in J]\\to R[U_j:j\\in J]$, $r\\otimes p\\mapsto r\\cdot\\bar p$ ($\\bar p$ the image of $p$ under the coefficient map $A\\to R$), is an isomorphism of $R$-algebras; it sends $r\\otimes1\\mapsto r$ and $1\\otimes U_j\\mapsto U_j$. (Used with $A=\\mathbf Z$.)"
 },
 {
  "step": 2,
  "node": "lem-weil-pbc-fibre-ring-primes-residue-fields",
  "quote": "Let $\\varphi:A\\to B$ be a homomorphism of commutative rings, $\\mathfrak p\\subset A$ a prime ideal with residue field $\\kappa(\\mathfrak p)=A_{\\mathfrak p}/\\mathfrak pA_{\\mathfrak p}$ [def-weil-pbc-localization-at-prime], $C=B\\otimes_A\\kappa(\\mathfrak p)$ the fibre ring and $j:B\\to C$, $b\\mapsto b\\otimes1$. For a prime $\\mathfrak q\\subset B$ with $\\varphi^{-1}(\\mathfrak q)=\\mathfrak p$ let $\\kappa(\\mathfrak q)=B_{\\mathfrak q}/\\mathfrak qB_{\\mathfrak q}$ and let $\\psi_{\\mathfrak q}:C\\to\\kappa(\\mathfrak q)$ be the ring map $b\\otimes\\lambda\\mapsto\\bar b\\,\\bar\\lambda$, where $\\bar b$ is the image of $b$ and $\\bar\\lambda$ the image of $\\lambda$ under the map $\\kappa(\\mathfrak p)\\to\\kappa(\\mathfrak q)$ induced by $\\varphi$. Then (1) the map $\\mathfrak Q\\mapsto j^{-1}(\\mathfrak Q)$ is a bijection from the set of prime ideals of $C$ onto the set of prime ideals $\\mathfrak q\\subset B$ with $\\varphi^{-1}(\\mathfrak q)=\\mathfrak p$, with inverse $\\mathfrak q\\mapsto\\ker\\psi_{\\mathfrak q}$, and it preserves and reflects inclusions; (2) for each such $\\mathfrak q$, with $\\mathfrak Q=\\ker\\psi_{\\mathfrak q}$, the map $\\psi_{\\mathfrak q}$ induces an isomorphism of fields $\\kappa(\\mathfrak Q)=C_{\\mathfrak Q}/\\mathfrak QC_{\\mathfrak Q}\\xrightarrow{\\sim}\\kappa(\\mathfrak q)$; in other words $\\psi_{\\mathfrak q}$ is the composite of $C\\to\\kappa(\\mathfrak Q)$ with this isomorphism. (Residue fields as in [def-weil-residue-field] at the points of $\\operatorname{Spec}$ [def-weil-affine-spectrum].)"
 },
 {
  "step": 2,
  "node": "lem-trf-refined-noether-normalization-prime",
  "quote": "Let $k$ be a field, let $n\\ge0$, and let $\\mathfrak q\\subset k[x_1,\\ldots,x_n]$ be a prime ideal. Put $r=\\operatorname{trdeg}_k\\kappa(\\mathfrak q)$, with residue field and transcendence degree as in [def-weil-residue-field, def-kun-transcendence-degree]. Then there exists a finite $k$-algebra homomorphism $\\varphi:k[y_1,\\ldots,y_n]\\to k[x_1,\\ldots,x_n]$ [def-weil-pbc-mv-polynomial-ring] such that $\\varphi^{-1}(\\mathfrak q)=(y_{r+1},\\ldots,y_n)$."
 },
 {
  "step": 2,
  "node": "def-kun-transcendence-degree",
  "quote": "Let $K\\subseteq L$ be a field extension (more generally, let $A$ be a commutative algebra over a commutative ring $K$). A family of elements of $L$ is *algebraically independent* over $K$ if no nonzero polynomial with coefficients in $K$ vanishes on it. The *transcendence degree* $\\operatorname{trdeg}_KL$ is the supremum of the cardinalities of the subsets of $L$ that are algebraically independent over $K$; for a field extension it equals the cardinality of any transcendence basis of $L$ over $K$. In particular $\\operatorname{trdeg}_KL\\le a$ for an integer $a\\ge0$ means that every algebraically independent subset of $L$ has at most $a$ elements."
 },
 {
  "step": 3,
  "node": "def-weil-pbc-localization-at-prime",
  "quote": "Let $R$ be a commutative ring and $\\mathfrak p\\subset R$ a prime ideal. The *localization* $R_{\\mathfrak p}=S^{-1}R$, $S=R\\setminus\\mathfrak p$, is the ring of fractions $r/s$ ($r\\in R$, $s\\in S$, with $r/s=r'/s'$ iff $u(rs'-r's)=0$ for some $u\\in S$), with the ring map $R\\to R_{\\mathfrak p}$, $r\\mapsto r/1$; it is a local ring with maximal ideal $\\mathfrak pR_{\\mathfrak p}$. The *residue field* of $\\mathfrak p$ is $\\kappa(\\mathfrak p)=R_{\\mathfrak p}/\\mathfrak pR_{\\mathfrak p}$, an $R$-algebra. For an $R$-algebra $\\Lambda$ (a ring map $R\\to\\Lambda$) the *fibre ring* of $\\Lambda$ over $\\mathfrak p$ is the tensor product of $R$-algebras $\\Lambda\\otimes_R\\kappa(\\mathfrak p)$, a $\\kappa(\\mathfrak p)$-algebra; it is isomorphic to $\\Lambda_{\\mathfrak p}/\\mathfrak p\\Lambda_{\\mathfrak p}$, $\\Lambda_{\\mathfrak p}$ the localization of $\\Lambda$ at the image of $R\\setminus\\mathfrak p$."
 },
 {
  "step": 3,
  "node": "def-weil-ring-localization-away",
  "quote": "Let $R$ be a commutative ring and $\\varpi\\in R$, and let $S=\\{1,\\varpi,\\varpi^2,\\dots\\}$. The *localization of $R$ at $\\varpi$* (*away from $\\varpi$*) is the ring $R[1/\\varpi]=R_\\varpi=S^{-1}R$ of fractions $x/\\varpi^n$ ($x\\in R$, $n\\geq0$), where $x/\\varpi^n=y/\\varpi^m$ if and only if $\\varpi^k(x\\varpi^m-y\\varpi^n)=0$ for some $k\\geq0$, with $x/s+y/t=(xt+ys)/st$ and $(x/s)(y/t)=xy/st$, together with the ring map $R\\to R[1/\\varpi]$, $x\\mapsto x/1$, which makes $R[1/\\varpi]$ an $R$-algebra in which $\\varpi$ is invertible. More generally an $R$-algebra $A$ *is a localization of $R$ at $\\varpi$* if the induced map $R[1/\\varpi]\\to A$ is an isomorphism; equivalently, the image of $\\varpi$ in $A$ is a unit, every element of $A$ is $x\\cdot\\varpi^{-n}$, and $x\\mapsto0$ in $A$ iff $\\varpi^kx=0$ for some $k$."
 },
 {
  "step": 3,
  "node": "def-weil-pbc-mv-polynomial-ring",
  "quote": "Let $R$ be a commutative ring and $J$ a set. The *polynomial ring* $R[x_j:j\\in J]$ is the commutative $R$-algebra whose elements are the finite $R$-linear combinations $\\sum_\\alpha c_\\alpha x^\\alpha$ of monomials $x^\\alpha=\\prod_jx_j^{\\alpha_j}$ ($\\alpha:J\\to\\mathbf Z_{\\ge0}$ finitely supported), with coefficientwise addition and the product determined by $x^\\alpha x^\\beta=x^{\\alpha+\\beta}$ and $R$-bilinearity; $R\\to R[x_j:j\\in J]$, $c\\mapsto c\\,x^0$, is its structure map. (For $J=\\{1,\\dots,n\\}$ one writes $R[x_1,\\dots,x_n]$.) Universal property: for every commutative $R$-algebra $C$ and every family $(c_j)_{j\\in J}$ of elements of $C$ there is a unique $R$-algebra homomorphism $R[x_j:j\\in J]\\to C$ with $x_j\\mapsto c_j$ for all $j$ (evaluation, $\\sum c_\\alpha x^\\alpha\\mapsto\\sum c_\\alpha\\prod_jc_j^{\\alpha_j}$); in particular two $R$-algebra homomorphisms out of $R[x_j:j\\in J]$ that agree on every $x_j$ are equal."
 },
 {
  "step": 3,
  "node": "def-weil-pbc-finite-type-algebra",
  "quote": "Let $R\\to S$ be a homomorphism of commutative rings. It is *of finite type*, or $S$ is a *finite type $R$-algebra*, if there are an integer $n\\ge0$ and a surjective homomorphism of $R$-algebras $R[x_1,\\dots,x_n]\\to S$ from the polynomial ring [def-weil-polynomial-ring]; equivalently, there are $s_1,\\dots,s_n\\in S$ such that every element of $S$ is a polynomial in $s_1,\\dots,s_n$ with coefficients in (the image of) $R$. For $R=\\mathbf Z$ this says that $S$ is generated as a ring by finitely many elements."
 },
 {
  "step": 3,
  "node": "lem-weil-pbc-localization-prime-residue-field-iso",
  "quote": "Let $A$ be a commutative ring, $W\\subseteq A$ a multiplicative subset and $\\lambda:A\\to A'$ a homomorphism of commutative rings which is a localization of $A$ at $W$: (a) $\\lambda(w)$ is a unit for every $w\\in W$; (b) every element of $A'$ is $\\lambda(a)\\lambda(w)^{-1}$ with $a\\in A$, $w\\in W$; (c) $\\lambda(a)=0$ implies $wa=0$ for some $w\\in W$ (for instance $A'=W^{-1}A$ with $a\\mapsto a/1$). Let $\\mathfrak q'\\subset A'$ be a prime ideal and $\\mathfrak q=\\lambda^{-1}(\\mathfrak q')$. Then: (1) $\\mathfrak q$ is a prime ideal of $A$ with $\\mathfrak q\\cap W=\\emptyset$; conversely, for every prime ideal $\\mathfrak p\\subset A$ with $\\mathfrak p\\cap W=\\emptyset$ the ideal $\\mathfrak pA'$ generated by $\\lambda(\\mathfrak p)$ is a prime ideal of $A'$ with $\\lambda^{-1}(\\mathfrak pA')=\\mathfrak p$, and $\\lambda(\\lambda^{-1}(\\mathfrak q'))A'=\\mathfrak q'$, so $\\mathfrak q'\\mapsto\\lambda^{-1}(\\mathfrak q')$ is a bijection from the primes of $A'$ onto the primes of $A$ disjoint from $W$, with inverse $\\mathfrak p\\mapsto\\mathfrak pA'$; (2) the composite $A\\xrightarrow{\\lambda}A'\\to A'_{\\mathfrak q'}$ is a localization of $A$ at $A\\setminus\\mathfrak q$ (in the sense of (a)-(c) with $W$ replaced by $A\\setminus\\mathfrak q$), so the ring map $A_{\\mathfrak q}\\to A'_{\\mathfrak q'}$, $a/s\\mapsto\\lambda(a)/\\lambda(s)$, is an isomorphism of $A$-algebras [def-weil-pbc-localization-at-prime]; (3) this isomorphism carries $\\mathfrak qA_{\\mathfrak q}$ onto $\\mathfrak q'A'_{\\mathfrak q'}$ and induces an isomorphism of fields and of $A$-algebras $\\sigma:\\kappa(\\mathfrak q)=A_{\\mathfrak q}/\\mathfrak qA_{\\mathfrak q}\\xrightarrow{\\sim}\\kappa(\\mathfrak q')=A'_{\\mathfrak q'}/\\mathfrak q'A'_{\\mathfrak q'}$, where $\\kappa(\\mathfrak q')$ is an $A$-algebra via $A\\to A'\\to\\kappa(\\mathfrak q')$."
 },
 {
  "step": 3,
  "node": "lem-weil-pbc-polynomial-scalar-extension",
  "quote": "Let $A\\to R$ be a homomorphism of commutative rings and $J$ a set. The map $R\\otimes_AA[U_j:j\\in J]\\to R[U_j:j\\in J]$, $r\\otimes p\\mapsto r\\cdot\\bar p$ ($\\bar p$ the image of $p$ under the coefficient map $A\\to R$), is an isomorphism of $R$-algebras; it sends $r\\otimes1\\mapsto r$ and $1\\otimes U_j\\mapsto U_j$. (Used with $A=\\mathbf Z$.)"
 },
 {
  "step": 3,
  "node": "lem-weil-pbc-fibre-ring-primes-residue-fields",
  "quote": "Let $\\varphi:A\\to B$ be a homomorphism of commutative rings, $\\mathfrak p\\subset A$ a prime ideal with residue field $\\kappa(\\mathfrak p)=A_{\\mathfrak p}/\\mathfrak pA_{\\mathfrak p}$ [def-weil-pbc-localization-at-prime], $C=B\\otimes_A\\kappa(\\mathfrak p)$ the fibre ring and $j:B\\to C$, $b\\mapsto b\\otimes1$. For a prime $\\mathfrak q\\subset B$ with $\\varphi^{-1}(\\mathfrak q)=\\mathfrak p$ let $\\kappa(\\mathfrak q)=B_{\\mathfrak q}/\\mathfrak qB_{\\mathfrak q}$ and let $\\psi_{\\mathfrak q}:C\\to\\kappa(\\mathfrak q)$ be the ring map $b\\otimes\\lambda\\mapsto\\bar b\\,\\bar\\lambda$, where $\\bar b$ is the image of $b$ and $\\bar\\lambda$ the image of $\\lambda$ under the map $\\kappa(\\mathfrak p)\\to\\kappa(\\mathfrak q)$ induced by $\\varphi$. Then (1) the map $\\mathfrak Q\\mapsto j^{-1}(\\mathfrak Q)$ is a bijection from the set of prime ideals of $C$ onto the set of prime ideals $\\mathfrak q\\subset B$ with $\\varphi^{-1}(\\mathfrak q)=\\mathfrak p$, with inverse $\\mathfrak q\\mapsto\\ker\\psi_{\\mathfrak q}$, and it preserves and reflects inclusions; (2) for each such $\\mathfrak q$, with $\\mathfrak Q=\\ker\\psi_{\\mathfrak q}$, the map $\\psi_{\\mathfrak q}$ induces an isomorphism of fields $\\kappa(\\mathfrak Q)=C_{\\mathfrak Q}/\\mathfrak QC_{\\mathfrak Q}\\xrightarrow{\\sim}\\kappa(\\mathfrak q)$; in other words $\\psi_{\\mathfrak q}$ is the composite of $C\\to\\kappa(\\mathfrak Q)$ with this isomorphism. (Residue fields as in [def-weil-residue-field] at the points of $\\operatorname{Spec}$ [def-weil-affine-spectrum].)"
 },
 {
  "step": 4,
  "node": "lem-weil-pbc-fibre-ring-primes-residue-fields",
  "quote": "Let $\\varphi:A\\to B$ be a homomorphism of commutative rings, $\\mathfrak p\\subset A$ a prime ideal with residue field $\\kappa(\\mathfrak p)=A_{\\mathfrak p}/\\mathfrak pA_{\\mathfrak p}$ [def-weil-pbc-localization-at-prime], $C=B\\otimes_A\\kappa(\\mathfrak p)$ the fibre ring and $j:B\\to C$, $b\\mapsto b\\otimes1$. For a prime $\\mathfrak q\\subset B$ with $\\varphi^{-1}(\\mathfrak q)=\\mathfrak p$ let $\\kappa(\\mathfrak q)=B_{\\mathfrak q}/\\mathfrak qB_{\\mathfrak q}$ and let $\\psi_{\\mathfrak q}:C\\to\\kappa(\\mathfrak q)$ be the ring map $b\\otimes\\lambda\\mapsto\\bar b\\,\\bar\\lambda$, where $\\bar b$ is the image of $b$ and $\\bar\\lambda$ the image of $\\lambda$ under the map $\\kappa(\\mathfrak p)\\to\\kappa(\\mathfrak q)$ induced by $\\varphi$. Then (1) the map $\\mathfrak Q\\mapsto j^{-1}(\\mathfrak Q)$ is a bijection from the set of prime ideals of $C$ onto the set of prime ideals $\\mathfrak q\\subset B$ with $\\varphi^{-1}(\\mathfrak q)=\\mathfrak p$, with inverse $\\mathfrak q\\mapsto\\ker\\psi_{\\mathfrak q}$, and it preserves and reflects inclusions; (2) for each such $\\mathfrak q$, with $\\mathfrak Q=\\ker\\psi_{\\mathfrak q}$, the map $\\psi_{\\mathfrak q}$ induces an isomorphism of fields $\\kappa(\\mathfrak Q)=C_{\\mathfrak Q}/\\mathfrak QC_{\\mathfrak Q}\\xrightarrow{\\sim}\\kappa(\\mathfrak q)$; in other words $\\psi_{\\mathfrak q}$ is the composite of $C\\to\\kappa(\\mathfrak Q)$ with this isomorphism. (Residue fields as in [def-weil-residue-field] at the points of $\\operatorname{Spec}$ [def-weil-affine-spectrum].)"
 },
 {
  "step": 4,
  "node": "lem-weil-pbc-finite-ring-map-quasi-finite",
  "quote": "Let $\\varphi:R\\to T$ be a homomorphism of commutative rings such that $T$, viewed as an $R$-module via $\\varphi$, is finitely generated [def-weil-finitely-generated-module]. Then $R\\to T$ is of finite type [def-weil-pbc-finite-type-algebra], and $R\\to T$ is quasi-finite at every prime ideal $\\mathfrak q\\subset T$ in the sense of [def-weil-pbc-ring-map-quasi-finite-at-prime]."
 },
 {
  "step": 4,
  "node": "def-weil-pbc-localization-at-prime",
  "quote": "Let $R$ be a commutative ring and $\\mathfrak p\\subset R$ a prime ideal. The *localization* $R_{\\mathfrak p}=S^{-1}R$, $S=R\\setminus\\mathfrak p$, is the ring of fractions $r/s$ ($r\\in R$, $s\\in S$, with $r/s=r'/s'$ iff $u(rs'-r's)=0$ for some $u\\in S$), with the ring map $R\\to R_{\\mathfrak p}$, $r\\mapsto r/1$; it is a local ring with maximal ideal $\\mathfrak pR_{\\mathfrak p}$. The *residue field* of $\\mathfrak p$ is $\\kappa(\\mathfrak p)=R_{\\mathfrak p}/\\mathfrak pR_{\\mathfrak p}$, an $R$-algebra. For an $R$-algebra $\\Lambda$ (a ring map $R\\to\\Lambda$) the *fibre ring* of $\\Lambda$ over $\\mathfrak p$ is the tensor product of $R$-algebras $\\Lambda\\otimes_R\\kappa(\\mathfrak p)$, a $\\kappa(\\mathfrak p)$-algebra; it is isomorphic to $\\Lambda_{\\mathfrak p}/\\mathfrak p\\Lambda_{\\mathfrak p}$, $\\Lambda_{\\mathfrak p}$ the localization of $\\Lambda$ at the image of $R\\setminus\\mathfrak p$."
 },
 {
  "step": 4,
  "node": "def-weil-pbc-ring-map-quasi-finite-at-prime",
  "quote": "Let $\\varphi:R\\to S$ be a ring map of finite type, i.e. $S$ is finitely generated as an $R$-algebra: there are $n\\ge0$ and $s_1,\\dots,s_n\\in S$ such that the $R$-algebra homomorphism $R[x_1,\\dots,x_n]\\to S$, $x_i\\mapsto s_i$ [def-weil-pbc-mv-polynomial-ring], is surjective. Let $\\mathfrak q\\subset S$ be a prime ideal and $\\mathfrak p=\\varphi^{-1}(\\mathfrak q)$, with residue field $\\kappa(\\mathfrak p)=R_{\\mathfrak p}/\\mathfrak pR_{\\mathfrak p}$, and let $F=S\\otimes_R\\kappa(\\mathfrak p)$ be the fibre ring of $S$ over $\\mathfrak p$ [def-weil-pbc-localization-at-prime], with $j:S\\to F$, $s\\mapsto s\\otimes1$. Let $\\overline{\\mathfrak q}\\subset F$ be the prime ideal of $F$ corresponding to $\\mathfrak q$, i.e. the unique prime ideal of $F$ with $j^{-1}(\\overline{\\mathfrak q})=\\mathfrak q$ (it exists and is unique by [lem-weil-pbc-fibre-ring-primes-bijection], since $\\varphi^{-1}(\\mathfrak q)=\\mathfrak p$). We say that $R\\to S$ is *quasi-finite at $\\mathfrak q$* if $\\overline{\\mathfrak q}$ is an isolated point of $\\operatorname{Spec}(F)$ [def-weil-affine-spectrum], that is, the singleton $\\{\\overline{\\mathfrak q}\\}$ is open in the Zariski topology of $\\operatorname{Spec}(S\\otimes_R\\kappa(\\mathfrak p))$."
 },
 {
  "step": 4,
  "node": "lem-weil-pbc-ring-quasi-finite-locus-open",
  "quote": "Let $A\\to B$ be a homomorphism of commutative rings of finite type [def-weil-pbc-finite-type-algebra]. In $\\operatorname{Spec}B$ [def-weil-affine-spectrum], the set $Q=\\{\\mathfrak q\\subset B: A\\to B\\text{ is quasi-finite at }\\mathfrak q\\}$, with quasi-finiteness at a prime as in [def-weil-pbc-ring-map-quasi-finite-at-prime], is open. Equivalently, for each $\\mathfrak q\\in Q$ there is $g\\in B\\setminus\\mathfrak q$ such that $A\\to B_g$ [def-weil-ring-localization-away] is quasi-finite at every prime of $B_g$."
 },
 {
  "step": 5,
  "node": "lem-weil-pbc-quasi-finite-at-prime-principal-localization",
  "quote": "Let $\\varphi:R\\to S$ be a ring map of finite type [def-weil-pbc-finite-type-algebra], let $\\mathfrak q\\subset S$ be a prime ideal and $\\mathfrak p=\\varphi^{-1}(\\mathfrak q)$. Let $f\\in R$ with $f\\notin\\mathfrak p$ and $g\\in S$ with $g\\notin\\mathfrak q$. Let $R_f$ be the localization of $R$ at $f$ and $S_{fg}$ the localization of $S$ at $\\varphi(f)g$ [def-weil-ring-localization-away], with the ring map $R_f\\to S_{fg}$, $r/f^n\\mapsto \\varphi(r)g^n/(\\varphi(f)g)^n$, induced by $\\varphi$ (it is of finite type), and let $\\mathfrak qS_{fg}=\\{y/(\\varphi(f)g)^n\\mid y\\in\\mathfrak q\\}$, a prime ideal of $S_{fg}$. Then $R\\to S$ is quasi-finite at $\\mathfrak q$ [def-weil-pbc-ring-map-quasi-finite-at-prime] if and only if $R_f\\to S_{fg}$ is quasi-finite at $\\mathfrak qS_{fg}$."
 },
 {
  "step": 5,
  "node": "lem-weil-pbc-localization-prime-residue-field-iso",
  "quote": "Let $A$ be a commutative ring, $W\\subseteq A$ a multiplicative subset and $\\lambda:A\\to A'$ a homomorphism of commutative rings which is a localization of $A$ at $W$: (a) $\\lambda(w)$ is a unit for every $w\\in W$; (b) every element of $A'$ is $\\lambda(a)\\lambda(w)^{-1}$ with $a\\in A$, $w\\in W$; (c) $\\lambda(a)=0$ implies $wa=0$ for some $w\\in W$ (for instance $A'=W^{-1}A$ with $a\\mapsto a/1$). Let $\\mathfrak q'\\subset A'$ be a prime ideal and $\\mathfrak q=\\lambda^{-1}(\\mathfrak q')$. Then: (1) $\\mathfrak q$ is a prime ideal of $A$ with $\\mathfrak q\\cap W=\\emptyset$; conversely, for every prime ideal $\\mathfrak p\\subset A$ with $\\mathfrak p\\cap W=\\emptyset$ the ideal $\\mathfrak pA'$ generated by $\\lambda(\\mathfrak p)$ is a prime ideal of $A'$ with $\\lambda^{-1}(\\mathfrak pA')=\\mathfrak p$, and $\\lambda(\\lambda^{-1}(\\mathfrak q'))A'=\\mathfrak q'$, so $\\mathfrak q'\\mapsto\\lambda^{-1}(\\mathfrak q')$ is a bijection from the primes of $A'$ onto the primes of $A$ disjoint from $W$, with inverse $\\mathfrak p\\mapsto\\mathfrak pA'$; (2) the composite $A\\xrightarrow{\\lambda}A'\\to A'_{\\mathfrak q'}$ is a localization of $A$ at $A\\setminus\\mathfrak q$ (in the sense of (a)-(c) with $W$ replaced by $A\\setminus\\mathfrak q$), so the ring map $A_{\\mathfrak q}\\to A'_{\\mathfrak q'}$, $a/s\\mapsto\\lambda(a)/\\lambda(s)$, is an isomorphism of $A$-algebras [def-weil-pbc-localization-at-prime]; (3) this isomorphism carries $\\mathfrak qA_{\\mathfrak q}$ onto $\\mathfrak q'A'_{\\mathfrak q'}$ and induces an isomorphism of fields and of $A$-algebras $\\sigma:\\kappa(\\mathfrak q)=A_{\\mathfrak q}/\\mathfrak qA_{\\mathfrak q}\\xrightarrow{\\sim}\\kappa(\\mathfrak q')=A'_{\\mathfrak q'}/\\mathfrak q'A'_{\\mathfrak q'}$, where $\\kappa(\\mathfrak q')$ is an $A$-algebra via $A\\to A'\\to\\kappa(\\mathfrak q')$."
 },
 {
  "step": 5,
  "node": "lem-trf-quasi-finite-composition",
  "quote": "Let $A\\to B$ and $B\\to C$ be homomorphisms of commutative rings. Assume that both maps are of finite type [def-weil-pbc-finite-type-algebra] and quasi-finite at every prime of the target in the sense of [def-weil-pbc-ring-map-quasi-finite-at-prime]. Then the composite $A\\to C$ is of finite type and quasi-finite at every prime of $C$."
 },
 {
  "step": 5,
  "node": "def-weil-ring-localization-away",
  "quote": "Let $R$ be a commutative ring and $\\varpi\\in R$, and let $S=\\{1,\\varpi,\\varpi^2,\\dots\\}$. The *localization of $R$ at $\\varpi$* (*away from $\\varpi$*) is the ring $R[1/\\varpi]=R_\\varpi=S^{-1}R$ of fractions $x/\\varpi^n$ ($x\\in R$, $n\\geq0$), where $x/\\varpi^n=y/\\varpi^m$ if and only if $\\varpi^k(x\\varpi^m-y\\varpi^n)=0$ for some $k\\geq0$, with $x/s+y/t=(xt+ys)/st$ and $(x/s)(y/t)=xy/st$, together with the ring map $R\\to R[1/\\varpi]$, $x\\mapsto x/1$, which makes $R[1/\\varpi]$ an $R$-algebra in which $\\varpi$ is invertible. More generally an $R$-algebra $A$ *is a localization of $R$ at $\\varpi$* if the induced map $R[1/\\varpi]\\to A$ is an isomorphism; equivalently, the image of $\\varpi$ in $A$ is a unit, every element of $A$ is $x\\cdot\\varpi^{-n}$, and $x\\mapsto0$ in $A$ iff $\\varpi^kx=0$ for some $k$."
 },
 {
  "step": 5,
  "node": "lem-weil-pbc-principal-localization-open-immersion",
  "quote": "Let $A$ be a commutative ring and $f\\in A$, and let $A_f$ be the localization of $A$ at the multiplicative set $\\{1,f,f^2,\\dots\\}$. Then the morphism of schemes $\\operatorname{Spec}A_f\\to\\operatorname{Spec}A$ induced by the localization map $A\\to A_f$ is an open immersion [def-weil-open-immersion] (with image the principal open $D(f)$)."
 },
 {
  "step": 6,
  "node": "lem-weil-pbc-localization-prime-residue-field-iso",
  "quote": "Let $A$ be a commutative ring, $W\\subseteq A$ a multiplicative subset and $\\lambda:A\\to A'$ a homomorphism of commutative rings which is a localization of $A$ at $W$: (a) $\\lambda(w)$ is a unit for every $w\\in W$; (b) every element of $A'$ is $\\lambda(a)\\lambda(w)^{-1}$ with $a\\in A$, $w\\in W$; (c) $\\lambda(a)=0$ implies $wa=0$ for some $w\\in W$ (for instance $A'=W^{-1}A$ with $a\\mapsto a/1$). Let $\\mathfrak q'\\subset A'$ be a prime ideal and $\\mathfrak q=\\lambda^{-1}(\\mathfrak q')$. Then: (1) $\\mathfrak q$ is a prime ideal of $A$ with $\\mathfrak q\\cap W=\\emptyset$; conversely, for every prime ideal $\\mathfrak p\\subset A$ with $\\mathfrak p\\cap W=\\emptyset$ the ideal $\\mathfrak pA'$ generated by $\\lambda(\\mathfrak p)$ is a prime ideal of $A'$ with $\\lambda^{-1}(\\mathfrak pA')=\\mathfrak p$, and $\\lambda(\\lambda^{-1}(\\mathfrak q'))A'=\\mathfrak q'$, so $\\mathfrak q'\\mapsto\\lambda^{-1}(\\mathfrak q')$ is a bijection from the primes of $A'$ onto the primes of $A$ disjoint from $W$, with inverse $\\mathfrak p\\mapsto\\mathfrak pA'$; (2) the composite $A\\xrightarrow{\\lambda}A'\\to A'_{\\mathfrak q'}$ is a localization of $A$ at $A\\setminus\\mathfrak q$ (in the sense of (a)-(c) with $W$ replaced by $A\\setminus\\mathfrak q$), so the ring map $A_{\\mathfrak q}\\to A'_{\\mathfrak q'}$, $a/s\\mapsto\\lambda(a)/\\lambda(s)$, is an isomorphism of $A$-algebras [def-weil-pbc-localization-at-prime]; (3) this isomorphism carries $\\mathfrak qA_{\\mathfrak q}$ onto $\\mathfrak q'A'_{\\mathfrak q'}$ and induces an isomorphism of fields and of $A$-algebras $\\sigma:\\kappa(\\mathfrak q)=A_{\\mathfrak q}/\\mathfrak qA_{\\mathfrak q}\\xrightarrow{\\sim}\\kappa(\\mathfrak q')=A'_{\\mathfrak q'}/\\mathfrak q'A'_{\\mathfrak q'}$, where $\\kappa(\\mathfrak q')$ is an $A$-algebra via $A\\to A'\\to\\kappa(\\mathfrak q')$."
 },
 {
  "step": 6,
  "node": "lem-weil-pbc-fibre-ring-primes-residue-fields",
  "quote": "Let $\\varphi:A\\to B$ be a homomorphism of commutative rings, $\\mathfrak p\\subset A$ a prime ideal with residue field $\\kappa(\\mathfrak p)=A_{\\mathfrak p}/\\mathfrak pA_{\\mathfrak p}$ [def-weil-pbc-localization-at-prime], $C=B\\otimes_A\\kappa(\\mathfrak p)$ the fibre ring and $j:B\\to C$, $b\\mapsto b\\otimes1$. For a prime $\\mathfrak q\\subset B$ with $\\varphi^{-1}(\\mathfrak q)=\\mathfrak p$ let $\\kappa(\\mathfrak q)=B_{\\mathfrak q}/\\mathfrak qB_{\\mathfrak q}$ and let $\\psi_{\\mathfrak q}:C\\to\\kappa(\\mathfrak q)$ be the ring map $b\\otimes\\lambda\\mapsto\\bar b\\,\\bar\\lambda$, where $\\bar b$ is the image of $b$ and $\\bar\\lambda$ the image of $\\lambda$ under the map $\\kappa(\\mathfrak p)\\to\\kappa(\\mathfrak q)$ induced by $\\varphi$. Then (1) the map $\\mathfrak Q\\mapsto j^{-1}(\\mathfrak Q)$ is a bijection from the set of prime ideals of $C$ onto the set of prime ideals $\\mathfrak q\\subset B$ with $\\varphi^{-1}(\\mathfrak q)=\\mathfrak p$, with inverse $\\mathfrak q\\mapsto\\ker\\psi_{\\mathfrak q}$, and it preserves and reflects inclusions; (2) for each such $\\mathfrak q$, with $\\mathfrak Q=\\ker\\psi_{\\mathfrak q}$, the map $\\psi_{\\mathfrak q}$ induces an isomorphism of fields $\\kappa(\\mathfrak Q)=C_{\\mathfrak Q}/\\mathfrak QC_{\\mathfrak Q}\\xrightarrow{\\sim}\\kappa(\\mathfrak q)$; in other words $\\psi_{\\mathfrak q}$ is the composite of $C\\to\\kappa(\\mathfrak Q)$ with this isomorphism. (Residue fields as in [def-weil-residue-field] at the points of $\\operatorname{Spec}$ [def-weil-affine-spectrum].)"
 },
 {
  "step": 6,
  "node": "lem-trf-refined-noether-normalization-prime",
  "quote": "Let $k$ be a field, let $n\\ge0$, and let $\\mathfrak q\\subset k[x_1,\\ldots,x_n]$ be a prime ideal. Put $r=\\operatorname{trdeg}_k\\kappa(\\mathfrak q)$, with residue field and transcendence degree as in [def-weil-residue-field, def-kun-transcendence-degree]. Then there exists a finite $k$-algebra homomorphism $\\varphi:k[y_1,\\ldots,y_n]\\to k[x_1,\\ldots,x_n]$ [def-weil-pbc-mv-polynomial-ring] such that $\\varphi^{-1}(\\mathfrak q)=(y_{r+1},\\ldots,y_n)$."
 },
 {
  "step": 6,
  "node": "def-weil-pbc-localization-at-prime",
  "quote": "Let $R$ be a commutative ring and $\\mathfrak p\\subset R$ a prime ideal. The *localization* $R_{\\mathfrak p}=S^{-1}R$, $S=R\\setminus\\mathfrak p$, is the ring of fractions $r/s$ ($r\\in R$, $s\\in S$, with $r/s=r'/s'$ iff $u(rs'-r's)=0$ for some $u\\in S$), with the ring map $R\\to R_{\\mathfrak p}$, $r\\mapsto r/1$; it is a local ring with maximal ideal $\\mathfrak pR_{\\mathfrak p}$. The *residue field* of $\\mathfrak p$ is $\\kappa(\\mathfrak p)=R_{\\mathfrak p}/\\mathfrak pR_{\\mathfrak p}$, an $R$-algebra. For an $R$-algebra $\\Lambda$ (a ring map $R\\to\\Lambda$) the *fibre ring* of $\\Lambda$ over $\\mathfrak p$ is the tensor product of $R$-algebras $\\Lambda\\otimes_R\\kappa(\\mathfrak p)$, a $\\kappa(\\mathfrak p)$-algebra; it is isomorphic to $\\Lambda_{\\mathfrak p}/\\mathfrak p\\Lambda_{\\mathfrak p}$, $\\Lambda_{\\mathfrak p}$ the localization of $\\Lambda$ at the image of $R\\setminus\\mathfrak p$."
 },
 {
  "step": 6,
  "node": "def-weil-pbc-mv-polynomial-ring",
  "quote": "Let $R$ be a commutative ring and $J$ a set. The *polynomial ring* $R[x_j:j\\in J]$ is the commutative $R$-algebra whose elements are the finite $R$-linear combinations $\\sum_\\alpha c_\\alpha x^\\alpha$ of monomials $x^\\alpha=\\prod_jx_j^{\\alpha_j}$ ($\\alpha:J\\to\\mathbf Z_{\\ge0}$ finitely supported), with coefficientwise addition and the product determined by $x^\\alpha x^\\beta=x^{\\alpha+\\beta}$ and $R$-bilinearity; $R\\to R[x_j:j\\in J]$, $c\\mapsto c\\,x^0$, is its structure map. (For $J=\\{1,\\dots,n\\}$ one writes $R[x_1,\\dots,x_n]$.) Universal property: for every commutative $R$-algebra $C$ and every family $(c_j)_{j\\in J}$ of elements of $C$ there is a unique $R$-algebra homomorphism $R[x_j:j\\in J]\\to C$ with $x_j\\mapsto c_j$ for all $j$ (evaluation, $\\sum c_\\alpha x^\\alpha\\mapsto\\sum c_\\alpha\\prod_jc_j^{\\alpha_j}$); in particular two $R$-algebra homomorphisms out of $R[x_j:j\\in J]$ that agree on every $x_j$ are equal."
 },
 {
  "step": 7,
  "node": "def-sbc-affine-space",
  "quote": "For a scheme $S$ [def-pc-scheme], with the conventions of [def-weil-pbc-scheme-conventions] and $n\\in\\mathbb N$, the affine $n$-space over $S$ is the scheme\n$$\\mathbf A^n_S=S\\times_{\\operatorname{Spec}\\mathbb Z}\\operatorname{Spec}(\\mathbb Z[x_1,\\ldots,x_n])$$\nwith its first projection to $S$ [def-pc-fibre-product, def-weil-affine-spectrum]. Equivalently, this is the relative spectrum $\\underline{\\operatorname{Spec}}_S(\\mathcal O_S[x_1,\\ldots,x_n])$, where the polynomial algebra sheaf is locally the polynomial algebra on $n$ variables. Over an affine open $U=\\operatorname{Spec}R$ of $S$, its restriction is canonically $\\operatorname{Spec}(R[x_1,\\ldots,x_n])$ with structure map induced by the inclusion of constants. For $n=0$, the projection $\\mathbf A^0_S\\to S$ is a canonical isomorphism; the notation $\\mathbf A^0_S=S$ uses this identification. Smoothness is a separate statement, [sbc-lem-affine-space-smooth]."
 },
 {
  "step": 7,
  "node": "def-weil-finite-type-morphism",
  "quote": "A morphism of schemes $f:X\\to Y$ is *locally of finite type* if, for every\naffine open $V=\\operatorname{Spec}A$ of $Y$, the preimage $f^{-1}(V)$ has an\naffine open cover by $\\operatorname{Spec}B$ with $B$ a finitely generated\n$A$-algebra. It is *quasi-compact* if every such preimage is quasi-compact.\nIt is *of finite type* if both conditions hold; equivalently, the affine\ncover of each $f^{-1}(V)$ can be chosen finite. For a scheme over a field,\nfinite type refers to its structure morphism. See\n[Stacks Project, Section 29.15](https://stacks.math.columbia.edu/tag/01T0)."
 },
 {
  "step": 7,
  "node": "pqf-def-quasifinite",
  "quote": "Let $f:X\\to S$ be a morphism of schemes.\n\n1. $f$ is *quasi-finite at a point $x\\in X$* if there exist an\naffine neighbourhood $\\operatorname{Spec}A=U\\subset X$ of $x$ and\nan affine open $\\operatorname{Spec}R=V\\subset S$ with\n$f(U)\\subset V$ such that the ring map $R\\to A$ is of finite type\nand quasi-finite at the prime of $A$ corresponding to $x$.\n1. $f$ is *locally quasi-finite* if it is quasi-finite at every\npoint of $X$.\n1. $f$ is *quasi-finite* if it is of finite type and every point\nof $X$ is an isolated point of its fibre.\n\nThis is Stacks Project, Morphisms of Schemes, Tag\n[01TD](https://stacks.math.columbia.edu/tag/01TD). We say that\n$f$ *has finite fibres* if for every $s\\in S$ the set\n$f^{-1}(\\{s\\})$ is finite; the *fibre* of $f$ at $s$ is the scheme\n$X_s=X\\times_S\\operatorname{Spec}\\kappa(s)$."
 },
 {
  "step": 7,
  "node": "lem-weil-pbc-affine-scheme-qcqs",
  "quote": "Let $X$ be an affine scheme, i.e. a scheme [def-pc-scheme] isomorphic to $\\operatorname{Spec}A$ for a commutative ring $A$ [def-weil-affine-spectrum]. Then $X$ is quasi-compact (its underlying topological space is quasi-compact [def-weil-pbc-quasi-compact-scheme]) and quasi-separated ($X\\to\\operatorname{Spec}\\mathbf Z$ is quasi-separated [def-weil-pbc-scheme-conventions]; equivalently the intersection of two quasi-compact open subsets of $X$ is quasi-compact)."
 },
 {
  "step": 7,
  "node": "pqf-lem-qf-locqf-qc",
  "quote": "Let $f:X\\to S$ be a morphism of schemes. Then $f$ is quasi-finite if\nand only if $f$ is locally quasi-finite and quasi-compact."
 },
 {
  "step": 7,
  "node": "pqf-lem-qf-finitefibres",
  "quote": "Let $f:X\\to S$ be a morphism of schemes. Then $f$ is\nquasi-finite if and only if $f$ is\nlocally of finite type, of finite type, quasi-compact and has finite\nfibres.\n(*Stacks Project, Morphisms of Schemes, Lemma 29.21.10, Tag\n[02NH](https://stacks.math.columbia.edu/tag/02NH).*)"
 },
 {
  "step": 7,
  "node": "lem-weil-pbc-fibre-product-affine-spectra",
  "quote": "Let $R$ be a commutative ring and $A,B$ commutative $R$-algebras, and let $\\operatorname{Spec}A\\to\\operatorname{Spec}R$, $\\operatorname{Spec}B\\to\\operatorname{Spec}R$ be the morphisms induced by the structure maps [def-weil-affine-spectrum]. Then there is an isomorphism $\\operatorname{Spec}A\\times_{\\operatorname{Spec}R}\\operatorname{Spec}B\\cong\\operatorname{Spec}(A\\otimes_RB)$ [def-pc-fibre-product] under which the two projections become $\\operatorname{Spec}$ of the ring maps $A\\to A\\otimes_RB$, $a\\mapsto a\\otimes1$, and $B\\to A\\otimes_RB$, $b\\mapsto1\\otimes b$. In particular the fibre product is affine with ring of global sections $A\\otimes_RB$."
 },
 {
  "step": 7,
  "node": "lem-weil-pbc-principal-localization-open-immersion",
  "quote": "Let $A$ be a commutative ring and $f\\in A$, and let $A_f$ be the localization of $A$ at the multiplicative set $\\{1,f,f^2,\\dots\\}$. Then the morphism of schemes $\\operatorname{Spec}A_f\\to\\operatorname{Spec}A$ induced by the localization map $A\\to A_f$ is an open immersion [def-weil-open-immersion] (with image the principal open $D(f)$)."
 },
 {
  "step": 8,
  "node": "lem-weil-pbc-fibre-ring-primes-residue-fields",
  "quote": "Let $\\varphi:A\\to B$ be a homomorphism of commutative rings, $\\mathfrak p\\subset A$ a prime ideal with residue field $\\kappa(\\mathfrak p)=A_{\\mathfrak p}/\\mathfrak pA_{\\mathfrak p}$ [def-weil-pbc-localization-at-prime], $C=B\\otimes_A\\kappa(\\mathfrak p)$ the fibre ring and $j:B\\to C$, $b\\mapsto b\\otimes1$. For a prime $\\mathfrak q\\subset B$ with $\\varphi^{-1}(\\mathfrak q)=\\mathfrak p$ let $\\kappa(\\mathfrak q)=B_{\\mathfrak q}/\\mathfrak qB_{\\mathfrak q}$ and let $\\psi_{\\mathfrak q}:C\\to\\kappa(\\mathfrak q)$ be the ring map $b\\otimes\\lambda\\mapsto\\bar b\\,\\bar\\lambda$, where $\\bar b$ is the image of $b$ and $\\bar\\lambda$ the image of $\\lambda$ under the map $\\kappa(\\mathfrak p)\\to\\kappa(\\mathfrak q)$ induced by $\\varphi$. Then (1) the map $\\mathfrak Q\\mapsto j^{-1}(\\mathfrak Q)$ is a bijection from the set of prime ideals of $C$ onto the set of prime ideals $\\mathfrak q\\subset B$ with $\\varphi^{-1}(\\mathfrak q)=\\mathfrak p$, with inverse $\\mathfrak q\\mapsto\\ker\\psi_{\\mathfrak q}$, and it preserves and reflects inclusions; (2) for each such $\\mathfrak q$, with $\\mathfrak Q=\\ker\\psi_{\\mathfrak q}$, the map $\\psi_{\\mathfrak q}$ induces an isomorphism of fields $\\kappa(\\mathfrak Q)=C_{\\mathfrak Q}/\\mathfrak QC_{\\mathfrak Q}\\xrightarrow{\\sim}\\kappa(\\mathfrak q)$; in other words $\\psi_{\\mathfrak q}$ is the composite of $C\\to\\kappa(\\mathfrak Q)$ with this isomorphism. (Residue fields as in [def-weil-residue-field] at the points of $\\operatorname{Spec}$ [def-weil-affine-spectrum].)"
 },
 {
  "step": 8,
  "node": "def-weil-pbc-localization-at-prime",
  "quote": "Let $R$ be a commutative ring and $\\mathfrak p\\subset R$ a prime ideal. The *localization* $R_{\\mathfrak p}=S^{-1}R$, $S=R\\setminus\\mathfrak p$, is the ring of fractions $r/s$ ($r\\in R$, $s\\in S$, with $r/s=r'/s'$ iff $u(rs'-r's)=0$ for some $u\\in S$), with the ring map $R\\to R_{\\mathfrak p}$, $r\\mapsto r/1$; it is a local ring with maximal ideal $\\mathfrak pR_{\\mathfrak p}$. The *residue field* of $\\mathfrak p$ is $\\kappa(\\mathfrak p)=R_{\\mathfrak p}/\\mathfrak pR_{\\mathfrak p}$, an $R$-algebra. For an $R$-algebra $\\Lambda$ (a ring map $R\\to\\Lambda$) the *fibre ring* of $\\Lambda$ over $\\mathfrak p$ is the tensor product of $R$-algebras $\\Lambda\\otimes_R\\kappa(\\mathfrak p)$, a $\\kappa(\\mathfrak p)$-algebra; it is isomorphic to $\\Lambda_{\\mathfrak p}/\\mathfrak p\\Lambda_{\\mathfrak p}$, $\\Lambda_{\\mathfrak p}$ the localization of $\\Lambda$ at the image of $R\\setminus\\mathfrak p$."
 },
 {
  "step": 8,
  "node": "lem-weil-pbc-localization-prime-residue-field-iso",
  "quote": "Let $A$ be a commutative ring, $W\\subseteq A$ a multiplicative subset and $\\lambda:A\\to A'$ a homomorphism of commutative rings which is a localization of $A$ at $W$: (a) $\\lambda(w)$ is a unit for every $w\\in W$; (b) every element of $A'$ is $\\lambda(a)\\lambda(w)^{-1}$ with $a\\in A$, $w\\in W$; (c) $\\lambda(a)=0$ implies $wa=0$ for some $w\\in W$ (for instance $A'=W^{-1}A$ with $a\\mapsto a/1$). Let $\\mathfrak q'\\subset A'$ be a prime ideal and $\\mathfrak q=\\lambda^{-1}(\\mathfrak q')$. Then: (1) $\\mathfrak q$ is a prime ideal of $A$ with $\\mathfrak q\\cap W=\\emptyset$; conversely, for every prime ideal $\\mathfrak p\\subset A$ with $\\mathfrak p\\cap W=\\emptyset$ the ideal $\\mathfrak pA'$ generated by $\\lambda(\\mathfrak p)$ is a prime ideal of $A'$ with $\\lambda^{-1}(\\mathfrak pA')=\\mathfrak p$, and $\\lambda(\\lambda^{-1}(\\mathfrak q'))A'=\\mathfrak q'$, so $\\mathfrak q'\\mapsto\\lambda^{-1}(\\mathfrak q')$ is a bijection from the primes of $A'$ onto the primes of $A$ disjoint from $W$, with inverse $\\mathfrak p\\mapsto\\mathfrak pA'$; (2) the composite $A\\xrightarrow{\\lambda}A'\\to A'_{\\mathfrak q'}$ is a localization of $A$ at $A\\setminus\\mathfrak q$ (in the sense of (a)-(c) with $W$ replaced by $A\\setminus\\mathfrak q$), so the ring map $A_{\\mathfrak q}\\to A'_{\\mathfrak q'}$, $a/s\\mapsto\\lambda(a)/\\lambda(s)$, is an isomorphism of $A$-algebras [def-weil-pbc-localization-at-prime]; (3) this isomorphism carries $\\mathfrak qA_{\\mathfrak q}$ onto $\\mathfrak q'A'_{\\mathfrak q'}$ and induces an isomorphism of fields and of $A$-algebras $\\sigma:\\kappa(\\mathfrak q)=A_{\\mathfrak q}/\\mathfrak qA_{\\mathfrak q}\\xrightarrow{\\sim}\\kappa(\\mathfrak q')=A'_{\\mathfrak q'}/\\mathfrak q'A'_{\\mathfrak q'}$, where $\\kappa(\\mathfrak q')$ is an $A$-algebra via $A\\to A'\\to\\kappa(\\mathfrak q')$."
 },
 {
  "step": 8,
  "node": "def-kun-transcendence-degree",
  "quote": "Let $K\\subseteq L$ be a field extension (more generally, let $A$ be a commutative algebra over a commutative ring $K$). A family of elements of $L$ is *algebraically independent* over $K$ if no nonzero polynomial with coefficients in $K$ vanishes on it. The *transcendence degree* $\\operatorname{trdeg}_KL$ is the supremum of the cardinalities of the subsets of $L$ that are algebraically independent over $K$; for a field extension it equals the cardinality of any transcendence basis of $L$ over $K$. In particular $\\operatorname{trdeg}_KL\\le a$ for an integer $a\\ge0$ means that every algebraically independent subset of $L$ has at most $a$ elements."
 },
 {
  "step": 8,
  "node": "def-weil-residue-field",
  "quote": "Let $X$ be a scheme and $x\\in X$ a point, with local ring $\\mathcal O_{X,x}$ (the stalk of the structure sheaf at $x$) and maximal ideal $\\mathfrak m_x$. The *residue field* of $X$ at $x$ is the field\n\n$$\n \\kappa(x)=\\mathcal O_{X,x}/\\mathfrak m_x .\n$$\n\nA morphism of schemes $f:X\\to Y$ induces, for every $x\\in X$, a homomorphism of fields $\\kappa(f(x))\\to\\kappa(x)$, the map induced on residue fields by the local homomorphism $\\mathcal O_{Y,f(x)}\\to\\mathcal O_{X,x}$. For $Y=\\operatorname{Spec}K$ with $K$ a field, $\\kappa(f(x))=K$, so $\\kappa(x)$ is a field extension of $K$ through $f$."
 }
]

```
