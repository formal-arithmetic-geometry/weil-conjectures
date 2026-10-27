# Repair delivery: det-sp-tower-gamma

## Files written

- dag/nodes/sec-smooth-purity/det-sp-tower-gamma.json: repaired split; unchanged statement; five assembly steps, 2262 characters.
- dag/nodes/sec-smooth-purity/lem-sp-finite-orientation-reduction.json: statement; unsplit; no exact or one-line Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- dag/nodes/sec-smooth-purity/lem-sp-strict-line-heart-assembly.json: statement; unsplit; no exact or one-line Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- dag/nodes/sec-smooth-purity/lem-sp-twisted-pullback-tower-domain.json: statement; unsplit; no exact or one-line Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- dag/nodes/sec-smooth-purity/lem-sp-tower-tensor-transpose-evaluation.json: statement; unsplit; no exact or one-line Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- dag/nodes/sec-smooth-purity/lem-sp-compact-support-tower-reduction.json: statement; unsplit; no exact or one-line Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- dag/nodes/sec-smooth-purity/lem-sp-purity-conjugates-tower-reduction.json: statement; unsplit; no exact or one-line Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.

## Attachments

None. The item tag and tower-purity concepts have no exact project declaration. The finite Reduction.lean theorem assumes coefficient compatibilities rather than constructing these strict towers; it is not an attachment.

## WANTED

None. The current blueprint, its ancestor integral-adjunction proof, and all cited DAG interfaces are present.

## What was wrong and what changed

The released stage-1 repair note overrides the historical 2026-10-17 passing review. The live proof had ten steps totalling 10925 characters, although its individual steps were short enough for the earlier rule. The sandbox was empty except dispatcher markers and the searches begun in this session, so the live reviewed version is the returned baseline. I extracted six independent statement-only work items, not one replacement for the entire proposition. No parent hypothesis or conclusion changed. The previously documented orientation-direction correction is retained: twist to dualizing object, then 1 tensor a, as required by the displayed source and target. The source wording about its inverse is the known slip, not a new statement change.

## Unfinished work

Each new lemma deliberately has status unsplit, proof=[], proof_deps=[] and proof_origin=null, as the repair order requires. Other workers can prove these separately. No Lean file was written and no compiler, Lake or build was run.

## Not duplicates

lem-sp-finite-orientation-reduction vs det-sp-reduction-compatibilities: the latter supplies a general purity square for its general-ring orientation; the new statement identifies the actual finite diagonal orientation at index en with coefficient-unit purity and then its actual tower reductions.
lem-sp-finite-orientation-reduction vs det-sp-finite-general-ring: the latter identifies general-ring and direct diagonal orientations, but does not give the coefficient-unit transpose identity and its tower transition interpretation.
lem-sp-strict-line-heart-assembly vs lem-sf-derived-concentrated-single: concentration alone does not lift the prescribed compatible finite morphisms through semilinear tower transitions.
lem-sp-strict-line-heart-assembly vs lem-weil-pbc-derived-single-fully-faithful: full faithfulness of the heart embedding does not state the strict varying-coefficient assembly and its prescribed evaluations.
lem-sp-strict-line-heart-assembly vs lem-pur-adic-normalized-purity-lift: that node concerns reductions of an already integral K, uniformizer indexing and a restricted-scalar tower; the new lemma works for an arbitrary ambient varying-coefficient object and specified shifted line maps.
lem-sp-strict-line-heart-assembly vs lem-pur-compatible-coefficient-tower: that node constructs ordinary tensor transitions; it does not lift prescribed morphisms in D(Tow) via single-degree cohomology.
lem-sp-twisted-pullback-tower-domain vs lem-sf-pullback-tor-amplitude: finite pullback alone does not give shifted twist bounds, two tower inputs or their etale-origin projection witnesses.
lem-sp-twisted-pullback-tower-domain vs lem-pur-system-normalized-tensor-closure: that node assumes normalization and proves tensor/inverse-image reduction formulas; here input towers may be unnormalized and the conclusion is uniform constructibility, amplitude and the projection domain.
lem-sp-tower-tensor-transpose-evaluation vs det-sp-tower-shriek-levels: the latter provides tower operations and finite evaluation of projection, but not the particular exceptional-adjunction transpose and its specified purity-map evaluation.
lem-sp-tower-tensor-transpose-evaluation vs lem-pur-tower-tensor-transpose-ground-field-retagging: the latter compares already defined transposes under ground-field retagging and cites the parent; it cannot construct the transpose here without circularity.
lem-sp-compact-support-tower-reduction vs det-sp-reduction-direct-image: finite b-isomorphisms alone do not identify the actual transition of Rp_* j_! on a strict tower or its uniform bound.
lem-sp-compact-support-tower-reduction vs det-sp-tower-bound-uniform: the latter gives bounds, not the actual transition factorization with the compactification-normalized b.
lem-sp-compact-support-tower-reduction vs lem-sf-package-compactified-tower-comparisons: that statement compares integral reduction and coefficient functors, rather than arbitrary unnormalized strict varying-coefficient towers and their actual quotient reductions.
lem-sp-purity-conjugates-tower-reduction vs det-sp-reduction-compatibilities: the latter compares purity across coefficient rings at a fixed K; the new statement includes the actual K transition, finite naturality in that transition and the resulting solved conjugacy formula for arbitrary towers.
lem-sp-purity-conjugates-tower-reduction vs lem-pur-system-normalized-tensor-closure: the latter supplies tensor and pullback normalization but no exceptional functor or diagonal-purity conjugacy.
lem-sp-purity-conjugates-tower-reduction vs lem-pur-adic-normalized-purity-lift: the latter concerns an integral reduction system and the existence of a restricted-scalar lift; the new statement is an explicit conjugacy formula for arbitrary, possibly unnormalized towers.

Blueprint searches run before creation: orientation reduction, tower heart, tower projection, tower reduction, purity reduction, tower transpose, and tower. The isolated Kummer-additivity hit is about c1 classes, not any new statement. Full-DAG concept and title searches, including every chapter, found the interfaces distinguished above. No new node is merely a restatement of a parent clause: finite compatibility, an abstract shifted-line lifting criterion, source-domain hypotheses, an evaluation formula, and two transition identities are the work items; the parent constructs the orientation, tests finite isomorphy and applies normalization.

## Review by Q112

I read the current main-20261015 gamma statement and its proof (1)-(3), the integral-adjunction ancestor Normalization/Purity paragraphs, the unit and chapter records, and all statements used by the retained ten-step proof. Each new node cites the gamma proof at its allocated precise place; the route remains diagonal/DNC, never an SGA trace route. For the abstract heart ingredient I also read the existing single-degree and fully faithful nodes, and the Mathlib concentration and singleFunctor sources returned by the searches. The whole old argument is reproduced below to preserve every task for the later workers.
Assembly step 1 uses the finite-orientation node for a_n=gamma(unit), coefficient compatibility and the actual omega reductions; scalar-extension-functor(3) says explicitly that rank-one sheaves reduce ordinarily and Tate twists reduce canonically; strict-line-heart-assembly gives the resulting derived isomorphism with the specified finite evaluations. Its hypotheses hold for the quotient Tate line tower. This does not assume that arbitrary compatible derived maps lift.
Assembly step 2 uses twisted-pullback-tower-domain for common Tor/cohomological bounds, finite-Tor etale-origin witnesses for both projection inputs and projection invertibility. It then uses tensor-transpose-evaluation for an actual map before evaluating it, the precise finite theta and gamma formulas and naturality. Those are conclusions of the cited statements, not facts taken from their proofs.
Assembly step 3 uses finite-coefficient-smooth-purity at index en (ramification is explicitly accounted for), tower-gluing for target membership and the finite adjunction, tower-shriek-levels(3) for conservativity, and normalized-towers for the full uniform category. Conservativity is used only after step 2 has produced the morphism. No normalization assumption is added to clause (2). The old step 8 argument, including full-subcategory invertibility, is retained here.
Assembly step 4 uses compact-support-tower-reduction for the actual b-factorization, constructibility and the [a,b+2d] interval; reduction-direct-image says b is invertible with no flatness hypothesis. Normalized-towers requires exactly those common bounds and invertible reductions. Applying a functor to an inverse is elementary. The new lemma does not simply assert parent clause (3).
Assembly step 5 uses purity-conjugates-tower-reduction for the actual P and GK reductions and the displayed conjugacy. It explicitly includes naturality applied to rho after finite coefficient extension and keeps its target-ring action. Invertibility follows by composing inverses; the uniform target membership was already checked. Normalized-towers supplies the definition being verified.
For new statements I checked d=0, f=id, the empty scheme, zero input, identity index n=m, ramified E, a zero-transition unnormalized tower and a nonflat quotient R_n to R_m. The arbitrary-tower lemmas make no unjustified normalized conclusion in the zero-transition case; only the parent steps 4-5 assume normalization. The heart lemma assumes invertible line reductions and a compatible derived family, which rules out the false assertion that any levelwise family can be lifted. I retained common bounds independently of n, and verified qcqs/Noetherian and both finite-Tor projection witnesses, not only one tensor input. Every assembly citation is quoted verbatim in citations.json. All new files are statement-only and have complete introduced objects and definition references. The parent proof is below both the 3000-character total and 2000-character individual-step limits.

## Preserved argument allocation (verbatim returned proof)

### lem-sp-finite-orientation-reduction

Allocated old steps 1, 2. The following is retained report material for the future worker, not a proof field of the unsplit node.

Old step 1:

Write $R_n=\mathcal O_E/\ell^n$. If $\ell=u\varpi_E^e$ with $u$ a unit, then $(\ell^n)=(\varpi_E^{en})$, so $R_n=A_{E,en}$: every finite purity statement applies at index $en$, including when $E$ is ramified. Let $a_n:R_{n,X}(d)[2d]\to f_{R_n}^!R_{n,Y}$ be the inverse of the finite diagonal isomorphism [thm-pur-diagonal-dualizing-object]. Equivalently $a_n=\gamma_{f,R_n}(R_{n,Y})$: by [def-pur-smooth-purity-map] the latter is the inverse orientation followed by the tensor map at the tensor unit. By [def-pur-co-smoothness] this tensor map is the transpose of the counit $Rf_{!,R_n}\omega_{f,n}\to R_{n,Y}$, hence is $1_{\omega_{f,n}}$ by the adjunction triangle identity. Here the projection map with coefficient-unit second input is the identity under the unit identifications: in the defining formula of [def-exchange-projection], its proper factor is $Rp_*(\varepsilon_p)\circ\eta_p=1$ and its open-immersion factor is the tensor-unit identification. Thus this construction uses exactly the diagonal/DNC normalization, with orientation pointing from twist to dualizing object.

Cited statements: thm-pur-diagonal-dualizing-object, def-pur-smooth-purity-map, def-pur-co-smoothness, def-exchange-projection.

Old step 2:

For $n\geq m$, apply [det-sp-reduction-compatibilities](3) to $R_n\twoheadrightarrow R_m$ and $K=R_{n,Y}$. The purity maps in that clause are those of [det-sp-finite-general-ring](3), built from the orientation of its clause (1); by its clause (2) that orientation agrees with the one obtained by running the diagonal construction directly with $R_n=A_{E,en}$-coefficients, i.e. with the finite diagonal isomorphism of [thm-pur-diagonal-dualizing-object] at index $en$, and its tensor map is the transpose $\theta$ of step 1. Hence its $\gamma_{f,R_n}(R_{n,Y})$ is $a_n$ of step 1, and likewise at $R_m$. The clause therefore gives $c_{n,m}(R_{n,Y})\circ(a_n)_{R_m}=a_m$ under the canonical twist reduction. These twist reductions are ordinary reductions of rank-one locally free sheaves by [det-sp-scalar-extension-functor](3). By [det-sp-tower-gluing](3), the reduction maps of $\omega_{f,\bullet}=G_\bullet R_{\bullet,Y}$ are precisely $c_{n,m}(R_{n,Y})$, since the coefficient-unit reduction maps are identities. This is the required compatibility of the finite orientations with the actual transitions of the tower, and does not infer coefficient compatibility from uniqueness for a fixed coefficient ring.

Cited statements: det-sp-reduction-compatibilities, det-sp-scalar-extension-functor, det-sp-tower-gluing, det-sp-finite-general-ring.

### lem-sp-strict-line-heart-assembly

Allocated old steps 3. The following is retained report material for the future worker, not a proof field of the unsplit node.

Old step 3:

We construct a morphism in the derived category of strict towers, rather than assuming that a compatible family of arbitrary derived morphisms lifts. By the chart formula of [det-sp-tower-gluing](1), $\omega_{f,\bullet}[-2d]$ has cohomology only in degree zero. Alternatively its evaluations do, by step 1; exact, jointly conservative evaluation in the abelian tower category [det-sp-coefficient-towers-abelian] detects the vanishing of each other cohomology sheaf. Put $W_\bullet=H^0(\omega_{f,\bullet}[-2d])$. By [lem-sf-derived-concentrated-single] at degree zero, $W_\bullet[0]\simeq\omega_{f,\bullet}[-2d]$. At each level, $a_n[-2d]$ is a unique map of sheaves $R_{n,X}(d)\to W_n$ by [lem-weil-pbc-derived-single-fully-faithful]. Write $\alpha_n:R_{n,X}(d)\to W_n$ for these sheaf isomorphisms, $q_{n,m}$ for the Tate quotient transition, and $t^W_{n,m}$ for the transition of $W_\bullet$. By [det-sp-coefficient-towers-abelian](3), the reduction map of $W_\bullet[0]$ is induced by $t^W_{n,m}$. Each $W_n$ is locally free of rank one via $\alpha_n$, so its derived reduction is its ordinary tensor reduction by [det-sp-scalar-extension-functor](3). Consequently step 2, after removing the shift and using full faithfulness, reads $t^W_{n,m}\circ\alpha_n=\alpha_m\circ q_{n,m}$ as an equality of semilinear sheaf maps. Multiplying this equality by the two inverses gives $\alpha_m^{-1}\circ t^W_{n,m}=q_{n,m}\circ\alpha_n^{-1}$. By [sk-def-sp-coefficient-towers] they therefore define an actual map of tower sheaves $R_{\bullet,X}(d)\to W_\bullet$. Its inverse family also commutes with transitions, so it is an isomorphism of tower sheaves. Shifting by $[2d]$ gives $a_\bullet$ in clause (1), with exactly the prescribed finite levels.

Cited statements: det-sp-tower-gluing, det-sp-coefficient-towers-abelian, lem-sf-derived-concentrated-single, lem-weil-pbc-derived-single-fully-faithful, sk-def-sp-coefficient-towers, det-sp-scalar-extension-functor.

### lem-sp-twisted-pullback-tower-domain

Allocated old steps 4, 5, 6. The following is retained report material for the future worker, not a proof field of the unsplit node.

Old step 4:

Choose common Tor bounds $[a,b]$ for $K_\bullet$. At every level $R_n=A_{E,en}$, [lem-sf-pullback-tor-amplitude] applies to the separated finite-type morphism $f$ and the bounded constructible finite-Tor complex $K_n$. It gives constructible $f_{R_n}^*K_n$ with Tor interval $[a,b]$. The interval is independent of $n$, since the cited assertion preserves the specified interval, not just existence of some finite interval.

Cited statements: lem-sf-pullback-tor-amplitude.

Old step 5:

By [lem-pur-twist-sheaf-locally-free](3)-(4) and [def-coefficient-twists-detailed], $R_{n,X}(d)$ is a constructible locally free line: the unit if $d=0$, and a tensor power of the Tate line if $d>0$. Locally trivializing this line identifies tensoring with it with the identity, so it preserves the Tor interval $[a,b]$ and constructibility. Shifting by $[2d]$ changes the interval to $[a-2d,b-2d]$; testing the Tor bound on the coefficient unit gives the same cohomological bound. Thus $P_\bullet=f^*_\bullet K_\bullet(d)[2d]$ lies in the uniform constructible finite-Tor tower category [sk-def-sp-normalized-towers]. Step 3 identifies $Q_\bullet=f^*_\bullet K_\bullet\otimes^L\omega_{f,\bullet}$ with $P_\bullet$, so $Q_\bullet$ is also in the tower adjunction domain.

Cited statements: lem-pur-twist-sheaf-locally-free, def-coefficient-twists-detailed, sk-def-sp-normalized-towers.

Old step 6:

The finite-etale-origin hypotheses of [det-sp-tower-shriek-levels](2a) hold. A field is Noetherian because its only ideals are zero and the whole field. By [lem-weil-pbc-finite-type-over-noetherian], $X,Y$ are Noetherian, hence quasi-compact, and [lem-weil-pbc-locally-noetherian-quasi-separated] makes them quasi-separated. Every $R_n$ is a finite, hence Noetherian, ring. The equivalence of [det-pe-finite-tor-comparison-noetherian] therefore supplies a bounded constructible finite-Tor etale-origin witness for each intrinsic finite-Tor level of $K_\bullet$ and of $\omega_{f,\bullet}$ (the latter is a shifted Tate line by step 1). Steps 3 and 5 give common lower cohomological bounds. These are precisely the two input towers required for the projection formula; compatible choices of the witnesses are not required.

Cited statements: det-sp-tower-shriek-levels, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, det-pe-finite-tor-comparison-noetherian.

### lem-sp-tower-tensor-transpose-evaluation

Allocated old steps 7. The following is retained report material for the future worker, not a proof field of the unsplit node.

Old step 7:

Use [det-sp-tower-shriek-levels](2a) to form the tower projection-formula/counit composite $h:F_\bullet Q_\bullet\to K_\bullet$ displayed in the statement. The adjunction of [det-sp-tower-gluing] defines its transpose $t=G_\bullet(h)\circ\eta_\bullet(Q_\bullet)$. By clause (3) of that node, evaluation carries $G_\bullet$, its unit and its counit to the finite ones; the projection map evaluates to the finite projection map by [det-sp-tower-shriek-levels](2a). Hence $t_n=f^!_{R_n}(h_n)\circ\eta_{R_n}(Q_n)=\theta_{f,K_n}$, the specified transpose in [def-pur-co-smoothness]. Composing $t$ with $1\otimes a_\bullet$ and twist reassociation constructs an actual tower map $\gamma_{f,\bullet}(K_\bullet)$ whose level is exactly the map of [def-pur-smooth-purity-map]. Naturality follows from the natural adjunction bijection applied to the natural projection-formula/counit composite, then composition with the fixed orientation and natural twist reassociation. This constructs the map before testing its evaluations.

Cited statements: det-sp-tower-shriek-levels, det-sp-tower-gluing, def-pur-co-smoothness, def-pur-smooth-purity-map.

### lem-sp-compact-support-tower-reduction

Allocated old steps 9. The following is retained report material for the future worker, not a proof field of the unsplit node.

Old step 9:

Let $C_\bullet$ be normalized and write $\rho^C_{n,m}:(C_n)_{R_m}\to C_m$ for its reduction isomorphisms. The reduction map of $F_\bullet C_\bullet$ is
$$\rho^{FC}_{n,m}=Rf_{!,R_m}(\rho^C_{n,m})\circ b_{R_n,R_m}(C_n).$$
Indeed, evaluation of $Rp_{*,\bullet}j_{!,\bullet}$ is the finite compactification composite by [det-sp-tower-shriek-levels](1); its coefficient reduction is first the coefficient exchange for $Rp_*$ and the extension-by-zero tensor identification, followed by the image of $\rho^C_{n,m}$. This is precisely the defining compactification normalization of $b$ in [det-sp-reduction-direct-image]. Both factors of the displayed map are isomorphisms, the first because a functor preserves inverses and the second by that cited theorem. No flatness of $R_m$ over $R_n$ is assumed. For common input Tor bounds $[a,b]$, [det-sp-tower-bound-uniform] gives common output bounds $[a,b+2d]$ and levelwise constructibility, because the smooth morphism has all geometric fibres of dimension $d$. Thus the levelwise constructibility, level-independent cohomological and Tor amplitude bounds, and reduction-isomorphism condition in the current definition [sk-def-sp-normalized-towers] hold for $F_\bullet C_\bullet$.

Cited statements: det-sp-tower-shriek-levels, det-sp-reduction-direct-image, det-sp-tower-bound-uniform, sk-def-sp-normalized-towers.

### lem-sp-purity-conjugates-tower-reduction

Allocated old steps 10. The following is retained report material for the future worker, not a proof field of the unsplit node.

Old step 10:

Let $K_\bullet$ be normalized and put $P_\bullet=f^*_\bullet K_\bullet(d)[2d]$. Its reduction maps are $f_{R_m}^*(\rho^K_{n,m})(d)[2d]$ under the canonical coefficient identifications: pullback commutes with derived coefficient extension by [lem-pur-derived-pullback-tensor-iso], the twist reduction is [det-sp-scalar-extension-functor](3), and shifts commute termwise. These maps are isomorphisms; the common bounds and constructibility were checked in steps 4-5. For $G_\bullet K_\bullet$, [det-sp-tower-gluing](3) gives
$$\rho^{GK}_{n,m}=f_{R_m}^!(\rho^K_{n,m})\circ c_{n,m}(K_n).$$
By [det-sp-reduction-compatibilities](3), whose purity maps are, by [det-sp-finite-general-ring](2)-(3) as in step 2, the maps $\gamma_{f,R}$ of [def-pur-smooth-purity-map] used in steps 7-8, followed by naturality in $K$ of $\gamma_{f,R_m}$ ([det-sp-finite-general-ring](3); equivalently the argument of the last sentence of step 7 at one level), applied to $\rho^K_{n,m}:(K_n)_{R_m}\to K_m$, where $(K_n)_{R_m}\in\Dctf$ by [det-sp-scalar-extension-functor](2),
$$\begin{aligned}
\rho^{GK}_{n,m}\circ(\gamma_{f,R_n}(K_n))_{R_m}
&=f_{R_m}^!(\rho^K_{n,m})\circ\gamma_{f,R_m}((K_n)_{R_m})\\
&=\gamma_{f,R_m}(K_m)\circ f_{R_m}^*(\rho^K_{n,m})(d)[2d].
\end{aligned}$$
All three factors other than $\rho^{GK}_{n,m}$ are isomorphisms by steps 8 and the normalization of $K_\bullet$, so the displayed equation explicitly expresses $\rho^{GK}_{n,m}$ as a composite of isomorphisms. Its common cohomological and Tor bounds are those of $P_\bullet$ via step 8. This proves levelwise constructibility, level-independent cohomological and Tor bounds, and all reduction isomorphisms required by the current definition [sk-def-sp-normalized-towers], completing clause (3).

Cited statements: lem-pur-derived-pullback-tensor-iso, det-sp-scalar-extension-functor, det-sp-tower-gluing, det-sp-reduction-compatibilities, sk-def-sp-normalized-towers, det-sp-finite-general-ring.

### Assembly retains old step 8

Every level of the map in step 7 is an isomorphism by [thm-pur-finite-coefficient-smooth-purity], applied at index $en$. The source category membership and the common shifted Tor and cohomological bounds were verified before the transpose in steps 4-5. The target is in the same tower category by [det-sp-tower-gluing]. The level conservativity of [det-sp-tower-shriek-levels](3) now makes the already constructed map an isomorphism in the ambient tower derived category, and hence in the full subcategory $\Dctf(X_{\mathrm{proét}},\mathcal O_E/\ell^\bullet)$ of [sk-def-sp-normalized-towers]: both its source and target have constructible levels and cohomological and Tor amplitude bounds independent of the level. No reduction-isomorphism condition is needed for this subcategory. This proves every assertion of clause (2); preservation of the normalized subcategory is proved in steps 9-10.

