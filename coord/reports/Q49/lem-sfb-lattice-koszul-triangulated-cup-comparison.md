# Worker report

## Files written

The parent `lem-sfb-lattice-koszul-triangulated-cup-comparison` keeps its statement byte for byte and replaces its fourteen-step proof with three assembly steps (1858 characters). No Lean is written or compiled. The sandbox initially contained only dispatcher marker files, so the existing repository node was copied rather than inventing missing previous sandbox work. The initial mandated dry run exited with the diagnostic that report.md was missing.

- `lem-sfb-lattice-koszul-total-triangles`: statement, unsplit, no Mathlib match.
- `lem-sfb-lattice-koszul-injective-normalization`: statement, unsplit, no Mathlib match.
- `lem-sfb-lattice-cubical-augmentation-evaluation`: statement, unsplit, no Mathlib match.
- `lem-sfb-lattice-evaluation-derived-counit`: statement, unsplit, no Mathlib match.
- `lem-sfb-lattice-flat-twisted-chain-pairing`: statement, unsplit, no Mathlib match.
- `lem-sfb-lattice-cubical-multiplication-roof`: statement, unsplit, no Mathlib match.

## Attachments

None. A project-wide upstream search by the exact blueprint tag and by lattice/Koszul/cup and cubical/evaluation found no exact closed project declaration. The current Sheaf module has the main theorem ending in `sorry` (line 388); its existence is not an attachment. The existing Lean records are preserved.

## WANTED

WANTED: an ordinary internal condensed-module reference for the multiplicative Laurent–Koszul comparison, including connecting triangles. This was already explicitly wanted in the returned node's source. The current blueprint paragraph (3) supplies only the open-direct-image route; these calculations remain agent-origin, not a falsely attributed blueprint theorem.

## Return repaired

The return required at least four comparable statement-only nodes and a parent assembly of at most 3000 characters, with every old argument preserved. Six obligations divide the work: totalization; resolution-normalized comparison; contraction/evaluation; derived counit and monoidal normalization; flat chain pairing; diagonal and multiplication roofs. Each has an independent fully quantified statement, empty proof and proof_deps, null proof_origin, status unsplit, and five actual logged searches (two semantic phrasings, Loogle, grep, LeanSearch). None assumes the parent or carries the whole conclusion. No target or parent statement was changed.

## Not duplicates

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-tw-finite-projective-model-pullback: the latter treats bounded constant finite-projective O_E-models extended to completed coefficient sheaves and their normalized derived pullback along scheme morphisms; it gives neither arbitrary flat condensed algebras with lattice automorphisms nor the twisted Koszul chain pairing and its Leibniz identity. The common Tag 06YQ only supplies bounded-flat K-flatness; neither full statement specializes to the other.


lem-sfb-lattice-koszul-total-triangles vs lem-sfb-discrete-lattice-koszul-resolution: the existing node treats modules and a derived comparison; the new node treats complexes, signed shifts, cone maps and totalization descent.

lem-sfb-lattice-koszul-total-triangles vs lem-sfb-ringed-complete-triangulated: that node concerns completed coefficient categories and Koszul completion, not discrete-action cochain totalization.

lem-sfb-lattice-koszul-injective-normalization vs lem-sfb-discrete-lattice-koszul-resolution: the old module comparison is input, whereas the new obligation constructs the normalized injective-resolution comparison on all bounded-below complexes with its triangle compatibility.

lem-sfb-lattice-koszul-injective-normalization vs lem-sp-derived-injective-resolution-naturality: the generic resolution comparison does not construct the invariant-to-Koszul quasi-isomorphism b_J.

lem-sfb-lattice-cubical-augmentation-evaluation vs lem-sfb-integral-lattice-cubical-contraction: the existing statement is integral abelian-group contraction only; the new one internalizes it, proves the acyclic tensor test and gives signed equivariant evaluation for arbitrary bounded-below complexes.

lem-sfb-lattice-cubical-augmentation-evaluation vs lem-sfb-integral-cubical-chain-diagonal: the existing node gives the integral diagonal, not internal tensor augmentation or evaluation.

lem-sfb-lattice-evaluation-derived-counit vs lem-sfb-resolving-derived-adjunction-normalization: the abstract transpose normalization does not identify the explicit cubical roof.

lem-sfb-lattice-evaluation-derived-counit vs lem-sfb-exact-flat-tensor-derived-counit-comparison: the existing theorem supplies an abstract derived tensor comparison; the new obligation verifies the lattice action-site and flatness hypotheses and identifies the actual evaluation counit.

lem-sfb-lattice-evaluation-derived-counit vs def-sfb-lattice-derived-invariants-tensor: the old node specifies conventions; the new theorem realizes them on the explicit cubical evaluation model.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-pc-bounded-above-flat-kflat-site: the generic ringed-site K-flat criterion has no twisted pairing, equivariant tensor or internal-module comparison.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-sfb-discrete-lattice-cup-exterior: the exterior cohomology description does not state this nontrivial-action chain pairing.

lem-sfb-lattice-cubical-multiplication-roof vs lem-sfb-integral-cubical-chain-diagonal: the integral chain diagonal is input; the new claim identifies its internal evaluation composites and roof denominators, including the unit.

lem-sfb-lattice-cubical-multiplication-roof vs lem-sfb-lattice-koszul-triangulated-cup-comparison: the new statement is a chain-level diagonal/evaluation identity and contains no triangulated derived-invariants comparison or derived cup theorem.

The whole DAG was searched by Koszul/cubical together with lattice/triangulation/evaluation/twisted/cup on titles and statements, following the initial rg search. Blueprint searches used Koszul, cubical, Koszul total, injective comparison, evaluation roof, twisted cup, monoidal inflation and cubical multiplication across every chapter. The only related imported statements concern other constructions; none states a new obligation. The ancestor command reports a null imported ancestor for this already agent-created chain, retained exactly.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-pc-bounded-above-flat-tensor-acyclic-degree: fixed-degree exactness for a general bounded-flat total tensor gives neither commuting actions nor the twisted multiplication chain equation.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-sfb-ringed-finite-free-resolution-tensor: that result starts with a specified finite-free resolution over a ring sheaf and computes a derived tensor; B here is only flat over R and the main additional content is the twisted Koszul product.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-weil-pbc-completed-adic-koszul-kflat: completed exterior Koszul complexes of an adic scheme datum are different objects from finite cochains of a discrete lattice acting on an arbitrary internal algebra.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-weil-pbc-independent-bounded-flat-kflat: the generic K-flat criterion is available to prove one component but contains no twisted chain pairing or action category.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-weil-pbc-site-tensor-local-model-comparison: that node computes fixed-degree sheaf cohomology using supplied good-truncation models with constant coefficients, and gives no lattice product.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-weil-pbc-split-perfect-tensor-kinjective: its conclusion is K-injectivity after tensoring a bounded split-projective complex, whereas here the complexes are K-flat and a twisted chain product is asserted.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-sfb-constant-field-tor-bounds: constant field coefficients make Tor amplitude equal cohomological amplitude; the new claim allows arbitrary condensed R and nontrivial automorphisms.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-sfb-finite-flat-constructible-total-tensor: finite coefficient etale constructible complexes and Tor windows are its objects; neither constructibility nor finite coefficients are assumed here and no twisted product is given there.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-sfb-finite-free-mono-cokernel-kflat: specified finite-free monomorphisms give two-term cokernel resolutions; no such monomorphism is assumed here and the cochain product is absent.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-sfb-flat-scalar-cyclic-resolution: a two-term resolution by a nonzero scalar in a domain is not a complex of commuting automorphism differences with its twisted pairing.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-sfb-flat-scalar-tensor-resolution: scalar projective resolutions and their realized derived tensor are distinct from internal-algebra lattice cochains and their chain multiplication.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-sfb-flat-scalar-tensor-units: the derived tensor unit for module sheaves is only one general tensor identity and has no Koszul product or nontrivial action.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-sf-integral-line-tensor-comparison-representative: rank-one completed integral line tensors and finite reduction are not arbitrary flat equivariant-algebra Koszul pairings.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-trf-finite-filtered-flat-resolution: its filtered replacement theorem does not involve lattice actions or a chain multiplication formula.

lem-sfb-lattice-flat-twisted-chain-pairing vs def-trf-split-flat-filtered-sheaf-models: it defines filtered split-flat models and convolution filtration rather than proving any twisted product.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-sfb-flat-scalar-tor-comparison: its scalar Tor formula is not a chain multiplication or internal action statement.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-sfb-ringed-site-point-kflat-resolution: simultaneous K-flatness at a point for a chosen resolution does not give the explicit finite cochain model or multiplication.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-pur-etale-single-functor-monoidal-compatibility: its equations transport degree-zero pairings along inverse image, not positive-degree twisted lattice cochains.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-pur-constant-field-restriction-representatives: restriction along fields preserving K-flatness does not construct this product over an arbitrary condensed ring.

lem-sfb-lattice-flat-twisted-chain-pairing vs lem-pur-constant-two-term-resolution: the constant scalar ell-power resolution is a different two-term complex and lacks an automorphism-twisted chain product.

## Mathlib reading

Every new node's five queries are in searches.jsonl; full outputs are retained in search-*.txt and the queries themselves are recorded literally in the nodes. All services returned answers. I read the hits: totalShift₂Iso provides the expected (-1)^(a n) shift formula (TotalComplexShift.lean:313), but no descent/cone construction for this lattice total functor. isoRightDerivedObj_hom_naturality (RightDerived.lean:126) compares individual ordinary right-derived cohomology functors, not the required total derived model. Rep.standardResolution (Resolution.lean:324) is the ordinary representation bar/standard resolution, not internal cubical lattice evaluation. Other hits are general adjunction counits, Tor, coalgebra counits, simplicial faces, ordinary algebra flatness and inhomogeneous/Lie cochain differentials. They do not supply an exact match or a one-line specialization. One candidate-locator rg was inadvertently used on Mathlib; it was immediately rerun through msearch with exactly the same pattern, and that genuine logged result is recorded for the affected nodes. No unrun query is asserted.

## Review by Q49

I read the current main-20261015 direct-images proof paragraph (3), the whole returned fourteen-step node, its six relevant definitional interfaces, and every existing proof dependency's statement. The paragraph discusses ordinary open direct image and contains no cubical calculation; the source fields therefore say explicitly that these are agent extractions. For the flatness component I also read Stacks Tag 06YQ, sites-cohomology.tex, label lemma-bounded-flat-K-flat: it assumes a bounded-above flat complex on a ringed site, which applies after the stated internal/section equivalence because K_B is supported in degrees 0 through r. No SGA source is used.

Assembly step 1 uses the full total-triangles statement (exact components, homotopies, quasi-isomorphisms, concrete shifts/cones) and the full injective-normalization statement (b_J, its inverse formula, lift independence, connecting arrows and module/rank-zero normalization). Both statements explicitly give every assertion taken from them. The common lower bound and finite Koszul strip justify the existing row/column comparison; no unbounded convergence claim is added. The injective-normalization obligation retains the actual natural derived isomorphism, not merely matching cohomology.

Assembly step 2 uses flat-twisted-chain-pairing for K_B and tK_B being K-flat and for the exact product formula. Cubical-augmentation-evaluation supplies the actual chain maps E_P and the acyclic tensor augmentation, including the invariant square. Evaluation-derived-counit identifies that very roof with the counit after the very same lambda defined through b_J. Thus the proof does not silently choose an unrelated module isomorphism to obtain cup compatibility. I checked that the latter statement also supplies the small action-site tensor realization, closedness, functorial flat resolutions, exact strong monoidal trivial action, preservation of flat objects and the normalized flat-representative tensor identification previously justified by the off-unit generic tools. Those facts have moved into that statement-only obligation, not disappeared.

Assembly step 3 uses cubical-multiplication-roof for equality of actual chain maps and augmentation denominators, evaluation-derived-counit for the normalized tensor/counit identification and regular-coefficient compatibility, and def-sfb-lattice-algebra-derived-cup for the definition as the mate of two counits followed by multiplication. Equality follows by the adjunction bijection on morphisms. The unit is separately covered by the explicit evaluation-of-unit equation. This last assembly is a transpose chase, not a hidden uniqueness theorem from cohomology. Every uses entry has a verbatim statement quote in citations.json.

For the six new statements I checked all object introductions, coefficient universes, action automorphisms, boundedness and the exact-tensor meaning of flatness. They have no proof steps or proof sketches. They need no hypotheses on R being nonzero, reduced, a field or of any characteristic. The contraction is only nonequivariant after forgetting; no equivariant splitting of the augmentation is asserted. This matters already for r=1. I recomputed theta_(a,b+1)/theta_(a,b)=(-1)^a and theta_(a+1,b)/theta_(a,b)=(-1)^(a+b+1), and c_(p+q)=(-1)^(pq)c_p c_q. At r=0 every complex and augmentation is the identity and the product is ordinary multiplication. At r=1 the two diagonal terms and the identity (T-1)(xy)=(T-1)x T(y)+x(T-1)y agree with the new formulas. In characteristic two the sign identities still hold; over the zero ring or zero algebra all maps are zero with the same identities. The new contraction and pairing nodes state internal morphisms, not a false objectwise projectivity claim for R.

An independent finite-function-algebra calculation passed all 60 twisted Leibniz cases over F2 and F3, ranks 0 through 3 and all pairs of cochain degrees, with the coordinate-shift automorphisms on functions on (Z/2)^r. Separate integer-parity checks passed 108 evaluation-sign recurrences (a=0 through 5 and b=-4 through 4) and 36 diagonal-evaluation sign identities (p,q=0 through 5). These are small-case checks, not claimed Lean proofs.

No statement dispute was needed. The repaired defect is granularity: all arguments below are retained, while the parent is now short and six workers can take distinct obligations. Existing sources, original searches, Lean and historical review metadata on the parent were preserved; no maintainer tool_uses field was edited. Generic tools formerly used inline are documented below for the future splitters rather than cited without a statement in the parent.

## Argument allocation and retained source proof

The following is the complete returned argument, verbatim step texts and citations. It is reference material for the workers splitting the new nodes, not proof steps in those statement-only nodes. The decomposition is A=steps 1–3, B=4–6, C=7–8, D=9 plus ambient/normalized-counit part of 13, E=10–11, F=12 plus unit part of 13 and the low-rank cases 14. The concluding adjunction-transpose chase of 13 is also written in the parent. Thus no original argument is lost or replaced with an assertion of cohomological agreement.

### Original step 1

Write $\mathcal M=\operatorname{Mod}_R$ and $\mathcal E=\mathcal A_R(D)$. By [lem-sfb-condensed-derived-restriction-calculus] these are Grothendieck abelian, forgetting is exact and detects exactness, and the exact trivial-action functor $t:\mathcal M\to\mathcal E$ is left adjoint to $\Gamma$. In each Koszul degree $a$, $K^a$ is a finite biproduct of the underlying-module functor; kernels and cokernels are componentwise, so $K^a$ is exact. The differential of [lem-sfb-discrete-lattice-koszul-resolution] is natural in equivariant maps and squares to zero. Totalizing with $d_K+(-1)^a d_P$ therefore defines an additive functor on bounded-below complexes.

Cited nodes: lem-sfb-condensed-derived-restriction-calculus, lem-sfb-discrete-lattice-koszul-resolution.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), ordinary open direct image: agent expansion of the discrete-lattice calculation below the tame-boundary route.

### Original step 2

For a chain homotopy $h:P\to Q[-1]$, put $H|_{K^a(P^b)}=(-1)^aK^a(h^b)$. The horizontal terms in $dH+Hd$ cancel, and the vertical terms are $K^a(dh+hd)$, so totalization respects homotopy. For a quasi-isomorphism $f$, each fixed-$a$ column $K^a(f)$ is a quasi-isomorphism by exactness. The bicomplexes vanish for $a<0$ and for $b$ below a common integer. Thus [lem-weil-pbc-bounded-below-total-column-comparison] gives that $K(f)$ is a quasi-isomorphism. Consequently $K$ descends to $\mathsf K_R$ on $D^+$; its output is bounded below since $0\leq a\leq r$.

Cited nodes: lem-weil-pbc-bounded-below-total-column-comparison.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), ordinary open direct image: agent expansion of the discrete-lattice calculation below the tame-boundary route.

### Original step 3

Use the shift comparison $K(P[1])\to K(P)[1]$ that multiplies Koszul degree $a$ by $(-1)^a$. For $f:P\to Q$, use the cone convention $\operatorname{Cone}(f)^n=Q^n\oplus P^{n+1}$, with differential $(q,p)\mapsto(d_Qq+fp,-d_Pp)$. The map $K(\operatorname{Cone}f)\to\operatorname{Cone}(Kf)$ is identity on $K^aQ$ and multiplication by $(-1)^a$ on $K^aP[1]$. The horizontal differential on that second summand changes sign because $a$ increases by one; the vertical differential and off-diagonal $f$ term acquire precisely the displayed cone signs. It commutes with the inclusion of $KQ$ and, with the preceding shift comparison, the projection to $KP[1]$. Thus $K$ preserves cone triangles and descends as a triangulated functor under the cone-triangle definition of [def-weil-abstract-derived-category].

Cited nodes: def-weil-abstract-derived-category.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), ordinary open direct image: agent expansion of the discrete-lattice calculation below the tame-boundary route.

### Original step 4

For an injective $J\in\mathcal E$, its degree-zero injective resolution computes $R\Gamma(J)=\Gamma(J)[0]$, by [lem-sp-derived-injective-resolution-naturality]. The normalized comparison in [lem-sfb-discrete-lattice-koszul-resolution] consequently says that the actual inclusion $\Gamma(J)[0]\to K(J)$ is a quasi-isomorphism: after localization its composite with that isomorphism is the identity of $\Gamma(J)[0]$. For a bounded-below $P$, take a monomorphic quasi-isomorphism $s:P\to J$ with bounded-below injective terms using [lem-weil-pbc-complex-injective-resolution-mono]; enough injectives follows from [lem-sp-grothendieck-enough-injectives]. Each row inclusion just described is a quasi-isomorphism. The row version of [lem-weil-pbc-bounded-below-total-column-comparison] yields a quasi-isomorphism $b_J:\Gamma(J)\to K(J)$. Define
$$\lambda_P=Q(b_J)^{-1}Q(Ks):QK(P)\longrightarrow Q\Gamma(J)=R\Gamma(P).$$

Cited nodes: lem-sp-derived-injective-resolution-naturality, lem-sfb-discrete-lattice-koszul-resolution, lem-weil-pbc-complex-injective-resolution-mono, lem-sp-grothendieck-enough-injectives, lem-weil-pbc-bounded-below-total-column-comparison.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), ordinary open direct image: agent expansion of the discrete-lattice calculation below the tame-boundary route.

### Original step 5

A chain map $P\to P'$ lifts along the monomorphic resolution of $P$ to a map $J\to J'$ by [lem-weil-pbc-lift-along-injective-quasi-iso]. Any two lifts are homotopic by [lem-weil-pbc-lift-to-injective-unique-up-to-homotopy]. The maps $b_J$ commute with every such lift on complexes, and step 2 sends the lift homotopies to total homotopies. The normalized resolution comparison [lem-sp-derived-injective-resolution-naturality] therefore makes $\lambda$ independent of resolutions and natural, including after localization. For a lifted map $J\to J'$, its cone is again bounded below and termwise injective. That same cited lemma computes the canonical derived cone triangle on this cone. The cone isomorphism of step 3 is identity on Koszul degree zero, so it commutes with $b$ and the invariant inclusions. Hence $\lambda$ respects the specified shifts and cone triangles. This proves an isomorphism of triangulated functors, and therefore compatibility with the canonical connecting arrow of any short exact sequence. Exactness of the $K^a$ identifies its image triangle with that of the termwise exact Koszul sequence.

Cited nodes: lem-weil-pbc-lift-along-injective-quasi-iso, lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, lem-sp-derived-injective-resolution-naturality.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), ordinary open direct image: agent expansion of the discrete-lattice calculation below the tame-boundary route.

### Original step 6

For a module $P$, both maps from $P^D[0]$ into $K(J)$ put the same invariant section in $J^0$ and zero elsewhere. Thus the comparison of step 4 has exactly the invariant-inclusion normalization of [lem-sfb-discrete-lattice-koszul-resolution], and supplies a simultaneous choice of those module comparisons. For $r=0$, $K$ and $\Gamma$ are the identity and $b_J=1_J$; under the normalized derived identity, the formula is the identity on $P$. This also fixes its restriction to modules.

Cited nodes: lem-sfb-discrete-lattice-koszul-resolution.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), ordinary open direct image: agent expansion of the discrete-lattice calculation below the tame-boundary route.

### Original step 7

Let $L^{-a}=\bigoplus_{|I|=a,v\in D}R[v,I]$, with differential the integral boundary of [lem-sfb-integral-lattice-cubical-contraction], now read as a cochain differential from $-a$ to $-a+1$. Translation acts on $v$. Replace each integer coefficient in that lemma's contraction by the same multiple of an identity morphism; finite support on each basis vector makes every map a coproduct map. This gives a nonequivariant homotopy between $1_L$ and the vertex section followed by $\varepsilon:L\to tR$. After tensoring with any complex $X$, $h\otimes1$ gives the same homotopy identity; the cross terms cancel by the total tensor sign of [lem-sfb-total-tensor-homotopy]. In particular $L\otimes tX\to tX$ is a quasi-isomorphism. Forgetting detects this by [lem-sfb-condensed-derived-restriction-calculus]. The same contraction shows that $L$ is K-flat: $L\otimes X$ is homotopy equivalent, after forgetting, to $X$, and is acyclic when $X$ is acyclic.

Cited nodes: lem-sfb-integral-lattice-cubical-contraction, lem-sfb-total-tensor-homotopy, lem-sfb-condensed-derived-restriction-calculus.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), ordinary open direct image: agent expansion of the discrete-lattice calculation below the tame-boundary route.

### Original step 8

Put $c_a=(-1)^{a(a+1)/2}$. For $x\in K^a(P^b)$ define an equivariant map
$$E_P:tK(P)\otimes L\longrightarrow P,\qquad E_P(x\otimes[v,I])=(-1)^{ab}c_aT^vx_I\quad(|I|=a),$$
and put it zero on the other Koszul/chain-degree pairs. Here $T^v=\prod_iT_i^{v_i}$ and $K(P)$ has trivial action. Translation of $v$ proves equivariance. To check the chain equation, identify the degree-$a,b$ component with equivariant maps $L^{-a}\to P^b$, multiplied by $\theta_{a,b}=(-1)^{ab}c_a$. The usual Hom differential is $df=d_Pf-(-1)^{a+b}f\partial$. The identities $\theta_{a,b+1}=(-1)^a\theta_{a,b}$ and $\theta_{a+1,b}=(-1)^{a+b+1}\theta_{a,b}$ identify it with $d_K+(-1)^ad_P$. Evaluation then has the stated chain equation. All assertions can be checked on each generator after every profinite base change, so they give morphisms of internal modules. On $t\Gamma(P)\otimes L$, evaluation is exactly the invariant inclusion composed with $1\otimes\varepsilon$: only $a=0$ and vertices survive.

Cited nodes: .

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), ordinary open direct image: agent expansion of the discrete-lattice calculation below the tame-boundary route.

### Original step 9

The adjunction $t\dashv\Gamma$ of step 1 has its normalized derived adjunction by [lem-sfb-resolving-derived-adjunction-normalization]: the left resolving class can be all complexes since $t$ is exact. Unbounded injective replacements exist by [lem-sfb-grothendieck-k-injective]. On a bounded-below injective $J$, its derived counit is $t\Gamma(J)\to J$, by the chain-transpose clause of the normalization lemma. Step 8 gives the commuting chain square with horizontal arrows $t\Gamma(J)\otimes L\to tK(J)\otimes L$ and $t\Gamma(J)\to J$, and vertical arrows $1\otimes\varepsilon$ and $E_J$. The top arrow is a quasi-isomorphism since $b_J$ is one and $L$ is K-flat (step 7). The left arrow is a quasi-isomorphism by the contraction. Thus, in the derived category, the roof
$$tQK(P)\xleftarrow{1\otimes\varepsilon}Q(tK(P)\otimes L)\xrightarrow{E_P}P$$
is the derived counit composed with $t\lambda_P$, first for $J$ and then for $P$ by the naturality of evaluation and $s:P\to J$. This identifies the actual derived arrow; it does not infer equality from cohomology.

Cited nodes: lem-sfb-resolving-derived-adjunction-normalization, lem-sfb-grothendieck-k-injective.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), ordinary open direct image: agent expansion of the discrete-lattice calculation below the tame-boundary route.

### Original step 10

For flat $B$, each term of $K_B$ is a finite sum of copies of $B$ and hence flat: tensor with it is a finite sum of exact functors. The internal-to-sectionwise equivalence [lem-pe-internal-section-tensor-comparison] preserves flatness, total tensors and acyclicity. Apply [lem-pc-bounded-above-flat-kflat-site] to this bounded complex on the small condensed site and transport back: $K_B$ is K-flat. The same reasoning on underlying modules proves that $tK_B$ is K-flat equivariantly, since forgetting creates exactness and the equivariant tensor has underlying tensor with diagonal action. Thus ordinary tensor models every derived tensor in the following evaluation calculation.

Cited nodes: lem-pe-internal-section-tensor-comparison, lem-pc-bounded-above-flat-kflat-site.

Source: literature/stacks-project/sites-cohomology.tex; Tag 06YQ, lemma-bounded-flat-K-flat; transported to internal modules by the cited tensor equivalence.

### Original step 11

Apply [lem-sfb-integral-cubical-chain-diagonal] and replace its integer entries by $R$-linear maps as in step 7. This gives a counital equivariant chain map $\Delta:L\to L\otimes_RL$. Define a bilinear map $\star$ by the formula in the statement. It is a chain map by an explicit twisted Leibniz identity: put $D_i=T_i-1$; then
$$D_i(xT_Ay)=D_i(x)T_{A\cup\{i\}}y+xT_A D_i(y)\quad(i\notin A).$$
For each ordered partition of $I\cup\{i\}$, group the differential terms according as $i$ is in the first or second factor. In the first group, moving $i$ through the ordered first block gives exactly the Koszul sign of $dx\star y$; in the second it passes all $p$ elements of the first block, adding $(-1)^p$, and gives $x\star dy$. The displayed identity supplies their coefficients. Therefore $d(x\star y)=dx\star y+(-1)^px\star dy$.

Cited nodes: lem-sfb-integral-cubical-chain-diagonal.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), ordinary open direct image: agent expansion of the discrete-lattice calculation below the tame-boundary route.

### Original step 12

Write $n=p+q$. Compare the two maps from $t(K_B\otimes K_B)\otimes L$ to $B$: evaluation after $t\star$, and multiplication after $\Delta$ and the two evaluations. On $x_A\otimes y_C\otimes[v,I]$ with $|A|=p$, $|C|=q$, both vanish unless $A\sqcup C=I$. The first is
$$c_n\epsilon(A,C)T^v(x_A)T^{v+u_A}(y_C).$$
In the second, the relevant diagonal term is $\epsilon(A,C)[v,A]\otimes[v+u_A,C]$. Moving $y_C$ past $[v,A]$ contributes $(-1)^{pq}$, and the evaluations contribute $c_pc_q$. These agree because $c_n=(-1)^{pq}c_pc_q$. Thus the maps agree on every summand and hence as chain maps. The counit identity $(\varepsilon\otimes\varepsilon)\Delta=\varepsilon$ identifies the left arrows of their evaluation roofs. Since $K_B$ is K-flat and the augmentations are quasi-isomorphisms, this is the derived equality between evaluation after $\star$ and multiplication after the two counit evaluations.

Cited nodes: lem-sfb-integral-cubical-chain-diagonal.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), ordinary open direct image: agent expansion of the discrete-lattice calculation below the tame-boundary route.

### Original step 13

For the ambient monoidal constructions, identify internal modules with section modules using [lem-pe-internal-section-tensor-comparison], and actions with module sheaves on the small action site using [lem-sfb-internal-action-site-presentation]. The latter equivalence also identifies tensors: both are the sheafification of the balanced local pure tensors, and an arrow $(f,a)$ acts on $m\otimes n$ as $a f^*m\otimes a f^*n$. The action site is small in the chosen universe. Thus [lem-trf-site-functorial-flat-resolution] provides functorial flat resolutions in both categories, and their tensor is closed by [lem-pc-sheaf-modules-tensor-closed]. The trivial-action functor $t$ is exact, left adjoint, and strong monoidal, with identity underlying tensor and unit identifications. It preserves flat objects since forgetting detects exactness. Apply [lem-sfb-exact-flat-tensor-derived-counit-comparison] to obtain its normalized derived tensor identification. The canonical cup is the adjunction transpose of multiplication after the tensor of the two derived counits. Step 9 identifies the evaluation roofs with these counits after $t\lambda_B$. Step 12 says exactly that the transposes of $\lambda_BQ(\star)$ and $\operatorname{cup}_B(\lambda_B\otimes^{\mathrm L}\lambda_B)$ coincide. The adjunction bijection proves their equality. Evaluation of $1_B$ is $\varepsilon$ followed by $R\to B$, since $T^v1_B=1_B$; its transpose is the derived unit. For trivial $B=R$, this is the cup and unit of [lem-sfb-condensed-derived-restriction-calculus].

Cited nodes: lem-pe-internal-section-tensor-comparison, lem-sfb-internal-action-site-presentation, lem-trf-site-functorial-flat-resolution, lem-pc-sheaf-modules-tensor-closed, lem-sfb-exact-flat-tensor-derived-counit-comparison, lem-sfb-condensed-derived-restriction-calculus.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), ordinary open direct image: agent expansion of the discrete-lattice calculation below the tame-boundary route.

### Original step 14

When $r=0$, only the empty partition occurs, $c_0=1$, and all evaluation, augmentation and diagonal formulas are identity or multiplication. For $r=1$, $\Delta[v,\{1\}]=[v,\varnothing]\otimes[v,\{1\}]+[v,\{1\}]\otimes[v+u_1,\varnothing]$; accordingly $x^0\star y^1=x^0y^1$ and $x^1\star y^0=x^1T_1(y^0)$, whose differential is $(T_1-1)(xy)=(T_1-1)x\,T_1y+x(T_1-1)y$. No division or alternating average was used. All formulas hold for the zero ring, the zero module, and characteristic two (where the signs become equal).

Cited nodes: .

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), ordinary open direct image: agent expansion of the discrete-lattice calculation below the tame-boundary route.

## Retained tool rationale

- lem-weil-pbc-bounded-below-total-column-comparison: Finite-strip bicomplex comparison supplies the generic total quasi-isomorphism theorem; the lattice unit gives only its degree-zero module instance.
- lem-sp-derived-injective-resolution-naturality: Normalized resolution and cone comparisons identify the specified triangulated derived maps, a generic homological-algebra input absent from the lattice unit.
- lem-weil-pbc-complex-injective-resolution-mono: Generic existence of monomorphic bounded-below injective replacements is needed for actual chain lifts; no lattice-unit statement supplies it.
- lem-sp-grothendieck-enough-injectives: Enough injectives for the given Grothendieck action category is a general existence theorem, not a lattice calculation.
- lem-weil-pbc-lift-along-injective-quasi-iso: Extends maps to the chosen injective replacements, a generic chain-level tool.
- lem-weil-pbc-lift-to-injective-unique-up-to-homotopy: Generic homotopy uniqueness makes the comparison independent of all lifts.
- lem-sfb-total-tensor-homotopy: Supplies the signed total tensor on homotopy categories used to tensor the explicit contraction.
- lem-sfb-resolving-derived-adjunction-normalization: The transpose-normalized derived adjunction identifies evaluation with the canonical counit, rather than an arbitrary isomorphism of cohomology.
- lem-sfb-grothendieck-k-injective: Unbounded replacement existence verifies the ambient hypothesis of the generic derived adjunction lemma.
- lem-pe-internal-section-tensor-comparison: Transports the ringed-site K-flat criterion to the actual internal tensor without changing coefficients.
- lem-pc-bounded-above-flat-kflat-site: Generic ringed-site bounded-flat criterion proves K-flatness of the finite lattice cochain complex.
- lem-sfb-exact-flat-tensor-derived-counit-comparison: Generic normalized exact derived tensor comparison identifies inflation of a derived tensor with the tensor of inflations.
- lem-trf-site-functorial-flat-resolution: Generic small-ringed-site flat resolution existence verifies both ambient hypotheses of the exact derived monoidal comparison.
- lem-pc-sheaf-modules-tensor-closed: Generic tensor-Hom adjunction gives the closed module tensor on both the coefficient and the action site.

## Unfinished work

All six extracted obligations intentionally remain unsplit and unproved for separate stage-1 workers. No Lean proof is claimed. The parent assembly is complete conditional on those cited statements, as a one-level DAG split requires.

## Promotion-return repair, 2026-10-22

The present return is the landing refusal “completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it)”. I retained the sandbox delivery certified by the previous receipt at 684242460db, including all six statement-only nodes, the original argument allocation, the full retained fourteen-step proof, citations.json and the genuine search log. I compared it with the current shared DAG rather than treating the side completion as landed. The shared parent still has all fourteen original proof steps. Each retained original step text occurs verbatim in this report. Its statement and stmt_deps are byte-identical to the sandbox parent's; the only differing parent fields are proof, proof_deps and split_report. None of the six extracted node ids is already present in the shared DAG. The delivery command rebuilds the overlay on freshly fetched origin/sheaf-dag and preserves the current maintainer-owned fields; no repository or launcher file was edited.

I reread the current statements used by the assembly, not historical statements inferred from their proofs. The six sandbox obligations still explicitly supply the exact total/shift/cone model, the same injective-normalized lambda, the K-flat pairing, the acyclic augmentation and evaluation, the actual derived counit equality, and the equal multiplication roofs. I also reread the current def-sfb-lattice-algebra-derived-cup: it specifies the binary map as the mate of the tensor of the two counits, followed by localized equivariant multiplication, and the unit from the adjunction unit and original algebra unit. Thus the transpose chase in step 3 uses its actual definition. The related current def-sfb-lattice-derived-invariants-tensor and def-sfb-lattice-restriction-cup-comparison retain the flat-representative tensor and invariant/computation-unit normalizations used by the extracted counit obligation. The action-site presentation now explicitly uses the generated Grothendieck topology of a precoverage; its stated module equivalence and diagonal tensor interpretation still supply exactly the interface named by that obligation. No categorical pullback-stability assertion about Presieve.bind is assumed here.

I checked all eight step/node entries in citations.json against the complete current statements: every quote is verbatim and every uses pair is present. The three assembly steps have 1858 characters in total and no step exceeds 2000. I revisited the r=0 identity, r=1 twist, zero-ring and characteristic-two cases directly from the displayed formulas: no new restriction or statement correction is needed. The current upstream WeilConjectures search by blueprint id and lattice/Koszul/cup/cubical-evaluation concepts found no exact completed declaration; the project Sheaf theorem still ends in sorry at line 388, so this remains a split delivery.

The first required fresh dry run exposed a newly present same-tag candidate, lem-tw-finite-projective-model-pullback. I opened its full statement and source and added the explicit distinction above under Not duplicates. Its constant finite-projective pullback comparison does not replace the lattice chain-product obligation. I reread Stacks Tag 06YQ (sites-cohomology.tex, lemma-bounded-flat-K-flat) and the current blueprint direct-images paragraph (3): the former states the bounded-above-flat K-flat criterion, and the latter supplies the ordinary-open-direct-image route without asserting the cubical calculations. The source attribution and agent-origin status remain accurate. The retained Mathlib searches and complete hit files were reread; their questions and the six statements have not changed, so no searches were fabricated or unnecessarily repeated. The current blueprint search for cubical has zero hits and its Koszul hits concern other constructions. This repair changes the review report for the current DAG and rebases the retained mathematical split through the required delivery tool; it is not an unchanged re-push of the refused head.
