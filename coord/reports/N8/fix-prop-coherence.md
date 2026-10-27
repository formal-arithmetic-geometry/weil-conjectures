# Worker report

## Files written

- fix-prop-coherence: unchanged statement; six-step assembly.
- lem-sf-completed-shriek-composition-laws: statement-only, status unsplit; no Mathlib match.
- lem-sf-finite-projection-exchange-transposes: statement-only, status unsplit; no Mathlib match.
- lem-sf-completed-projection-exchange-realization: statement-only, status unsplit; no Mathlib match.
- lem-sf-general-hom-comparison-cocycles: statement-only, status unsplit; no Mathlib match.
- lem-sf-constructible-exceptional-mate-cocycles: statement-only, status unsplit; no Mathlib match.
- lem-sf-verdier-hom-chain-composition: statement-only, status unsplit; no Mathlib match.

## Attachments

None. The item tag has no project declaration. Existing etale projection/base-change proofs cover only part of the finite argument; LowerShriekCompositionCoherence.lean has sorry in its composition declarations (lines 63,104), and does not state the integral system or four-stage result.

## WANTED

WANTED: literature/blueprint/main-20261017/blueprint/sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md, absent locally. I read the main-20261015 statement (identical to the current item) and full proof, the current chapter and unit records, and the current returned proof. The added obligations are agent-formulated, not attributed to a Stacks tag which does not state them.

## Return repaired

The return requires at least five new statement-only tasks, preserving the statement and the entire 17333-character argument, with a parent assembly at most 3000 characters. Six new nodes are delivered, with empty proof and proof_deps and null proof_origin. They isolate independent arguments, not one replacement for the entire item. The full old text below is retained verbatim. Each argument has an explicit destination. Geometric assembly steps remain direct applications of existing nodes because another node for that assembly alone would be elementary/duplicate.

## Argument allocation

- Old steps 1,2,3 -> lem-sf-completed-shriek-composition-laws. The statement specifies the objects, normalizations, formulas, and conclusions of those arguments; its proof is a separate queued task.
- Old steps 4,5,6 -> lem-sf-finite-projection-exchange-transposes. The statement specifies the objects, normalizations, formulas, and conclusions of those arguments; its proof is a separate queued task.
- Old steps 7,8 -> lem-sf-completed-projection-exchange-realization. The statement specifies the objects, normalizations, formulas, and conclusions of those arguments; its proof is a separate queued task.
- Old steps 9 -> lem-sf-general-hom-comparison-cocycles. The statement specifies the objects, normalizations, formulas, and conclusions of those arguments; its proof is a separate queued task.
- Old steps 10 -> lem-sf-constructible-exceptional-mate-cocycles. The statement specifies the objects, normalizations, formulas, and conclusions of those arguments; its proof is a separate queued task.
- Old steps 11,12 -> lem-sf-verdier-hom-chain-composition. The statement specifies the objects, normalizations, formulas, and conclusions of those arguments; its proof is a separate queued task.
- Old step 13 -> parent step 5 using the existing orientation reduction and site-perfect pairing nodes, with the explicit composition-of-squares calculation.
- Old step 14 -> parent step 6 using the existing algebraic, duality and geometric/scheme-Frobenius equivariance nodes, with the explicit equivariant-composition calculation.

## Not duplicates

Searched the full DAG, Lean source, and the full imported blueprint by coherence, compact-support composition, evaluation transpose, Verdier, projection base change and each extraction topic. The searches and actual Mathlib results are retained in the sandbox.
lem-sf-completed-shriek-composition-laws vs lem-sf-semilinear-compositor-coherence: only proper/open/pullback compositors, not the compactified shriek word, common refinement and completed/field laws.
lem-sf-completed-shriek-composition-laws vs lem-sf-integral-compactification-system-realization: realizes expressions and generators; does not assert the compact-support triple-word associativity calculation.
lem-sf-finite-projection-exchange-transposes vs prop-sf-pf-coherence: abstract six-functor axioms rather than the specified witnessed finite pro-etale maps and their open/proper transpose normalizations.
lem-sf-finite-projection-exchange-transposes vs lem-weil-pbc-ringed-exchange-tensor-coherence: proper/direct-image factor only, not the compactification open factor or projection identity.
lem-sf-completed-projection-exchange-realization vs lem-sf-pf-coefficient-realization-transport: conditional transport with supplied coherent comparison data; does not supply the actual system diamond or verify its uniform integral domains.
lem-sf-general-hom-comparison-cocycles vs thm-coef-finite-hom: finite two-variable comparison alone; not integral/finite overlap and finite-field-extension assembly.
lem-sf-constructible-exceptional-mate-cocycles vs lem-weil-pbc-mate-pasting: abstract formal calculus only; not the specified four coefficient-stage exceptional comparisons.
lem-sf-verdier-hom-chain-composition vs fix-cor-verdier-exchange: gives the isomorphism and coefficient compatibility but no composition equation.
lem-sf-verdier-hom-chain-composition vs lem-pur-system-tensor-transpose-composition: orientation-style tensor-to-exceptional map in normalized systems, not the representing internal-Hom/Verdier comparison.

## Review by N8

I read the main-20261015 blueprint statement and proof, the current compatibility unit clause (7), and every statement cited by the six parent steps. The statement is unchanged. Source scope is explicit: none of these new synthetic comparison obligations is claimed to be a Stacks theorem. The current source path is absent locally; the available earlier statement agrees word for word. The return specifically authorizes extracting substantial subarguments that would normally stay inline.

Assembly 1: fix-lem-exchanges clauses (1),(2),(4) state naturality, identity, horizontal/vertical pasting and refinement. thm-sf-comp-composition supplies finite composition. The new composition node explicitly states the semilinear word, associativity equation, common refinements, nested realization and finite-cover bounds; no equality is detected by finite evaluation.

Assembly 2: the finite node gives exactly both open restriction identities and the proper counit transpose, and the completed node gives equality before total limit and its actual realization. I checked the open-normalization, ringed-exchange-tensor, system-realization and stability statements used by the old argument. The generic prop-sf-pf-coherence assumes an abstract axiom package, so it cannot replace this obligation for actual maps. K remains bounded constructible; only L has the displayed finite-Tor assumption, and integral K obtains its bound from the stated integral equality of categories.

Assembly 3: the Hom node distinguishes finite two-variable finite-Tor from site-perfect elementary comparison; its integral overlap is conditional on the finite comparison being defined. Its extension cocycles are for finite coefficient fields. The exceptional node pins the constructible units/counits and composite adjunction formulas; it does not claim arbitrary mate invertibility. I read thm-coef-finite-hom, integral Hom reduction, integral finite extension, finite exceptional, integral exceptional adjoint, rational operations and mate-pasting statements.

Assembly 4: the Verdier node gives the exact representing chain, with inverse projection arrow. f, g, gf and all three structure maps retain exceptional admissibility. The ctf test restriction includes the representing objects by stability, so evaluating at their identity is legitimate. The displayed Verdier composition has the target Rg_*Rf_*D_X M after canonical compositors, and coefficient transposes preserve the entire chain.

Assembly 5: thm-pur-finite-reduction-of-purity is the actual orientation square, thm-pod-finite-reduction states the site-perfect pairing square, and lem-fix-operation-reduction preserves evaluation. I checked smoothness, normalized orientation, admissible structure map and site-perfectness remain required. The square composition is elementary and is written explicitly.

Assembly 6: lem-fix-weil-operations covers algebraic maps only; cor-coef-verdier-weil-equivariance covers general duality without a stable lattice; geometric purity uses its separate actual orientation/trace and scheme-Frobenius nodes. The final purity compatibility node states reduction, scalar extension, composition and base-change compatibility. I read each of these statements before quoting it in citations.json.

Small-case checks: identity schemes/maps/squares give the unit equations and the counit identity; zero inputs and empty opens give zero diagrams; equal quotient indices n=m give identity comparisons; three fields with identity extension obey the cocycle; a degree-zero free module at a point gives ordinary evaluation. The finite i_*A on A^1 is not treated as site-perfect: no tensor-dual formula or dimension-free interval is asserted for it. Nonseparated finite-type schemes in compact-support diagrams are handled on finite affine covers; separatedness is required explicitly in the Hom, exceptional and Verdier tasks. Common bound hypotheses are retained before system realization. Every new statement is a proposition about derived maps or isomorphisms, never a per-degree substitute.

B–E review: new nodes have no proofs, define their objects and cite their notion interfaces, carry source and blueprint metadata and real logged searches with two semantic phrasings. No SGA source is used. No new node states the whole item. Six independent argument packages spread the work; all remaining short geometric steps are explicit. All cited statements appear verbatim in citations.json. No statement dispute or source correction was necessary. The main change is the requested distribution of work; no mathematical clause was shortened away. Final reading made $F_f=S_pJ_j$, $f=pj$, and $g=qi$ explicit in the composition task. The generic Mathlib Adjunction.comp source (Basic.lean:567–587), mateEquiv (Mates.lean:91 onward), and internal-Hom evaluation (Monoidal/Closed/Basic.lean:81–110) were read; they are useful ingredients, but do not state the actual geometric coefficient comparisons. The existing etale projection/base-change theorem (LowerShriekProjectionBaseChange.lean:216) covers the etale finite factor, whereas the task specifies the witnessed pro-etale maps and normalizations. All parent steps are under 600 characters; no long step conceals another obligation.

## Unfinished work

The six extracted nodes are deliberately unsplit for independent stage-1 workers, as the return requires. Nothing required for this delivery is left outside the files.

## Preserved returned proof

### Old step 1

Work with the coefficient and scheme datum of
[def-fix-six-functor-datum]. All equations are restricted to the domains of
their cited comparisons: finite compact support has etale-origin witnesses;
integral operations are completed with compatible witnessed reductions;
rational operations use raw localization, and algebraically closed coefficients
use a common finite coefficient field. Retain the lattice and interval conditions
of [fix-lem-exchanges]. Its clauses (1), (2), and (4) supply naturality,
identity squares, horizontal and vertical pasting, and refinement compatibility.
In the canonical composition coordinates these are
$$\operatorname{Ex}_{gh}=(\operatorname{Ex}_h Lg'^*)\circ
(Lh^*\operatorname{Ex}_g),\qquad
\operatorname{Ex}_{fe}=(P(f')\operatorname{Ex}_e)\circ
(\operatorname{Ex}_fP(e)),\quad P=R(-)_*,R(-)_!.$$
No ordinary exchange is assumed invertible. The finite compact-support
composition is unital and associative by [thm-sf-comp-composition].

Cited statements: def-fix-six-functor-datum, fix-lem-exchanges, thm-sf-comp-composition.

### Old step 2

Here is the additional argument for higher-coefficient compact-support
composition. Use the simultaneous coefficient-system operations of
[lem-sf-integral-compactification-system-realization], and write $S_p,J_j$
for proper direct image and open extension. The geometric compatible towers
and common refining towers of [lem-cbc-compactifiable-compatible-tower]
let the composition maps for $f,g$ and for triples be computed on common
compactifications. The map for $g=q i$, $f=pj$ is the adjacent interchange
$J_iS_p\to S_rJ_k$, followed by the proper- and open-composition
identifications in the resulting compactification. For three factors the
initial expression is $S_sJ_aS_qJ_iS_pJ_j$. The two compositions are the
two orders of moving each $S$ left past an adjacent $J$. Moves at disjoint
positions commute by naturality. Moving past two successive proper factors,
or two successive open factors, is precisely the vertical, respectively
horizontal, proper/open pasting equation in
[lem-cbc-strict-tower-proper-open-calculus]. That statement asserts these
equations and independence of parenthesization as actual strict-tower
transformations, including for the intermediate refinement squares. Their
coefficient-system versions are asserted before restriction or evaluation
by [lem-sf-integral-compactification-system-realization], which specifies
the intrinsic open-adjunction construction and its pasting identities. The
remaining proper and open compositors are conjugates of the canonical
pullback compositors. Those compose associatively: before localization both
routes identify the same iterated inverse image and send an iterated tensor
of coefficients to their product. Conjugation preserves this identity by
[lem-weil-pbc-mate-pasting]. Thus the two system transformations agree; the
identity-square clauses in the same calculus give both unit laws. Common
refinement comparisons intertwine them by its refinement and pasting clauses.


Cited statements: lem-sf-integral-compactification-system-realization, lem-cbc-compactifiable-compatible-tower, lem-cbc-strict-tower-proper-open-calculus, lem-weil-pbc-mate-pasting.

### Old step 3

Use the natural realization isomorphisms of [lem-sf-integral-compactification-system-realization]. Applying the natural realization isomorphisms $c_V$ and $R\lim$ proves the
integral unit and associativity equations for the specified compact-support
composition maps, including nested functors. Uniform constructible finite-Tor
domains for the intermediate expressions are the ones supplied by
[thm-sf-ctf-stability], so the realization node applies. If a scheme in
the compact-support diagram is not separated over $k$, check these bounds
on finite affine covers and their inverse images: a separated finite-type
map over an affine has separated source, so the cited theorem applies
there. Constructibility and Tor/cohomology bounds are local; take the
minimum lower and maximum upper endpoint over the finite covers. Raw rationalization
and common finite-stage scalar transport preserve this equality of maps by
[lem-fix-operation-reduction]. This proves the higher composition laws;
they are not attributed to the phrase “forms constructed in the proof” in
[fix-lem-exchanges].

Cited statements: lem-sf-integral-compactification-system-realization, thm-sf-ctf-stability, lem-fix-operation-reduction, fix-lem-exchanges.

### Old step 4

For $K\in D^b_c(X,\Lambda)$ and
$L\in D^b_{ctf}(Y,\Lambda)$, [fix-prop-projection-formula] gives the
canonical projection isomorphism, naturality, associativity pentagon,
compactification compatibility, proper coincidence and coefficient
compatibility. For the identity choose the identity compactification in
[def-exchange-projection]. Its adjunction is the identity adjunction, so
the counit-defined projection is the identity under the canonical tensor
and functor identifications.

Cited statements: fix-prop-projection-formula, def-exchange-projection.

### Old step 5

Choose a compactification $f=pj$ and its base change $f'=p'j'$, with
$h:\overline X'\to\overline X$ and $M=j_!K$. First work at finite
coefficients. The formulas of [def-exchange-projection] express projection
and exchange as the open and proper factors. For the open factor use
[lem-sf-open-tensor-normalization]: it states $j'^*j'_!\cong1$, the
full-faithfulness of $j'_!$, and the specific restriction normalizations
of both $\beta$ and $\gamma$, identifying the finite maps with those of
[lem-cbc-proetale-extension-zero-base-change] and
[lem-cbc-extension-zero-projection-formula]. Both routes therefore have
source and target in the image of $j'_!$ and restrict to the identity of
$Lg'^*K\otimes^L Lf'^*Lg^*L$; the open adjunction gives equality.


Cited statements: def-exchange-projection, lem-sf-open-tensor-normalization, lem-cbc-proetale-extension-zero-base-change, lem-cbc-extension-zero-projection-formula.

### Old step 6

Use the counit-defined transformations of [def-exchange-projection]. For the proper factor, transpose the two maps
$$Lg^*(Rp_*M\otimes^L L)\longrightarrow
Rp'_*(Lh^*M\otimes^L Lp'^*Lg^*L)$$
under $Lp'^*\dashv Rp'_*$. Both transposes are
$$Lp'^*Lg^*(Rp_*M\otimes^L L)\cong
Lh^*Lp^*Rp_*M\otimes^L Lp'^*Lg^*L
\xrightarrow{Lh^*\varepsilon_{p,M}\otimes1}
Lh^*M\otimes^L Lp'^*Lg^*L.$$
For exchange first this is the defining exchange transpose; for projection
first, naturality moves the counit past exchange and its adjacent unit
cancels by the triangle identity. The compatibility of the tensor map
$\mu$ with the square comparison $\theta$ in these identifications is
exactly the canonical ringed-topos equation of
[lem-weil-pbc-ringed-exchange-tensor-coherence], not an extra property
inferred from the definition of the symbols. Combining the two factors gives
$$\operatorname{Ex}_{!,K\otimes^L Lf^*L}\circ Lg^*\operatorname{PF}_{f,K,L}
=\operatorname{PF}_{f',Lg'^*K,Lg^*L}\circ(\operatorname{Ex}_{!,K}\otimes1)$$
after the canonical tensor/pullback identifications. Refinement compatibility
from [fix-lem-exchanges] and [fix-prop-projection-formula] removes the
compactification choice.

Cited statements: def-exchange-projection, lem-weil-pbc-ringed-exchange-tensor-coherence, fix-lem-exchanges, fix-prop-projection-formula.

### Old step 7

At integral coefficients do this calculation in the derived category of
strict semilinear coefficient systems, before total inverse limit.
[lem-sf-integral-compactification-system-realization] supplies the actual
system adjunctions, canonical tensor/square comparisons and open maps,
and identifies the realization of each of the four words in the diamond
and each generator map with its integral counterpart. The ringed-system
version of [lem-sf-open-tensor-normalization] proves equality for the open
factor by the same restriction argument, and
[lem-weil-pbc-ringed-exchange-tensor-coherence] proves equality for the
proper factor on the ringed diagram topoi. Hence the composites are equal
as system maps. Apply $R\lim$ and the natural $c_V$ comparisons to this
equality. This gives exactly the integral diamond for completed pullback
and tensor; no faithfulness of derived evaluation or finite reduction is
used. The inputs and all intermediate expressions meet the uniform
constructible finite-Tor conditions by [thm-sf-ctf-stability], using
finite affine covers as in step 3 when necessary. In particular its integral
conclusion $D^b_c=D^b_{ctf}$ applies locally to $K$; this imposes no
extra finite-Tor assumption on the integral $K$. 

Cited statements: lem-sf-integral-compactification-system-realization, lem-sf-open-tensor-normalization, lem-weil-pbc-ringed-exchange-tensor-coherence, thm-sf-ctf-stability.

### Old step 8

For rational
objects take their integral presentations and apply the localization
functor; for algebraically closed coefficients represent the finite
diagram at a common finite field and apply its transition functor. These
functors take equal composites to equal composites; the operation and
generator comparisons are the rational/common-stage comparisons of
[lem-fix-operation-reduction]. Thus the same diamond holds at both field
stages on the stated domains.

Cited statements: lem-fix-operation-reduction.

### Old step 9

The elementary operation comparisons preserve tensor associativity, evaluation, units and counits by the last sentence of [lem-fix-operation-reduction]. For general finite-quotient internal Hom, take $K,M\in D^b_{ctf}(X,A_{E,n})$ and $n\ge m\ge1$. [thm-coef-finite-hom] supplies the isomorphism to $R\mathcal Hom_{A_{E,m}}(K_m,M_m)$, defined as the unique transpose of the reduced evaluation, and states its quotient-composition equation. This requires both variables to have finite Tor amplitude; it does not follow just from the site-perfect elementary case. For integral reduction, [lem-coef-integral-hom-reduction] supplies the same evaluation-transpose description and isomorphism, even for arbitrary ambient variables. To check successive reductions in any overlap where the finite comparison applies, transpose the direct and successive comparisons: both are the reduction of $K\otimes^L R\mathcal Hom(K,M)\to M$ under the canonical tensor identifications. The bijectivity of tensor–Hom transposition makes the comparisons equal. For finite coefficient-field extension [lem-coef-integral-finite-extension] gives evaluation preservation, identity-extension and extension-composition compatibility, including tensor associators. The same transpose argument for identity coefficient change gives the identity map. Thus the extended Hom comparisons agree with the elementary ones on their overlap and preserve every equation built from evaluations and tensor reassociations. Rational and common-stage passage use the comparison functors in [lem-fix-operation-reduction]; this does not introduce a reduction functor from rational coefficients to a finite quotient.

Cited statements: lem-fix-operation-reduction, thm-coef-finite-hom, lem-coef-integral-hom-reduction, lem-coef-integral-finite-extension.

### Old step 10

For the finite constructible finite-Tor exceptional functors, use [lem-coef-finite-exceptional], including its quotient cocycle and its two explicit unit/counit equations. For the integral exceptional functor, use the right adjunction and the unit/counit reduction identifications of [prop-coef-integral-exceptional-adjoint]. For rational coefficients and finite scalar extension, use the right adjunction and evaluation/unit/counit compatibility of [lem-coef-rational-operations]. These statements concern the constructible adjoints; an unrestricted ambient pro-étale exceptional adjoint is not used. The reason the same coherence passes to exceptional comparisons is the explicit transpose formula. For an adjunction $F\dashv G$ with unit $\eta$ and counit $\epsilon$, the transpose of $a:FU\to V$ is $G(a)\eta_U$, and the inverse sends $b:U\to GV$ to $\epsilon_VF(b)$. A coefficient comparison intertwining $\eta,\epsilon$ and the functors therefore intertwines these two formulas. Applying it to two equal maps gives equal transposes; applying it to an identity gives the corresponding identity. For composable adjunctions $F_f\dashv G_f$ and $F_g\dashv G_g$, substitution into these formulas gives the pasted unit $(G_f\eta_gF_f)\eta_f$ and counit $\epsilon_g(F_g\epsilon_fG_g)$. Naturality and the two triangle identities show that transposing successively with $f$ and $g$ is transposing once with this composite adjunction. The compact-support unit and associativity laws at all four coefficient stages were proved in steps 1–3 from the finite composition theorem, actual strict-tower interchange identities and coherent realization. Substituting these equal left-functor composites in the displayed Hom bijections gives equal right-adjoint identifications; their identity and associativity equations follow by bijectivity of transposition. This calculation proves the compatibility claimed here without treating a mate of an arbitrary square isomorphism as automatically invertible. The formal identity, vertical-pasting and composite-adjunction formulas used here are precisely [lem-weil-pbc-mate-pasting], clauses (2) and (4).

Cited statements: lem-coef-finite-exceptional, prop-coef-integral-exceptional-adjoint, lem-coef-rational-operations, lem-weil-pbc-mate-pasting.

### Old step 11

Use the projection isomorphism of [fix-prop-projection-formula]. On the domain where [fix-cor-verdier-exchange] supplies the proved Verdier comparison, it supplies its naturality and coefficient/shift compatibility; retain its stated exceptional hypotheses. Its composition coherence is a formal calculation, not an additional clause taken from that statement. Write $F_f=Rf_!$, $P_f=Lf^*$ and $H_X=R\mathcal Hom_X$. For this comparison of maps, use the already established preservation in [thm-sf-ctf-stability] to keep the representing internal-Hom and direct-image objects, as well as the test objects $T$, in the common constructible finite-Tor categories at the stated coefficient stages. Thus the projection isomorphisms in the following chain are applied only with finite-Tor test objects; the identity of the representing object is an allowed test. This invokes a separate preservation theorem and proves no new preservation assertion here. The canonical comparison is obtained by transposing the chain
$$\operatorname{Hom}(T,H_Y(F_fM,N))\cong\operatorname{Hom}(F_fM\otimes T,N)\xrightarrow{\operatorname{PF}_f^{-1}}\operatorname{Hom}(F_f(M\otimes P_fT),N)\cong\operatorname{Hom}(M\otimes P_fT,f^!N)\cong\operatorname{Hom}(T,Rf_*H_X(M,f^!N)),$$
then setting $N=\omega_Y$ and using $f^!\omega_Y\cong\omega_X$, the right-adjoint composition identification from the preceding step. The first and last bijections, and the resulting isomorphism, are the tensor–Hom adjunction of [fix-lem-tensor-adjunction] on its exceptionally admissible domain. Tensor–Hom adjunction is the evaluation transposition used in [thm-coef-finite-hom] and [lem-coef-integral-hom-reduction]; the operation comparisons preserve it. 

Cited statements: fix-cor-verdier-exchange, fix-prop-projection-formula, fix-lem-tensor-adjunction, thm-coef-finite-hom, lem-coef-integral-hom-reduction, thm-sf-ctf-stability.

### Old step 12

For the canonical comparison constructed in step 11, for $gf$, substituting the projection associativity equation from [fix-prop-projection-formula] replaces its projection arrow by the two projection arrows for $g$ and $f$. Substituting the pasted counit $\epsilon_g\circ F_g\epsilon_fG_g$ of [fix-prop-adjunctions], clause (3), replaces its exceptional transposition by the two exceptional transpositions. Pullback and ordinary direct-image composition identifications are the ones used in [fix-lem-exchanges]. Hence, on each input map in the displayed Hom set, the chain for $gf$ is exactly the chain first for $g$ and then for $f$. Evaluating at the identity of the representing object proves that the corresponding object maps agree. In particular, after the canonical composition identifications,
$$\varepsilon_{gf,M}=Rg_*(\varepsilon_{f,M})\circ\varepsilon_{g,Rf_!M}.$$
The identity case is the same chain with identity functors. Coefficient comparison of this chain agrees term by term by the evaluation compatibilities of [thm-coef-finite-hom] and [lem-coef-integral-hom-reduction] used in the preceding Hom step and the exceptional unit/counit compatibilities in the preceding exceptional step. No Verdier-duality exchange with arbitrary pullback, and no new biduality or preservation theorem, is asserted.

Cited statements: fix-prop-projection-formula, fix-prop-adjunctions, fix-lem-exchanges, thm-coef-finite-hom, lem-coef-integral-hom-reduction.

### Old step 13

For a smooth separated morphism of pure relative dimension $d$ and a finite-Tor input at $A_{E,n}$, [thm-pur-finite-reduction-of-purity] gives the commutative reduction square for $Lf^*K(d)[2d]\to Rf^!K$, and states the corresponding affine-orientation, smooth-trace, composition and base-change compatibilities. For the site-perfect constructible input and admissible smooth structure morphism of [thm-pod-finite-reduction], that statement gives reduction of the derived Poincare pairing and the displayed square for its adjoint isomorphism. These are separate geometric inputs; evaluation compatibility alone does not prove compatibility of the orientation. Once their squares are composed with the preserved evaluation from [lem-fix-operation-reduction], the resulting pairing squares commute: if $b'u=vb$ and $c'v=wc$, then $(c'b')u=c'(vb)=(wc)b=w(cb)$. This verifies the assembly while keeping the site-perfect hypothesis and the hypotheses on the smooth structure morphism of the pairing theorem.

Cited statements: thm-pur-finite-reduction-of-purity, thm-pod-finite-reduction, lem-fix-operation-reduction.

### Old step 14

At $E$ and $\overline{\mathbf Q}_\ell$, suppose $f$ is the geometric fiber of a separated finite-type morphism $f_0:X_0\to Y_0$ over the finite base field, and work with the Weil structures on the stated constructible domains. [lem-fix-weil-operations] makes the algebraic evaluation, adjunction data, composition, exchange and projection maps equivariant. [cor-coef-verdier-weil-equivariance] supplies the general Verdier-duality, exceptional-adjunction and finite scalar-extension equivariance, without requiring a Frobenius-stable integral lattice. Equivariance is preserved under composition: from $\varphi_B F(a)=a\varphi_A$ and $\varphi_C F(b)=b\varphi_B$, one obtains $\varphi_C F(ba)=b\varphi_BF(a)=ba\varphi_A$. For geometric purity, use the actual orientation and trace equivariance squares of [thm-pur-weil-equivariance-of-purity-and-trace], and their scheme-Frobenius versions from [prop-pur-weil-equivariance-scheme-frobenius]; the additional finite-reduction, scalar-extension, composition and base-change compatibility of those squares is exactly [prop-pur-weil-equivariance-compatibilities]. Their composition with equivariant evaluation gives equivariance of the orientation-induced pairing on its stated domain. Thus every proved comparison in the assertion has the claimed Weil compatibility, and the extra geometric assertion has its own cited input.

Cited statements: lem-fix-weil-operations, cor-coef-verdier-weil-equivariance, thm-pur-weil-equivariance-of-purity-and-trace, prop-pur-weil-equivariance-scheme-frobenius, prop-pur-weil-equivariance-compatibilities.

