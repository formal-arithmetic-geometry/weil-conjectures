## Worker report

Repair of the batch5 re-split return for lem-trf-scheme-galois-coefficient-change, Q34, 2026-10-22. The sandbox initially contained only dispatcher marker files, with no saved node, report, citations or search log. I copied the returned four-step split from the current shared repository, retaining its statement verbatim, all previous Mathlib searches, source/citations, and maintainer-owned fields. No repository or launcher file was written; no git command, Lean compiler, Lake command, or local preflight/check script was run.

Files written:

- dag/nodes/sec-trace-formula/lem-trf-scheme-galois-coefficient-change.json: same statement, short assembly of the following two independent intermediate statements.
- dag/nodes/sec-trace-formula/lem-trf-scheme-galois-comparison-normal-form.json: statement, unsplit; no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-frobenius-contraction-scalar-pasting.json: statement, unsplit; no exact Mathlib match.
- report.md and citations.json: review and verbatim per-step statement quotes.

Attachments: none. The existing Sheaf.SixFunctors.SchemeGaloisCoefficientChange theorem at lines 66–83 ends in sorry. Searches for the tag and the comparison/coefficient notions in lean/WeilConjectures found no exact project declaration. Its unrelated Galois-module and stalk declarations do not establish this coefficient square. The two new intermediate claims likewise have no exact source-library declaration.

WANTED: none.

What was wrong: the previous proof combined geometric normalization with scalar-compositor transport, absolute-Frobenius coefficient naturality, and the final five-line calculation. The return asks that this work be spread over at least two comparable statement-only nodes. No statement dispute or change of route was needed. The item's statement, coefficient category, normalization of kappa, and unrestricted derived objects are unchanged.

## New nodes

lem-trf-scheme-galois-comparison-normal-form separates the geometric identification of the specified multiplicative comparison. It states characteristic p, the inverse-Galois factorization, and equality of the specified iterate with the single-exponent absolute-Frobenius trivialization after the canonical compositor. It has no coefficient map and asserts no coefficient naturality.

lem-trf-frobenius-contraction-scalar-pasting separates the scalar argument for an arbitrary characteristic-p scheme Y and arbitrary endomorphism v. It concerns the explicit contraction of L(v composed with F^b)^* to Lv^*. It has neither a finite field nor a scheme/Galois comparison. Its assertion includes the ordinary constant-coefficient normalization, arbitrary unbounded objects, b=0, and nonflat coefficient maps. Establishing it requires the scalar composition law, its finite-constant coefficient transport, the existing absolute-Frobenius scalar-naturality theorem, and the typed pasting calculation. It is not merely a stand-alone associativity or naturality equation. The new nodes are comparable pieces of the original proof: geometric normalization versus coefficient-compatible contraction. They can be worked on independently.

Both files have status unsplit, proof [], proof_deps [], proof_origin null, complete self-contained TeX statements, definition dependencies, an agent-extracted source place, and blueprint.from.node thm-trf-finite-coefficient-map with via [lem-trf-scheme-galois-coefficient-change]. Their statements contain no proof sketch. All proof material for the next workers is retained below.

## Search record

I searched the entire DAG by titles and statements for scheme/Galois comparisons, Frobenius normal forms, coefficient/composition coherence and contractions, and searched the whole blueprint with blueprint_refs.py: coefficient, Frobenius, Frobenius trivialization, scheme--Galois, absolute-Frobenius, contraction, Frobenius contraction, and scheme Galois comparison normal form. I also searched 0F6W and opened the relevant matching nodes. The blueprint ancestor command gives thm-trf-finite-coefficient-map. No existing node states either intermediate assertion with the specified normalizations and full hypotheses.

All new Mathlib searches ran through the required msearch.py and their actual results are in searches.jsonl. The normal-form searches returned ring Frobenius equivalences, Witt-vector isocrystal maps, and ordinary scheme-module pullback composition. Scheme.Modules.pullbackComp (Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:241) is about ordinary structure-sheaf modules; it does not identify the specified pro-etale derived scheme/Galois comparison. A second semantic phrasing returned iterateFrobeniusEquiv_add and related perfect-ring identities, likewise no match.

The contraction searches returned CatCommSq naturality/pasting and ring-map Frobenius commutation. I read Mathlib/CategoryTheory/CatCommSq.lean:35–100: these statements compose supplied abstract functor squares; they do not prove scalar compatibility of the specified relative-Frobenius trivialization or identify the transported constant coefficient maps. They are tools for a future proof, not exact matches or one-line specializations of the contraction statement. CategoryTheory.Regular.frobeniusMorphism_isPullback (RegularCategory/Basic.lean:191) is the regular-category subobject Frobenius law, not characteristic-p Frobenius. The algebraic-geometry grep for Frobenius together with scalar/coefficient/tensor/pullback returned no hit. The later LeanSearch contraction query was rate limited and is recorded unavailable, not no match. The invalid Loogle AlgebraicGeometry identifier is explicitly recorded as invalid; the independent valid Loogle query "frobenius", "pullback" and both semantic phrasings were read before deciding no match. No Mathlib leaf is claimed.

## Not duplicates

lem-trf-scheme-galois-comparison-normal-form vs prop-trf-scheme-galois-comparison: the old statement supplies multiplicative isomorphisms and says they respect factorization; the new assertion is the componentwise normalization formula for the specified iterate, identifying it with the single exponent am and the actual canonical compositor, rather than just existence or unspecified compatibility. It isolates the construction-identification work from the coefficient square.
lem-trf-scheme-galois-comparison-normal-form vs prop-trf-frobenius-factorization: the latter is the scheme-map equality with arithmetic Frobenius; it has no derived compositor or normalization of kappa. The new statement includes the inverse geometric factorization and canonical derived comparison formula.
lem-trf-scheme-galois-comparison-normal-form vs lem-pur-frobenius-trivialization-pullback: the latter gives naturality and addition of absolute trivializations at fixed coefficients, not the geometric-Galois comparison's normalized form.
lem-trf-scheme-galois-comparison-normal-form vs lem-trf-scheme-galois-pullback-naturality: the latter compares a scheme/Galois family under another scheme morphism; no normalization formula for the specified family is its conclusion.
lem-trf-frobenius-contraction-scalar-pasting vs lem-trf-absolute-frobenius-coefficient-naturality: the old result is the scalar square for F^b alone; the new result is the contraction of a composite v composed with F^b, with the scalar comparison for that entire composite. Relating that comparison to the separate comparisons and the compositor is part of its work, not an additional hypothesis supplied to it.
lem-trf-frobenius-contraction-scalar-pasting vs det-prop-scalar-six-pullback: that theorem supplies scalar/pullback composition coherence, not the canonical Frobenius contraction or compatibility of its trivialization with coefficients.
lem-trf-frobenius-contraction-scalar-pasting vs lem-sfb-kflat-scalar-comparison-normalization: this supplies balancing/mate normalization and composition, with no relative-Frobenius trivialization or contraction.
lem-trf-frobenius-contraction-scalar-pasting vs lem-trf-frobenius-coefficient-reduction-coherence: the latter concerns integral derived-complete constructs and a quotient tower, and its scheme/Galois coefficient clause requires the particular finite-field geometry. The new result concerns any characteristic-p scheme, arbitrary v and arbitrary finite coefficient homomorphisms.
lem-trf-frobenius-contraction-scalar-pasting vs lem-trf-quotient-system-mixed-coherence: that statement is about entire strict quotient diagrams with number-field towers, not ordinary constant module categories and the relative-Frobenius contraction.
lem-trf-frobenius-contraction-scalar-pasting vs lem-sp-ordinary-horizontal-pasting-transport: that abstract transport theorem assumes respected cells and a primed pasting equation; it does not supply the actual constant-coefficient or Frobenius squares required here.
lem-trf-frobenius-contraction-scalar-pasting vs lem-trf-scheme-galois-coefficient-change: the new lemma supplies a contraction square for arbitrary v and Y; it does not identify any kappa. The separate geometric-normalization node is essential to get the parent theorem.

No new source claims to be a new statement of Stacks 0F6W: that tag supplies existing geometric input to the already-present absolute-Frobenius nodes. Neither new statement is attributed as a verbatim Stacks theorem.

## Argument allocation and proof briefs for the new unsplit nodes

The return's old step 1 (627 characters) and geometric part of step 2 go to the normal-form node. Its future proof uses prop-trf-frobenius-factorization, the inverse arithmetic/geometric product maps in def-trf-scheme-frobenius, the canonical pullback compositor, and the normalized construction of prop-trf-scheme-galois-comparison in the current blueprint proof. The equation H=g_sigma^m Phi^m and g=g_sigma^{-1} yields Phi^m=g^m H=H g^m. Characteristic p follows by applying the structure ring map to p times 1. The specified multiplicative iterate is the single am trivialization because the relative Frobenius maps compose to the corresponding power maps, as the second paragraph of the source explicitly states; an arbitrary isomorphism between these functors is insufficient.

The ordinary-coefficient and scalar-composition part of old step 2, all of old step 3, and all of old step 4 go to the contraction node, generalized from g^m to arbitrary v. Here is its complete intended argument, retaining the original calculation rather than abbreviating it. Put S_R=L(vH)_R^*, P_R=LH_R^*, V_R=Lv_R^*, and t_R=tau_R^(b). The finite discrete condensed/constant ring identification followed by its scheme-site monoidal transport identifies the ring objects used in det-prop-scalar-six-pullback (1) with the actual ordinary constant coefficients; use its inverse comparison c. Its composition law, with the canonical compositor d:S to PV, is

$$T(d_{A,K})\circ c_{vH,K}=c_{H,V_AK}\circ P_B(c_{v,K})\circ d_{B,TK}.$$

Both sides have source S_BTK and target TP_AV_AK. Applying lem-trf-absolute-frobenius-coefficient-naturality with exponent b to V_AK yields

$$T(t_{A,V_AK})\circ c_{H,V_AK}=t_{B,TV_AK}.$$

Naturality of the specified t_B at the morphism c_{v,K}:V_BTK to TV_AK gives

$$t_{B,TV_AK}\circ P_B(c_{v,K})=c_{v,K}\circ t_{B,V_BTK}.$$

For e_R=t_R V_R composed with d_R, functoriality and these three equations give the full five-line calculation

$$\begin{aligned}
T(e_{A,K})\circ c_{vH,K}
&=T(t_{A,V_AK})\circ T(d_{A,K})\circ c_{vH,K}\\
&=T(t_{A,V_AK})\circ c_{H,V_AK}\circ P_B(c_{v,K})\circ d_{B,TK}\\
&=t_{B,TV_AK}\circ P_B(c_{v,K})\circ d_{B,TK}\\
&=c_{v,K}\circ t_{B,V_BTK}\circ d_{B,TK}\\
&=c_{v,K}\circ e_{B,TK}.
\end{aligned}$$

This uses arbitrary unbounded objects throughout. The scalar and absolute-Frobenius lemmas require no flatness or Tor-amplitude bound. For b=0, the trivialization is the identity with the standard pullback unitor. None of the argument requires invertibility of v or a lift to a finite-field model. In the parent, apply it at b=am and v=g^m, then replace e by the specified kappa using the other new node. Thus the new parent proof only assembles the two results, while no part of the old four-step argument has disappeared.

## Review by Q34

I read the current thm-trf-finite-coefficient-map.proof.md final sentence, both paragraphs and the displayed formula of prop-trf-scheme-galois-comparison.proof.md, the complete absolute-Frobenius-site proof, and Stacks more-morphisms.tex, Tag 0F6W, label lemma-relative-frobenius-weakly-etale, lines 19215–19238. I also read chapter sec-trace-formula and unit sk-p-trace-coeff. The chapter route is retained; the unit's natural coefficient comparisons are being resolved, not replaced by another trace route. No forbidden SGA source is used.

For the normal-form node, the source explicitly forms kappa from Phi=g_gamma F^(q) and the specified absolute-Frobenius trivialization; its second paragraph identifies the analogous construction for Phi^m with the multiplicative iterate. I checked the statement of prop-trf-frobenius-factorization: it supplies H=g_sigma^m Phi^m=Phi^m g_sigma^m for every positive m. The statement of def-trf-scheme-frobenius defines g_gamma as inverse to g_sigma, so cancellation uses the correct geometric, not arithmetic, Frobenius. I checked the canonical compositor statement: L(k composed with h)^* goes to Lh^* Lk^*, so for h=H, k=g^m the order P_R G_R is correct. The new formula does not claim that g is k-linear. Its coefficient annihilator and finite-type hypotheses are exactly those of the existing comparison.

For the contraction node, I opened every original cited statement: det-prop-scalar-six-pullback actually supplies composition in clause (1), not just isolated pullback isomorphisms; lem-weil-pbc-finite-discrete-condensed-ring-constant identifies finite discrete coefficient ring objects; lem-weil-pbc-finite-discrete-scheme-ring-constant transports the monoidal ring identification to the scheme site. The definition def-sp-constant-scalar-pullback-comparison specifies the actual constant ring maps and tensor-normalized mate, so the new node does not substitute an arbitrary coefficient comparison. The existing absolute-Frobenius coefficient-naturality statement permits every b>=0, every finite unital coefficient homomorphism, and arbitrary derived objects. Its displayed equality has exactly the orientation needed at V_AK. Naturality of t_B is used at the morphism c_v with source V_BTK and target TV_AK; all five lines of the calculation have source S_BTK and target TV_AK. The helper does not assert the composite vH result already, and the scalar compositor theorem alone says nothing about t, so both genuine inputs are needed. I read the existing lem-pur-frobenius-trivialization-pullback statement for its addition/iteration normalization, rather than taking a claimed formula from its proof.

Parent step 1 cites only the new normal-form statement. I checked that its displayed formula and characteristic-p assertion supply all data taken there, including the specified rather than arbitrary iterate. Step 2 cites only the new contraction statement; Y=X, v=g^m, b=am are admissible, both coefficient rings are finite and u is unital, and the formula printed in citations.json is precisely the square used. Step 3 is elementary substitution of these two equations under the equality Phi^m=g^m H, with their already-specified canonical compositors. There is no further comparison theorem hidden in this last step. The citation quotes are literal substrings of the two new statements. No parent proof step exceeds 2000 characters; the entire assembly is below 3000 characters.

Small cases checked: m=1 uses b=a, not b=1 unless a=1; this tests the p-power versus q-power distinction. Empty schemes and the zero coefficient ring are allowed by both constant-ring identifications and impose no cancellation of ring elements. For b=0 the contraction reduces to the ordinary identity-compositor normalization. Taking v=id gives the old absolute-Frobenius scalar square; taking an arbitrary noninvertible v leaves every displayed composite typed. A=Z/l^2 to B=F_l with l different from p is a nonflat allowed test, so replacing derived tensor by ordinary tensor would be wrong; no step makes that replacement. The same contraction statement even allows p-torsion coefficients because relative-Frobenius site trivialization is coefficient-independent. No argument requires properness, separatedness, boundedness or constructibility.

This repairs the return by adding exactly two statement-only unsplit nodes, of distinct scope and comparable argument size, and retaining the full original argument below for audit. The parent's statement and all maintainer-owned fields remain unchanged. No second worker or sub-agent was started, as required by the direct-delivery brief.

## Original four-step proof retained verbatim

### Original step 1

Fix $m\geq1$. Put $F=F_X$, absolute $p$-power Frobenius, and $H=F^{am}$, absolute $q^m$-power Frobenius. The factorization [prop-trf-frobenius-factorization] gives $H=g_\sigma^m\Phi^m=\Phi^m g_\sigma^m$. In [def-trf-scheme-frobenius], $g=g_\gamma$ is inverse to $g_\sigma$: their second-factor field maps are inverse, and their first-factor maps are identities. Cancelling $g_\sigma^m$ gives $\Phi^m=g^mH=Hg^m$. This is an equality of scheme morphisms; it does not require $g$ to be a $k$-morphism. The characteristic-$p$ hypothesis holds because every structure map from $k_0=\mathbf F_{p^a}$ sends $p\cdot1=0$ to $p\cdot1=0$.

Cited nodes: prop-trf-frobenius-factorization, def-trf-scheme-frobenius

### Original step 2

For $R=A,B$ abbreviate $S_R=L(\Phi^m)_R^*$, $P_R=LH_R^*$, and $G_R=L(g^m)_R^*$. Let $d_R:S_R\xrightarrow{\sim}P_RG_R$ be the canonical composition isomorphism of [lem-weil-pbc-proetale-derived-pullback-composition] for $\Phi^m=g^mH$. Write $t_R=\tau_R^{(am)}:P_R\xrightarrow{\sim}\operatorname{id}$ for the specified absolute-Frobenius trivialization. Unfolding the specified canonical comparison of [prop-trf-scheme-galois-comparison] fixed in the statement (built from the factorization through absolute $q^m$-power Frobenius and the canonical trivialization) gives $\kappa^{(m)}_{R,K}=t_{R,G_RK}\circ d_{R,K}$; this uses the specified construction, not a choice of an arbitrary isomorphism. The finite-discrete coefficient identifications [lem-weil-pbc-finite-discrete-condensed-ring-constant] and [lem-weil-pbc-finite-discrete-scheme-ring-constant] identify the constant ring objects used here with the finite condensed ring objects. Thus clause (1) of [det-prop-scalar-six-pullback] applies in these ordinary categories. Write $c_S=c_{\Phi^m}$, $c_P=c_H$, and $c_G=c_{g^m}$. Its composition clause, in the inverse-comparison direction, says precisely
$$
 T(d_{A,K})\circ c_{S,K}
 =c_{P,G_AK}\circ P_B(c_{G,K})\circ d_{B,TK}.
$$
Both sides go from $S_BTK$ to $TP_AG_AK$. No constructibility, boundedness, or coefficient flatness assumption occurs in clause (1).

Cited nodes: prop-trf-scheme-galois-comparison, lem-weil-pbc-proetale-derived-pullback-composition, lem-weil-pbc-finite-discrete-condensed-ring-constant, lem-weil-pbc-finite-discrete-scheme-ring-constant, det-prop-scalar-six-pullback

### Original step 3

Apply [lem-trf-absolute-frobenius-coefficient-naturality] on $X$ with exponent $b=am$ to the object $G_AK\in D_A$. Its hypotheses hold: $X$ has characteristic $p$, both rings are finite commutative, and $u$ is unital. It gives
$$
T(t_{A,G_AK})\circ c_{P,G_AK}=t_{B,TG_AK}.
$$
Moreover $t_B$ is a natural transformation $P_B\to\operatorname{id}$. Its naturality at the morphism $c_{G,K}:G_BTK\to TG_AK$ is
$$
t_{B,TG_AK}\circ P_B(c_{G,K})=c_{G,K}\circ t_{B,G_BTK}.
$$
The second equation is the defining naturality square of this specified trivialization, evaluated at this morphism.

Cited nodes: lem-trf-absolute-frobenius-coefficient-naturality

### Original step 4

Starting at $S_BTK$, substitute the composition identity of Step 2 and then both equations of Step 3:
$$
\begin{aligned}
T(\kappa^{(m)}_{A,K})\circ c_{S,K}
&=T(t_{A,G_AK})\circ T(d_{A,K})\circ c_{S,K}\\
&=T(t_{A,G_AK})\circ c_{P,G_AK}\circ P_B(c_{G,K})\circ d_{B,TK}\\
&=t_{B,TG_AK}\circ P_B(c_{G,K})\circ d_{B,TK}\\
&=c_{G,K}\circ t_{B,G_BTK}\circ d_{B,TK}\\
&=c_{G,K}\circ\kappa^{(m)}_{B,TK}.
\end{aligned}
$$
Every composite has target $TG_AK$. This is the asserted equality with the original $c_{\Phi^m}$ and $c_{g^m}$. The calculation works for every $m\geq1$ and every $K$, so in particular for $m=1$. Derived coefficient comparison and the helper already hold without flatness or Tor-amplitude assumptions, so none is introduced here.

Cited nodes: 

