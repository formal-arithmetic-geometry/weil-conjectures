# Q110: repair of lem-pur-adic-scalar-trace-coherence

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-adic-scalar-trace-coherence.json: repaired item, statement unchanged, three assembly steps (1862 characters total).
- dag/nodes/sec-smooth-purity/lem-pur-shifted-tate-unit-scalar-coherence.json: new statement-only lemma, status unsplit, no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-pur-compact-support-arrow-scalar-transport.json: new statement-only lemma, status unsplit, no Mathlib match.
- citations.json: one entry for each direct citation of the parent, quoting the cited statement literally.
- report.md: this review, with the full retained old argument and its work allocation.

The sandbox initially contained only .brief2 through .brief5: no prior node files, report or searches.jsonl. I recovered the delivered split from the current shared DAG, preserving all its metadata, statement and historical Mathlib searches, and archived it as returned-item.json inside this sandbox. I made no git invocation or write in the shared repository. repair_split.py is a sandbox-only transformation script. All new Mathlib searches are genuine msearch.py invocations in searches.jsonl; none is inferred from an old summary. No Lean was written or compiled.

## Attachments

None. I searched lean/WeilConjectures by the blueprint id and the notions. The existing exact statement is WeilConjectures.PurAdicScalarTrace.scalar_trace_coherence, lean/Sheaf/SecSmoothPurity/AdicScalarTraceCoherence.lean:206, whose proof is sorry at line 220. It is not an attachment. The existing IntegralTwistScalarCoherence statement provides unshifted beta coherence; it does not already state either new lemma. No matching project declaration was found for the children.

## WANTED

None. Both new nodes are agent auxiliaries for the existing blueprint calculation; neither claims a nonexistent numbered literature theorem. The source path in their source fields is the current main-20261015 purity-transport theorem, with the exact extracted proof portions named. The current theorem states transport but has no detailed proof. The detailed old unit is literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Step 3. The generic line/coefficient construction is also in literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-existence/prop-weil-twist-preserves.md. No SGA source is used.

## What was wrong and what changed

The human's 2026-10-21 return is a request to spread an already reviewed long proof across independently available tasks. The mathematical statement is retained verbatim; there is no statement dispute or weakening. I replaced the long parent proof by the assembly of two new statement-only children and existing compact-support naturality. Both children have empty proof, empty proof_deps, null proof_origin and status unsplit; no child was recursively split.

The first child isolates the coefficient-unit normalization, strict-tower/ordinary tensor identification, finite-Tor domains, and the shifted Tate-unit tower equation. This has no f, compact support or trace. Its comparisons are pinned by degree-zero multiplication, the specified natural beta and termwise shift maps, so it does not assume the desired equation by choosing arbitrary coherent maps.

The second child transports an arbitrary arrow P_0 M to an arbitrary V along the literal extended objects A_X M and D_X M. It has no theta, no twist, no coefficient-unit map and no smoothness assumption. Its explicit hypothesis that A_X M has finite Tor amplitude is needed to type the further compact-support comparison. It isolates the inverse compact-support composition/naturality argument, leaving the parent to identify the source with the twisted unit and the target with its coefficient unit. Neither child states the item's trace equation, and neither can replace the parent by a direct application alone. Their statements are of comparable size (2384 and 1825 characters).

The child concerning arrow transport is deliberately the separate comparison argument requested by this human re-split, not a new node for the single elementary inverse cancellation. It states the complete varying-coefficient Hom transport, including its actual compact-support/strict-tower normalization. Its eventual proof can use the existing compact-support comparison as a black box; the argument and its cancellations are retained below. In particular I did not create individual nodes for inverting an isomorphism or applying naturality.

## What remains unfinished

Only the proofs of the two statement-only children, intentionally assigned to future workers by the return. The parent has a complete assembly proof. The delivery is not a stage-2 or stage-3 repair, and the Lean statement and its sorry remain untouched.

## Mathlib and duplicate searches

Before creating either child I searched the whole DAG by the notions, titles, coefficient-unit normalization and arrow transport, inspected the closest statements, and ran tools/blueprint_refs.py ancestor on the item. The ancestor is thm-pur-rational-and-qbar-purity. I ran blueprint_refs.py search for twist scalar, unit scalar, trace coherence, twist, coefficient unit, unit comparison, scalar coherence, coefficient comparison and transport morphism. The broad searches were supplemented by reading the closest unshifted twist, scalar, and compact-support statements. Both children have that ancestor, via the item, precise from.place descriptions and same_as=[]; the item retains its already precise from.place and same_as=[]. Their chapter and unit are inherited from the current item, including its current sk-thm-sf-compatibility reroute. No unit/chapter record is changed.

For each child I used LeanFinder, LeanSearch, valid Loogle searches and grep, then a second wording. The exact tool/query strings are recorded in the child and searches.jsonl. I read the results, including Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:984-1041: ordinary module extension associativity has no completed sheaf coefficient category, Tate twist or compact-support comparison. CategoryTheory.NatTrans.naturality and NatIso.naturality_1 supply individual generic rewrites, not either child as a one-line specialization. I read NatTrans.lean and NatIso.lean:140-153. The semantic results about scalar towers, cyclotomic characters, ordinary pushforward of sheaves, cochains and topological compactly supported functions do not state these derived integral claims. Two Loogle identifier guesses were rejected and are labelled as failed identifier queries; successful valid follow-ups are recorded. One grep scope CategoryTheory/NatIso was a nonexistent directory and is explicitly not evidence of absence; I corrected it to CategoryTheory/NatIso.lean and read that file. No service outage is represented as a negative mathematical result.

## Not duplicates

lem-pur-shifted-tate-unit-scalar-coherence vs lem-weil-integral-twist-scalar-coherence: the existing statement compares unshifted beta on an arbitrary complete C; the new statement pins multiplication maps on three different coefficient units, their compatibility with the tower associator, the canonical [2d] comparisons and the uniform finite-Tor domains. The existing beta equation is an input to the new argument, not its full assertion.
lem-pur-shifted-tate-unit-scalar-coherence vs lem-weil-integral-twist-derived-scalar: the existing statement constructs one natural beta; it asserts neither the tower equation for normalized units nor its shift/unit compatibility.
lem-pur-shifted-tate-unit-scalar-coherence vs prop-weil-twist-preserves: that statement supplies line invertibility and domain preservation, not the specified comparison equations.
lem-pur-shifted-tate-unit-scalar-coherence vs lem-pur-coefficient-pullback-coherence: that node concerns already constructed inverse-image comparisons for a ringed-site morphism, explicitly separating all shift laws; it does not state the completed Tate-unit coefficient-tower law.
lem-pur-shifted-tate-unit-scalar-coherence vs lem-pur-signed-line-derived-base-change: that statement transports signed line powers under a single exact inverse-image functor and a ring isomorphism; our coefficient inclusions are generally not isomorphisms and our conclusion compares a three-field tower with shifts and unit normalizations.
lem-pur-shifted-tate-unit-scalar-coherence vs lem-pc-coefficient-unit-composition: that node is the abelian geometric pullback unit after forgetting O-module structure, not multiplication of completed coefficient rings in a derived coefficient tower.
lem-pur-compact-support-arrow-scalar-transport vs lem-pur-compact-support-integral-coefficient-comparison: the latter constructs c and gives its objectwise tower equation. The new statement is the induced contravariant Hom transport for arbitrary t:P_0 M to V, comparing inverse c followed by scalar extension and associator naturality at t. It neither constructs c again nor assumes the Hom identity.
lem-pur-compact-support-arrow-scalar-transport vs det-sfb-coefficient-comparisons-compact-support: that blueprint statement says the coefficient comparison is an isomorphism independent of compactification and compatible with composition, but gives no arrow transport identity with the normalized associators.
lem-pur-compact-support-arrow-scalar-transport vs det-prop-scalar-six-compact-support: that statement treats a single coefficient extension and geometric composition; our assertion is about successive coefficient changes on Hom into arbitrary V.
lem-pur-compact-support-arrow-scalar-transport vs lem-sfb-scalar-inverse-image-tower-diagram: that node compares geometric inverse image with underived scalar extension of sheaves and explicitly asserts no derived existence; it is not a compact-support Hom transport assertion.
lem-pur-shifted-tate-unit-scalar-coherence vs lem-pur-adic-scalar-trace-coherence: the child has no trace or compact support; it supplies the source/target comparison equations needed for the item's assembly.
lem-pur-compact-support-arrow-scalar-transport vs lem-pur-adic-scalar-trace-coherence: the child has neither twisted-unit source identification nor coefficient-unit target multiplication; the item needs the independent first child and naturality at theta_E inverse to obtain its assertion.

## Review by Q110

I read the entire returned proof, the chapter record and current unit record, the old purity-transport Step 3 and the current main-20261015 theorem, and the statements of every direct parent dependency. I also opened all the earlier proof dependencies (finite-free completed scalar comparison, twist-preserves, finite-Tor definition, integral twist/scalar coherence, derived beta and compact-support comparison) to check precisely what can be extracted. I checked the normalized multiplication and comparison structures in the existing Lean module as source material: UnitMultiplication has the pure-tensor formula plus the derived counit normalization; CoefficientComparison pins compact to the recorded c. No arbitrary unnormalized comparison is introduced in either child. The source is agent-written and is identified as such.

For parent Step 1 the new shifted-unit statement explicitly gives uniform finite-Tor domains and the two displayed equations, both of which I quoted/checked against the written statement. S=X and S=Y satisfy separated finite type over k and ell invertible because ell differs from p. Its T_0, theta and a are exactly the parent's canonical beta, unit multiplication and shift comparisons. Taking inverses to get theta_F inverse composed with a is elementary. The strict-tower comparison is the same natural chi used by both original nodes; no change from integral coefficients to rational/discrete coefficients occurs.

For Step 2 the new arrow-transport statement is used exactly at M=T_0, V=U_0,Y and t=t_0. The first child supplies all its object-domain hypotheses, including A_X T_0 at E; the original geometric hypotheses give separated finite type for f. Its conclusion is literally the displayed r_F P_F(alpha) c_B = alpha B(r_E) equation, with no unit maps suppressed. I separately read lem-pur-compact-support-integral-coefficient-comparison: its statement says c is a natural isomorphism on this finite-Tor domain, so its naturality applies to theta_E inverse. That is the only additional non-elementary citation of this step, and citations.json quotes the natural-isomorphism clause. No fact is taken from an unmentioned proof rather than a node statement.

For Step 3 I recomputed the chain with source B_Y P_E T_E and target U_F,Y. Expanding t_F cancels theta_F against the inverse-twist equation, naturality moves B_X theta_E inverse across c_B, the child arrow equation moves the compact coefficient associator to U_0,Y, and the child unit equation replaces u_F alpha by v B_Y(u_E). Functoriality then gives v B_Y(t_E). This is the displayed chain, not an assertion that compatibility is automatic. This step only substitutes equations already proved in Steps 1-2 and the stated definitions, so it is elementary and cites no extra theorem. There are no parent steps exceeding 2000 characters, and the total is below the human's 3000-character bound.

For the first child's mathematical statement I verified that all objects and coefficient inclusions are introduced, beta is canonical rather than existential, the multiplication normalization fixes the map even after resolving, and the cohomological shift [2d] changes [0,0] to [-2d,-2d]. The beta tower equation plus naturality at u_E is precisely what is needed to turn an arbitrary-object twist coherence into a coefficient-unit coherence; the retained old Step 2 below gives the detailed expansion. Shift comparison maps have no new interchange sign because the coefficient ring and line live in degree zero. A worker taking this child still has to justify the descent and shift/normalization compatibility; the statement carries no proof sketch.

For the second child I checked every arrow type before and after inversion: c_D inverse P_F(alpha_M) c_B maps B_Y P_E A_X M to D_Y P_0 M, alpha_V B_Y(tau_E) has that same input and output D_Y V. The original compact-support statement gives c_D alpha_(P_0 M)=P_F(alpha_M)c_B B_Y(c_A), while associator naturality gives D_Y(t)alpha_(P_0 M)=alpha_V B_Y A_Y(t). These are exactly the two arguments allocated to this child in the retained work below. Naturality of alpha is part of the natural tensor associator, and no finite-Tor claim about an arbitrary V beyond the child's explicit hypothesis is silently inferred.

I checked small cases: d=0 gives the untwisted unit equations; E=E_0 or F=E gives canonical multiplication/unit comparisons; t_0=0 gives zero on both sides; on empty schemes the only morphisms agree; ramified extensions require no etaleness or unramifiedness hypothesis and use the same finite-free completed comparison, with no identification of incompatible reduction levels. The new Hom assertion also works for M=0, V=0, t=0 and arbitrary nonsmooth separated finite-type f. Replacing the canonical unit multiplication by its negative would violate the normalization, so the sign ambiguity is excluded by the statement itself.

The corrections are structural: the old large proof is now two independent statement-only work items plus explicit assembly, all old hypotheses and actual maps retained. No false imported statement was found. I checked delivery-errors B-E: self-contained statements and notion dependencies; no recursive proof in a new node; exact logged searches; all direct parent uses quoted verbatim; no duplicate or dependency cycle introduced; no source-route substitution or SGA citation. Existing parent tool_uses metadata is retained unchanged; the new direct parent dependencies are in its own unit and need no newly declared off-route proof tool.

## Full retained argument and allocation

The following is the previous split's proof, retained verbatim as the future workers' argument, not placed in a statement-only child's proof field. Old Steps 1-2 are assigned to lem-pur-shifted-tate-unit-scalar-coherence. Old Step 3's inverse-comparison equation and old Step 5's associator-naturality argument are assigned to lem-pur-compact-support-arrow-scalar-transport for general M and V. Old Step 3's naturality at theta_E inverse, old Step 4's source-identification substitutions and old Step 5's final unit substitution are the parent's remaining short assembly. Thus none of the original arguments has been erased, replaced by an unsupported compatibility phrase, or turned into an assumption.

### Retained old Step 1

Write $A_W=C_{E/E_0,W}$, $B_W=C_{F/E,W}$, $D_W=C_{F/E_0,W}$, and let $\alpha^W:B_WA_W\xrightarrow{\sim}D_W$ be ordinary derived tensor associativity. The finite-free completed scalar comparison identifies these with the specified strict-tower extensions on derived-complete objects, naturally in the object. Put $U_L=\mathbf1_{L,Y}$ and restore the coefficient-unit maps suppressed in the statement: $u_E:A_YU_0\xrightarrow{\sim}U_E$, $u_F:D_YU_0\xrightarrow{\sim}U_F$, $v:B_YU_E\xrightarrow{\sim}U_F$. Thus the actual formula is $t_L=u_L C_{L/E_0,Y}(t_0)c_{L/E_0,T_0}^{-1}P_L(\theta_L^{-1})$. All comparisons are on their stated domains: by twist preservation the units twisted by $d$ lie in the integral constructible finite-Tor category; shift by $[2d]$ shifts the uniform Tor interval $[0,0]$ to $[-2d,-2d]$. Hence $T_0,T_E,T_F$ have uniform finite Tor amplitude. Since $\theta_E$ identifies $A_XT_0$ with $T_E$, the comparison at $A_XT_0$ below is also on this domain. The schemes satisfy the separated finite-type hypotheses, and $\ell$ is invertible because $\ell\ne p$.

Uses: lem-weil-finite-free-completed-scalar-comparison, prop-weil-twist-preserves, def-weil-finite-tor-amplitude

### Retained old Step 2

Apply integral twist/scalar coherence with the tower $E_0\subset E\subset F$, $S=X$, $C=\mathbf1_{E_0,X}$ and $m=d$. After the coefficient-unit identifications its equation, shifted by $[2d]$, is
$$\theta_F\circ\alpha^X_{T_0}=a_{F/E,\mathbf1_E}\circ B_X(\theta_E).$$
The shifts introduce no extra sign: extension tensors with a coefficient ring in degree zero, so reassociation before or after shifting has the same termwise map. Here $\theta_L=u_L(d)[2d]\circ\beta_{L/E_0,\mathbf1_{E_0,X}}[2d]$ and $a_{F/E,\mathbf1_E}=v(d)[2d]\circ\beta_{F/E,\mathbf1_{E,X}}[2d]$, with $\beta$ the natural twist comparison of [lem-weil-integral-twist-derived-scalar] and $u_L,v$ the coefficient-unit maps at $X$; the coherence equation gives $\theta_F\alpha^X_{T_0}=u_F(d)\,\alpha^X_{\mathbf1}(d)\,\beta_{F/E,A_X\mathbf1}\,B_X(\beta_{E/E_0,\mathbf1})[2d]$, and naturality of $\beta_{F/E}$ at $u_E$ gives $a_{F/E,\mathbf1_E}B_X(\theta_E)=v(d)\,B_X(u_E)(d)\,\beta_{F/E,A_X\mathbf1}\,B_X(\beta_{E/E_0,\mathbf1})[2d]$; the two agree by the unit equation below, which holds at $X$ by the same multiplication argument. Inverting and multiplying the displayed equation gives
$$\theta_F^{-1}\circ a_{F/E,\mathbf1_E}=\alpha^X_{T_0}\circ B_X(\theta_E^{-1}).$$
The coefficient-unit maps satisfy $u_F\circ\alpha^Y_{U_0}=v\circ B_Y(u_E)$: both are the multiplication map $(x\otimes b)\otimes c\mapsto xbc$. This also verifies the unit specialization used to obtain the displayed twist equation.

Uses: lem-weil-integral-twist-scalar-coherence, lem-weil-integral-twist-derived-scalar

### Retained old Step 3

Abbreviate $c_A=c_{E/E_0,T_0}$, $c_D=c_{F/E_0,T_0}$, and $c_{B,M}=c_{F/E,M}$. The compact-support coefficient comparison states, for the tower $E_0\subset E\subset F$,
$$c_D\circ\alpha^Y_{P_{E_0}T_0}=P_F(\alpha^X_{T_0})\circ c_{B,A_XT_0}\circ B_Y(c_A).$$
Since all these maps are isomorphisms, multiply by $c_D^{-1}$ on the left and $B_Y(c_A^{-1})$ on the right to get
$$c_D^{-1}\circ P_F(\alpha^X_{T_0})\circ c_{B,A_XT_0}=\alpha^Y_{P_{E_0}T_0}\circ B_Y(c_A^{-1}).$$
Naturality of the same comparison at the morphism $\theta_E^{-1}:T_E\to A_XT_0$ gives
$$P_F(B_X\theta_E^{-1})\circ c_{B,T_E}=c_{B,A_XT_0}\circ B_Y(P_E\theta_E^{-1}).$$

Uses: lem-pur-compact-support-integral-coefficient-comparison

### Retained old Step 4

Expand the left side of the required equality, restoring its target $U_F$. Substitute the inverse twist equation of Step 2, use functoriality of $P_F$, and then the naturality equation of Step 3. With $a=a_{F/E,\mathbf1_E}$ this gives
$$\begin{aligned}
t_F\circ P_F(a)\circ c_{B,T_E}
&=u_F\circ D_Y(t_0)\circ c_D^{-1}\circ P_F(\theta_F^{-1}\circ a)\circ c_{B,T_E}\\
&=u_F\circ D_Y(t_0)\circ c_D^{-1}\circ P_F(\alpha^X_{T_0})\circ c_{B,A_XT_0}\circ B_Y(P_E\theta_E^{-1}).
\end{aligned}$$
Every map in this equality has source $B_YP_ET_E$ and target $U_F$; only functoriality and the preceding equations were used.

Uses: 

### Retained old Step 5

Substitute the inverse composition equation of Step 3 into Step 4. Naturality of the tensor associator at $t_0:P_{E_0}T_0\to U_0$ reads $D_Y(t_0)\circ\alpha^Y_{P_{E_0}T_0}=\alpha^Y_{U_0}\circ B_YA_Y(t_0)$. Thus
$$\begin{aligned}
t_F\circ P_F(a)\circ c_{B,T_E}
&=u_F\circ D_Y(t_0)\circ\alpha^Y_{P_{E_0}T_0}\circ B_Y(c_A^{-1})\circ B_Y(P_E\theta_E^{-1})\\
&=u_F\circ\alpha^Y_{U_0}\circ B_Y\bigl(A_Y(t_0)\circ c_A^{-1}\circ P_E(\theta_E^{-1})\bigr)\\
&=v\circ B_Y\bigl(u_E\circ A_Y(t_0)\circ c_A^{-1}\circ P_E(\theta_E^{-1})\bigr)
=v\circ B_Y(t_E).
\end{aligned}$$
The third equality is the unit equation of Step 2, and the last is the definition of $t_E$. Identifying $B_YU_E$ with $U_F$ by $v$ is precisely the coefficient-unit convention in the statement, so this is the asserted identity. No normalization or nonzero condition on $t_0$ has been used.

Uses: 
