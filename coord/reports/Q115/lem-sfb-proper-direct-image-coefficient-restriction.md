# Stage-1 direct delivery Q115

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-direct-image-coefficient-restriction.json`: unchanged statement and statement dependencies; a short assembly proof, with new transpose nodes and the existing base-change and pullback results.
- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-open-coefficient-left-transpose.json`: statement, unsplit; no exact Mathlib match. It specifies the inverse transpose of the coefficient-then-restriction route and the coherent compositor equation reducing it to the common value.
- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-open-coefficient-right-transpose.json`: statement, unsplit; no exact Mathlib match. It specifies the inverse transpose of the restriction-then-coefficient route, its naturality rewrite and the exchange counit normalization.
- `citations.json`: one verbatim statement quote for every step citation. `searches.jsonl` and `search-results/` retain the actual queries and returned hits. The new nodes have no proof or proof dependencies. The full inherited proof is retained below as the handoff material for their future splitters.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag, coefficient/restriction terminology throughout the library, and the condensed coefficient module-operation implementation. The current `ChangeOfCoefficients.lean` constructs the mates, but does not supply the entire proper/open restriction statement; no exact finished declaration was found. Mathlib's general mate formulas are tools for the new calculations, not declarations of the concrete derived condensed-module comparisons with their coherent compositors.

## WANTED

None. All sources used are present. No SGA source is used.

## Corrections and scope

The released stage-1 repair note dated 2026-10-22 explicitly reopens this reviewed item, keeps its statement/route, and demands at least two comparable statement-only argument nodes with an assembly of at most 3000 characters. This delivery does that. The two sides' transpose computations are the two independent arguments; neither new node asserts equality of the two original routes or includes the proper-base-change isomorphism clause. The original base-change and coefficient-identification steps remain short applications of existing nodes rather than redundant new nodes. Their arguments, as well as the extracted ones, are preserved in full below. The assembly is 1711 characters of proof text.

The statement is byte-for-byte the live item's statement. No target, coefficient category, hypothesis or comparison morphism is changed. In particular uncompleted module-derived tensors, possibly nonflat coefficient maps, and the finite-subextension convention for the algebraic closure remain in force. A symbol for characteristic is renamed $p_0$ only in the new nodes to distinguish it from the proper morphism $p$.

The latest source read is `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-compact-support.proof.md`, Independence and Composition paragraphs; also the direct-image and pullback statements/proofs in that directory, the current chapter `_section.md`, and the unit `_section.md`. The blueprint gives a terse restriction characterization; the explicit transpose calculation is the existing agent argument, not a verbatim claim that the blueprint proves all displayed equations. `proof_origin.by` stays `agent`. The new source places and blueprint ancestry identify precisely the restriction argument they serve, with the item recorded in `via`.

## Not duplicates

Searches before creating nodes: full DAG statement search for transpose with exchange/coefficient, coefficient/restriction and mate/pasting; full-blueprint `blueprint_refs.py search` for mate, transpose, coefficient exchange, scalar transpose, coefficient restriction, scalar counit, proper open coefficient, transpose coefficient, scalar base change; ancestor query gave `det-prop-scalar-six-compact-support`. No new node takes a Stacks tag, so there is no same-tag collision to conceal.

lem-sfb-proper-open-coefficient-left-transpose vs lem-sfb-proper-direct-image-coefficient-restriction: the item equates two full routes and asserts invertibility of restriction; the new node computes only the first route's inverse transpose, including its intermediate counit expression and compositor formula. It does not assert the item's equation or isomorphisms.

lem-sfb-proper-open-coefficient-right-transpose vs lem-sfb-proper-direct-image-coefficient-restriction: the new node computes only the second route's inverse transpose and the exchange counit identity. The item still needs the first calculation and injectivity to get the equality, and existing base change for invertibility.

lem-sfb-proper-open-coefficient-left-transpose vs lem-sfb-proper-open-coefficient-right-transpose: each handles a different morphism; neither computes the other's route. Their common value is a morphism before the adjunction, not the final equality after it.

lem-sfb-proper-open-coefficient-left-transpose vs lem-sfb-scalar-direct-image-mate-coherence: that existing result gives the counit identity for gamma and compatibility along composable direct images and coefficient maps. It does not compute restriction around a geometric square or the four pullback coefficient comparisons.

lem-sfb-proper-open-coefficient-right-transpose vs lem-sfb-scalar-direct-image-mate-coherence: that result does not give the exchange counit identity or the coefficient-extension/naturality formula for the concrete exchange b. It is an available tool for the future proof.

lem-sfb-proper-open-coefficient-left-transpose vs lem-sfb-proetale-open-restriction-counit: the existing node is an underived module-sheaf open restriction theorem for one ring; it has no derived scalar-change cube or gamma.

lem-sfb-proper-open-coefficient-right-transpose vs lem-sfb-proetale-open-restriction-counit: the new node concerns ordinary unbounded internal-module derived categories and a change of condensed coefficients; the existing statement is underived with one sheaf ring.

lem-sfb-proper-open-coefficient-left-transpose vs lem-sp-proper-open-coefficient-mate-transposed: the existing smooth-purity node treats finite discrete rings and the lower-bounded proper/open interchange composite involving extension by zero. It does not state the present condensed-coefficient restriction-comparison transpose or the coherent-compositor equation.

lem-sfb-proper-open-coefficient-right-transpose vs lem-sp-proper-open-coefficient-mate-transposed: the existing node compares transposes of a different proper/open interchange composite with extension by zero, for finite coefficients and lower bounds; it does not compute the present exchange b and gamma on the ordinary module-derived categories for all listed maps.

lem-sfb-proper-open-coefficient-left-transpose vs lem-pur-topos-scalar-inverse-exchange-mate: that topos result uses constant ordinary ring sheaves, gives the final scalar/exchange equation and an extension-by-zero adjunct, but not this condensed module-ring setting or the displayed intermediate transpose/compositor normal forms.

lem-sfb-proper-open-coefficient-right-transpose vs lem-pur-topos-scalar-inverse-exchange-mate: same difference in coefficient objects; its statements do not give this inverse-transpose formula and exchange-counit normal form.

lem-sfb-proper-open-coefficient-left-transpose vs lem-sfb-open-star-shriek-scalar-mate-square: that result is an open-star/shriek comparison on a lisse sheaf, with extensions by zero and two opens; it neither treats proper direct-image open restriction nor states this transpose formula.

lem-sfb-proper-open-coefficient-right-transpose vs lem-sfb-open-star-shriek-scalar-mate-square: that result has different source and target involving extension by zero and a lisse input; it cannot supply the present exchange-counit calculation.

## Mathlib searches and verdicts

For each new id I ran the mandatory semantic, Loogle, and grep searches, read their hits, and tried a second semantic phrasing. Every recorded query is exactly in `searches.jsonl`. All services responded. The left search returned underived SheafOfModules adjunctions, Kan base change, and scalar counits; the right returned ordinary ModuleCat extension/restriction adjunctions and presheaf pullback composition. I read `Mathlib/CategoryTheory/Adjunction/Mates.lean`, in particular mateEquiv at line 84, mateEquiv_counit at line 123, and the mate-pasting formulas. Those are useful generic formulas, but neither complete concrete calculation is a one-line specialization: one must expand the actual derived comparison, insert its pullback compositors and transport through both coefficient actions before applying the formal identities. Hence both nodes are unsplit, not falsely classified as Mathlib leaves. The item's existing searches and recorded results are retained rather than rerun.

## Review by Q115

I read the released repair order, chapter/unit route, current latest compact-support proof, direct-image and pullback comparison statements/proofs, and every node statement cited by the four assembly steps. No statement dispute was found. For each new node I read the same latest source's Independence restriction argument and its Composition reference, and checked the explicit formulas against the inherited steps 3 and 4 and the direct-image counit equation. The new statements share a full, self-contained setup: schemes, proper/open Cartesian square, coefficient-map reference, ambient derived categories, all four pullback/direct-image functors, c,a,a', actual mate definitions, P,t, and inverse Hom transpose. Neither is allowed to replace a canonical map by an arbitrary isomorphism of endpoints. I rewrote the extracted formulas as conclusions (not proofs within the statement) and removed an initial implicit-reference setup on the right node. I also corrected the coefficient-identification directions: the left arrow explicitly precomposes by c_v inverse and postcomposes by Rq'(c_u), so its source and target agree literally with the right arrow.

Step 1 uses precisely the finite theorem's clause 2, integral theorem's clause 3, rational theorem's clause 3, and scalar-ctf's clause 3. I opened those statements: finite uses Dctf, while integral and rational allow Dbc, which contains the bounded constructible finite-Tor category by its definition. The coefficient endpoints of every listed map are exactly those covered; taking E=Q_l covers Z_l and Q_l. Scalar-ctf puts T_ZM in Dctf at the target coefficient, so the second restriction map is covered, including nonflat finite maps. Properness and the standing finite-type hypotheses are exactly those of the item, with q the given base change; no stronger base or smoothness assumption is needed. The module-derived node states the adjunction used to specify the exchange. These are already the item's accepted three off-unit generic proper-base-change tool uses, retained in split_report, with no new route departure.

Step 2 uses the actual statement of pullback comparison (1), including naturality and composition coherence, and the coefficient-change definition. I checked their direction and endpoints; the new nodes use the inverse orientation c_f. Step 3 now cites the left-transpose statement itself, which gives both the full expression with the primed p-counit and its common value T(t)c_q. Step 4 cites the right-transpose statement giving all three displayed normal forms and the exchange-counit identity, then the actual module-derived adjunction, so injectivity is legitimate. The two new nodes have independent statement dependencies and no dependency on the item or one another, avoiding a circular proof. Every cited quote is copied from its statement, not a proof or a definition that only alludes to a theorem. I checked C1 and C4 by mapping every use to those explicit clauses; citations.json has all pairs.

I checked all the B--E failure modes: new nodes are statement-only, introduce their objects, retain TeX with single backslashes, have actual source places and blueprint ancestry, and name all notions through definition/operation nodes. There are no invented Stacks attributions or unrun searches. The repair-order exception, rather than generic relabelling, is why these two named intermediate calculations are extracted: neither states the item's clause, and their formulas preserve the previous real arguments. No single new node moves the whole item. No general false assertion of scalar flatness, inverse-image fully faithfulness, or preservation of injectives enters the assembly. I checked no reference reaches back to the item and no object is confused with a different fibre product. All assembly steps are below 2000 characters, total below 3000; the long hypothesis setup in a new statement is not a hidden proof step.

Edge tests: for M=0 the formulas are zero maps between zero objects; for V empty all targets and transposes on Z_V are zero. For v=id_Y the square gives u=id_Z and q=p, both exchange maps are identities under the canonical unitors and the normal form is the coefficient counit transpose T(epsilon_p)c_p; no spurious equality to an identity on another object is claimed. For identity coefficient change all c's normalize to identity and the formulas reduce to the defining transpose of b. For finite nonflat change (Z/l^2 to F_l) no exactness of underived tensor was assumed: T is derived throughout, so the same formulas remain typed. No axiom/Lean code/compiler was introduced.

## Remaining work

Only stage 1 is delivered. The two new nodes are deliberately unsplit statements for other workers to prove; no Lean is written or compiled. The required server dry run is run after this report and every failure is repaired before push.

## Preserved inherited argument for the extracted workers

These are the original four proof steps, retained verbatim as source material rather than hidden as proof fields in the new statement-only nodes. Old steps 1 and 2 remain the item's applications of existing theorems; old step 3 belongs to the left-transpose argument; old step 4's transpose computation belongs to the right-transpose argument, and its final injectivity is the assembly.

### Original step 1

For the cartesian square defining $Z_V$, the canonical exchange map $b_{p,M}:v^*Rp_*M\to Rp_{V,*}u^*M$ is the proper base-change map. In the finite coefficient case it is an isomorphism by [det-thm-sfb-proper-base-change-finite](2); for $\mathcal O_E$ it is an isomorphism by [det-thm-sfb-proper-base-change-integral](3); and for $E$ or $\overline{\mathbf Q}_\ell$ it is an isomorphism by [det-thm-sfb-proper-base-change-rational](3). Taking $E=\mathbf Q_\ell$ covers the $\mathbf Z_\ell$ and $\mathbf Q_\ell$ stages. The coefficient-change theorem [det-prop-scalar-six-ctf](3) puts $T_ZM$ in $\Dctf(Z,\Lambda')$, so the same argument applies to $b_{p,T_ZM}$; the displayed exchange map is exactly the unit--pullback--counit map specified in the statement by the derived adjunction of [sk-def-sfb-module-derived-pushpull].

Cited nodes: det-thm-sfb-proper-base-change-finite, det-thm-sfb-proper-base-change-integral, det-thm-sfb-proper-base-change-rational, det-prop-scalar-six-ctf, sk-def-sfb-module-derived-pushpull

### Original step 2

The pullback coefficient identifications $v^*T_Y\simeq T_Vv^*$ and $u^*T_Z\simeq T_{Z_V}u^*$ are the instances for $v$ and $u$ of the natural pullback--coefficient-change isomorphism in [det-prop-scalar-six-pullback](1). Its composition compatibility identifies both ways of transporting a coefficient-changed object around the cartesian square, so the source and target of the desired equality are literally the displayed objects after these identifications.

Cited nodes: det-prop-scalar-six-pullback, sk-def-sfb-coefficient-change

### Original step 3

Put $q=p_V$ and $P=Rp_*M$. For any scheme morphism $f$, write $c_f:f_{\Lambda'}^*T\xrightarrow{\sim}Tf_\Lambda^*$ for the inverse of the identification in [det-prop-scalar-six-pullback](1), and write $a:q_\Lambda^*v_\Lambda^*\xrightarrow{\sim}u_\Lambda^*p_\Lambda^*$ and $a'$ for the pullback composition comparisons over the two coefficient rings. The adjoint transpose of $b_{p,M}$ is $t=u_\Lambda^*(\epsilon_{p,M})\circ a_P$. By the definition of $b$ and naturality of $a'$, the transpose under $q_{\Lambda'}^*\dashv Rq_{*,\Lambda'}$ of the left-hand composite, with the coefficient identifications in the statement, is
$$c_{u,M}\circ u_{\Lambda'}^*(\epsilon'_{p,T_ZM})\circ u_{\Lambda'}^*p_{\Lambda'}^*(\gamma_{p,M})\circ a'_{T_YP}\circ q_{\Lambda'}^*(c_{v,P}^{-1}).$$
The counit equation of [det-prop-scalar-six-direct-image](2) replaces $\epsilon'_p\circ p_{\Lambda'}^*\gamma_p$ by $T_Z(\epsilon_p)\circ c_{p,P}$. Naturality of $c_u$ moves $T_Z(\epsilon_p)$ past $c_u$. Finally pullback composition compatibility in [det-prop-scalar-six-pullback](1), applied to $p\circ u=v\circ q$, gives
$$c_{u,p_\Lambda^*P}\circ u_{\Lambda'}^*(c_{p,P})\circ a'_{T_YP}\circ q_{\Lambda'}^*(c_{v,P}^{-1})=T_{Z_V}(a_P)\circ c_{q,v_\Lambda^*P}.$$
Thus the left-hand transpose is $T_{Z_V}(t)\circ c_{q,v_\Lambda^*P}$.

Cited nodes: det-prop-scalar-six-direct-image, det-prop-scalar-six-pullback, sk-def-sfb-module-derived-pushpull

### Original step 4

For the right-hand composite, the counit equation of [det-prop-scalar-six-direct-image](2) for $q$ says that its adjoint transpose is
$$T_{Z_V}(\epsilon_{q,u^*M})\circ c_{q,Rq_*u^*M}\circ q_{\Lambda'}^*T_V(b_{p,M}).$$
Naturality of $c_q$ rewrites this as
$$T_{Z_V}\bigl(\epsilon_{q,u^*M}\circ q_\Lambda^*(b_{p,M})\bigr)\circ c_{q,v_\Lambda^*P}=T_{Z_V}(t)\circ c_{q,v_\Lambda^*P},$$
where the final equality is exactly the unit--counit transpose identity for the defining exchange map $b_{p,M}$. This is the transpose computed in step 3, so the adjunction bijection in [sk-def-sfb-module-derived-pushpull] proves the required equality. Only the counit identities and pullback coherence are needed for this equality; invertibility of $b$ was established in step 1.

Cited nodes: det-prop-scalar-six-direct-image, det-prop-scalar-six-pullback, sk-def-sfb-module-derived-pushpull

