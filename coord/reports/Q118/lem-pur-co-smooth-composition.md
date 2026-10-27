## Worker report

Files written: the item JSON and four new statement-only JSON files in dag/nodes/sec-smooth-purity/. No Lean source, repository file, launcher file, compiler or build was touched. The sandbox initially contained only dispatcher brief markers, not a retained split/report/search log. I copied the current repository node, which contains exactly the eight-step returned proof (the source of the old argument below). The item statement, source metadata, imported fields and Lean record are retained. The delivery tool rebases the sandbox against current server main.

- lem-pur-constructible-tensor-composition: statement, unsplit; no Mathlib match. No proof steps, proof dependencies or proof sketch in its statement.
- lem-pur-tensor-mate-invertible-input: statement, unsplit; no Mathlib match. No proof steps, proof dependencies or proof sketch in its statement.
- lem-pur-tensor-mate-base-change: statement, unsplit; no Mathlib match. No proof steps, proof dependencies or proof sketch in its statement.
- lem-pur-exceptional-base-change-pasting: statement, unsplit; no Mathlib match. No proof steps, proof dependencies or proof sketch in its statement.

Attachments: none. The project's compared pro-etale theorem in Sheaf/Paper/CohomologicalSmoothComposition.lean:109 ends in sorry at line 138. The ordinary etale IsCohomologicallySmooth.comp and upper-shriek tensor/base-change declarations use the etale predicate/categories, not the transported pro-etale predicate of this item; they are reference material, not an exact attachment. Searched WeilConjectures by blueprint tag, cohomological smoothness and the four new notions before creating nodes.

WANTED: none. The local main-20261015 blueprint proof is the source. Its displayed calculation and final base-change sentence require the canonical-map expansions already in the returned proof; those are agent arguments, not attributed to a missing literature theorem. No SGA source is used.

## Repair of the return

The return asks for at least three comparable independent argument nodes and a parent proof at most 3000 characters, without erasing the old argument. There are four new nodes. Returned Steps 1–2 belong to constructible-tensor-composition (composition adjunction, counit normalization, tensor assembly and exact transpose); Step 3 remains verbatim as the parent's inverse argument; Step 4 belongs to tensor-mate-invertible-input; Steps 5–7 belong to tensor-mate-base-change (using the existing coherence and transport statements); Step 8 belongs to exceptional-base-change-pasting. These are distinct arguments rather than four renamed clauses of cohomological smoothness. In particular neither base-change lemma assumes cohomological smoothness, the invertible-input lemma assumes only an invertible input, and the tensor-composition lemma assumes only tensor clauses and proves an actual morphism equality. No new lemma restates the entire item. The new nodes are left unsplit so their arguments can be assigned independently.

The new parent proof contains 2539 characters across three steps, compared with 10643 before repair. The complete old proof is retained below; the change is allocation of work, not summarization of its mathematical content.

## Source and argument allocation

All four new nodes use the same local main-20261015 composition proof, with precise distinct from.place descriptions. Blueprint ancestor is lem-pur-co-smooth-composition, via is empty. Whole-blueprint searches included tensor mate, invertible input, exceptional composition, tensor transitivity, dualizing base change, base change composition, projection formula, cohomologically smooth and invertible exceptional. Whole-DAG statement/title searches and source searches were also read. The parent is itself the blueprint node, so from remains null and same_as is empty. No new node with the same statement was found. The existing tool comparisons below are used in the allocated argument, not copied into new nodes.

For the first new node: old Step 1 takes compact-support composition from thm-sf-comp-composition and lem-amb-etale-compact-comparisons, forms its right-adjoint conjugate with lem-cat-right-adjoint-composition, and transports the constructible adjunctions of def-weil-exceptional-inverse-image. It preserves the explicit composite-counit normalization. Old Step 2 gives the complete Phi construction, its unit value a, the evaluation e_W, and the transpose comparison using fix-prop-projection-formula's stated naturality and composition compatibility. Pullback-composition, tensor-pullback, finite-Tor pullback and tensor closure retain exactly their roles. This is not the stronger unsupported assertion of an ambient pro-etale exceptional adjunction.

For the second new node: old Step 4 is the Hom-chain with P inverse, projection formula and exceptional adjunction. Its Yoneda isomorphism must be checked to be the specified theta by undoing that chain; the node demands that canonical map, not only the endpoints. That argument is separate from the composition and base-change normalizations.

For the third new node: old Step 5 uses the actual statement of lem-pur-co-smooth-pf-exchange-coherence for arbitrary schemes/base arrows, and Step 6 uses the actual equality in lem-pur-co-smooth-exchange-transport plus thm-cbc-finite-level-proetale to identify and invert this very exchange. These two existing nodes remain prerequisites of the future proof, not new duplicate lemmas. Old Step 7 supplies arbitrary-pullback finite-Tor typing using lem-weil-pbc-pullback-preserves-bounded-constructible, lem-sf-flat-model and the flat-term assertion of lem-weil-pbc-ringed-topoi-derived-tensor-pullback. It defines b by the displayed inverse-exchange/counit transpose and proves the tensor/beta square by the two explicit transposes. No smoothness of u' is used. The old final consequence about invertible inputs is assembled in parent Step 3 with the second node.

For the fourth new node: old Step 8's substantial argument is the equality identifying the composite mate with beta_gf,t, via its four-arrow transpose, vertical exchange pasting of thm-cbc-finite-torsion transported by thm-cbc-finite-level-proetale, the first node's counit normalization, and lem-weil-pbc-mate-pasting. This equality is stated without isomorphy hypotheses; the elementary conclusion that a composite of isomorphisms is invertible belongs to the parent. The schemes X',Y' and all arrows are introduced in its own statement.

## Not duplicates

lem-pur-constructible-tensor-composition vs lem-sf-exceptional-tensor-transitivity: the existing node is ordinary unbounded etale and assumes theta_f on every ambient object; the new statement is the transported pro-etale constructible finite-Tor canonical identity with only that finite-Tor hypothesis.

lem-pur-constructible-tensor-composition vs lem-sf-constructible-exceptional-compositor: the existing node assumes absolute separatedness of all schemes and states the compositor/counit only; the new statement permits nonseparated finite-type bases and proves the canonical tensor-map identity.

lem-pur-constructible-tensor-composition vs lem-pur-dualizing-unit-composite: the existing node treats unit-valued omega_g and etale-like rho; the new identity is for general tensor clauses at all finite-Tor inputs.

lem-pur-tensor-mate-invertible-input vs lem-sf-invertible-factor-hom-cancellation: the existing node is an internal-Hom cancellation theorem in a closed symmetric monoidal category; it does not state the canonical exceptional tensor mate.

lem-pur-tensor-mate-base-change vs lem-pur-co-smooth-pf-exchange-coherence: the existing node equates the ambient compact-support PF/exchange square; the new node concerns its exceptional adjoint tensor/beta square and finite-Tor typing.

lem-pur-tensor-mate-base-change vs lem-pur-co-smooth-exchange-transport: the existing node identifies the compact-support exchange across sites; the new node gives the exceptional transpose identity on arbitrary finite-Tor inputs.

lem-pur-tensor-mate-base-change vs lem-pur-exceptional-mate-site-comparison: the existing node compares exceptional mates across sites under separated-scheme and dimension assumptions; the new node compares theta and beta without absolute separatedness.

lem-pur-tensor-mate-base-change vs lem-pur-smooth-exceptional-tensor-pasting: the existing node requires smooth pure-dimensional morphisms; the new identity requires neither u nor u prime smooth.

lem-pur-exceptional-base-change-pasting vs lem-pur-smooth-exceptional-tensor-pasting: the existing node requires smooth towers and proves more identities there; the new pasting equation has arbitrary separated finite-type vertical maps.

lem-pur-exceptional-base-change-pasting vs lem-weil-pbc-mate-pasting: the existing node is abstract mate calculus; the new node identifies the actual specified transported compactification exchanges, compositors and dualizing maps.

## Review by Q118

I read the current main-20261015 statement and proof, the master chapter and sk-prop-cohsm route, the current item and its Lean declaration, and the statements quoted in citations.json. The source really requires three canonical clauses, so I kept the item statement exactly and did not replace any canonical map by an arbitrary isomorphism. The new nodes make precise different sentences of the same proof: composition calculation, invertibility input argument, arbitrary-base-change tensor square, and vertical-pasting identification. Their source is this agent-written blueprint expansion; no unsupported Stacks label or prohibited SGA trace route is claimed.

Parent Step 1 uses def-pur-co-smoothness clause (2), exactly the two theta hypotheses of constructible-tensor-composition. Its statement supplies both a and Phi and explicitly equates Phi with theta_gf(1 tensor a); cancellation of two isomorphisms is the only assembly there. Parent Step 2 retains the two written inverse identities, takes inverse objects from clause (1), finite-Tor values of omega from def-weil-exceptional-inverse-image, finite-Tor pullback/tensor closure from lem-sf-pullback-tor-amplitude and lem-sf-tensor-ctf, monoidality from lem-weil-pbc-ringed-topoi-derived-tensor-pullback, and the coefficient-unit pullback identification from def-weil-derived-pullback-tensor-hom. None of those citations is being used for a fact absent from its statement; the tensor reassociation and inverse substitution are elementary once they are cited. Parent Step 3 uses def-pur-co-smoothness clause (3) only for f and g, never for f' or g'. The base-change geometry is exactly lem-pod-separated-finite-type-base-change. The new base-change node explicitly supplies finite-Tor typing along the arbitrary horizontal map and the theta/beta equation. The invertible-input node then applies to both f and f' without circular smoothness assumptions. Finally the pasting node's displayed equality, rather than an appeal to unnamed compatibility, identifies the final isomorphism with beta_gf,t. Every node cited in each step has a verbatim quote in citations.json.

I checked finite coefficients n>=1 and ell different from p throughout, all schemes finite type over the fixed field, all vertical maps separated finite type, and arbitrary horizontal maps without absolute separatedness. Source/target of b is w*G_uP to G_u'v*P; inverse exchange is required in its transpose. Source/target of the pasting identity is s*omega_gf to omega_g'f'. The first node's counit has F_g F_f(c_K) before the two counits, with the correct order. For identity f or g, the maps reduce to the unit/counit-normalized identities; for identity base change the tensor/beta square is naturality with identity exchange. For P equal to the unit, the invertible-input lemma reduces to the unitor theta and the third node gives b=beta. Empty schemes give the unique zero-category maps and do not require a dimension or a nonempty cover; n=1 is included. Shifts or nontrivial invertible P are allowed, so the invertible-input node is not restricted to locally free degree-zero lines. No orientation or pure relative dimension is inserted.

Against delivery-errors B–E: all new objects/hypotheses are introduced within each statement; their notions cite actual defining nodes, TeX is singly escaped, source places are explicit, and the nodes are statement-only. I read the generic adjunction, ordinary module/pullback and exponentiable-morphism search hits; none specializes in one line to these transported exceptional maps. The search log contains two semantic phrasings per node plus LeanSearch, Loogle and Mathlib grep, and each mathlib_searches entry is taken from that real log. Exact ordinary etale project lemmas are not disguised as Mathlib results or pro-etale attachments. I compared the nearby existing nodes listed above and ruled out duplicates by their domains or conclusions. The parent and new nodes make no route change, no false elementary designation on a transpose comparison, and no use of a cited proof rather than its statement. All three parent steps are below 2000 characters, and the new nodes have no proof steps. The repair replaces the overlong parent's distribution only; no mathematical statement correction was needed.

## Preserved returned proof and future proof briefs

The following eight paragraphs are the returned proof verbatim, with their cited node lists. They preserve every argument for the workers who split the new nodes; they are not proof steps on the new statement-only nodes.

### Returned Step 1 → lem-pur-constructible-tensor-composition

Work with the finite coefficient $\Lambda=A_{E,n}$ and the constructible exceptional functors of [def-pur-co-smoothness, def-weil-exceptional-inverse-image]. The morphisms $f,g$ are separated of finite type, hence so is $gf$: composites of separated, of locally finite type and of quasi-compact morphisms are again such (elementary; Mathlib instances `AlgebraicGeometry.IsSeparated` composition, `Morphisms/Separated.lean`:75, `locallyOfFiniteType_comp`, `Morphisms/FiniteType.lean`:68, `quasiCompact_comp`, `Morphisms/QuasiCompact.lean`:69). Use the compact-support composition isomorphism [thm-sf-comp-composition] and its ordinary etale form [lem-amb-etale-compact-comparisons]. Apply [lem-cat-right-adjoint-composition] to the ordinary etale adjunctions defining these functors and then their specified pro-etale constructible realizations. This gives $c:R(gf)^!\xrightarrow{\sim}Rf^!Rg^!$. If $\varepsilon_u:Ru_!Ru^!\to1$ denotes a counit, its normalization is
$$\varepsilon_{gf,K}=\varepsilon_{g,K}\circ Rg_!(\varepsilon_{f,Rg^!K})$$
after inserting $c$ and the compact-support composition comparison. This construction uses the etale adjoints and their transported constructible restrictions; it needs no unrestricted pro-etale exceptional adjoint. All applications of clause (2) below have finite-Tor inputs: pullback preserves that category by [lem-sf-pullback-tor-amplitude], and tensor products stay in it by [lem-sf-tensor-ctf].

Uses: def-pur-co-smoothness, def-weil-exceptional-inverse-image, thm-sf-comp-composition, lem-cat-right-adjoint-composition, lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf, lem-amb-etale-compact-comparisons.

### Returned Step 2 → lem-pur-constructible-tensor-composition

Put $W=\omega_f\otimes^L Lf^*\omega_g$. The monoidal and composite pullback comparisons [lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-proetale-derived-pullback-composition], followed by the two isomorphisms $\theta$ of clause (2) in [def-pur-co-smoothness], give for $K\in D^b_{ctf}(Z,\Lambda)$
$$\Phi_K:L(gf)^*K\otimes^LW\xrightarrow{\sim}Lf^*(Lg^*K\otimes^L\omega_g)\otimes^L\omega_f\xrightarrow{\theta_{f,Lg^*K\otimes^L\omega_g}}Rf^!(Lg^*K\otimes^L\omega_g)\xrightarrow{Rf^!\theta_{g,K}}Rf^!Rg^!K\xrightarrow{c^{-1}}R(gf)^!K.$$
At the unit this gives $a=\Phi_{\Lambda_Z}:W\xrightarrow{\sim}\omega_{gf}$. Check the required canonical map, rather than just an abstract tensor isomorphism. Let $e_W:R(gf)_!W\to\Lambda_Z$ be the transpose of $a$. By Step 1 and the definition of $\theta$, it is
$$Rg_!Rf_!W\xrightarrow{Rg_!Rf_!\theta_{f,\omega_g}}Rg_!Rf_!Rf^!\omega_g\xrightarrow{Rg_!\varepsilon_{f,\omega_g}}Rg_!\omega_g\xrightarrow{\varepsilon_{g,\Lambda_Z}}\Lambda_Z,$$
where the first arrow uses the symmetry $W\cong Lf^*\omega_g\otimes^L\omega_f$ before applying $\theta_{f,\omega_g}$. Expand the two $\theta$'s in $\Phi_K$ by their counit transposes. Naturality of the projection formula moves the map $\theta_{g,K}$ through the $f$-projection formula. Compatibility of the projection formula with composition [fix-prop-projection-formula] identifies the successive $f$- and $g$-projection formulas with that for $gf$. The resulting transpose is exactly
$$R(gf)_!(L(gf)^*K\otimes^LW)\xrightarrow{\mathrm{sym},\operatorname{PF}_{gf}^{-1}}R(gf)_!W\otimes^LK\xrightarrow{e_W\otimes1}\Lambda_Z\otimes^LK\cong K.$$
By the counit equation defining $a$, this is also the transpose of $\theta_{gf,K}\circ(1\otimes a)$. Uniqueness of transposes proves $\Phi_K=\theta_{gf,K}\circ(1\otimes a)$. Since $a$ and $\Phi_K$ are isomorphisms, clause (2) holds for $gf$, and $a^{-1}$ gives the asserted dualizing-object identification.

Uses: def-pur-co-smoothness, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-proetale-derived-pullback-composition, fix-prop-projection-formula.

### Returned Step 3 → parent Step 2

Choose two-sided tensor inverses $M_f,M_g$ from clause (1) of [def-pur-co-smoothness]. The objects $\omega_f=Rf^!\Lambda_Y$ and $\omega_g=Rg^!\Lambda_Z$ lie in $D^b_{ctf}$ by the finite-Tor preservation of the constructible exceptional functor [def-weil-exceptional-inverse-image], and $M_f,M_g\in D^b_{ctf}$ by clause (1). Hence both $W$ and $B=Lf^*M_g\otimes^LM_f$ lie in $D^b_{ctf}(X,\Lambda)$ by [lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf]. The monoidal comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and the inverse identities give
$$W\otimes^LB\cong\omega_f\otimes^LLf^*(\omega_g\otimes^LM_g)\otimes^LM_f\cong\omega_f\otimes^LM_f\cong\Lambda_X,$$
$$B\otimes^LW\cong Lf^*M_g\otimes^L(M_f\otimes^L\omega_f)\otimes^LLf^*\omega_g\cong Lf^*(M_g\otimes^L\omega_g)\cong\Lambda_X.$$
The pullback of the unit is the unit: on constant-coefficient complexes it is inverse image of the constant coefficient sheaf, as specified in [def-weil-derived-pullback-tensor-hom]. Thus $W$, and hence $\omega_{gf}$ via $a$ from Step 1, is invertible. This proves clause (1).

Uses: def-pur-co-smoothness, lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-weil-derived-pullback-tensor-hom, def-weil-exceptional-inverse-image.

### Returned Step 4 → lem-pur-tensor-mate-invertible-input

For use after base change, verify a formal consequence of the projection formula without assuming the base-changed morphism cohomologically smooth. Let $u:T\to U$ be separated of finite type in this setting, let $P\in D^b_{ctf}(U,\Lambda)$ be tensor-invertible with inverse $P^{-1}$, and write $F_u=Ru_!$, $G_u=Ru^!$, $u^*=Lu^*$. The adjunctions of [def-weil-exceptional-inverse-image] and the projection formula [fix-prop-projection-formula] give natural bijections, for every $A\in D^b_{ctf}(T,\Lambda)$,
$$\begin{aligned}
\operatorname{Hom}(A,G_uP)&\cong\operatorname{Hom}(F_uA,P)\cong\operatorname{Hom}(F_uA\otimes^LP^{-1},\Lambda_U)\\
&\cong\operatorname{Hom}(F_u(A\otimes^Lu^*P^{-1}),\Lambda_U)\cong\operatorname{Hom}(A\otimes^Lu^*P^{-1},\omega_u)\\
&\cong\operatorname{Hom}(A,u^*P\otimes^L\omega_u).
\end{aligned}$$
Pullback of the two inverse identities is valid by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]; the finite-Tor domains follow from [lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf]. Yoneda gives an isomorphism $u^*P\otimes^L\omega_u\to G_uP$. Its transpose, undoing the displayed bijections, is $(\varepsilon_{u,\Lambda_U}\otimes1)\operatorname{PF}_u^{-1}$ with symmetry and units inserted, so it is exactly the canonical $\theta_{u,P}$ of [def-pur-co-smoothness]. In particular $\theta_{u,P}$ is invertible for an invertible input even when cohomological smoothness of $u$ has not been established.

Uses: def-weil-exceptional-inverse-image, fix-prop-projection-formula, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf, def-pur-co-smoothness.

### Returned Step 5 → lem-pur-tensor-mate-base-change

Let $u:T\to U$ be separated of finite type in the fixed setting, let $v:U'\to U$ be arbitrary, and form the Cartesian square with $w:T'=T\times_UU'\to T$ and $u':T'\to U'$. Write $F_u=Ru_!$, $G_u=Ru^!$, and $u^*=Lu^*$. For the chosen compactification and its base change, [lem-pur-co-smooth-pf-exchange-coherence] gives
$$E_u(N\otimes^Lu^*P)\circ v^*\operatorname{PF}_{u,N,P}=\operatorname{PF}_{u',w^*N,v^*P}\circ(E_u(N)\otimes1).$$
Here $E_u:v^*F_u\to F_{u'}w^*$ is the specified ambient compactification exchange. The lemma allows arbitrary schemes and arbitrary $v$; its supplied compactification is the one used for our functors. Apply it to $N=\omega_u$ and finite-Tor $P$ when needed below.

Uses: lem-pur-co-smooth-pf-exchange-coherence.

### Returned Step 6 → lem-pur-tensor-mate-base-change

By [lem-pur-co-smooth-exchange-transport], $E_u$ is the exchange obtained by transporting [def-cbc-exchange-map] on every etale-origin input: the lemma's equality identifies the proper-then-open composites as transformations, including for arbitrary $v$. Thus the equality of Step 5 concerns precisely the exchange used in clause (3) of cohomological smoothness. On the present etale-origin inputs $E_u$ is invertible by [thm-cbc-finite-level-proetale].

Uses: lem-pur-co-smooth-exchange-transport, def-cbc-exchange-map, thm-cbc-finite-level-proetale.

### Returned Step 7 → lem-pur-tensor-mate-base-change

For arbitrary $v$, $v^*P$ is bounded constructible by [lem-weil-pbc-pullback-preserves-bounded-constructible]. Pull back a bounded flat model [lem-sf-flat-model]: [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] preserves its flat terms and degree range. Thus $v^*P$ has finite Tor amplitude, so Step 4 applies to $u'$ as well. In the square of Step 5, define for a finite-Tor input $P$ the map $b_{u,v;P}:w^*G_uP\to G_{u'}v^*P$ as the transpose of
$$F_{u'}w^*G_uP\xrightarrow{E_u(G_uP)^{-1}}v^*F_uG_uP\xrightarrow{v^*\varepsilon_{u,P}}v^*P.$$
For $P=\Lambda_U$ this is the specified $\beta_{u,v}$ in [def-pur-co-smoothness]. The defining counit equation for $\theta_{u,P}$, the equality in Step 5, and naturality of $E_u$ give
$$b_{u,v;P}\circ w^*\theta_{u,P}=\theta_{u',v^*P}\circ(1\otimes\beta_{u,v}).$$
Indeed transpose both sides with source $u'^*v^*P\otimes^Lw^*\omega_u$. For the left side, substitute the definition of $b$ and use naturality of $E_u^{-1}$ to put $w^*\theta_{u,P}$ inside $v^*F_u$; the counit equation for $\theta$ then leaves $v^*((\varepsilon_{u,\Lambda_U}\otimes1)\operatorname{PF}_u^{-1})E_u^{-1}$. For the right side, the counit equation for $\theta_{u',v^*P}$ leaves $(\varepsilon_{u',\Lambda_{U'}}\otimes1)(F_{u'}\beta_{u,v}\otimes1)\operatorname{PF}_{u'}^{-1}$. Substituting the counit equation defining $\beta_{u,v}$ makes this $(v^*\varepsilon_{u,\Lambda_U}\otimes1)(E_u(\omega_u)^{-1}\otimes1)\operatorname{PF}_{u'}^{-1}$. These expressions agree by Step 5 with $N=\omega_u$. This proves the equality by injectivity of the adjunction bijection. Consequently, if $P$ is tensor-invertible and $\beta_{u,v}$ is invertible, then $b_{u,v;P}$ is invertible: both tensor maps are invertible by Step 4 and pullback preserves the inverse of $P$. This argument uses only the canonical definitions, not an assertion that $u'$ is cohomologically smooth.

Uses: def-pur-co-smoothness, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-pullback-preserves-bounded-constructible, lem-sf-flat-model.

### Returned Step 8 → lem-pur-exceptional-base-change-pasting

Now take any $t:Z'\to Z$ in the fixed setting, put $Y'=Y\times_ZZ'$, $X'=X\times_ZZ'$, and write $h:Y'\to Y$, $s:X'\to X$, $g':Y'\to Z'$, $f':X'\to Y'$. The vertical maps $f',g'$ remain separated of finite type by [lem-pod-separated-finite-type-base-change]. Clause (3) of [def-pur-co-smoothness] gives isomorphisms $\beta_{g,t}:h^*\omega_g\to\omega_{g'}$ and $\beta_{f,h}:s^*\omega_f\to\omega_{f'}$. Since $\omega_g$ is invertible, Step 7 gives the isomorphism $b_{f,h;\omega_g}:s^*Rf^!\omega_g\to Rf'^!h^*\omega_g$. Hence
$$s^*\omega_{gf}\xrightarrow{s^*c}s^*Rf^!\omega_g\xrightarrow{b_{f,h;\omega_g}}Rf'^!h^*\omega_g\xrightarrow{Rf'^!\beta_{g,t}}Rf'^!\omega_{g'}\xrightarrow{c'^{-1}}\omega_{g'f'}$$
is invertible. It is the specified $\beta_{gf,t}$, as follows by transposing. The transpose of this composite, under the pasted adjunction of Step 1, is
$$Rg'_!Rf'_!s^*Rf^!Rg^!\Lambda_Z\xrightarrow{Rg'_!E_f^{-1}}Rg'_!h^*Rf_!Rf^!Rg^!\Lambda_Z\xrightarrow{E_g^{-1}}t^*Rg_!Rf_!Rf^!Rg^!\Lambda_Z\xrightarrow{t^*Rg_!\varepsilon_f}t^*Rg_!Rg^!\Lambda_Z\xrightarrow{t^*\varepsilon_g}\Lambda_{Z'}.$$
Naturality moves the $f$-counit through $E_g^{-1}$. The vertical-pasting assertion of [thm-cbc-finite-torsion], transported on etale-origin objects by [thm-cbc-finite-level-proetale], identifies the first two arrows with $E_{gf}^{-1}$ under compact-support composition. The last two arrows are $t^*\varepsilon_{gf}$ by Step 1. Thus the transpose is exactly the composite defining $\beta_{gf,t}$; equivalently this is the mate-pasting rule [lem-weil-pbc-mate-pasting]. It is therefore invertible for every $t$, proving clause (3). Together with Steps 2 and 3 this proves cohomological smoothness of $gf$ and the claimed isomorphism.

Uses: def-pur-co-smoothness, thm-cbc-finite-torsion, thm-cbc-finite-level-proetale, lem-weil-pbc-mate-pasting, lem-pod-separated-finite-type-base-change.

## Remaining work

The four new nodes deliberately remain unsplit, as the return requires. Their future proofs can be assigned independently using the complete allocated arguments above. Required server dry run and final direct delivery are performed after this report is written.
