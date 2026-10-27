# Worker report — Q65 repair

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-constant-extension-weil-heart-equivalence.json`: repaired split, statement unchanged; four assembly steps.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-constant-extension-sheet-heart-coordinates.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-cyclic-return-exact-equivalence.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-constant-extension-return-local-operators.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-constant-extension-pullback-return-residue.json`: statement, unsplit; no Mathlib match.

## Attachments

None. Searched the project library for the blueprint tag, constant-extension, cyclic-return and Frobenius terminology. The main theorem `WeilConjectures.constantExtensionWeilHeartEquivalence` in `lean/Sheaf/Paper/ConstantExtensionWeilHeartEquivalence.lean:523` ends in `sorry` at line 570. The separate cyclic-sheet theorem is also sorried. The WeilConjectures source hits on constant extension concern lisse representations or other theorems, not the full item. No Lean file was written or compiler run.

## WANTED

None.

## What was wrong and what changed

The released repair note requests spreading the work of the nine-step proof among at least two comparable statement-only nodes. The sandbox contained only dispatcher markers, no prior node, report or search log. I copied the live returned item, including its existing statement, metadata, proof and searches; no git command was run in the read clone. The item has the identical statement. Four new nodes carry the four substantive arguments (old-step workloads approximately 1618, 2373, 1706 and 1941 characters, with the coordinate interpretation of old step 3 moved into the first). They have no proof steps, no proof dependencies and no proof sketch in their statements. The parent has a short assembly, below 3000 characters. Existing tool_uses and reviewed metadata are historical and retained; split_report identifies this repair.

The source route is unchanged: Deligne, Weil II (1.1.7)–(1.1.10), printed pp.150–152, especially the paragraph after (1.1.10), combined with the blueprint main-20261015 thm-zl-real-mixed-by-curves proof paragraphs 1 and 5. I read the chapter and unit records and this current blueprint proof. The parent is not the unit's key statement, so no unit record changes.

## Not duplicates

lem-zl-constant-extension-sheet-heart-coordinates vs lem-pur-finite-clopen-derived-decomposition: that existing node assumes a finite clopen covering; the new node constructs the cyclic covering from constants and gives the Frobenius transition coordinates, including the semilinear return. Its generic coefficient equivalence is reused, not re-proved as a new generic node.

lem-zl-constant-extension-sheet-heart-coordinates vs lem-exc-finite-galois-algebra-tensor-decomposition: the existing tensor theorem is algebraic and does not give the Frobenius-sheet coordinate presentation of the constructible Weil heart.

lem-zl-cyclic-return-exact-equivalence vs def-weil-endofunctor-fixed-pair-category: the existing node only defines fixed pairs; the new statement proves the twisted cyclic-return equivalence, the specified natural normalization, and componentwise abelian exactness.

lem-zl-constant-extension-return-local-operators vs lem-trf-point-transport-composition: the existing finite-level identity does not compare the two base-field interpretations of the same sheaf; the new comparison also requires whole-tower realization and common-stage passage.

lem-zl-constant-extension-return-local-operators vs lem-fd-weil-pullback-local-frobenius: the latter concerns a morphism of models over one fixed finite field; the new statement compares different finite base fields on the same model and specified return transports.

lem-zl-constant-extension-pullback-return-residue vs lem-zl-weil-constant-extension-frobenius: that node assumes lissity and includes compact cohomology. The new node supplies the actual pullback-return functor comparison for all constructible sheaves and the residue compositum formula; it does not assert local Frobenius powers.

lem-zl-constant-extension-pullback-return-residue vs def-zl-constant-extension-restriction-local-data: the existing node defines the restriction specification and conjugacy notion, but does not prove the natural pullback-return identity or the residue lcm formula.

Blueprint searches used `blueprint_refs.py ancestor` and searches for cyclic, constant extension, return, sheet, residue degree, fixed pair and base field. Whole-DAG concept searches found no existing cyclic normalization statement or exact constant-extension sheet/local comparison other than the parent being repaired. No new node carries a Stacks tag. The auxiliary gluing source used in the old proof is Stacks 04TS, `sites.tex`, `lemma-mapping-property-glue`; I read it. It gives ordinary gluing data, not the coefficient or cyclic-return enhancements, which were already explicitly separated among existing cited nodes.

## Review by Q65

I read Deligne's actual pp.150–152, not just the blueprint: (1.1.7) fixes geometric Frobenius, (1.1.8) raises it by the residue extension degree, (1.1.10) defines Weil sheaves and the following paragraph explains changing the finite base field via the disjoint geometric union. The four new statements are agent-written elaborations of that route, rather than claims that Deligne states the project's derived coefficient constructions. For the sheet node I also read the old cited statements for Galois tensor splitting, finite-field Frobenius, finite-clopen derived decomposition, exact inverse image under scheme isomorphisms, integral derived pullback, scalar localization and the common-stage coefficient definition. For cyclic normalization the source is the explicit old tuple calculation, now a general abelian-category lemma with all its data and commuting equations stated. For local comparison I read the precise finite transport composition, whole-tower powers/realization, transport naturality and local-Frobenius definition; I kept the requirement to compare whole systems before rationalization. For restriction/residue I read the normalized compositor, finite-field Frobenius and generic constructible local-pullback statements.

Assembly step 1 uses exactly the sheet node's decomposition, return equality, exact heart coordinates and tuple interpretation, and exactly the cyclic node's specified equivalence, inverse, natural partial products and subquotient/filtration correspondence. The hypotheses match: the constructible heart is abelian and P is an additive exact autoequivalence, m is positive, and coordinates need only be scheme isomorphisms, not k-linear maps. Step 2 takes equality up to conjugacy, absolute residue size and weight/filtration preservation from the new return-local-operator statement. Step 3 takes the natural return formula, exact restriction functor and pullback identification from the new restriction/residue statement. Step 4 applies the existing pullback-local-Frobenius statement to g_m: both its source and target are separated finite-type schemes over k_0 because the constants extension is finite. That statement supplies the entire residue-degree power conjugacy, not merely the definition of Frobenius. The new comparison supplies the change of finite-base interpretation, and the new residue statement supplies f and the absolute cardinality. Every uses-entry has its statement copied verbatim in citations.json.

For new statements I tested m=1 (no intermediate arrows, identity return and f=1), an empty scheme (all local assertions vacuous), zero objects and stalks (vacuous purity and empty filtration), a degree d point with d dividing m (f=m/d), m dividing d (f=1), and coprime d,m (f=m). General d,m yields lcm, not dm: for d=m=2 the residue fields have degree 2 over k_0, not degree 4. The generated-field condition prevents a larger residue extension. Nontrivial Jordan blocks are permitted: all comparisons are intertwining maps, never semisimplifications. No lissity was inserted, no fixed-degree m local power was substituted for the residue degree f, and no finite Tor-amplitude assumption was used for the point-transport tower comparison.

I checked delivery-errors B–E in full: each new statement introduces its own objects and definitions, single TeX escaping is used, all new nodes are unsplit with empty proofs, searches are actual logged commands (including the initially invalid Loogle name queries and corrected valid-name searches), no Mathlib result is promoted merely for a related concept, and no argument is moved wholesale into one replacement of the item. The four nodes divide distinct tasks and none states the whole item. The parent does not depend on any descendant of itself. I retained every old argument explicitly below for subsequent workers, instead of deleting detail while shortening the assembly. No assembly step exceeds 2000 characters.

## Argument preservation for future workers

The following is the old proof verbatim, with its destination. It is source material for splitting the new nodes later, not a proof stored in a statement-only node. Existing lemma citations remain visible here for future workers to check rather than being silently dropped.

### Returned step 1 → lem-zl-constant-extension-sheet-heart-coordinates

Put $Y=X_{0,m}\times_{k_0}k$ and $H=\operatorname{id}_{X_{0,m}}\times\operatorname{Spec}(\gamma)$. The extension $k_m/k_0$ is Galois with cyclic Frobenius group of order $m$. Apply the finite Galois tensor decomposition with $E=k_m$, $L=k_0$, and then extend its first factor from $k_m$ to $k$. It gives $k_m\otimes_{k_0}k\simeq\prod_{\sigma:k_m\hookrightarrow k}k$. Base changing $X_0$ therefore decomposes $Y$ into $m$ open-and-closed sheets. Let $j_0:X\to Y$ denote the inclusion corresponding to $k_m\subset k$, and put $h_i=H^i j_0$ for $0\leq i<m$. Frobenius acts transitively on the embeddings, so these are precisely the sheets. Directly on tensor coordinates, $H^m j_0=j_0 g_X^m$. The latter map is geometric Frobenius for the $k_m$-model. The maps $h_i$ are isomorphisms onto their sheets as schemes; for $i>0$ they need not be $k$-linear.

Cited nodes: def-weil-finite-field-fiber, def-weil-frobenius-detailed, lem-sfb-finite-field-galois-frobenius, lem-exc-finite-galois-algebra-tensor-decomposition.

### Returned step 2 → lem-zl-constant-extension-sheet-heart-coordinates

Restriction to the sheets decomposes the bounded constructible categories and their cohomology componentwise, including at $\Qlb$ coefficients, by the finite-clopen decomposition. Pullback by each sheet isomorphism and its inverse is an exact inverse-image equivalence at finite and integral coefficients. Its derived pullback is that inverse image. Rationalization extends these functors and their inverse identities, and the common-stage construction extends them to $\Qlb$. Consequently these identifications preserve the standard heart and its kernels and cokernels. This applies also to the semilinear automorphism $g_X$; write $P=Lg_X^*$ on the heart. Thus $P$ and every $h_i^*$ used below are exact equivalences. No assertion of $k$-linearity of $h_i$ is needed.

Cited nodes: lem-pur-finite-clopen-derived-decomposition, lem-weil-proetale-isomorphism-inverse-image, lem-weil-isomorphism-derived-pullback, lem-pur-semilinear-scalar-localization, def-weil-algebraically-closed-coefficients, def-weil-constructible-heart.

### Returned step 3 → lem-zl-cyclic-return-exact-equivalence

For $(N,\eta)$ in $W_{k_0}(X_{0,m})$, set $A_i=h_i^*N$. The canonical pullback-composition comparisons and step 1 identify its Weil map with arrows $a_i:A_{i+1}\xrightarrow{\sim}A_i$ for $i<m-1$ and $a_{m-1}:P^m A_0\xrightarrow{\sim}A_{m-1}$. Send this tuple to $(A_0,\phi)$, where $\phi=a_0\circ\cdots\circ a_{m-1}:P^m A_0\xrightarrow{\sim}A_0$; on morphisms use the component on sheet zero. This is a $k_m$-Weil sheaf because its geometric Frobenius is $g_X^m$. Conversely, from $(A,\phi)$ form the tuple $A_i=A$, $a_i=\operatorname{id}$ for $i<m-1$, $a_{m-1}=\phi$, and glue it by the inverse of the clopen equivalence in step 2. On the actual sheets these are the successive Frobenius translates of $A$. A morphism $u$ commuting with the return map gives the componentwise morphism $u_i=u$ of these tuples, including the last arrow by $u\phi=\phi'P^m(u)$. This defines the inverse functor explicitly.

Cited nodes: def-weil-weil-sheaf-complex, lem-pod-integral-pullback-composition, lem-pur-semilinear-scalar-localization, lem-pur-finite-clopen-derived-decomposition.

### Returned step 4 → lem-zl-cyclic-return-exact-equivalence

The return functor followed by this construction is the identity on $(A,\phi)$. For an arbitrary cyclic tuple, define $r_0=\operatorname{id}$ and $r_i=a_0\circ\cdots\circ a_{i-1}:A_i\xrightarrow{\sim}A_0$ for $1\leq i<m$. These give an isomorphism from the tuple to the normalized tuple of its return: $r_i a_i=r_{i+1}$ for $i<m-1$, while $r_{m-1}a_{m-1}=\phi P^m(r_0)$. If $u_i$ is a morphism of tuples, its commuting squares imply $r_i' u_i=u_0 r_i$ by induction on $i$, proving naturality. Hence the two functors are quasi-inverse. For $m=1$ there are no intermediate arrows and both functors are the identity.

Cited nodes: def-weil-weil-sheaf-complex.

### Returned step 5 → lem-zl-cyclic-return-exact-equivalence

The underlying constructible hearts are abelian. Because $P$ is exact, kernels and cokernels of commuting Weil morphisms inherit invertible Weil maps: apply $P$ to the kernel (respectively cokernel) universal diagram and use the two original invertible structure maps to identify its universal object. Their universal properties then hold in the category of pairs, since the underlying factorization is unique and the commuting equation follows after composing with the kernel inclusion or cokernel projection. Thus exactness of a Weil sequence is detected on its underlying sheaves. The restriction and normalized inverse above are componentwise exact by step 2, so the equivalence is exact. It carries monomorphisms, their quotients, and finite chains to the corresponding ones; using the inverse gives all subobjects and filtrations in either direction.

Cited nodes: prop-weil-heart-abelian, def-weil-weil-sheaf-complex, def-weil-constructible-heart.

### Returned step 6 → lem-zl-constant-extension-return-local-operators

Let $z$ be a closed point of $X_{0,m}$, and put $r=[\kappa(z):k_m]$. Its residue field is finite and has cardinality $q^{mr}$. For the $k_0$-interpretation the local operator uses $mr$ transitions of $H$; for the $k_m$-interpretation it uses $r$ return transitions of $H^m$. Expanding the latter return maps gives exactly the same $mr$ factors of $\eta$, in the same order. The point transports also agree: finite-level composition identifies the transport for $\gamma^m$ with the block of $m$ transports for $\gamma$; the whole-tower power identity and its specified integral realization give this identity before rationalization, rather than merely after separate reductions. Rationalizing preserves the equality, and naturality and coefficient compatibility give it on the common-stage $\Qlb$ category. Repeating $r$ blocks therefore gives precisely the point transport used in the $k_0$ local operator. On the chosen sheet the two operators are equal under the canonical stalk identification; another choice conjugates this identification. This proves the local-operator assertion in (b), with the same absolute residue size $q^{mr}$ in both interpretations.

Cited nodes: lem-kun-closed-point-field, def-weil-local-frobenius-trace, lem-trf-point-transport-composition, lem-trf-integral-point-transport-tower-powers, lem-pur-semilinear-scalar-localization, lem-weil-frobenius-point-transport-natural, def-weil-algebraically-closed-coefficients.

### Returned step 7 → lem-zl-constant-extension-pullback-return-residue

Define restriction in (a) by $(M,\theta)\mapsto(M,\theta^{[m]})$. Pullback composition identifies $L(g_X^m)^*$ with $P^m$. Multiplying the $m$ pullbacks of the commuting equation for a morphism proves that it commutes with $\theta^{[m]}$, so this is a functor; it is exact because its underlying functor is the identity and exactness is detected there by step 5. Let $\pi:Y\to X$ be the geometric base change of $g_m$. It satisfies $\pi H=g_X\pi$ and $\pi j_0=\operatorname{id}_X$. Hence the restriction of $\pi^*(M,\theta)$ to sheet zero is $M$, and the product of its $m$ Weil transitions is exactly $\theta^{[m]}$, by composing the pullbacks of $\theta$. The equivalence of (b) therefore sends $g_m^*\mathcal F$ to this restriction. Its inverse recovers $g_m^*\mathcal F$ canonically up to the natural isomorphism of step 4; this assertion is made before any direct image.

Cited nodes: def-weil-weil-sheaf-complex, def-weil-frobenius-detailed, lem-pod-integral-pullback-composition, lem-pur-semilinear-scalar-localization.

### Returned step 8 → lem-zl-constant-extension-pullback-return-residue

Apply the constructible Weil pullback/local-Frobenius theorem to the $k_0$-morphism $g_m:X_{0,m}\to X_0$. Its source is separated and of finite type over $k_0$, since $k_m/k_0$ is finite. For $x=g_m(z)$, that theorem gives the compatible-stalk identity $F_{z,g_m^*\mathcal F}=F_x^f$ up to conjugacy, and $q_z=q_x^f$, where $f=[\kappa(z):\kappa(x)]$. Steps 6–7 identify its left side with the local operator of the restriction in (a), proving the required assertion without lissity or semisimplicity.
For the stated formula, write $d=[\kappa(x):k_0]$ and $R=[\kappa(z):k_0]$. The finite field $\kappa(z)$ is the quotient of $\kappa(x)\otimes_{k_0}k_m$ by the prime specifying $z$, and is generated by the images of its two factors. Thus $d\mid R$ and $m\mid R$. Its $q$-power automorphism has order $R$. The power $\operatorname{lcm}(d,m)$ fixes both generating fields, so is the identity; hence $R\mid\operatorname{lcm}(d,m)$. Conversely the two divisibilities imply $\operatorname{lcm}(d,m)\mid R$, giving $R=\operatorname{lcm}(d,m)$. Therefore $f=R/d=m/\gcd(d,m)$.

Cited nodes: lem-fd-weil-pullback-local-frobenius, lem-sfb-finite-field-galois-frobenius.

### Returned step 9 → lem-zl-constant-extension-return-local-operators

For corresponding subquotients under (b), step 6 identifies the local eigenvalues up to conjugacy at every closed point, and leaves $q_z=\#\kappa(z)$ unchanged. Thus the equations $|\iota(\alpha)|=q_z^{w/2}$ agree for every real $w$. Exactness identifies the successive quotients of any finite filtration, so purity of each quotient, its weight and any specified upper weight bound agree. Applying the inverse functor proves the converse. The argument includes zero stalks (whose purity condition is vacuous), zero objects and the empty scheme.

Cited nodes: def-weil-punctual-weights.

The coordinate-identification part of returned step 3 belongs to the sheet node; its return/inverse construction belongs to cyclic normalization. Returned step 8's invocation of the existing general local-pullback theorem remains in parent assembly step 4; its nontrivial finite-field compositum argument is assigned to the restriction/residue node. This is reuse of an existing node rather than creating a duplicate specialized local-power theorem.

## What remains

The four new statement-only nodes are intentionally queued for independent stage-1 workers. Their proofs are not claimed complete. The parent split is complete subject to the required server dry run and independent maintainer review.
