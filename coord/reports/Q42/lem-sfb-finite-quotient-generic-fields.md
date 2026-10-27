# Stage-1 repair report

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-finite-quotient-generic-fields.json` retains its exact statement and statement dependencies and is split into five steps (2745 proof characters). Three new files, all statements, all `unsplit`, no proof steps, no proof dependencies, no Mathlib match:
   - `lem-sfb-closed-orbit-component-map.json`: Closed orbit maps on spaces with disjoint clopen components. Mathlib has ingredients, not the full statement.
   - `lem-sfb-equivariant-component-affine-germs.json`: Equivariant affine component charts and canonical generic germs. Mathlib has ingredients, not the full statement.
   - `lem-sfb-transitive-domain-product-invariants.json`: Stabilizer invariants of transitive domain products and their fraction fields. Mathlib has ingredients, not the full statement.
2. Attachments: none. The live project declaration `AlgebraicGeometry.finiteQuotient_genericFields` at `lean/Sheaf/AlgebraicGeometry/FiniteQuotientGenericFields.lean:138` has `sorry`. Searches of `lean/WeilConjectures/` by the blueprint tag and quotient/generic/component/invariant concepts found no finished declaration stating the item. The existing homogeneous equivariant-functions theorem was read and differs from the new dependent-product statement.
3. WANTED: none. All sources used are available locally. No SGA is used.
4. Fault repaired: the returned eight-step proof was correct but too large for one independently assigned item. The initial sandbox contained only dispatcher markers, not an earlier node/report/search log. I copied the live returned node, retained its metadata and searches, and ran the required initial dry run; it exited because the sandbox lacked report.md and its review section. This repair now distributes the old work without changing the statement, the unit route, or the Lean interface. There is no statement dispute.
5. Unfinished: proofs of the three new lemmas are deliberately left to independently assigned workers, as the human's return requires. No Lean was written and no compiler, Lake, or build tool was run.

## Work distribution and retained arguments

The new topology lemma owns old steps 3 and 4 (1454 characters); its hypotheses are purely topological and it does not assume normality, a scheme structure, or invariant sections. The affine-germ lemma owns old steps 5 and 7 (1849 characters); it assumes the component images and generic-point images and proves the equivariant affine factor model and its canonical germ maps, with no quotient or fixed-field hypothesis. The product-invariants lemma owns old steps 6 and 8 (1501 characters); it is purely algebraic for varying domains and prescribed transition isomorphisms, with no scheme hypotheses. Thus the three arguments are of comparable size, and none states the whole item. Old steps 1 and 2 stay verbatim in the parent. The following text preserves ALL eight old arguments verbatim; it is handoff material in this report, not a proof on the new unsplit nodes.

### Original step 1

Apply [lem-sc-affine-noetherian-underlying-space] to the finitely many affine opens in the Noetherian hypothesis on each of $X,Z$. A descending chain of closed subsets restricts to a stabilizing chain on each such open; the maximum of the finitely many stabilization indices works on their union. Thus both underlying spaces are Noetherian. Apply [lem-trf-normal-topologically-noetherian-components] to obtain finite, disjoint, clopen normal integral components $X_i$ and $Z_j$. The hypotheses on local rings are exactly the normality hypotheses of that node. The empty case has no components and the assertions are vacuous.

Original cited nodes: lem-sc-affine-noetherian-underlying-space, lem-trf-normal-topologically-noetherian-components.

### Original step 2

On an affine open $V=\operatorname{Spec}A$ of $Z$, finiteness [def-weil-finite-integral-morphism] gives $q^{-1}V=\operatorname{Spec}B$. Invariance of $q$ makes this open $H$-stable, and the assumed sheaf equality identifies the actual map $A\to B$ with the inclusion $B^H\subset B$. Apply [lem-a1-affine-groupoid-orbit-fibres] to the constant action groupoid $R=\coprod_{h\in H}\operatorname{Spec}B$: its affine presentation is supplied by [lem-weil-pbc-finite-affine-coproduct-spectrum], source is the identity on each copy, and target is the action automorphism on that copy. Both maps are finite locally free: the source algebra is $\prod_{h\in H}B$, free over $B$ with its standard coordinate basis; the target is conjugate to this source projection by the automorphism $(h,x)\mapsto(h,hx)$. Its invariant ring is exactly $B^H$ . The groupoid identities are the action identities. The cited node therefore says that two points over $V$ have the same image exactly when one is an $H$-translate of the other. Since any common image lies in an affine open, this holds on all of $X$.

Original cited nodes: def-weil-finite-integral-morphism, lem-a1-affine-groupoid-orbit-fibres, lem-weil-pbc-finite-affine-coproduct-spectrum.

### Original step 3

By [lem-weil-pbc-finite-closed-map-finite-fibres], $q$ is closed. The group permutes the components $X_i$, since its maps are homeomorphisms. For a component orbit $O$, put $T_O=\bigcup_{i\in O}X_i$. It and its complement are closed. The point-orbit assertion of Step 2 gives $q^{-1}(q(T_O))=T_O$; surjectivity then gives $Z\setminus q(T_O)=q(X\setminus T_O)$. Hence $q(T_O)$ is clopen. For $i\in O$, invariance gives $q(T_O)=q(X_i)$, an irreducible nonempty subset: if its image lay in a union of two closed subsets, their inverse images would cover $X_i$, forcing one to contain it. Thus $q(T_O)$ is a nonempty irreducible clopen subset. By the disjoint integral component decomposition of $Z$ from Step 1 it is precisely one component $Z_j$. The sets $q(T_O)$ are disjoint by saturation and cover $Z$ by surjectivity, proving the desired component-orbit bijection.

Original cited nodes: lem-weil-pbc-finite-closed-map-finite-fibres.

### Original step 4

Let $\eta_i$ be the generic point of $X_i$, whose existence and uniqueness follow from [lem-sc-scheme-sober]. Continuity gives $q(X_i)=q(\overline{\{\eta_i\}})\subseteq\overline{\{q(\eta_i)\}}$. The reverse inclusion holds because $q(X_i)$ is closed and contains $q(\eta_i)$. By Step 3 this closed image is $Z_j$, so $q(\eta_i)$ is its generic point $\xi_j$. A group element fixes $\eta_i$ exactly when it stabilizes $X_i$: take closures for one implication, and uniqueness of its generic point for the other. Thus the stabilizer of this factor is exactly the group $D$ in the statement.

Original cited nodes: lem-sc-scheme-sober.

### Original step 5

Fix $i$ and $j$ as above and choose a nonempty affine open $V\subset Z_j$. Since $Z_j$ is open in $Z$, this is also an affine open of $Z$. Put $W=q^{-1}V=\operatorname{Spec}B$ and $A=\Gamma(V,\mathcal O_Z)$, using [def-weil-finite-integral-morphism]. Each $W_k=X_k\cap W$, for $k\in O$, is clopen in $W$ and is nonempty because $q(X_k)=Z_j$. There are no other components meeting $W$. By [lem-weil-pbc-spec-clopen-idempotent] it is $D(e_k)$ for an idempotent of $B$, and by [lem-weil-pbc-affine-open-section-vanishing-prime], part (b), it is affine. It is an open subscheme of the integral $X_k$. In fact its coordinate ring $B_k=\Gamma(W_k,\mathcal O_X)$ is a domain by [lem-sc-integral-function-field-affine-fraction], applied to $X_k$. Sheaf gluing on the disjoint open cover $(W_k)_{k\in O}$ gives the actual restriction isomorphism $B\cong\prod_{k\in O}B_k$: a tuple of sections glues uniquely since all intersections are empty. This isomorphism intertwines the $H$-action, which sends the factor $B_k$ to $B_{hk}$ by inverse pullback.

Original cited nodes: def-weil-finite-integral-morphism, lem-weil-pbc-spec-clopen-idempotent, lem-weil-pbc-affine-open-section-vanishing-prime, lem-sc-integral-function-field-affine-fraction.

### Original step 6

Write $h:B_k\to B_{hk}$ for the inverse-pullback action. Projection to factor $i$ identifies $(\prod_{k\in O}B_k)^H$ with $B_i^D$. Explicitly an invariant tuple satisfies $b_{hi}=h(b_i)$, so its $i$th entry is fixed by $D$, and it is determined by that entry. Conversely for $a\in B_i^D$ set $b_{hi}=h(a)$. If $hi=h\prime i$, then $h^{-1}h\prime\in D$, so the entries agree; moreover $b_{ghi}=g(b_{hi})$, proving invariance. The inverse and projection preserve addition, multiplication and $1$ coordinatewise. Combining this with $A=B^H$ from the sheaf hypothesis gives an injective map $A\to B_i$ whose image is exactly $B_i^D$. It is the actual restriction of $q^\sharp$ to $W_i$, not an unspecified isomorphism.

Original cited nodes: none; explicit calculation.

### Original step 7

By [lem-sc-integral-function-field-affine-fraction] applied to the integral components $Z_j,X_i$ and their nonempty affine opens $V,W_i$, the generic stalks are respectively $\operatorname{Frac}A$ and $\operatorname{Frac}B_i$. A field has zero maximal ideal, so [def-weil-residue-field] identifies these stalks with $\kappa(\xi_j)$ and $M=\kappa(\eta_i)$. By [def-weil-open-immersion], restricting to these open components does not change the stalks or residue fields. The map $\kappa(\xi_j)\to M$ is the extension of $A\to B_i$ from Step 6: both send a section to its germ at the indicated generic point, and functoriality of germs makes that square commute. Its extension to fractions is unique because each nonzero denominator becomes a unit. The action of $D$ on $M$ similarly extends its action on $B_i$.

Original cited nodes: lem-sc-integral-function-field-affine-fraction, def-weil-residue-field, def-weil-open-immersion.

### Original step 8

The image of $\operatorname{Frac}A$ in $M=\operatorname{Frac}B_i$ is fixed by $D$, by Step 6. Conversely let $x=b/c\in M$ be fixed by $D$, with $b,c\in B_i$ and $c\ne0$. Set $d=\prod_{g\in D}g(c)$. This lies in $B_i^D$ and is nonzero because $B_i$ is a domain. Also $xd=b\prod_{g\in D,\,g\ne1}g(c)$ belongs to $B_i$, and $g(xd)=g(x)g(d)=xd$ for every $g\in D$. Thus both $d$ and $xd$ belong to $B_i^D$, the image of $A$, so $x=(xd)/d$ lies in the image of $\operatorname{Frac}A$. This proves $\kappa(\xi_j)=M^D$ through the canonical embedding of Step 7. The calculation uses finiteness but never faithfulness, never division by $|D|$, and it was carried out on an arbitrary component orbit; it therefore covers disconnected schemes, nonfree generic actions and arbitrary characteristic.

Original cited nodes: none; explicit calculation.

## Review by Q42

I read the current node, its attached Lean statement/docstring, GOAL.md, the chapter and unit records, and the inherited blueprint provenance. The nearest-blueprint-ancestor command still returns None. I retained that honest null and the inherited route through the alteration and semilinear Sylow arguments, adding the parent to each new node's via list. The item is an auxiliary node, not the unit's key statement, so no unit realization record is changed. Whole-blueprint searches for component quotient, orbit, 03BK, generic field, stabilizer, clopen and 01RV found no statement of the new lemmas.

For the item and algebra lemma I read groupoids.tex Tag 03BK, `lemma-invariants-base-change`, especially part (3) and its kernel-of-the-difference-map proof. This tag is context for the agent's more explicit product/denominator argument, not a falsely claimed verbatim source for our entire assertion. I also read Tag 03BL, `lemma-points`, including its ordinary-point assertion. For the topology lemma I read topology.tex Tag 004V, `definition-irreducible-components`, and Tag 004X, `definition-generic-point`, including the definition of sober. Its proof is the agent's saturated-clopen-union argument retained above, not a hidden appeal to a stronger quotient theorem. For the normal decompositions I read properties.tex Tags 0357 and 033M, `lemma-normal-locally-finite-nr-irreducibles` and `lemma-normal-Noetherian`. For the affine-germ lemma I read schemes.tex Tag 01I3, `lemma-standard-open-affine`, Tag 01HV, `lemma-spec-sheaves` (sections, restrictions and stalks), algebra.tex Tag 00EE, `lemma-disjoint-decomposition`, and morphisms.tex Tag 01RV, `lemma-integral-scheme-rational-functions`. These give the affine pieces and fraction fields; the actual restriction-product and germ-map equivariance calculations retained above are also part of this new lemma's assigned work.

I opened and read the STATEMENT of every node cited by the repaired parent, not just its title or source. Step 1 uses `lem-sc-affine-noetherian-underlying-space`, which gives the Noetherian topology on each affine of the finite cover, and `lem-trf-normal-topologically-noetherian-components`, whose statement explicitly supplies finite disjoint clopen normal integral components under exactly this topological Noetherianity and stalk normality. Stabilization on the finite cover is written out. The trf prefix is only the location of this general Stacks 0357 tool, not a change to the constructibility route.

Step 2 uses the definition of finite morphism for affine inverse images, `lem-weil-pbc-finite-affine-coproduct-spectrum` for the actual constant action groupoid, and `lem-a1-affine-groupoid-orbit-fibres`, whose statement gives equivalence of ordinary-point images with a groupoid arrow. The two structure maps are finite locally free because one is the finite free coproduct projection and the other is its conjugate by (h,x) ↦ (h,hx). The actual sheaf equality gives A=B^H, not an unrelated ring isomorphism. No faithfulness or generically free hypothesis is inserted.

Step 3 uses `lem-weil-pbc-finite-closed-map-finite-fibres` only for closedness, `lem-sc-scheme-sober` for uniqueness and existence of generic points, and the new topology lemma for the orbit/component bijection, generic-point images, and equality of stabilizers. Its hypotheses are precisely Step 1, Step 2, continuity and invariance of q, and the stated surjectivity. Empty X forces empty Z, and then the conclusions are vacuous. No generic-point statement is inferred from finiteness alone.

Step 4 uses the new affine-germ lemma: all its finite disjoint integral decompositions and component/generic-image equalities have been supplied in Steps 1 and 3. Choosing j in the image and a nonempty affine V ensures A and every selected B_i are nonzero domains; unselected components do not meet q^{-1}V. Its conclusion explicitly provides the REAL restriction map, the varying-factor H action, and the compatibility of the canonical residue-field map and stabilizer action with fractions. Thus the parent does not borrow these compatibilities from the proof of a definition or from unspecified naturality.

Step 5 uses the new algebra lemma with the A→B of the actual sheaf hypothesis. Transitivity holds for the selected component orbit by Step 3. The algebra lemma explicitly gives both the image B_i^D and the image of the fraction extension. Step 4 explicitly identifies that extension with the residue map. This covers all clauses of the parent and no comparison is hidden in the assembly. citations.json quotes the full exact statement of each node cited by every step, so each quoted piece is genuinely in that node's statement.

I checked the elementary/non-elementary distinction (C1/C2) and the actual interfaces (C4). The parent's two retained preparatory steps are non-elementary with their original citations, and its final three steps use the extracted statements. The largest parent step is 1083 characters, below the long-step threshold; total proof text is 2745, below 3000. None of the new nodes has a proof or proof dependency. The report's preserved old proofs specify the detailed future work, including clopen affineness, the index-stabilizer evaluation inverse, germ functoriality, and the product of conjugate denominators.

Small cases: the topology lemma allows empty spaces, a trivial H, a permutation of isolated components, and an action with a nontrivial kernel. Its irreducible clopen image must be one component: it lies in one member of the finite clopen decomposition, and that connected component cannot split into the nonempty image and its clopen complement. For the affine-germ lemma, nonempty V in an integral component contains its generic point; surjectivity of each selected component image makes every W_i nonempty, and empty extra components are not indexed. For the algebra lemma, I is explicitly nonempty and every B_i is a nonzero domain; otherwise the fraction-field assertion would fail. For I a singleton it reduces to domain fraction invariance. For two swapped copies it reduces to the diagonal ring; for a trivial or nonfaithful stabilizer it still holds. In characteristic p dividing |H|, d=∏g g(c) is still nonzero in the domain, and no averaging or division by |H| occurs. The equality of fixed fields is unchanged if one uses pullbacks rather than inverse pullbacks, since all elements of D are tested.

I read the Mathlib hits for both phrasings of each new node and the relevant source declarations. `irreducibleComponentsEquivOfIsPreirreducibleFiber` and `image_mem_irreducibleComponents_of_isPreirreducible_fiber` need preirreducible fibres, while finite orbits can be disconnected. `functionField_isFractionRing_of_isAffineOpen` identifies one function field, not the equivariant product and its prescribed maps. `IsFractionRing.isInvariant` at Invariant/Basic.lean:510 is a usable ingredient for the algebra node's fraction clause, but does not establish evaluation of the dependent product. LeanSearch was actually attempted for each and returned a rate-limit error; all three records correctly say unavailable, while LeanFinder, Loogle and grep succeeded. Every new-node query is taken directly from searches.jsonl and records the actual tool/query text, including successful searches with no hits.

I compared the new statements with all source-tag-sharing node statements listed below, and with the existing homogeneous affine-torsor orbit-product statement and its Lean source. The latter uses functions into ONE fixed coefficient algebra and existentially chosen orbit representatives, whereas our product has differing B_i and a prescribed chosen-factor projection and fraction-field image. No existing node covers the new statements by a one-line specialization. Definition nodes and the scalar/localization/component ingredients are reused as prerequisites or left available for future splits, not relabelled as the new conclusions. All definitions needed to read the new statements are either cited or specified inline, and no statement refers to a tag to define its meaning. I checked B–E: complete object introductions, actual sources and labels, ordinary TeX escaping, no cycles through the parent, no changed target/statement, no whole-item transfer, no elementary one-line lemma added merely to inflate the node count, and no off-route geometric theorem used. The split_report declares the retained off-unit tools, and the accepted old top-level tool_uses metadata is preserved.

For the 2026-10-23 repair I compared the retained sandbox with the current repository again: only proof, proof_deps and split_report differ, and original-proof.json is exactly the current live eight-step proof. The released keep_plan repair order still requires at least two independent statement-only nodes and a short assembly. I re-read every parent citation's current statement and verified all ten exact quotes and step/node pairs. The five-step assembly has 2965 characters, with no step above 1083 characters. Its hypotheses still give normal integral components in Step 1, the actual invariant affine ring and finite locally free constant groupoid in Step 2, closedness/sobriety and the component index map in Step 3, nonempty equivariant affine charts and canonical germs in Step 4, and the fixed fraction-field image in Step 5. The empty case and the nonfaithful, swapped-component and positive-characteristic cases remain valid.

I re-opened Stacks 03BK/03BL, 004V/004X, 0357/033M, 01I3/01HV, 00EE and 01RV and read the retained Mathlib search results and their candidate source declarations. No statement or search question changed, so I retained the existing queries and genuine unavailable responses. The mandatory initial dry run for this retry exited with four newly required duplicate comparisons. I read all three distinct existing node statements named by those diagnostics: the polynomial-norm node is shared by two pairs, the prime-separation node supplies functions and norm values at geometric points, and the relation-preparation node supplies an affine comparison and flat equalizer base change. None replaces our topology or varying-domain-product lemma. The four precise distinctions are recorded below. This updates the returned delivery against current DAG additions rather than sending the stale report unchanged. The final delivery command will package the retained mathematical split against freshly fetched server state. No Lean or shared-repository file was written.

## Not duplicates

lem-sfb-closed-orbit-component-map vs lem-a1-affine-groupoid-basechange-polynomial-norm: The existing statement gives base-changed affine groupoids and polynomial norm identities, including equality of norm values on algebraically closed points. It neither assumes arbitrary sober spaces with disjoint clopen components nor gives their component-orbit bijection, generic images, or stabilizer equality.

lem-sfb-closed-orbit-component-map vs lem-a1-affine-groupoid-norm-prime-separation: The existing statement separates two algebraically closed points by a function and its norm using a finite source fibre. It does not identify irreducible components of an arbitrary sober closed orbit map or their generic-point stabilizers.

lem-sfb-transitive-domain-product-invariants vs lem-a1-affine-groupoid-basechange-polynomial-norm: The existing statement controls groupoid norms after arbitrary scalar extension, not evaluation of an invariant dependent product at a prescribed factor. It gives neither the isomorphism to the factor stabilizer ring nor the canonical fraction-extension image.

lem-sfb-transitive-domain-product-invariants vs lem-a1-affine-relation-comparison-preparation: The existing statement starts with an affine finite locally free equivalence relation, constructs its comparison closed immersion and proves flat base change for its equalizer. It does not give chosen-factor evaluation for varying domains or identify its fraction field with stabilizer invariants. A general action with stabilizers need not even define the equivalence-relation monomorphism required there.

lem-sfb-closed-orbit-component-map vs def-sc-generic-point: The existing node concerns Generic point of an irreducible closed subset; it does not state the closed saturated component-orbit bijection together with generic-point/stabilizer compatibility for sober spaces.

lem-sfb-closed-orbit-component-map vs def-weil-irreducible-components: The existing node concerns Irreducible components; it does not state the closed saturated component-orbit bijection together with generic-point/stabilizer compatibility for sober spaces.

lem-sfb-closed-orbit-component-map vs lem-a1-affine-groupoid-orbit-fibres: The existing node concerns Fibres of the affine groupoid invariant spectrum are orbits; it does not state the closed saturated component-orbit bijection together with generic-point/stabilizer compatibility for sober spaces.

lem-sfb-closed-orbit-component-map vs lem-a1-integral-residue-extension-algebraic: The existing node concerns Integral ring maps induce algebraic residue-field extensions; it does not state the closed saturated component-orbit bijection together with generic-point/stabilizer compatibility for sober spaces.

lem-sfb-closed-orbit-component-map vs lem-pc-irreducible-space-connected: The existing node concerns An irreducible space is connected; it does not state the closed saturated component-orbit bijection together with generic-point/stabilizer compatibility for sober spaces.

lem-sfb-closed-orbit-component-map vs lem-per-admissible-quotient-affine-integral-charts: The existing node concerns Invariant affine charts of an admissible finite-group scheme quotient; it does not state the closed saturated component-orbit bijection together with generic-point/stabilizer compatibility for sober spaces.

lem-sfb-closed-orbit-component-map vs lem-sc-components-open-injection: The existing node concerns Components meeting an open subset inject into components of that open subset; it does not state the closed saturated component-orbit bijection together with generic-point/stabilizer compatibility for sober spaces.

lem-sfb-equivariant-component-affine-germs vs def-pc-affine-base-change-tilde-coordinates: The existing node concerns Explicit affine base-change module and target coordinates; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs def-sc-affine-free-basis-germs: The existing node concerns Explicit affine basis germs and their linear combination map; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs def-sc-rational-functions: The existing node concerns The ring of rational functions of a scheme; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-base-change-ordinary-stalk-comparison: The existing node concerns Localization of the ordinary affine tensor comparison; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-base-change-tilde-global-comparison: The existing node concerns Global mate square for explicit affine tensor coordinates; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-base-change-tilde-stalk-comparison: The existing node concerns Stalk localization of explicit affine tensor coordinates; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-derived-cohomology-presentation: The existing node concerns Canonical module localization and exact stalk presentations of affine cohomology; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-free-complex-module-lift: The existing node concerns Affine lifting of a free complex with its supplied unit coefficient; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-localization-sheafification: The existing node concerns Sheafification preserves affine values of localizing module presheaves; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-localized-tensor-stalk-square: The existing node concerns Localized affine derived tensor comparison in germ-normalized chain coordinates; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-localizing-presheaf-basis-sheaf: The existing node concerns A localizing module presheaf satisfies the affine-basis sheaf condition; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-localizing-presheaf-sheafification: The existing node concerns Affine sections of a localizing presheaf survive sheafification; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-opcycles-flat-from-sections: The existing node concerns Transfer flat global-sections opcycles to affine sheaf opcycles; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-ordinary-tensor-stalk-coordinates: The existing node concerns Ordinary tensor target coordinates before the derived stalk presentation; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-perfect-module-model: The existing node concerns Actual K-projective module models on affine opens; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-pullback-chart-tensor-flat-stalks: The existing node concerns Tensor flatness and relative stalk flatness on one pulled-back affine chart; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-pullback-chart-tensor-sections: The existing node concerns Tensor sections of one inverse-image affine chart; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-scalar-localized-tensor-square: The existing node concerns Affine algebraic tensor comparison after scalar extension to the fourth stalk; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-sheaf-resolution-from-ring-model: The existing node concerns Sheafifying an actual finite-free affine ring resolution; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-stalk-scalar-extension-coordinates: The existing node concerns Exact affine stalk homology in scalar-extension coordinates; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-tensor-pullback-stalk-coordinates: The existing node concerns Canonical ordinary pullback cohomology coordinates at a stalk; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-tilde-kflat: The existing node concerns Associated sheaf of a K-flat complex on an affine scheme is K-flat; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-affine-tilde-stalk-tensor-comparison: The existing node concerns Natural tensor comparison for associated-sheaf stalks; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-dimension-affine-open-cover: The existing node concerns The dimension of a scheme is the supremum of the dimensions of the rings of an affine open cover; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-flat-module-tilde: The existing node concerns The associated sheaf of a flat module is tensor-flat; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-intrinsic-flat-module-stalk-tensor-presentation: The existing node concerns Affine quasi-coherent stalks are tensor products of sections with the stalk ring; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pc-localizing-principal-cover-gluing: The existing node concerns Unique gluing for a localizing module presheaf on a principal affine cover; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-pur-coordinate-subspace-generic-stalk: The existing node concerns Ambient fibre stalk at the generic point of a coordinate subspace; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sbc-affine-module-germ-localization: The existing node concerns Quasi-coherent affine module germs are localization maps; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sbc-affine-restriction-source-depth: The existing node concerns Affine localization comparison for the injective restriction source; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sbc-affine-section-associated-stalk: The existing node concerns Unequal affine module sections are detected at an associated stalk; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-basis-dual-matrix: The existing node concerns Affine sheafification preserves transposed dual-basis components; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-chart-scalar-transport: The existing node concerns Affine chart and slice scalar transport; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-finite-free-coefficient-comparisons: The existing node concerns Degreewise finite-free affine Hom comparisons with arbitrary coefficients; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-finite-free-dual-naturality: The existing node concerns Explicit finite basis affine dual comparisons commute with precomposition; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-free-basis-germ-map: The existing node concerns Matrix action on the explicit finite free basis germs; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-free-sheaf-stalk-realization: The existing node concerns Natural finite-coordinate stalk comparison for affine sheafification; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-free-stalk-comparison-bijective: The existing node concerns Bijectivity of finite coordinate combinations of affine basis germs; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-koszul-coefficient-hom-coordinates: The existing node concerns Underived affine Koszul Hom coefficient square; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-koszul-finite-free-resolution: The existing node concerns Sheafification of an augmented affine Koszul complex; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-koszul-hom-coefficient-complex-square: The existing node concerns Affine Koszul Hom coefficient complex square; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-koszul-hom-coefficient-homology-square: The existing node concerns Homology transport of the affine Koszul coefficient square; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-koszul-hom-coordinates: The existing node concerns Homology of the affine Koszul Hom model; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-principal-model-comparison: The existing node concerns Exact associated-sheaf comparison on a principal affine neighbourhood; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-regular-stalk-comparison-bijective: The existing node concerns The regular affine unit germ generates its ambient stalk freely; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-regular-stalk-scalar: The existing node concerns Scalar endomorphisms act on the affine unit germ by their germs; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-affine-scalar-section-action: The existing node concerns Affine scalar endomorphism action on sections over its chart; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-clopen-rank-strata-homology-lift: The existing node concerns Lifting a single-degree map on one clopen rank stratum; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-clopen-rank-stratum-derived-projector: The existing node concerns The retract of a derived module cut out by one rank stratum; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-clopen-rank-stratum-module-projector: The existing node concerns Characteristic rank-stratum idempotent on direct-image-algebra module sheaves; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-finite-free-resolution-sheafification: The existing node concerns Sheafification of an explicit finite free resolution on an affine chart; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-free-sheaf-dual-transpose: The existing node concerns Canonical finite free sheaf duality transposes matrix components; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-integral-function-field-affine-fraction: The existing node concerns Function field of an integral scheme is the fraction field of an affine open; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-integral-scheme-stalks-in-function-field: The existing node concerns Integral schemes: sections and stalks inject into the function field; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-k3-affine-hom-comparison-finite-free: The existing node concerns Finite-basis inverse for a natural Hom comparison; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-k3-affine-hom-comparison-maps: The existing node concerns Natural forward affine Hom comparison, invertible in rank one; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-k4-affine-hom-comparison-left: The existing node concerns Contravariant naturality of the normalized affine Hom comparison; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-k4-affine-hom-comparison-rankone: The existing node concerns Rank-one invertibility of the normalized affine Hom comparison; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-k4-affine-hom-comparison-right: The existing node concerns Covariant naturality of the normalized affine Hom comparison; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-k4-affine-hom-generator-extension: The existing node concerns Unique affine Hom comparison extending global generators; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-rational-functions-generic-stalks: The existing node concerns Rational functions are the product of the generic local rings; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-tilde-preserves-finite-limits: The existing node concerns Finite-limit preservation by affine associated sheafification; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-sc-tilde-scalar-section-action: The existing node concerns Associated sheaf scalar action on all sections; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-affine-ideals-closed-subscheme: The existing node concerns Closed subscheme cut out by ideals on affine opens compatible with principal opens; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-affine-module-basic-open-localization: The existing node concerns Affine basic-open sections of a quasi-coherent module satisfy the two localization conditions; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-affine-open-section-vanishing-prime: The existing node concerns Sections over an affine open: vanishing at a point iff membership in its prime; basic opens are affine with ring the localization; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-affine-open-stalk-localization: The existing node concerns Stalk of a scheme at a point of an affine open: the canonical open immersion and the localization; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-affine-tilde-gamma-adjunction: The existing node concerns On Spec R, M ↦ M~ is left adjoint to global sections, fully faithful, and an equivalence onto quasi-coherent modules; it preserves colimits; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-base-change-nilpotent-thickening-idempotents: The existing node concerns Idempotents lift uniquely along a base change of a nilpotent thickening; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-formal-fibre-transition-idempotents: The existing node concerns Unique one-step lifting of formal-fibre idempotents; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-integral-closure-finite-fibre-choose-g: The existing node concerns A lift of the fibre idempotent gives the localization isomorphism; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-integral-closure-finite-fibre-image-clopen: The existing node concerns The finite fibre component has a clopen image in the integral closure; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-integral-closure-finite-fibre-part-localization: The existing node concerns The part of the fibre over V(I) finite over A/I comes from the integral closure; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-module-pullback-affine-sections: The existing node concerns Sections of the pullback of a quasi-coherent module over an affine open; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-module-pullback-affine-sections-bijective: The existing node concerns Bijectivity of the affine pure-tensor sections map; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-principal-localization-open-immersion: The existing node concerns Spec of a principal localization is an open immersion; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-core: The existing node concerns Normalized sectionwise fixed-chart comparisons; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-generators: The existing node concerns Whole-chart sections generate principal-open sections; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-quasicoherent-epi-affine-cover: The existing node concerns Surjectivity on an affine cover implies a quasi-coherent-target epimorphism; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-scheme-clopen-idempotent: The existing node concerns Open and closed subsets of a scheme correspond to idempotent global functions; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-spec-clopen-idempotent: The existing node concerns Open and closed subsets of Spec R are the D(e) of unique idempotents; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-spec-domain-stalks-function-field: The existing node concerns Stalks and function field of the spectrum of a domain; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-spec-map-global-sections: The existing node concerns Spec of a ring map induces that ring map on global sections; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-spec-map-residue-field-naturality: The existing node concerns Spec of a ring map on points and on residue fields; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-spec-map-stalk-localization: The existing node concerns The stalk maps of Spec of a ring map are the induced maps of localizations; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-spec-module-tilde-sections: The existing node concerns The quasi-coherent sheaf of a module on Spec and its sections over principal opens; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-spec-residue-field-identification: The existing node concerns Residue fields of Spec R and the canonical morphism Spec kappa(p) -> Spec R; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-spec-tilde-free-module: The existing node concerns On Spec R the free module of rank n is the sheaf associated to R^n (Stacks 01HV(1)-(2), 01I7); it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-spec-tilde-stalk-localization: The existing node concerns Stalks of tilde modules are localizations; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs lem-weil-pbc-tilde-principal-localization-transport: The existing node concerns TildePrincipalLocalizationTransport; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs new-affine-double-dual-stalk: The existing node concerns Stalk comparison for the actual affine double dual; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs new-e3-affine-model-stalk-presentation: The existing node concerns Natural affine model presentation over the original local ring; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs new-g3-affine-koszul-signed-dual-coefficient-square: The existing node concerns Affine koszul signed dual coefficient square; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs new-lem-pc-affine-tilde-global-sections-stalk-coordinates: The existing node concerns Global-sections and stalk coordinates for a morphism from an affine tilde module; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs new-p4-self-tor-affine-chart-sections: The existing node concerns Normalized sections of the open pushforward of an associated affine module; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs new-q1-exterior-sheaf-affine-unit-bijective: The existing node concerns The exterior sheafification unit is bijective on affine quasi-coherent sections; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs new-s2-affine-model-stalk-transport-linear: The existing node concerns Coordinate scalar compatibility of explicit affine stalk transport; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs new-s3-koszul-regular-affine-refinement: The existing node concerns A common regular affine refinement around a point of the immersion; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs new-v2-exterior-power-localization: The existing node concerns Exterior powers preserve module localization, characterized on pure wedges; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs stage3-affine-pushout-ring-affine-sections: The existing node concerns Affine sections preserve the structure-algebra ring pushout; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs stage3-affine-pushout-ring-section-comm: The existing node concerns Commutativity of the ring-sheaf pushout section square; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs stage3-affine-pushout-ring-section-delta: The existing node concerns Second leg on sections from the inverse-image unit; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs stage3-affine-pushout-ring-section-map: The existing node concerns Canonical tensor section map for a ring-sheaf pushout; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs stage3-affine-pushout-ring-section-map-injective: The existing node concerns Injectivity of the canonical affine tensor section map; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs stage3-affine-pushout-ring-section-map-tmul: The existing node concerns Pure-tensor formula for the section tensor map; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-equivariant-component-affine-germs vs stage3-affine-pushout-ring-section-products: The existing node concerns Finite product generation of affine ring-sheaf pushout sections; it does not identify the equivariant product of varying integral component section rings and the canonical generic residue-field map and stabilizer action together.

lem-sfb-transitive-domain-product-invariants vs lem-per-torsor-subgroup-quotient-finite-etale: The existing node concerns Quotient of a connected Galois cover by a subgroup; it does not give prescribed-factor evaluation for a transitive dependent product of domains and its induced fraction-field fixed image.

lem-sfb-transitive-domain-product-invariants vs lem-sfb-finite-quotient-generic-fields: The parent is the full normal-scheme quotient theorem, while this node is a purely algebraic intermediate result for an explicit product with specified transition isomorphisms and contains neither scheme components nor a quotient scheme.

lem-sfb-transitive-domain-product-invariants vs lem-sbc-affine-torsor-equivariant-orbit-product: the existing node treats equivariant functions into one common coefficient ring and only existentially indexed orbit representatives; the new node treats varying rings B_i, prescribed evaluation at i, and the canonical image on fractions. It is not an attachment or a one-line specialization of that theorem.

lem-sfb-closed-orbit-component-map vs lem-sbc-affine-torsor-component-image-orbit: the existing node is an explicit label-image criterion for one affine torsor stabilizer component and needs specified splitting/descent data; the new node is about arbitrary sober closed orbit maps and irreducible component images.

lem-sfb-closed-orbit-component-map vs lem-sfb-generic-invariant-field-orbit-open: The existing statement constructs a dense affine quotient chart for a morphism of integral finite-type schemes with a purely inseparable invariant function-field extension. It gives neither the sober-space component-orbit bijection for disconnected spaces nor the generic-point and component stabilizer comparison.

lem-sfb-equivariant-component-affine-germs vs lem-sfb-normal-generic-chart-clopens: The existing statement treats weakly etale pro-etale charts over one normal integral base and compares their idempotents with the generic fibre. It does not decompose a finite morphism between disjoint integral components equivariantly or identify its actual generic residue-field maps with component fraction extensions.

lem-sfb-transitive-domain-product-invariants vs lem-sfb-sylow-generic-prime-to-ell-lift: The existing statement is a geometric existence theorem selecting a generic point with prime-to-ell residue degree for two group quotients and a universal-homeomorphism hypothesis. It provides no prescribed-factor isomorphism for a varying product of domains and no canonical fraction extension for an arbitrary invariant-ring map.

## Validation

The initial dry run exited for missing report/review. The first repaired preflight required a cited notion in the purely algebraic statement. I read def-pc-field-extension, whose statement defines exactly the fraction-field extension used here, added that reference and statement dependency, and regenerated its citation quote. The other basic ring and action notions remain explicitly defined inline. Required final dry run and push results will be recorded after the checks complete. All writes are confined to this item sandbox.


## Repair of the returned side completion (2026-10-22)

The current return says the reader approved the split but the landing did not promote its side completion into the live DAG. I retained the previous three statement-only nodes, all original arguments, all searches and their results, and the existing review. The mandatory initial dry run finished with three duplicate-tag diagnostics caused by current DAG additions; it did not report a mathematical failure. I opened all three named existing nodes and compared their complete statements; the distinctions are now recorded above. In particular none supplies a replacement for our topology, affine-germ, or dependent-product lemma.

I compared the sandbox parent with the current repository parent field by field. The statement, statement dependencies, source, blueprint provenance, Lean interface and maintainer review metadata agree. The live parent still has the old eight-step proof; the sandbox has the retained three-part extraction with a short five-step assembly. The released stage-1 keep_plan repair order remains present and explicitly requires this extraction, so the older live passing review does not cancel it. Packaging through deliver.py overlays only the split-owned fields onto freshly fetched origin/sheaf-dag, preserving its latest metadata; no repository file or git state was changed by this worker.

I re-read all seven external parent proof dependencies and the finite-morphism definition, along with all three new statements. Every citation quote remains a verbatim part of the current statement, so no changed interface requires replacing a dependency. Step 1 still gets finite disjoint integral components from exactly topological Noetherianity and normal stalks. Step 2 still gets ordinary point-orbit fibres from the actual invariant ring, via the finite free constant groupoid. Step 3 still has closedness and sobriety; I now explicitly define the index map phi by q(X_i)=Z_phi(i). Step 4 now explicitly sets O=phi^{-1}(j), checks it is a nonempty orbit, and records phi(hi)=phi(i), so every hypothesis of the affine-germ statement is visible. Step 5 applies the product statement to the actual section map and the canonical fraction maps. These are substantive assembly clarifications in addition to the rebase and new duplicate comparisons; the returned content is not being pushed unchanged.

The new statements are unchanged, so their recorded searches remain the relevant ones. I read searches.jsonl, including the two phrasings and the unavailable LeanSearch responses, and re-read the cited Mathlib fraction-invariance theorem. The full product conclusion still requires varying-factor evaluation beyond that theorem. The small-case checks in the signed review above remain valid: empty schemes, trivial or nonfaithful actions, swapped components, nonempty affine charts, and characteristic dividing the group order. I re-opened the Stacks sources 03BK/03BL, 004V/004X, 0357/033M, 01I3/01HV, 00EE and 01RV for this repair. No SGA source or compiler was used.


## Final rebase verification by Q42

The mandatory initial dry run in this repair completed successfully: OK (not pushed), commit b7d1d6cbd48. I compared the complete current parent with the sandbox: only proof, proof_deps and split_report differ; all live statement, source, provenance, Lean and maintainer-review fields are preserved. I re-read the ten quoted dependency statements and verified all ten citations.json quotes against their current text. The three new lemmas still have no proof steps or proof dependencies and remain unsplit. Their recorded Mathlib searches were read and retained, including the actual unavailable LeanSearch results.

I checked the Stacks text at 03BK/03BL, 004V/004X, 0357/033M, 01I3/01HV, 00EE and 01RV, and the Mathlib candidate declarations for component equivalences, affine function fields and fraction invariance. The final assembly now explicitly explains that inverse pullback and pullback have identical fixed elements, since inversion permutes the stabilizer. This matches the canonical residue-map action in the live Lean interface without changing the statement or any new lemma. The current five-step proof has 2965 characters (largest step 1083); earlier character counts in the retained review describe its earlier revision. The final dry run and push below package this repaired content onto the current server DAG; no git command was run in the shared repository.

## Current retry validation (2026-10-23)

The initial dry run exited normally with the four duplicate comparisons above. Those diagnostics have been repaired after reading the complete existing statements. Earlier validation entries describe prior attempts; the current final dry run and delivery are performed after this report update.
