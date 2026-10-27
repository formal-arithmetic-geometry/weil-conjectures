## Worker report

Repair by O2, 2026-10-22, of the batch5 human re-split request for `lem-sfb-transverse-tame-open-shriek-exchange`.

Files written under `dag/nodes/sec-six-functors-basics/`:

- `lem-sfb-transverse-tame-open-shriek-exchange.json`: existing statement kept byte-for-byte; six-step assembly, 2600 proof-text characters, replacing the nine-step proof returned for length.
- `lem-sfb-open-square-closed-unit-triangle.json`: new statement, unsplit, no Mathlib match. Coefficient-linear localization with the actual closed unit, pushed along an open immersion and restricted to a closed boundary.
- `lem-sfb-finite-frontier-strata-derived-detection.json`: new statement, unsplit, no Mathlib match. Finite closed/open induction for a frontier partition, including the finite-family boundary-stratum application.
- `lem-sfb-open-square-support-scalar-counit.json`: new statement, unsplit, no Mathlib match. Open-slice comparison, support criterion, actual open counit, naturality and scalar-restriction square.

All three new nodes have empty `proof` and `proof_deps`, null `proof_origin` and `mathlib_match`, and status `unsplit`. Their statements have respectively 1846, 1807 and 2375 characters. They present three independent formal arguments, of comparable size, without tame/Kummer hypotheses. None asserts the geometric transverse exchange conclusion without an additional vanishing hypothesis. Other workers can start all three without waiting for each other.

Attachments: none. Searching `lean/WeilConjectures/` for the item tag and tame/transverse exchange found no matching completed declaration. `lean/Sheaf/Paper/TransverseTameOpenShriekExchange.lean` has the recorded theorem, but its main proof ends in `sorry` at line 380, as do `openUnit_isIso`, `restrictionComparison_isIso`, `exchange_naturality`, and `exchange_scalar`. These are unfinished material, not an attachment. The upstream binary open/closed detection declarations are not the finite-stratification assertion.

WANTED: a published all-continuous-coefficient proof/reference for the partial Kummer boundary-unit model, in the scope of blueprint direct-image paragraph (3). This is the inherited obligation, not a newly claimed finite-coefficient theorem.

WANTED: an exact published reference for the extracted coefficient-linear closed-unit triangle, finite-stratum detection, and scalar-compatible open-square counit in the ordinary internal condensed-module categories. The new nodes accurately cite the agent-formulated proof obligation and the report supplies the existing-node route and full original argument; the blueprint itself does not print these lemmas.

No item statement error or change was found. No target statement, definition, coefficient category, topology, prime hypothesis, tameness condition, canonical exchange map, or scalar comparison was changed. The imported proof's problem for this repair was its size and concentration of formal work in one node. The current main-20261015 blueprint paragraph (3) supplies only the open-image finiteness route, not the all-continuous tame calculation; it remains explicitly agent-authored work below that route.

The sandbox initially contained only `.brief*` markers, no node, searches or report. I copied the current repository item into it. The required initial dry run exited with the expected missing-report diagnostic. I retained that repository proof in `original-item.json` and reproduce it below. No repository or launcher file was written and no git, Lean, compiler or Lake command was run by me. Packaging and server checks use only the prescribed delivery tool. The item is taken from current main; deliver.py overlays only split-owned fields onto current origin, preserving maintainer metadata.

Unfinished by design: the proofs of the three new statements are future stage-1 tasks. The pre-existing partial Kummer geometric model remains its existing independent node. This repair splits and delivers the assembly; it does not claim to have completed the Lean proof.

## Repair of the return

The return has one numbered obligation in substance: spread the 7658-character proof across at least two statement-only nodes and leave at most 3000 characters in the item, preserving every argument. I created three, not a single replacement for the item. The allocation is:

| Original step | Destination of its argument |
|---|---|
| 1 | Closed-unit triangle task: internal/section-ring equivalence and exact coefficient identifications. |
| 2 | Closed-unit triangle task: actual open counit and the localization triangle on V, with boundedness and quasi-compactness. |
| 3 | Closed-unit triangle task: apply the derived direct image and exact closed restriction, retaining the exact closed-unit map and triangle. |
| 4 | Assembly step 2, using the existing condensed-product-action-inflation and derived-composition-adjunction-normalization nodes. The formal invariants comparison already has these separate tasks, so no duplicate lemma was created. |
| 5 | Assembly step 3, using the existing partial-kummer-boundary-unit-model and cover-restriction-conservative nodes. It retains the whole-stratum cover and the exact arrow comparison. |
| 6 | Finite-frontier-strata-derived-detection task: closed/open filtration and joint reflection. Assembly step 4 applies it and the closed-unit triangle criterion. |
| 7 | Support-scalar-counit task: the actual slice isomorphism, inverse open unit, formula for the adjunct, and the counit support criterion. |
| 8 | Support-scalar-counit task: naturality, coefficient restriction of extension presheaf/sheafification and adjunction maps, sectionwise slice comparison, K-injective normalization, and the explicit scalar square. |
| 9 | Assembly step 6 verbatim: empty parts, empty divisor and rank zero. |

The preservation appendix contains the entire old text and dependencies, so shortening the assembly has not discarded the work instructions. The assertions of the new nodes encode the maps, triangles and compatibility the old arguments establish; they contain no proof steps or disguised sketches.

## Blueprint and existing-node searches

I read the chapter record `sec-six-functors-basics`, the inherited unit record `sk-thm-sf-ctf-stability`, and the current main-20261015 file `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). The inherited unit record has the older sec-six-functors route, whereas the item's source and blueprint provenance give the current additional all-continuous obligation. I preserved both records and the item's statement. `tools/blueprint_refs.py ancestor lem-sfb-transverse-tame-open-shriek-exchange` reports a null ancestor; each child preserves that null and prepends this item to the inherited via list. Exact places identify the extracted original steps. The item's existing non-unspecified `from.place` remains intact.

Whole-DAG searches examined statements, titles and key words for closed-unit triangles, support reconstruction, finite stratification conservativity and scalar/open-counit compatibility. The whole-blueprint command was run with `stratification conservative`, `localization triangle`, `scalar restriction extension zero`, `strata conservative`, `closed unit`, `open square`, `stratum restriction`, `boundary localization`, `exchange counit`, `finite stratification`, `scalar counit`, `open direct image extension zero`, and `closed restriction`. Close hits were opened and distinguished below. The finite-stratum claim has no exact matching node. The binary detection nodes are inputs to its induction, not its conclusion. Project source searches additionally inspected the pro-etale module-object open/closed files and the finite-coefficient recollement module. These do not supply the three exact new assertions as completed declarations.

Each new node has five genuine msearch.py records: LeanSearch, two LeanFinder phrasings, Loogle and Mathlib grep. Their query strings and hit names are preserved exactly in the node and `searches.jsonl`. Services responded. Generic `DerivedCategory.triangleOfSES` and its distinguishedness result concern a supplied short exact sequence of complexes, not the ringed-site coefficient transport and named boundary arrow. I read `Mathlib/Algebra/Homology/DerivedCategory/ShortExact.lean` around lines 32-82. Zariski `Scheme.Modules.restrictAdjunction` and `restrictFunctorComp` concern O_X-modules and the other open adjunction; I read `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` around lines 425-489. Ordinary `ModuleCat` scalar adjunction counits do not supply the open-slice/sheafified-extension comparison. The searches are therefore not exact or one-line Mathlib matches, and no Mathlib leaf is claimed.

## Not duplicates

lem-sfb-finite-frontier-strata-derived-detection vs lem-exc-open-closed-detection: the existing node detects zero module SHEAVES from a single complementary open/closed pair; the new task gives finite-frontier induction for morphisms of arbitrary unbounded derived condensed modules.

lem-sfb-open-square-closed-unit-triangle vs lem-weil-pbc-condensed-open-closed-recollement: the latter gives the localization triangle on one scheme; the new task identifies the triangle after an additional derived open image and closed restriction, with the actual b-counit and h-unit and internal/section-ring coefficient identifications. It has no Kummer or exchange assertion.

lem-sfb-open-square-closed-unit-triangle vs lem-sp-subterminal-derived-image-calculus: the latter gives derived slice direct-image identifications and their maps, not the pushed closed-unit localization triangle. The slice self-counit is one input to the new argument.

lem-sfb-finite-frontier-strata-derived-detection vs lem-sfb-exact-open-closed-unbounded-calculus: the latter gives binary open/closed joint reflection from explicit sheaf recollement assumptions, not the filtration from a finite frontier poset or its finite-family intersection-stratum specialization.

lem-sfb-finite-frontier-strata-derived-detection vs lem-sfb-condensed-support-derived-localization: this is also binary open/closed derived localization; it does not state detection on finitely many locally closed strata.

lem-sfb-finite-frontier-strata-derived-detection vs lem-trf-stratified-product-coherent-conservative: that node concerns a morphism from a coproduct of oriented etale product topoi; our statement concerns ordinary small pro-etale condensed-module restrictions on one scheme.

lem-sfb-finite-frontier-strata-derived-detection vs lem-dl-a1-constructible-fibres-exact: that assertion uses geometric fibres on the constructible adic heart; this one is for arbitrary unbounded complexes of internal condensed modules and uses scheme strata, without ordinary-point conservativity.

lem-sfb-open-square-support-scalar-counit vs lem-sfb-proetale-supported-reconstruction: that node is underived module reconstruction on nested closed/open supports, with no derived open-square slice comparison or coefficient-restriction equation.

lem-sfb-open-square-support-scalar-counit vs lem-sfb-closed-supported-scalar-comparison: that node is a derived scalar-EXTENSION comparison for closed supported objects; this one concerns scalar RESTRICTION, an open-square counit and its slice normalization, without moving extension past Rj_*.

lem-sfb-open-square-support-scalar-counit vs lem-sfb-proetale-open-restriction-counit: that node gives an underived open-restriction/direct-image comparison and compatibility with the direct-image adjunction counit; it does not assert the shriek-adjunct support criterion or its derived scalar-restriction square.

lem-sfb-open-square-support-scalar-counit vs lem-sfb-kinjective-direct-image-open-word-model: that node derives transformations of words in restrictions and direct images. It does not include shriek or the supported open counit; it is the normalization input to that part of the new task.

## Review by O2

I read the item and all sixteen statements cited in its returned proof, including the complete statements of the partial Kummer model, product-action inflation, normalized composition and pro-etale cover conservativity. I checked the repaired item against the statement rather than the old proof's wording: it still uses the all-continuous rings C_E and C_Omega with their norm topologies, ordinary internal modules and tensor, and the stipulated actual adjunct. No SGA source or finite-subextension-valued coefficient substitution enters.

For the three new nodes I read the exact current blueprint source above; it contains no such theorem, so their source places say agent-extracted formal lemma. For the formal route I also opened Stacks `proetale.tex`, Tag 09BM (`lemma-closed-immersion-complement-retrocompact-exact`) and Tag 09AH (`lemma-ses-associated-to-open`), and `sites-modules.tex`, Tag 03DJ (`lemma-extension-by-zero-exact`). The former two explicitly require the retrocompact/quasi-compact complement. In the new tasks every ambient scheme is Noetherian, and its closed subschemes and open subschemes remain Noetherian; hence each complementary open encountered in the induction is quasi-compact. I use these sources through the existing ringed-module and unbounded-calculus statements, rather than pretending the abelian-sheaf source already states an internal-module theorem.

Repaired step 1 uses exactly the new closed-unit triangle statement, with M=L_F and the reduced inner boundary Z. That statement specifies both arrows, not just three cohomology objects. Its future proof is precisely original steps 1-3 below: the internal/section-ring equivalence preserves the underlying sections, pullback from the point identifies coefficient actions via p_{T'}f=p_T, exact inverse image is supplied by the site inverse-image tensor theorem, the slice self-counit removes b^*Rb_*, and the actual localization triangle is carried along Rj_* and i^*. The old exact-derived-functor citation is kept in this task's full preservation record. The target's Y is finite type over a field, so the new Noetherian hypothesis is satisfied; M[0], Rb_*M[0], and Rj_*b_!M[0] are bounded below by the injective-resolution bound. I additionally opened the Mathlib leaf pqf-lem-locnoeth-lft (Stacks Tag 01T6); its statement gives local Noetherianity of Y from the locally finite-type structural map. Spec k satisfies its base hypothesis because a field has only the ideals 0 and 1, and finite type makes Y quasi-compact. I added that explicit citation to step 1 and citations.json after the first successful dry run to avoid leaving the Noetherian-domain inference uncited. This closes the original bounded-below recollement domain issue without assuming bounded constructibility of a direct image.

Repaired step 2 uses the exact inflation and composite-identity clauses of condensed-product-action-inflation, and precisely the normalized K-injective isomorphism clause of derived-composition-adjunction-normalization. The three equivariant module categories are Grothendieck abelian by the former statement; its inflation functors are exact, so all hypotheses of the latter hold. Choosing lambda as the identity composite inflation gives the same conjugate as the invariants identity, hence exactly theta in the Kummer model. No unrecorded analytic acyclicity, Koszul complex or commutation of scalar extension with invariants is used.

Repaired step 3 uses the partial Kummer model's actual pro-etale covering family of the WHOLE stratum and the displayed derived arrow p_T^*theta, not merely its cohomology or geometric stalks. I checked regularity, strict normal crossings, distinct primes, finite E, the norm topology on Omega and the exact stipulated Kummer-triviality hypothesis against its statement. The cover-conservativity node explicitly permits any commutative condensed ring and arbitrary unbounded derived complexes; applied with X=S_J and Lambda=C_F it detects the map on that cover. Functors preserving inverses is the only elementary inference here.

Repaired step 4 uses the finite-family clause of the new stratum-detection statement with I=A_i. To check that clause I wrote out the geometry: S_J lies in every D_a for a in J, so its closure can meet only S_K with K containing J. The union of a collection of indices closed under taking supersets is the finite union of the corresponding intersections D_J, hence is closed. Removing a minimal J from such a collection leaves a collection of the same type; S_J is therefore open in the remaining closed union. Starting with the empty union, binary open/closed joint reflection from the opened ringed-open-closed and exact-unbounded-calculus nodes proves the assertion by finite induction. Empty strata may be discarded. This is the separate filtration argument now assigned to the new task, not an appeal to geometric-point conservativity. Once the closed-unit arrow is an isomorphism, the new triangle criterion supplies i^*B=0, including every inner/outer intersection.

Repaired step 5 takes the exact adjunct formula, the zero-closed-restriction criterion, naturality and the scalar square from the new support-scalar-counit statement. Its independent future proof is original steps 7-8 below. I verified the inputs of those old steps against their statements: the subterminal calculus supplies the cross-slice identification and its actual maps; ringed-open-closed supplies b^*b_! and the extension-presheaf construction; condensed recollement supplies the actual open counit triangle; ring-sheaf-change-adjunction supplies derived direct-image/restriction comparisons and their adjunction normalization; open-restriction-counit supplies the sectionwise fibre-product identity; K-injective-open-word-model supplies its derived normalization and preservation of the finite equality of maps. Forgetting scalars keeps the extension presheaf and sheafification's underlying groups and restriction maps, so its adjunction sends a map to the same restricted map and preserves the unit and counit. Thus rho and epsilon, not arbitrary replacements, commute with scalar restriction. Substituting mu:x -> 1 tensor x gives exactly the equation in the original statement. The scalar equality needs no support-vanishing assumption; the support assumption is used only for invertibility of e. This new lemma has no tame hypothesis and does not itself imply the geometric vanishing.

Repaired step 6 is the original elementary edge-case check. I also tested each new task separately: for b the identity the localization triangle has h empty and the expected zero third term; for b with empty source it is a zero triangle. For an empty partition or empty X, the stratification theorem asserts detection in the zero derived category; for one stratum it is the identity restriction (up to nilpotent reduction, which does not change the pro-etale topos). For a two-piece open/closed partition it reduces to the existing binary detection theorem. For the support criterion, c the identity gives the identity counit; c empty forces B=0 under its hypothesis; the coefficient identity makes the scalar equation ordinary naturality. Rank zero, empty divisor, and either empty boundary part remain admitted in the item.

I checked B1-B10: statement-only new nodes, all objects introduced, notation and coefficient definitions cited, TeX escaped once, accurate agent source attribution rather than a fabricated Stacks theorem, exact logged queries and hit inspection, completed blueprint metadata, and no completed project proof displaced. I checked C1-C8: all six steps cite precisely what they use; every citation has a verbatim statement excerpt in citations.json; the new tasks do not depend on the item or on each other. The normalized-composition and cover-detection citations are declared generic tool uses in split_report; they retain the old unit route. I checked D1-D5: none of the new lemmas restates the unconditional tame exchange or moves its entire proof to one node. The geometry is still assembled from the existing Kummer model and normalized invariants comparison. I checked E1-E7 through the domain checks and small cases just given. No statement dispute needed repair. There is no non-elementary assembly step over 2000 characters.

The change sent back by the return was proof size, not a requested new theorem statement. I corrected that exact issue by exposing the three independent statement-only tasks and retaining the original work below. The item statement and all maintainer fields remain the repository values.

## Original argument preserved for the new workers

The following is verbatim from the current repository proof that was returned for re-splitting. It is work material for the three new tasks, not a proof assigned to their node JSON. Steps 4-5 remain short assembly from existing independent statements; step 9 is retained verbatim in the item.

### Original step 1

Work for one $F\in\{E,\Omega\}$. By [def-weil-pbc-internal-abelian-sheaf-module-equivalence], internal modules may be treated as modules over the section-ring sheaf, leaving underlying sections and maps unchanged. Coefficient identifications for any map $f:T\to T'$ here follow from $p_{T'}f=p_T$ and the definition $C_{F,T}=p_T^*C_F$ in [sk-def-sfb-pulled-back-coefficients, sk-def-sfb-pullback-from-point]. The inverse-image theorem [lem-weil-pbc-left-exact-site-inverse-image-tensor] gives exactness and the monoidal composition comparisons for these site inverse images; after the displayed ring identifications, module inverse image is the same exact sheaf inverse image with its transported action. These identifications use the whole ring $S\mapsto C(S,F)$; in particular they make no identification of $C_\Omega$ with a finite-subextension-valued coefficient ring.

Cited nodes: def-weil-pbc-internal-abelian-sheaf-module-equivalence, sk-def-sfb-pulled-back-coefficients, sk-def-sfb-pullback-from-point, lem-weil-pbc-left-exact-site-inverse-image-tensor

### Original step 2

Let $Z=\bigcup_{a\in A_i}D_a$ with reduced structure, $i:Z\hookrightarrow Y$, $Z_V=Z\cap V$, and $h:Z_V\hookrightarrow V$. Its complementary open in $V$ is $b:W\hookrightarrow V$. Put $K=Rb_*L_F[0]$. The open-slice calculus [lem-sp-subterminal-derived-image-calculus] gives $b^*K\cong L_F[0]$, using the actual counit. Apply the first localization triangle of [lem-weil-pbc-condensed-open-closed-recollement] on $V$ to obtain
$$b_!L_F[0]\longrightarrow K\xrightarrow{\eta_h}h_*h^*K\longrightarrow b_!L_F[0][1].$$
The hypotheses hold: the schemes are Noetherian finite type over a field, so the displayed opens are quasi-compact; $L_F[0]$ and $K$ are bounded below, as a nonnegative injective resolution computes the latter. The ring in the recollement statement is any commutative condensed ring, so includes both $C_E$ and $C_\Omega$.

Cited nodes: lem-sp-subterminal-derived-image-calculus, lem-weil-pbc-condensed-open-closed-recollement

### Original step 3

Apply $Rj_*$ and then exact $i^*$ to this triangle. Exactness of the ambient derived functors follows from [lem-sfb-derived-exchange-exact-normalization] (take the identity base-change square for $j$); exact inverse image is also part of the recollement statement [lem-weil-pbc-condensed-open-closed-recollement]. Set $B=Rj_*b_!L_F[0]$. The resulting distinguished triangle is
$$i^*B\longrightarrow i^*Rj_*K\xrightarrow{i^*u_F}i^*Rj_*h_*h^*K\longrightarrow i^*B[1],$$
where $u_F=Rj_*(\eta_h)$ is precisely the map in [lem-sfb-partial-kummer-boundary-unit-model]. It will suffice to prove $i^*u_F$ invertible.

Cited nodes: lem-sfb-derived-exchange-exact-normalization, lem-weil-pbc-condensed-open-closed-recollement, lem-sfb-partial-kummer-boundary-unit-model

### Original step 4

For any pair of profinite groups $G_o,G_i$, [lem-sfb-condensed-product-action-inflation] supplies three Grothendieck abelian categories $\mathcal A_1(C_F),\mathcal A_{G_o}(C_F),\mathcal A_{G_o\times G_i}(C_F)$ and their specified exact inflation left adjoints. Apply [lem-sfb-derived-composition-adjunction-normalization] to these functors, with the identity identification between their composite and inflation of a trivial $G_o\times G_i$-action. Its conjugate is the natural isomorphism
$$\theta:R\Gamma_{G_o\times G_i}\xrightarrow{\sim}R\Gamma_{G_o}R\Gamma_{G_i}^{G_o}.$$
The theorem's normalization identifies this map on K-injective representatives with the class of the identity $M^{G_o\times G_i}=(M^{G_i})^{G_o}$, so it is exactly the comparison named $\theta$ in the new geometric model. In particular no analytic cochain acyclicity, Koszul calculation, completeness, or commuting of scalar extension with invariants is required here.

Cited nodes: lem-sfb-condensed-product-action-inflation, lem-sfb-derived-composition-adjunction-normalization

### Original step 5

Fix a boundary stratum $S_J$ with $J\cap A_i\ne\varnothing$. Apply [lem-sfb-partial-kummer-boundary-unit-model] to $Y,D,L$ and the given partition. Its hypotheses are exactly the assumed regularity of $Y$, strict normal crossings of $D$, and specified Kummer-triviality of $L$, with the same all-continuous rings. It gives an actual pro-etale cover of the entire $S_J$, on which $u_F|_{S_J}$ is $p_T^*\theta_{M_F}$. Step 4 makes $\theta_{M_F}$ invertible, and a functor preserves inverses, so the covered restrictions are isomorphisms. By [lem-zl-condensed-cover-restriction-conservative], $u_F|_{S_J}$ is an isomorphism in the derived module category of $S_J$. This checks sheaves on whole strata rather than only their ordinary geometric stalks.

Cited nodes: lem-sfb-partial-kummer-boundary-unit-model, lem-zl-condensed-cover-restriction-conservative

### Original step 6

The finitely many strata with $J\cap A_i\ne\varnothing$ partition $Z$. To pass from step 5 to $i^*u_F$, use finite closed/open induction, not a geometric-point conservativity assertion. A finite stratification by these normal-crossing strata admits a filtration by closed unions: order the nonempty strata so that every stratum in the closure of a chosen stratum comes earlier (the closure of $S_J$ can only meet $S_{J'}$ with $J\subseteq J'$). Successively remove an open stratum from the remaining closed union. On each such closed union the open complement is quasi-compact, so [lem-weil-pbc-proetale-ringed-open-closed] and [lem-sfb-exact-open-closed-unbounded-calculus] apply. Their two restriction functors jointly reflect isomorphisms. The restriction to the removed stratum is an isomorphism by step 5, and the restriction to the remaining closed union is an isomorphism by induction, starting with the empty union. Hence $i^*u_F$ is invertible. The triangle in step 3 now has zero first object (equivalently, apply its long exact cohomology sequence), giving $i^*B=0$.

Cited nodes: lem-weil-pbc-proetale-ringed-open-closed, lem-sfb-exact-open-closed-unbounded-calculus

### Original step 7

Apply the open-slice calculus [lem-sp-subterminal-derived-image-calculus] to the two open subobjects $V,Y^\circ$ of $Y$. It identifies $c^*B$ with $Ra_*b^*b_!L_F[0]=Ra_*L_F[0]$; the last identification is the invertible open unit from [lem-weil-pbc-proetale-ringed-open-closed]. Let $\rho:c^*B\xrightarrow{\sim}Ra_*L_F[0]$ be this natural isomorphism. By the adjunction $c_!\dashv c^*$ in [lem-weil-pbc-condensed-open-closed-recollement], the map in the statement is exactly
$$e_F=\varepsilon_{c,B}\circ c_!(\rho^{-1}).$$
The same recollement lemma gives the triangle $c_!c^*B\xrightarrow{\varepsilon_c}B\to i_*i^*B\to$. Since step 6 gives $i^*B=0$, the counit $\varepsilon_{c,B}$ is invertible. Thus $e_F$ is an isomorphism, with precisely the requested normalization.

Cited nodes: lem-sp-subterminal-derived-image-calculus, lem-weil-pbc-proetale-ringed-open-closed, lem-weil-pbc-condensed-open-closed-recollement

### Original step 8

The slice identification $\rho$ is natural in its input, and the counit is natural, so the displayed formula for $e_F$ is natural. For the coefficient map $C_E\to C_\Omega$, [lem-weil-pbc-ring-sheaf-change-adjunction] gives the ordinary derived direct-image and inverse-image scalar-restriction identifications, with their adjunction compatibility. Extension by zero commutes with restriction of scalars: on the extension presheaf it keeps the same groups, restrictions and scalar action, and sheafification gives the same module; this is the sheafified presheaf description in [lem-weil-pbc-proetale-ringed-open-closed]. Its adjunction bijection sends a map to its same restriction, so the resulting identification also preserves the open unit and counit. The slice comparison is the sectionwise fibre-product identity of [lem-sfb-proetale-open-restriction-counit]; restricting scalars leaves it unchanged. On K-injectives this remains the same derived comparison by [lem-sfb-kinjective-direct-image-open-word-model]. Hence, writing $\mu:L_E\to\operatorname{Res}L_\Omega$ for $x\mapsto1\otimes x$ and inserting these identifications, naturality gives the equality
$$\operatorname{Res}(e_\Omega)\circ c_!Ra_*(\mu)=Rj_*b_!(\mu)\circ e_E.$$
No scalar extension has been moved past a direct image.

Cited nodes: lem-weil-pbc-ring-sheaf-change-adjunction, lem-weil-pbc-proetale-ringed-open-closed, lem-sfb-proetale-open-restriction-counit, lem-sfb-kinjective-direct-image-open-word-model

### Original step 9

Step 6 is the stated zero restriction on the union of inner components, including its intersections with outer components. If $A_i=\varnothing$, then $c,b$ are identities and $e_F$ is the identity under the canonical comparisons; if $A_o=\varnothing$, $j,a$ are identities and the map is again the identity on extension by zero. For $D=\varnothing$ both checks coincide. For rank zero all objects and maps are zero. These cases also follow from the same proof (there are no boundary strata when $Z=\varnothing$).

Cited nodes: 
