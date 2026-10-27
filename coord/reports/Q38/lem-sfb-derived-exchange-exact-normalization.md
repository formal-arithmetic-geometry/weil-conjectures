# Worker report: lem-sfb-derived-exchange-exact-normalization

1. Files written:
   - dag/nodes/sec-six-functors-basics/lem-sfb-derived-exchange-exact-normalization.json: statement unchanged; short five-step assembly, 2319 characters, status split.
   - dag/nodes/sec-six-functors-basics/lem-sfb-module-derived-functor-compositor-shifts.json: statement; unsplit, no whole-statement Mathlib match.
   - dag/nodes/sec-six-functors-basics/lem-sfb-kflat-derived-adjunction-transport-shifts.json: statement; unsplit, no whole-statement Mathlib match.
   - citations.json: one verbatim statement quote for each node cited in each assembly step.
2. Attachments: none. The item tag does not occur in WeilConjectures. The existing Sheaf.Paper.DerivedExchangeExactNormalization theorems contain sorry. The module-object UpperLowerStar definitions provide the functors, compositor and derived adjunction, not the full assertion. Finite-coefficient and bounded-below etale results do not state the arbitrary-condensed-ring item.
3. WANTED: none; all sources are present locally.
4. Repair of return: the sole numbered substance of the handoff was to distribute the 6880-character proof, add at least two comparable independent tasks, and leave at most 3000 assembly characters. Old steps 1 and 3 now have the first node as their interface; old step 2 has the second. The remaining typed mate, shift-composition, connecting-square and full-subcategory computations are the short assembly. Neither new statement is the exchange theorem or asserts its counit/triangle/restriction conclusion. The extracted work is 2403 and 1651 characters of the reviewed proof, respectively; the statements have no proof sketch or steps. The full seven original steps are retained below, including the maintainer's previous correction to the derived-adjunction transport. No argument is erased by the shorter assembly.
5. Unfinished work: precisely the proofs of the two new unsplit lemmas, assigned to future workers. They depend only on existing notions and can be worked on independently. No Lean was written and no compiler, Lake or local preflight was run.

## Base, retained work and statement history

At startup the sandbox contained only launcher brief markers: no node, report or search log. The current read clone contains the reviewed split and its Lean statement, and coord/returns/Q38.md names returned head e2a95534abdca96856ae1c3b80c5b78fb624dc06. I read that return and the current node, preserving all metadata and all existing searches. The full current node is retained in research/returned-node.json. The prior Q32 report is retained verbatim in research/prior-report-Q32.md and appended below. Thus its mathematical argument, citations, search account and statement-dispute history survive even though this sandbox had no older files. No repository git command was run.

There is no new STATEMENT-DISPUTED correction in Q38. The previously reviewed correction about full triangulated bounded-constructible subcategories remains literally unchanged. Its square-zero-ring counterexample and the reason the rational application is unaffected are preserved in the prior report below. This repair does not remove that hypothesis.

## Sources and allocation of the original arguments

The chapter sec-six-functors-basics and unit sk-thm-sfb-proper-base-change, including the finite/integral/rational route, were read. The current blueprint source is main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.proof.md, paragraph (3), specifically “all functors are exact and the maps are natural transformations of exact functors”. The two new statements make the canonical normalization behind that sentence explicit. Their nearest blueprint ancestor is det-thm-sfb-proper-base-change-rational, through the present item; neither is an existing blueprint statement. The unit and chapter files are not changed.

For the first new node I read Stacks derived.tex Tag 015F, label lemma-right-derived-exact-functor, including the quasi-isomorphism argument; Tag 014X, lemma-additive-exact-homotopy-category, including the split-triangle proof; and Tag 05SE, proposition-derived-functor, including descent of exactness. These give the termwise and derived functor facts, not the entire specified module compositor assertion. I also read the actual UpperLowerStar.lean definitions: leftDerivedUpperStarIsoMapDerivedCategory, leftDerivedUpperStarComp, and the ordinary derived functor specifications. The complete specialized proof material is old steps 1 and 3 reproduced below. In particular it retains the comparison on a resolution arrow, the degree-r component b at M^(r+n), the common (-1)^n differential sign, passage through localization, inversion of the shift square, and insertion of the commutative-square equality. Its node is deliberately statement-only, not falsely attributed verbatim to Stacks.

For the second new node I read Stacks Tag 0DVC, label lemma-pre-derived-adjoint-functors, and its general canonical Hom-adjunction proof immediately above; I read Mathlib CategoryTheory/Functor/Derived/Adjunction.lean at the derived counit factorization (derivedε_fac_app, line 125). I read the statements of lem-sp-canonical-right-derived-adjunction-shift and lem-sc-derived-adjunction-from-underived, and the published module derived adjunction definition (UpperLowerStar.lean). The remaining specialized task is exactly old step 2 below: compare both left-derived presentations with the same beta; cancel beta on K-injectives; extend equality of counits to all objects by resolutions; identify the actual adjunction as transport; conclude the unit/counit fixed-shift equations. The new statement specifies both transport formulas, so it is stronger than merely choosing a shift structure on a right adjoint.

## Searches and existing interfaces

For both new nodes I ran leanfinder, loogle, grep and leansearch using only the authorized msearch.py command, followed by a second semantic phrasing and a more focused grep. All queries and full returned hits are recorded exactly in mathlib_searches, searches.jsonl and research/*-*.txt. No service was down. The Loogle exact-functor hits and ExactFunctor.lean supply mapDerivedCategory, its shift-compatible factorization and general maps, but they do not identify the specified K-flat module functor/compositor with those maps. The adjunction hits give derived, derived_counit and derivedε_fac_app; these provide part of the second task, not its identification of two derived presentations and the fixed-shift conclusion. The hit commShift_of_leftAdjoint equips a right adjoint with an adjoint-induced shift; identifying that with the existing K-injective shift remains work. Neither new node is a Mathlib leaf or a one-line specialization of these hits. The grep command's file-root output drops filenames for an individual file; its exact returned output is preserved, and I read the actual known source paths instead of inventing line records.

Whole-DAG searches included the tags 015F, 014X, 05SE, 0DVC and the concepts canonical shifts, K-flat adjunction, derived module compositor and derived-adjunction transport. Whole-blueprint searches used blueprint_refs.py for derived adjunction, pullback composition, canonical shift, derived pullback, K-flat adjunction and pullback compositor. I opened the closest existing statements: def-sfb-left-derived-exact; prop-sfb-module-left-derived-upper-star-comp; lem-sfb-exact-derived-natural-iso; lem-sfb-exact-derived-composition; lem-sp-canonical-right-derived-adjunction-shift; lem-sc-derived-adjunction-from-underived; lem-sfb-resolving-derived-adjunction-normalization; lem-sfb-derived-composition-adjunction-normalization; lem-weil-pbc-derived-adjunction-shift; lem-weil-pbc-exact-square-derived-counit; lem-weil-pbc-derived-square-shift-on-kinjectives; def-pur-ringed-module-derived-operations; lem-pur-sequence-adjoint-resolution-shifts; lem-sfb-identity-open-derived-adjunction-normalization; and lem-sp-exact-derived-transformation-pasting. None states the new module-specific normalization. The generic ones remain available to the future workers; they are not silently replaced by invented versions.

## Review by Q38

I checked B--E against the node files and the sources open. The parent statement is byte-for-byte the current reviewed statement. Both children introduce their condensed ring, coefficient sheaves, module-object derived categories, scheme arrows, resolution conventions and canonical comparisons. They have status unsplit, empty proof and proof_deps, null proof_origin and mathlib_match, real source places with Stacks tags, three distinct available search kinds (indeed four), the correct unit/chapter and blueprint.from via this item, and no Lean claim. Every formula lives in the unbounded derived category; the degreewise representative clause in the first child normalizes that derived isomorphism and is not offered as a substitute for it.

Assembly step 1 uses the first child's exactness and theta shift equation, and the second child's conclusion for the actual units/counits with fixed shifts. I checked these clauses in their statements, not an intended proof. lem-weil-pbc-triangulated-functor-composite explicitly gives exactness with the composite shift. The ordinary unbounded module categories and arbitrary commutative condensed coefficients are the same in all three statements; neither cartesianness nor finite coefficients nor a constructibility-preservation theorem is introduced.

Assembly step 2 uses the actual adjunction supplied by sk-def-sfb-module-derived-pushpull. I checked types: A is on Y', C and FA on X', and a:FA→C; B_K=H(a)η'_A. Naturality is ε'_C FH(a)=a ε'_(FA), then the triangle identity ε'_(FA)Fη'_A=1 cancels. This is precisely the stated counit normalization and is elementary; no new lemma is hidden.

Assembly step 3 applies the actual clauses (i)--(iv) of lem-weil-pbc-commshift-nattrans-comp-whisker to the three specified factors, at each fixed integer n. The two new children supply the input compatibilities. Naturality is composition/whiskering of natural transformations. The canonical composite comparison is χ, not an arbitrary new choice.

Assembly step 4 uses only the definition of a triangle morphism in def-weil-triangulated-category and earlier steps. I checked the connecting arrow has type M→K[1], and both image arrows are χ¹ composed with the image of w. The displayed first equality is naturality, the second is the n=1 shift equation. The first two squares are ordinary naturality; exactness from step 1 ensures distinguished image triangles. This small calculation preserves the full connecting-square argument.

Assembly step 5 uses the full three-factor formula in det-def-sfb-base-change-morphism-bc, the inherited shifts and triangles in def-weil-triangulated-subcategory, and the explicit assertion of ambient morphisms/identities/composition in sk-def-sfb-bounded-constructible. I verified preservation of all four pullbacks and both pushforwards is assumed before restricting: each intermediate object therefore lies in the right category. Restricted adjunctions and comparators must be the actual ambient restrictions, as the parent assumes. Their arrows are literally the same three components; full-subcategory composition gives the same B. The parent’s triangulatedness condition is retained, including for Dbc. No proof of constructible preservation for arbitrary coefficients is being smuggled in.

For the extracted first task, exactness of module pullback comes from det-prop-sfb-module-pullback-exact-main, and additivity of pushforward from def-sfb-module-lower-star, both read. def-sfb-left-derived-exact and lem-weil-pbc-exact-functor-derived-factorization say the needed comparison and its fixed shift normalization. The two existing exact-derived isomorphism/composition statements specify the termwise normalization. lem-pc-right-derived-functor-triangulated assumes K-injective resolutions and additivity, available in the cited ambient construction. These are the inputs the retained old argument calls on, not claims that every underived right adjoint is exact.

For the second task, lem-sp-canonical-right-derived-adjunction-shift is about D(u*)⊣G, while def-sfb-module-derived-pushpull-adjunction specifies P⊣G. I preserved this distinction, the same beta, the equation alpha^A(cQ)=alpha^P and both resulting transport equations. In particular the earlier maintainer's counit comparison on K-injectives is not deleted. lem-sc-derived-adjunction-from-underived supplies its normalization, not the shift assertion; the former shift lemma supplies that separate assertion after the transport is identified. No requirement that u_* preserve K-injectives is used.

Small cases checked: identity arrows and the identity square make the comparison and mate cancel by the unit/counit laws; zero coefficients/zero objects give zero-module categories with the same equations; shifts n=0,1,-1 retain the common differential sign in the first child and transported units/counits in the second. A commutative square which is not cartesian is allowed throughout: nothing asserts B is an isomorphism. For full subcategories, preserving objects alone is insufficient if their adjunctions are replaced by arbitrary ones, so the restriction hypothesis is essential and present. For arbitrary noncoherent coefficients, bounded constructibility need not be triangulated; the prior counterexample and explicit conditional hypothesis remain.

There is no new cycle: neither child cites the item (created.item and blueprint.from.via are provenance, not dependency edges); the two children have no dependence on one another. Each is strictly below the exchange assertion: the first covers termwise/compositor normalization, the second adjunction-presentation normalization. These are not new names for the whole exchange lemma or for a mathematical application in another unit. The explicit re-split instruction authorizes exposing these previously inline subarguments. The retained elementary mate and connecting-square calculations make the parent's assembly an actual argument. All five assembly steps are below 2000 characters. The existing generic tool declarations are retained as history; the active new citations are within the same unit. No SGA source is used.

## Retained original seven-step argument

The following is the complete current reviewed proof, unabridged, to give the next workers the exact arguments distributed into the child interfaces and the assembly. Steps 1 and 3 belong to the first child; step 2 belongs to the second; steps 4--7 are retained in the assembly.

### Original step 1

For each arrow $u$, the module-object pullback is exact and additive by [det-prop-sfb-module-pullback-exact-main]. By [sk-def-sfb-module-derived-pushpull] these are ordinary unbounded total derived functors, computed on K-flat and K-injective resolutions; in particular the ambient module categories have the required resolutions. Apply [def-sfb-left-derived-exact] to identify $P_u$ with the termwise derived pullback $D(u^*)$. The comparison respects the canonical shifts: on a resolution $J\to M$, it is induced by $u^*J\to u^*M$, and on the shifted resolution it is the shift of this map, since exactness sends both resolution arrows to quasi-isomorphisms. Thus [lem-weil-pbc-exact-functor-derived-factorization] gives the exactness and fixed integer-shift structure of $P_u$. The underived pushforward is additive by [def-sfb-module-lower-star]. Apply [lem-pc-right-derived-functor-triangulated] to it to get the exactness of $G_u$ with its canonical K-injective shift. The two composites $\Phi=P_gG_p$ and $\Psi=G_{p'}P_{g'}$ are exact with composite shift comparisons by [lem-weil-pbc-triangulated-functor-composite].

Uses: det-prop-sfb-module-pullback-exact-main, sk-def-sfb-module-derived-pushpull, def-sfb-left-derived-exact, lem-weil-pbc-exact-functor-derived-factorization, def-sfb-module-lower-star, lem-pc-right-derived-functor-triangulated, lem-weil-pbc-triangulated-functor-composite

Source: literature/stacks-project/derived.tex; Tags 015F (lemma-right-derived-exact-functor), 014X (lemma-additive-exact-homotopy-category), 05SE (proposition-derived-functor); exact module pullback from the cited blueprint node

### Original step 2

The underived adjunction is precisely that of [def-sfb-module-upper-lower-adjunction], and its canonical derived adjunction is [def-sfb-module-derived-pushpull-adjunction]. Apply [lem-sp-canonical-right-derived-adjunction-shift] with $L=u^*$ and $R=u_*$, using the exactness and the resolution hypotheses checked in step 1. It states compatibility with the fixed canonical shifts, so the unit $\eta_u$ and counit $\varepsilon_u$ commute with every integer shift. This lemma concerns $D(u^*)\dashv G_u$; the specified adjunction is $P_u\dashv G_u$, with $P_u$ computed on K-flat resolutions. Let $c:P_u\cong D(u^*)$ be the canonical isomorphism of step 1. It is the comparison of left derived functors, so $\alpha^D\circ cQ=\alpha^P$ for their comparisons $\alpha^P:P_uQ\to Q\,C(u^*)$ and $\alpha^D:D(u^*)Q\to Q\,C(u^*)$. Both adjunctions are derived adjunctions of $u^*\dashv u_*$ with the same $G_u$ and K-injective comparison $\beta$. By [lem-sc-derived-adjunction-from-underived] their counits satisfy $\varepsilon'_{QJ}\circ P'(\beta_J)=Q(\varepsilon_J)\circ\alpha'_{u_*J}$ for $(P',\alpha')=(P_u,\alpha^P),(D(u^*),\alpha^D)$. For K-injective $J$, $\beta_J$ is invertible. Naturality of $c$ then gives $\varepsilon^P_{QJ}=\varepsilon^D_{QJ}\circ c_{G_uQJ}$. Every object is isomorphic to such a $QJ$, so $\varepsilon^P=\varepsilon^D\circ cG_u$. Thus the specified adjunction is the transport of $D(u^*)\dashv G_u$ along $c$, not a newly chosen adjunction on isomorphic functors. Its unit and counit are composites of those of $D(u^*)\dashv G_u$ with $c^{\pm1}$, which is shift-compatible by step 1. They therefore commute with every integer shift.

Uses: def-sfb-module-upper-lower-adjunction, def-sfb-module-derived-pushpull-adjunction, lem-sp-canonical-right-derived-adjunction-shift, lem-sc-derived-adjunction-from-underived

Source: literature/stacks-project/derived.tex; Tag 0DVC (lemma-pre-derived-adjoint-functors); fixed canonical right-derived shift compatibility in the cited general lemma

### Original step 3

The composition comparison of ambient pullbacks is the one induced by the underived comparison, by [prop-sfb-module-left-derived-upper-star-comp]. To check its shifts, use the exact termwise descriptions from step 1. Write $b:(vu)^*\cong u^*v^*$ for the underived comparison. By [lem-sfb-exact-derived-natural-iso] and [lem-sfb-exact-derived-composition], its derived comparison is represented on every complex $M$ by the degreewise map $b_{M^r}$ followed by the termwise composition identification. For $M[n]$ the degree-$r$ component is $b_{M^{r+n}}$, exactly the degree-$r$ component of the shifted comparison; both differentials are multiplied by $(-1)^n$. The localization factorizations in [lem-weil-pbc-exact-functor-derived-factorization] respect these shifts. Every derived object is represented by a complex, so this proves the shift square for the canonical composition comparison for all $n\in\mathbf Z$. The same equation for its inverse follows by multiplying the square by inverse isomorphisms. The comparison $\theta$ is the inverse compositor for $(p',g)$ followed by the compositor for $(g',p)$, with the equality $gp'=pg'$ in between. The equality inserts identical termwise functors, hence respects shifts. Therefore $\theta$ commutes with all integer shifts.

Uses: prop-sfb-module-left-derived-upper-star-comp, lem-sfb-exact-derived-natural-iso, lem-sfb-exact-derived-composition, lem-weil-pbc-exact-functor-derived-factorization

Source: literature/stacks-project/derived.tex; Tags 015F (lemma-right-derived-exact-functor) and 014X (lemma-additive-exact-homotopy-category); degreewise shift check for the exact composition and natural-isomorphism factorizations

### Original step 4

Fix $K$. Put $A=P_gG_pK$, $C=P_{g'}K$, $F=P_{p'}$, $H=G_{p'}$, and $a=P_{g'}(\varepsilon_{p,K})\circ\theta_{G_pK}:FA\to C$. The definition gives $B_K=H(a)\circ\eta'_{A}$. Naturality of the counit of $F\dashv H$ gives $\varepsilon'_{C}\circ FH(a)=a\circ\varepsilon'_{FA}$. Consequently
$$\varepsilon'_C\circ F(B_K)=a\circ\varepsilon'_{FA}\circ F(\eta'_A)=a,$$
where the last equality is the adjunction triangle identity. This is exactly the asserted counit equation. Only the adjunction laws of [sk-def-sfb-module-derived-pushpull] are used; cartesianness plays no role.

Uses: sk-def-sfb-module-derived-pushpull

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.proof.md; paragraph (3): canonical exchange; explicit unit--counit cancellation

### Original step 5

Let $\chi_\Phi^n(K):\Phi(K[n])\to\Phi(K)[n]$ and $\chi_\Psi^n(K):\Psi(K[n])\to\Psi(K)[n]$ be the composite comparisons. The three transformations making up $B$ are the unit for $p'$ whiskered by $P_gG_p$, the comparison $\theta$ whiskered by $G_{p'}$ and $G_p$, and the counit for $p$ whiskered by $G_{p'}P_{g'}$. Steps 2 and 3 make each factor shift-compatible. Apply the composition and whiskering rules of [lem-weil-pbc-commshift-nattrans-comp-whisker], for each shift $[n]$, to obtain
$$\chi_\Psi^n(K)\circ B_{K[n]}=B_K[n]\circ\chi_\Phi^n(K).$$
Here $B$ is a natural transformation because it is a composite of whiskered natural transformations.

Uses: lem-weil-pbc-commshift-nattrans-comp-whisker

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.proof.md; paragraph (3): the canonical exchange is a natural transformation of exact functors; fixed shifts checked in steps 2--3

### Original step 6

For a distinguished triangle $K\xrightarrow{u}L\xrightarrow{v}M\xrightarrow{w}K[1]$, the image triangles under $\Phi$ and $\Psi$ are distinguished by step 1. Naturality of $B$ gives the squares for $u$ and $v$. For the last square, naturality at $w$ and step 5 give
$$\chi_\Psi^1(K)\circ\Psi(w)\circ B_M
=\chi_\Psi^1(K)\circ B_{K[1]}\circ\Phi(w)
=B_K[1]\circ\chi_\Phi^1(K)\circ\Phi(w).$$
Thus $(B_K,B_L,B_M)$ is a morphism of the two image triangles, including their connecting arrows, by the definition of a triangle morphism in [def-weil-triangulated-category].

Uses: def-weil-triangulated-category

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.proof.md; paragraph (3): connecting square required for triangle devissage

### Original step 7

Now impose exactly the stated preservation and restriction hypotheses. Every object occurring in the three factors of $B_K$ then belongs to its chosen subcategory. A full-subcategory inclusion leaves Hom sets, identities and composition unchanged, so the same three arrows define the restricted natural transformation. By the assumed restriction of the adjunctions and composition maps, these arrows are respectively the restricted unit, $G_{p'}$ of the restricted square comparison, and $G_{p'}P_{g'}$ of the restricted counit. Their composite is word for word the formula of [det-def-sfb-base-change-morphism-bc], with $f=p$ and $f'=p'$. Fullness and faithfulness make equality of the ambient components equality of the restricted components. Shifts and distinguished triangles are inherited by [def-weil-triangulated-subcategory], so steps 4--6 remain valid. For $\Dbc$ its morphisms are explicitly the ambient morphisms by [sk-def-sfb-bounded-constructible]; the conclusion applies whenever the preservation hypotheses in the statement hold.

Uses: det-def-sfb-base-change-morphism-bc, sk-def-sfb-bounded-constructible, def-weil-triangulated-subcategory

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.proof.md; paragraph (3): ambient exchange restricted to the preserved constructible categories

## Not duplicates

lem-sfb-module-derived-functor-compositor-shifts vs cor-cbc-derived-extension-zero-base-change: the existing node concerns “Derived extension-by-zero base change”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-coef-system-derived-transition: the existing node concerns “Canonical localized semilinear transitions of strict coefficient systems”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-coef-tower-derived-evaluation-transition: the existing node concerns “Canonical localized transitions between derived tower evaluations”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-kun-constant-sheaf: the existing node concerns “Constant sheaves and constant complexes”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-pe-finite-discrete-presentation-encoding: the existing node concerns “Specified finite-discrete section-action presentation encoding”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-pur-tower-derived-localization-comparisons: the existing node concerns “Canonical constant-tower interchange and cochain localization unit”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-sbc-tower-derived-evaluation-interchange: the existing node concerns “Canonical exact derived tower evaluation interchange”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-sf-comparison-derived-pullback: the existing node concerns “The derived pullback along the comparison morphism of sites”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-sf-open-normalization-data: the existing node concerns “Geometric and operation data for open tensor normalization”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-sf-scalar-reduction-categories-restriction: the existing node concerns “Completed and finite coefficient module categories and scalar restriction”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-sfb-dc-open-lower-shriek-adjunction: the existing node concerns “The adjunction $j_!\dashv Lj^*$ on $D_{\mathrm{cons}}$”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-sfb-derived-comap-lower-star-iso: the existing node concerns “Derived restriction of scalars commutes with $Rf_*$”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-sfb-derived-comap-upper-star-iso: the existing node concerns “Derived restriction of scalars commutes with $D(f^*)$”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-sfb-derived-open-immersion-shriek-iso: the existing node concerns “Extension by zero commutes with $T$”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-sfb-exact-compactification-unit: the existing node concerns “Normalized derived unit for an exact compactification sheaf functor”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-sfb-left-derived-exact: the existing statement gives LF≅D(F) or the exact termwise factorization; it does not identify the specified module pullback compositors and their square comparison under those maps.

lem-sfb-module-derived-functor-compositor-shifts vs def-sfb-preserves-kflat-quasi-iso: the existing node concerns “K-flat complexes; functors preserving K-flat quasi-isomorphisms”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-sfb-proetale-ring-derived-inverse-image: the existing node concerns “Exact derived inverse image over an arbitrary pro-etale ring sheaf”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-sfb-right-derived-exact: the existing node concerns “Right derived functor of an exact functor”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-weil-ambient-exceptional-adjoint: the existing node concerns “Ambient exceptional right adjoint datum”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-weil-exact-derived-adjunction: the existing node concerns “Localization of an exact adjunction to derived categories”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-weil-integral-derived-restriction-of-scalars: the existing node concerns “Derived restriction of scalars from finite to completed integral coefficients”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-weil-pbc-adic-coefficient-datum: the existing node concerns “Tower category and adic coefficient datum”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-weil-pbc-derived-exchange: the existing node concerns “Derived exchange map”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-weil-pbc-derived-inverse-image: the existing node concerns “Inverse image on bounded below derived categories”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-weil-pbc-derived-inverse-limit: the existing node concerns “Sequential derived inverse limit”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs def-weil-pbc-truncation-exact-couples: the existing node concerns “The two truncation exact couples”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs det-lem-formal-closed-support-adjunction: the existing node concerns “Sections with closed support: adjunction and fiber triangle for all coefficients”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs det-nagata-density-normalization-pushforward: the existing node concerns “Proper direct image through the schematic closure”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs det-pe-wc-sections-derived: the existing node concerns “Derived sections over a w-contractible affine”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs det-proper-heart-bound-lattice: the existing node concerns “The lattice bound $2d+1$”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs det-proper-heart-bound-torsion: the existing node concerns “The torsion bound over a weakly contractible base”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs det-proper-image-localizing-open: the existing node concerns “Extension by zero on the localizing categories”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs det-sf-mate-open-restriction: the existing node concerns “Open immersions and open restriction for $f^!$”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-a1-finite-map-lisse: the existing node concerns “Lissity under finite étale pushforward”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-a1-finite-pullback-strict-tower-comparison: the existing node concerns “Natural finite pullback comparison of strict reduction towers”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-asd-clopen-geometric-sections-derived-evaluation: the existing node concerns “Unbounded evaluation on finitely many clopen geometric sections”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-asd-derived-counit-k-injective-termwise: the existing node concerns “Derived counit on a K-injective representative”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-asd-proper-open-refinement-adjoint-projection: the existing node concerns “Adjoint of the unbounded proper-open refinement comparison”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-asd-supported-kummer-scalar-derived-units: the existing node concerns “Derived universal properties of supported scalar maps”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-cbc-completed-pullback-triangles: the existing node concerns “Completed pullback preserves shifts and distinguished triangles”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-cbc-derived-constant-tower-normalization: the existing node concerns “Unique representative normalization of the derived constant-tower comparison”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-cbc-integral-compact-support-uniform-restriction: the existing node concerns “Integral compact-support image preserves uniform constructibility”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-cbc-localized-extension-zero-linear-derived: the existing node concerns “Module extension by zero is linear on the unbounded derived category”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-cbc-open-closed-recollement: the existing node concerns “Open-closed recollement”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-cbc-proetale-extension-zero-base-change: the existing node concerns “Pro-etale extension-by-zero base change”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-coef-derived-tower-counit-projections: the existing node concerns “Derived constant/limit adjunction with its actual projection counit”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-fin-finite-reflects-derived: the existing node concerns “Finite direct image reflects bounded constructibility”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-kun-0ezp: the existing node concerns “Cohomology of a separably closed field vanishes in positive degrees”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-kun-0f1c: the existing node concerns “Direct image commutes with base change along field extensions”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-kun-derived-adjoint-square-comparison: the existing node concerns “Canonical right-derived comparison respects an exact adjoint square”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-kun-exact-equivalence-derived-plus: the existing node concerns “An exact equivalence induces an equivalence on bounded below derived categories”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-kun-sep-closure-conservative: the existing node concerns “Conservativity of base change to a separable closure”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-kun-stalk-faithful-derived: the existing node concerns “Stalk faithfulness for derived objects”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-kun-stalks-of-cohomology: the existing node concerns “Stalks of cohomology sheaves”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pc-affine-tensor-cohomology-additive-parts: the existing node concerns “Additivity of affine tensor cohomology”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pc-base-derived-extension-coherent-triangle: the existing node concerns “Coherent universal derived extension preserves distinguished triangles”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pc-bounded-complex-tensor-proper-support-bound: the existing node concerns “Proper closed bound for supports of a bounded tensor”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pc-ext-exact-functor-square: the existing node concerns “Ext maps intertwine a natural isomorphism of composite exact functors”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pc-ext-restriction-map-calculus: the existing node concerns “Constructed Ext restriction maps and their composition calculus”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pc-module-pullback-comparison-iso-transport: the existing node concerns “Transport of a module comparison through a scheme isomorphism”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pc-open-ordinary-tensor-germ-equation: the existing node concerns “Homology transport from the canonical open tensor-stalk chain square”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pc-open-stalk-representative-coherence: the existing node concerns “Exact open stalk comparison on arbitrary representatives”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pc-open-tensor-restriction-representative: the existing node concerns “Representative formula for ordinary tensor restriction”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pd-section-derived-open-adjunction-normalization: the existing node concerns “Section equivalence identifies the canonical derived open adjunction”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pd-section-derived-pushpull-normalization: the existing node concerns “Section equivalence and canonical derived push-pull adjunctions”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pe-classical-derived-image: the existing node concerns “Classical cohomology of comparison inverse image”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pe-finite-scalar-restriction-constructible: the existing node concerns “Finite scalar restriction preserves constructible complexes and bounds”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-per-artin-gabber-affine-curve: the existing node concerns “Affine pushforward is perverse up to the relative dimension”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-per-finite-closed-support-exchange: the existing node concerns “Closed extraordinary restriction commutes with finite direct image”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-per-finite-etale-derived-ambidexterity: the existing node concerns “Finite etale ambidexterity and its counit on ordinary derived categories”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-per-local-cohomology-adjoint-cech: the existing node concerns “Extended Čech model for derived closed support”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-per-noetherian-supported-product-calculus: the existing node concerns “Supported products and Cartier interchange on ordinary etale sites”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-per-potential-finite-bidual-comparison: the existing node concerns “Finite direct image and evaluation biduality for potential complexes”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-per-proper-finite-coefficient-bounded-preservation: the existing node concerns “Proper direct image preserves ordinary finite-coefficient bounded constructibility over a Noetherian base”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-per-rational-module-realization-functor: the existing node concerns “Construction and cohomology of raw rational module realization”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-adjunction-evaluation-composition: the existing node concerns “Evaluation and composition of normalized adjunction mates”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-adjunction-mate-transpose: the existing node concerns “Transpose formula for a general mate square”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-adjunction-transition-coherence: the existing node concerns “Transition coherence for evaluation mates”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-classical-localization-triangle-transport: the existing node concerns “Transport of the pre-pushforward classical localization triangle”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-closed-finite-adjoint-counit-transport: the existing node concerns “Closed finite exceptional adjoint and counit on classical inputs”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-closed-supported-cup-vanishing: the existing node concerns “Restriction to a closed support detects the zero action on supported cohomology”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-cochain-adjunction-compatibility: the existing node concerns “Normalized derived Hom formulas on cochain complexes”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-cochain-homotopy-derived-comparison: the existing node concerns “Comparison through the homotopy quotient”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-comparison-direct-image-resolution-mate: the existing node concerns “Restriction-transpose resolution model for the specified comparison mate”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-derived-change-of-rings: the existing node concerns “Derived change of rings along a morphism of sheaves of rings, computed by K-flat resolutions”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-derived-mate-comparison: the existing node concerns “Cochain representative formula for normalized derived mates”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-derived-representable-transport: the existing node concerns “Derived transport of represented left exact functors through injective comparisons”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-etale-iso-descent: the existing node concerns “Isomorphisms descend along etale surjections”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-exact-pullback-signed-comparison: the existing node concerns “Exact ringed pullback identifies the canonical signed derived tensor comparison”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-exact-restriction-composition: the existing node concerns “Exact restriction compositors and their localization formulas”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-extension-evaluation-comparison: the existing node concerns “Evaluation comparison for derived left extensions”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-finite-clopen-derived-decomposition: the existing node concerns “Finite clopen decomposition of pro-etale derived coefficient categories”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-finite-product-derived-tensor-calculus: the existing node concerns “Unbounded derived and K-flat tensor calculus for finite clopen module gluing”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-finite-pullback-localization-cohomology: the existing node concerns “Finite derived pullback and normalized slice cohomology restriction”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-good-truncation-exact-normalization: the existing node concerns “Good-truncation normalization and exact-functor compatibility”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-left-derived-exact-chosen-localization: the existing node concerns “Exactness of an everywhere-defined left derived functor on a chosen derived category”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-left-derived-exact-when-defined: the existing node concerns “Everywhere-defined left derived functors are exact”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-left-derived-from-kflat-class: the existing node concerns “Left derived functor on the derived category computed by a resolving class”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-left-derived-kan-source-triangles: the existing node concerns “The Kan extension preserves distinguished source triangles”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-left-derived-kan-triangle-value-comparison: the existing node concerns “Canonical comparison of the Kan image triangle with denominator values”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-line-unbounded-derived-tensor: the existing node concerns “Derived tensor by a locally free line is the exact termwise equivalence”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-normalized-adjunction-composition: the existing node concerns “Composition and uniqueness of normalized adjunction formulas”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-normalized-left-extension: the existing node concerns “Normalized left extension from a resolving class”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-open-cover-cohomology-detection: the existing node concerns “Open-site cohomology comparisons and Zariski vanishing detection”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-origin-class-projective-comparison: the existing node concerns “Comparison of the supported affine-origin class with the projective Chern generator”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-proetale-derived-pullback-identity: the existing node concerns “Identity normalization of finite-coefficient pro-etale derived pullback”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-quasi-isos-saturated-triangulated: the existing node concerns “Quasi-isomorphisms are saturated and triangulation-compatible”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-right-kan-extension-coherent-shift: the existing node concerns “Coherent shifts on a right Kan extension”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-ringed-derived-composition-cocycle: the existing node concerns “Cocycle and identity laws for normalized ringed-topos derived composition”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-signed-line-derived-base-change: the existing node concerns “Signed line comparisons and their unbounded derived tensor action”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-support-localization-triangle: the existing node concerns “Localization triangle for the exceptional inverse image”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-derived-subsequence: the existing node concerns “Canonical exact derived subsequence comparisons”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-derived-subsequence-evaluation-composition: the existing node concerns “Subsequence evaluation respects restriction composition”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-derived-subsequence-transition: the existing node concerns “Subsequence evaluation respects derived transitions”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-derived-transition: the existing node concerns “Localization of actual semilinear transitions”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-derived-transition-coherence: the existing node concerns “Derived semilinear transitions compose”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-derived-transition-unit: the existing node concerns “Identity transitions and the canonical derived tensor unit”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-scalar-derived-extension: the existing node concerns “A scalar model as normalized derived extension data”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-selected-derived-composition: the existing node concerns “Canonical composition of derived subsequence extensions”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-selected-derived-composition-evaluation: the existing node concerns “Evaluation of the derived subsequence compositor”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-selected-derived-evaluation: the existing node concerns “Derived evaluation of the subsequence left extension”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-selected-derived-evaluation-index: the existing node concerns “Reindexing the selected derived evaluation comparison”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-selected-derived-extension: the existing node concerns “Deriving the ordinary subsequence extension”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-selected-derived-transition: the existing node concerns “The specified tensor-adjoint selected derived transition”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-single-derived-evaluation: the existing node concerns “Derived singleton evaluation below and above the input level”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-pur-system-single-derived-extension: the existing node concerns “Deriving the ordinary singleton extension”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sbc-derived-scalar-extension-counit-shift: the existing node concerns “Counit-compatible shift structure of derived change of rings on a site”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sbc-higher-image-raw-pullback-composition: the existing node concerns “Composition of explicit raw cohomology pullbacks”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sbc-higher-image-raw-pullback-functorial: the existing node concerns “Functorial additive raw cohomology pullback”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sbc-higher-image-raw-pullback-identity: the existing node concerns “Identity of explicit raw cohomology pullback”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sbc-integral-test-pushforward-arrow: the existing node concerns “Integral pushforward identifies the two test-base comparison arrows”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sbc-scalar-extension-counit-properties: the existing node concerns “K-flat computation and triangulatedness of a specified scalar-extension counit”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sbc-unbounded-exact-adjunction-square: the existing node concerns “Constant towers and evaluations preserve the unbounded derived adjunctions of a ringed morphism”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sc-cohomology-closed-immersion-pushforward: the existing node concerns “Cohomology is unchanged by pushforward along a closed immersion”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sc-derived-open-shriek-derived-adjunction: the existing node concerns “Derived extension-by-zero and restriction adjunction”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sc-exact-derived-adjunction-single-counit: the existing node concerns “The exact derived adjunction counit on a single complex”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sc-exact-functor-higher-derived-vanishing: the existing node concerns “Exact functors have vanishing higher right derived functors”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-automorphism-constructible-stage-equivalence: the existing node concerns “Automorphism pullback preserves constructible categories at every coefficient stage”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-boundary-bounded-tensor-comparison: the existing node concerns “Bounded tensor preparation for the boundary direct-image comparison”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-cbc-strict-tensor-model-evaluation: the existing node concerns “Strict tensor towers compute diagram-derived reduction with the specified transitions”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-class-compact-support-comparison: the existing node concerns “On the coefficient class the compact-support functor is computed on the étale site”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-closed-support-tor-bound: the existing node concerns “Closed support triangle adds one to the Tor upper bound”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-cyclic-derived-hom-exact-sequence: the existing node concerns “Invariant and coinvariant sequence for native derived morphisms”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-derived-immersion-comparison-normalization: the existing node concerns “Derived open/closed site mates retain sheaf restriction normalization”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-etale-derived-pullback-stalk: the existing node concerns “Derived etale module pullback has the stalk at the image point”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-etale-immersion-shriek-normalization: the existing node concerns “Specified open and closed normalization of ordinary etale compact supports”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-etale-module-stalk-cohomology-test: the existing node concerns “Module geometric stalks compute and detect unbounded cohomology”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-etale-origin-pushforward-amplitude: the existing node concerns “Etale heart bounds control cohomological ranges on pro-etale complexes of etale origin”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-etale-smooth-stratified-ctf: the existing node concerns “Smooth-stratum finite-Tor devissage over an arbitrary algebraically closed field”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-etale-stratified-stalk-identification: the existing node concerns “Derived geometric stalk of a constant local model”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-exact-functor-derived-triangulated: the existing node concerns “An exact functor of abelian categories induces a triangulated functor on derived categories”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-exact-pullback-counit-normalization: the existing node concerns “Counit normalization of exact pullback and its strict completed construction”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-finite-immersion-constructibility-interval: the existing node concerns “Finite constructibility partitions and unchanged intervals for immersion restriction and closed direct image”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-free-derived-weil-resolution: the existing node concerns “Exact free induction and the cyclic resolution in ordinary derived categories”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-kinjective-derived-map-computation: the existing node concerns “Computation of unbounded derived morphisms on arbitrary K-injective resolutions”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-locally-closed-closure-adjoint-realization: the existing node concerns “Closure compactification realizes the immersion adjoint and its bounds”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-open-extension-scalar-restriction-coherence: the existing node concerns “Coherent finite scalar restriction for sheafified and derived open extension”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-open-finite-constructibility-interval: the existing node concerns “Open extension preserves finite constructibility and its cohomological interval”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-open-tensor-normalization: the existing node concerns “Open-extension unit normalization for derived tensor and base change”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-rational-localization-triangle-orthogonality: the existing node concerns “Normalized rational localization triangles and cross-object orthogonality”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-ringed-closed-kernel-adjoint: the existing node concerns “The support-kernel adjoint for an arbitrary pro-etale ring sheaf”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-ringed-open-roos-preservation: the existing node concerns “Ringed pro-etale open extension preserves products and Roos triangles”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sf-semilinear-clopen-unit-projector: the existing node concerns “Clopen system projection is the specified direct-image unit”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-cech-localization-unit-totalization: the existing node concerns “Closed localization unit through bounded-below Cech descent”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-condensed-localization-exact-cohomology: the existing node concerns “Condensed coefficient localization is exact and commutes with cohomology”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-constant-realization-reflects-isomorphism: the existing node concerns “Constant realization reflects algebraic derived isomorphisms locally”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-constructible-exact-scalar-triangulation: the existing node concerns “Inherited constructible triangles and exact ambient scalar extension”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-derived-cech-image-totalization: the existing node concerns “Normalized derived Cech descent followed by exact inverse image”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-derived-exchange-exact-normalization: explicitly requested extraction from this returned proof: the original additionally asserts exchange counit, triangle and restriction conclusions, none asserted by the child.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-derived-scalar-localization-reflection: the existing node concerns “Derived scalar localization is reflective with its normalized unit”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-divisible-extension-derived-reduction: the existing node concerns “Derived reduction of an extension by a divisible sheaf”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-etale-finite-compactification-sheaf-iso: the existing node concerns “The etale graph sheaf map in a finite compactification is invertible”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-exact-compactification-unit-finite: the existing node concerns “Finite compactification units are invertible”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-exact-compactification-unit-identity: the existing node concerns “Identity normalization of the exact compactification unit”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-exact-open-closed-unbounded-calculus: the existing node concerns “Unbounded support calculus from exact abelian open/closed localization data”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-finite-discrete-constructible-model: the existing node concerns “Finite discrete internal constructibility has a classical etale model”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-flat-scalar-tower-coherence: the existing node concerns “Coherent comparisons for exact scalar extension along a tower of sheaf ring objects”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-free-representable-derived-functions-model: the existing node concerns “Derived functions on a free representable module as sheafified derived sections”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-identity-open-derived-adjunction-normalization: the existing node concerns “K-injective normalization and derived adjunction at an identity open locus”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-ind-finite-free-scalar-model: the existing node concerns “Exact unbounded scalar model for an ind-finite-free coefficient algebra”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-integral-derived-extension-comparison: the existing node concerns “Actual integral coefficient extension and its termwise triangulated comparison”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-integral-residue-class-triangle-closure: the existing node concerns “Triangle closure for complete complexes with finite étale residue origin”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-interchange-proper-pasting: the existing node concerns “Normalized proper-open interchange respects successive proper maps”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-intrinsic-finite-derived-pullback: the existing node concerns “Intrinsic finite-coefficient derived pullback preserves bounded constructibility”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-local-integral-perfect-model-cohomology: the existing node concerns “Cohomology of a local integral perfect scalar model”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-local-model-cohomology-descent: the existing node concerns “Cohomology bounds descend from finite local models”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-module-upper-star-kflat-quasi-iso: the existing node concerns “The pullback of module objects preserves K-flat quasi-isomorphisms”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-normed-coefficient-realization: the existing node concerns “Realizing finite normed coefficient fields and their module functors”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-perfect-constant-derived-map-local: the existing node concerns “Derived maps out of a perfect constant complex are locally algebraic”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-qcqs-proper-constructible-closed-base-change: the existing node concerns “Closed proper base change on bounded constructible finite-Tor inputs over a qcqs base”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-quasifinite-compact-support-exact: the existing node concerns “Quasi-finite compact support is exact and agrees with compactifications”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-resolving-derived-adjunction-normalization: the existing theorem constructs a normalized derived adjunction with a Hom formula; the new task identifies two already specified adjunctions under c and proves their fixed-shift compatibility.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-scalar-adjunction-unit-coefficient-normalization: the existing node concerns “Normalized scalar adjunction on K-flat models and the coefficient unit”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-stratified-local-cohomological-bounds: the existing node concerns “Finite stratified local cohomological bounds become global”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sfb-tor-interval-local-detection: the existing node concerns “Tor bounds detected on pro-etale covers and open-closed decompositions”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sp-exact-derived-transformation-pasting: the existing node concerns “Exact derived localization preserves pasting of noninvertible transformations”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sp-normalized-koszul-roos-models: the existing node concerns “Normalized principal-quotient and strict Roos chain models”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sp-shift-identification: the existing node concerns “Shift rule for derived functors”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sp-subterminal-derived-image-calculus: the existing node concerns “K-injective derived direct-image comparisons for subterminal slices”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sp-subterminal-module-local-calculus: the existing node concerns “Intersection and local detection calculus for subterminal module slices”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sp-varying-ring-proper-open-pasting: the existing node concerns “Clopen proper/open projections and pasting over a varying ring system”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-sp-varying-ring-pullback-unit-coherence: the existing node concerns “Identity unit law for actual varying-ring inverse-image compositors”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-artin-tensor-etale-acyclic: the existing node concerns “Artin tensor acyclicity for strict-local algebras”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-bounded-constructible-derived-hom-continuity: the existing node concerns “Derived Hom continuity for bounded constructible etale complexes”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-bounded-stage-roof-comparison: the existing node concerns “Compatible cohomology comparisons for bounded stages of a quasi-isomorphism”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-continuous-cocontinuous-derived-shriek: the existing node concerns “Unbounded derived lower shriek for continuous and cocontinuous site functors”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-etale-shifted-line-normalized-descent: the existing node concerns “Normalized descent of ordinary-etale shifted lines on an affine line”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-external-comparison-triangles: the existing node concerns “Triangle compatibility of the external direct-image comparison”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-filtered-cone-localization: the existing node concerns “Cone triangles in the localization of finite filtered complexes”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-general-nearby-slice-test: the existing node concerns “General specialization slices test the ordinary nearby comparison”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-left-acyclic-short-exact: the existing node concerns “Left-acyclic objects in short exact sequences”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-localization-filtered-section-exchange: the existing node concerns “The sheaf localization filtration and its pullback comparison”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-nearby-compact-tensor-coherence: the existing node concerns “Tensor and compact-support coherence before duality”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-nearby-spread-out: the existing node concerns “Spread out finite-type nearby-cycle input to an arithmetic base”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-open-base-change-site-transport: the existing node concerns “Site comparison preserves the named open base-change map”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-point-exact-derived-model: the existing node concerns “Exact point models and normalization of derived pullback composition”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-point-system-transport-descent: the existing node concerns “Strict semilinear point transport and descent to whole derived systems”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-point-transport-composition: the existing node concerns “Composition of finite-level point transports”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-smooth-source-constructible-local-acyclicity: the existing node concerns “Smooth source local acyclicity for constructible complexes”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-trf-witnessed-open-pullback: the existing node concerns “Derived pullback and open extension transport explicit etale-origin witnesses”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-coefficient-complex-rationalization: the existing node concerns “Exact rationalization and coherent scalar extension of coefficient-module complexes”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-derived-field-scalar-extension-tower: the existing node concerns “Derived scalar extensions along a tower of fields compose”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-isomorphism-derived-pullback: the existing node concerns “Derived pullback along an isomorphism of schemes is the termwise inverse image”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-isomorphism-derived-pullback-equivalence: the existing node concerns “Derived pullback along an isomorphism of schemes is an equivalence of ambient derived categories”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-isomorphism-derived-pullback-reduction-tower: the existing node concerns “Inverse-image relabelling identifies completed coefficient reduction towers”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-completed-realization-derived-cohomology: the existing node concerns “Exact completed realization and its normalized derived cohomology comparisons”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-constant-tower-pushforward-normalization: the existing node concerns “Constant-tower direct image and limit normalization for identified ring sheaves”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-derived-direct-image-triangulated: the existing node concerns “The derived direct image on bounded below derived categories is a triangulated functor”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-derived-square-shift-on-kinjectives: the existing node concerns “Shift coherence of a derived square computed on K-injectives”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-etale-compact-support-open-closed-triangle: the existing node concerns “Open-closed localization for relative etale compact support”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-exact-functor-bounded-below: the existing node concerns “Exact functors preserve bounded below derived objects”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-exact-functor-complex-cohomology: the existing node concerns “An exact functor commutes with cohomology of cochain complexes”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-exact-functor-derived-factorization: the existing statement gives LF≅D(F) or the exact termwise factorization; it does not identify the specified module pullback compositors and their square comparison under those maps.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-exact-functor-derived-functor: the existing node concerns “The functor induced by an exact functor is its own right and left derived functor”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-exact-square-derived-counit: the existing node concerns “Counits in an exact square from normalization on K-injectives”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-ext-exact-functor-composition-comparison: the existing node concerns “ExtExactFunctorCompositionComparison”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-ext-exact-functor-identity-comparison: the existing node concerns “ExtExactFunctorIdentityComparison”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-flat-constant-tensor-pro-zero-cones: the existing node concerns “Flat constant extension and K-flat tensor of pro-zero cone towers”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-homotopic-maps-equal-cohomology: the existing node concerns “Homotopic maps induce equal maps on cohomology, also after an additive functor”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-integral-stratified-perfect-characterization: the existing node concerns “Stratified perfect description of the integral completed category”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-local-derived-restriction-comparisons: the existing node concerns “Comparison of derived local restriction with exact inverse image and slice restriction”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-localization-inverse-image-coherence: the existing node concerns “Coherent localization comparison for exact inverse image”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-noetherian-stratum-detection: the existing node concerns “Finite stratified restrictions detect pro-etale sheaves”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-proper-open-comparison-proetale: the existing node concerns “Proper-open comparison for complexes from the etale site”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-realization-scalar-functor: the existing node concerns “Actual scalar-extension functor on raw integral rationalizations”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-ringed-topoi-derived-pullback: the existing node concerns “Derived pullback on ringed topoi computed by K-flat resolutions”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-scalar-extension-unit-triangles: the existing node concerns “Scalar-extension maps form morphisms of distinguished triangles”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-scalar-localization-derived-hom: the existing node concerns “Localization of shifted derived Hom from a bounded-below compact source”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-scalar-localization-telescope-leg-laws: the existing node concerns “Naturality and shifts of inverse-scalar adjunction legs”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-scalar-localization-underlying-telescope: the existing node concerns “Underlying telescope for derived scalar localization”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-scalar-localization-unit-factors: the existing node concerns “Scalar compatibility of exact derived factorization”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-scalar-localization-unit-shift: the existing node concerns “Shift coherence of normalized derived scalar unit”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-singleton-site-module-comparison: the existing node concerns “Evaluation identifies the punctual ringed site with ordinary modules”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-strictly-henselian-etale-acyclic: the existing node concerns “Etale cohomology of a strictly henselian local scheme vanishes in positive degrees”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-pbc-tower-derived-evaluation-normalization: the existing node concerns “Derived tower evaluation with its unit and counit normalization”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-point-derived-sections-tensor-descent: the existing node concerns “Derived descent and K-flat normalization of the ordinary point sections-tensor comparison”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-point-integral-perfect-realization: the existing node concerns “Completed perfect realization is fully faithful and left adjoint to point sections”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-point-proetale-sections-exact: the existing node concerns “Sections over an algebraically closed point are exact on the pro-etale site”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs lem-weil-proetale-direct-image-restriction-of-scalars: the existing node concerns “Derived pro-etale direct image commutes with restriction of scalars”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs prop-exc-finite-etale-adjoint: the existing node concerns “The right adjoint for a finite etale morphism”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs prop-exc-open-adjoint: the existing node concerns “The right adjoint for an open immersion”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs prop-sfb-module-left-derived-upper-star-comp: the existing statement gives the derived pullback composition isomorphism; the child additionally pins it to the exact termwise/K-flat comparison and proves compatibility with fixed integer shifts.

lem-sfb-module-derived-functor-compositor-shifts vs prop-weil-pbc-derived-inverse-image-adjunction: the existing node concerns “Derived adjunction of inverse and direct image on D^+”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs prop-weil-pbc-derived-product-representation: the existing node concerns “Representation of the derived product of a tower”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs sbc-lem-integral-etale-direct-image-exact: the existing node concerns “Etale direct image is exact for integral morphisms”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs sk-d-setup: the existing node concerns “Coefficients and geometric categories”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs sk-lem-pbc-finite: the existing node concerns “Finite morphisms”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs sk-lem-sf-flat-model: the existing node concerns “Flat models and generators”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-module-derived-functor-compositor-shifts vs src-sbc-exact-functor-plus-unit: the existing node concerns “The bounded-below right-derived unit of an exact functor is invertible”; it does not assert the canonical exact termwise/K-flat normalization of internal condensed-module pullback compositors and fixed shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs def-pur-tower-derived-localization-comparisons: the existing node concerns “Canonical constant-tower interchange and cochain localization unit”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs def-weil-pbc-derived-exchange: the existing node concerns “Derived exchange map”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs def-weil-pbc-flat-ringed-diagram-adjuncts: the existing node concerns “Normalized coefficient comparison with adjunct compatibility”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs def-weil-pbc-flat-ringed-diagram-comparisons: the existing node concerns “Comparison functors and localization factors for flat coefficient restriction”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs def-weil-pbc-flat-ringed-diagram-input: the existing node concerns “Compatible flat coefficient input and its module diagram functors”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-asd-clopen-geometric-sections-derived-evaluation: the existing node concerns “Unbounded evaluation on finitely many clopen geometric sections”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-asd-derived-counit-k-injective-termwise: the existing node concerns “Derived counit on a K-injective representative”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-asd-proper-open-refinement-adjoint-projection: the existing node concerns “Adjoint of the unbounded proper-open refinement comparison”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-cbc-strict-tower-proper-open-calculus: the existing node concerns “Normalized proper/open calculus on strict pro-etale towers”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-coef-rational-operations: the existing node concerns “Identification with the rational internal Hom and exceptional inverse image”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-kun-derived-adjoint-square-comparison: the existing node concerns “Canonical right-derived comparison respects an exact adjoint square”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-pbc-torsion-stalk-proetale-resolution-map: the existing node concerns “Resolution-level pro-étale section map”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-pc-derived-adjoint-functors: the existing result derives an adjunction/Hom formula; it does not compare the two specified P and D(u*) adjunctions, state their c-transport equations, and retain the fixed K-injective shifts.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-pc-derived-base-change-unit-compatibility: the existing node concerns “Derived mate compatibility with the right-derived unit”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-pc-homotopy-pullback-square-localization: the existing node concerns “Localization of the homotopy pullback square”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-pc-pre-derived-adjoint-functors-general: the existing result derives an adjunction/Hom formula; it does not compare the two specified P and D(u*) adjunctions, state their c-transport equations, and retain the fixed K-injective shifts.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-pc-ringed-spaces-derived-adjoint: the existing node concerns “Derived pullback is left adjoint to derived direct image”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-pur-comparison-global-resolution-model: the existing node concerns “Resolution model for normalized global site comparison”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-pur-comparison-unit-injective-model: the existing node concerns “Injective-resolution representative of the derived etale/pro-etale comparison unit”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-pur-proetale-direct-image-global-evaluation: the existing node concerns “Normalized derived global sections after pro-etale direct image”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-pur-sequence-adjoint-resolution-shifts: the existing node concerns “Resolution-normalized identification of the sequence-site derived adjoints”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-pur-sheaf-ring-derived-coefficient-adjunction: the existing node concerns “Derived change of rings along a map of ring sheaves is left adjoint to restriction of scalars, with normalized unit and transposes”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-pur-supported-hom-adjunction-transpose: the existing node concerns “The supported-Hom identification is the closed-support adjunction transpose”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-sbc-completed-operations-linear-natural-exchange: the existing node concerns “Linearity and naturality of completed pullback, direct image, and exchange”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-sbc-unbounded-exact-adjunction-square: the existing node concerns “Constant towers and evaluations preserve the unbounded derived adjunctions of a ringed morphism”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-sfb-acyclic-hypercover-pullback-normalization: the existing node concerns “Acyclic hypercover comparison represents the derived section pullback”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-sfb-closed-test-derived-exchange-model: the existing node concerns “Derived exchange on lifted closed pro-etale test objects”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-sfb-derived-composition-adjunction-normalization: the existing theorem identifies a composition comparison of right adjoints conjugate to composed exact left adjoints; the new task compares two left-derived presentations of a single adjunction and their fixed shifts.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-sfb-derived-exchange-exact-normalization: explicitly requested extraction from this returned proof: the original additionally asserts exchange counit, triangle and restriction conclusions, none asserted by the child.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-sfb-qcqs-proper-constructible-closed-base-change: the existing node concerns “Closed proper base change on bounded constructible finite-Tor inputs over a qcqs base”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-sp-canonical-right-derived-adjunction-shift: the existing statement concerns D(u*) as left adjoint; the new task identifies the specified K-flat P adjunction under c and states both transport equations before retaining the fixed shifts.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-sp-etale-derived-chain-transpose: the existing node concerns “Canonical etale derived adjunction on ordinary chain transposes”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-sp-finite-free-direct-image-shift: the existing node concerns “Shift compatibility of the actual coefficient/direct-image mate”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-trf-continuous-cocontinuous-derived-shriek: the existing node concerns “Unbounded derived lower shriek for continuous and cocontinuous site functors”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-trf-derived-colimit-bar: the existing node concerns “Category bar complex and functorial derived colimits”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-trf-derived-shriek-comma-homology: the existing node concerns “Pointwise comma-category computation of derived presheaf left Kan extension”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-trf-finite-structural-maps-commshift: the existing node concerns “Canonical finite-coefficient structural maps commute with shifts”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-trf-integral-comparison-counit-characterization: the existing node concerns “Whole-tower adjunct characterization of the specified integral comparison”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-trf-integral-inverse-image-comparison-composition: the existing node concerns “The integral inverse-image/pullback comparison respects composition”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-derived-scalar-extension-restriction-adjunction: the existing node concerns “Derived reduction modulo varpi^n is left adjoint to restriction of scalars”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-derived-adjunction-commshift: the existing node concerns “The unit and counit of the derived adjunction u^{-1} -| Ru_* commute with the shift isomorphisms”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-derived-adjunction-shift: the existing node concerns “Canonical derived ringed-topos adjunction is shift-compatible”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-derived-exchange-bounded-comparison: the existing node concerns “The bounded below exchange comparison equation”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-derived-exchange-module-termwise: the existing node concerns “K-injective representative of the module derived exchange mate”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-derived-exchange-termwise: the existing node concerns “The termwise construction of the derived exchange morphism”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-derived-exchange-unbounded-transport: the existing node concerns “Transport of the exchange equation to arbitrary K-injective representatives”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-exact-square-derived-counit: the existing node concerns “Counits in an exact square from normalization on K-injectives”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-flat-ringed-diagram-restriction: the existing node concerns “Flat coefficient restriction and normalized derived operations on module diagrams”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-raw-restricted-class-normalization: the existing node concerns “Raw restricted evaluation preserves the canonical higher-image class”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-raw-restricted-resolution-class: the existing node concerns “Raw resolution evaluation has the canonical cocycle class”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-raw-restricted-resolution-naturality: the existing node concerns “Raw evaluation is natural on a prescribed injective resolution”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-raw-restricted-resolution-restriction: the existing node concerns “Etale cohomology pullback on a chosen resolution”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-strict-quotient-scalar-direct-isomorphisms: the existing node concerns “Invertibility of the normalized ordinary and strict scalar right mates”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-strict-tower-exchange-mate-normalization: the existing node concerns “Strict tower exchange agrees with the canonical mate”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lem-weil-pbc-tower-derived-evaluation-normalization: the existing node concerns “Derived tower evaluation with its unit and counit normalization”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lemma-weil-pbc-projection-formula-finite-free: the existing node concerns “Finite-free projection formula”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs lemma-weil-pbc-projection-formula-totalization: the existing node concerns “Signed totalization of the perfect formula”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs prop-coef-integral-dualizing: the existing node concerns “The integral dualizing object and its adjunction”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs prop-weil-pbc-derived-inverse-image-adjunction: the existing node concerns “Derived adjunction of inverse and direct image on D^+”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

lem-sfb-kflat-derived-adjunction-transport-shifts vs sk-def-exchange: the existing node concerns “Derived exchange”; it does not assert the comparison of the specified K-flat module adjunction with the exact termwise adjunction along c, including both transport equations and the fixed K-injective shifts for arbitrary condensed coefficients and scheme morphisms.

## Prior report retained verbatim

# Worker report: lem-sfb-derived-exchange-exact-normalization

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-derived-exchange-exact-normalization.json` — statement, split in seven steps, no whole-item Mathlib match. `citations.json` contains a verbatim statement excerpt for every proof citation. No new nodes; no new Mathlib leaves. The sandbox had no earlier item or report, so this starts from the current live node.
2. Attachments: none for the item. The project declaration `AlgebraicGeometry.Etale.commShift_baseChange` in `WeilConjectures/SixFunctors/BaseChange/DerivedComparison.lean:183` concerns bounded-below étale sheaves; it does not state the unbounded condensed module-object item. The node tag has no hit in `lean/WeilConjectures/`. I read the module-object derived definitions and their composition description in `SixFunctors/ProEtale/ModuleObject/Derived/UpperLowerStar.lean`; they provide inputs, not every clause of this item. Existing generic DAG nodes are reused rather than claiming the partial étale result as an attachment.
3. WANTED: none. All sources needed for this split are available locally.
4. The imported proof was empty. Its statement dependencies omitted the ambient pullback compositor and the full triangulated-subcategory notion; both are now explicit. The final conditional application to arbitrary coefficients needed the clarification explained below. Other clauses and all imported metadata are retained.
5. Unfinished work: none for this level of splitting. Existing unsplit inputs retain their own work; none is duplicated or proved by its own proof text here.

## Statement corrected

STATEMENT-DISPUTED: the final sentence, if read as requiring only preservation of bounded constructible objects for arbitrary condensed rings, does not ensure a triangulated bounded constructible category. The previous sentence correctly assumed chosen full triangulated subcategories. I made that hypothesis explicit also in the final sentence: “In particular this applies to $\Dbc$ whenever these are full triangulated subcategories and the stated preservation and restriction hypotheses hold.” No ambient claim is changed and no hypothesis is added to the rational-coefficient proper-base-change application.

Here is the obstruction to the broader reading. Take a discrete ring $R=k\oplus V$ with square-zero ideal $V$, where $V$ is an infinite-dimensional $k$-vector space, and choose $0\ne v\in V$. Multiplication by $v$ is a map between the two finite free modules $R\to R$. Its kernel is $V$, which is not finitely generated: multiplication by $R$ on $V$ factors through $k$. Hence the cone has non-finitely-presented cohomology. Thus bounded complexes with finitely presented cohomology need not be closed under cones, already in the module case at a geometric point. For constant discrete coefficients on its pro-étale site the same example is constant; local finite generation would imply finite generation after taking a point of a covering profinite set. Identity functors preserve the bounded constructible objects but do not repair this cone failure. This is why preservation alone cannot justify the assertion that these are triangulated categories.

This correction is faithful to the actual source: paragraph (3) of `sk-thm-sfb-proper-base-change-rational.proof.md` says all functors are exact on the triangulated categories used for devissage; paragraph (2) specifically invokes `det-cor-coefficient-heart-ii-triangulated`. Its coefficients are $E$ and $\overline{\mathbf Q}_\ell$, not an arbitrary noncoherent discrete ring. The current `sk-def-sfb-bounded-constructible` itself makes triangulatedness conditional on Serre closure of constructible modules. The chapter and unit statements/routes are untouched.

## Searches and reuse

I read the chapter and proper-base-change unit records and the current rational proof paragraphs (1)–(3). The nearest blueprint ancestor is `det-thm-sfb-proper-base-change-rational`; this item serves paragraph (3), the exactness and triangle-devissage assertion formerly in steps 7 and 10. Searches of the whole DAG for canonical shifts, derived adjunctions, exact derived composition and counits found the existing generic nodes used below. `tools/blueprint_refs.py search` was run for `exchange`, `shift compatibility`, `derived adjunction`, `unit--square--counit`, `canonical integer-shift`, and `Ambient exchange`. No blueprint node states this whole arbitrary-condensed-ring ambient normalization lemma. In particular `fix-lem-exchanges` uses coefficient stages, completed integral operations, and witnessed domains; `lem-weil-pbc-transport-identifies-exchange` is a finite constant-coefficient étale/pro-étale transport theorem. I opened both statements and did not substitute either for this item. The existing generic exact-derived composition and natural-isomorphism nodes avoid creating duplicates of localization facts.

The five actual msearch queries are retained in `searches.jsonl` and appended, with their exact tool/query text and result names, to the item's existing search history. Both semantic phrasings were read. Loogle and grep hits in `Mathlib/CategoryTheory/Shift/Adjunction.lean:209–210` assume an already compatible adjunction; `Triangulated/Adjunction.lean:60` also assumes it. They do not prove the required compatibility for the specified derived module-object adjunction, nor the module compositor normalization or full-subcategory clause. I read these source declarations and kept the whole item split rather than incorrectly marking it Mathlib. The old imported searches remain as historical searches; the new verdicts describe the actual scope of this item (there is no lattice assertion in it).

## Review by Q32

I read the current source proof `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.proof.md`, especially paragraph (3), alongside the unit and chapter records. I also read Stacks `derived.tex`, Tags 015F/014X (exact termwise functors), 05SU (derived shifts), 05SE (exact derived functors), and 0DVC/09T5 (canonical derived adjunction), with their labels. The seven-step argument is my expansion of the blueprint's exact-transformation assertion, not a claim that Stacks states this combined condensed-coefficient lemma verbatim. There are no new nodes whose source, notion dependencies, searches or small cases are postponed.

Step 1 uses `det-prop-sfb-module-pullback-exact-main`, whose statement really says additive and finite-limit/finite-colimit preserving, and `sk-def-sfb-module-derived-pushpull`, whose statement really gives the ordinary unbounded derived functors on module objects, computed on K-flat and K-injective resolutions. It does not replace these categories with constant étale modules or with a completed derived category. `def-sfb-left-derived-exact` identifies the exact pullback's total left derived functor with its termwise functor. I wrote out the short shift check for this identification on a resolution arrow, rather than assuming an arbitrary identification preserves shifts. `lem-weil-pbc-exact-functor-derived-factorization` explicitly supplies shift-compatible factorizations and exactness; `lem-pc-right-derived-functor-triangulated` states exactness and integer shifts for the K-injective right derived functor. Its resolution hypotheses hold for the ambient module categories in the first cited construction. The underived pushforward is additive (a right adjoint between these additive categories preserves finite products/biproducts and their diagonal/codiagonal addition law). Finally the statement of `lem-weil-pbc-triangulated-functor-composite` is precisely exactness with the composite shift, as needed for both ambient composites. No preservation of constructibility is used here.

Step 2 uses `def-sfb-module-upper-lower-adjunction` to specify the ordinary module adjunction and `def-sfb-module-derived-pushpull-adjunction` to specify its derived one. The statement of `lem-sp-canonical-right-derived-adjunction-shift` is fully generic in abelian categories, assumes an exact additive left adjoint and K-injective resolutions on its target, and explicitly retains the fixed canonical shifts. These are exactly the hypotheses from step 1; it applies separately to $p$ and $p'$. This is stronger evidence than merely equipping an abstract right adjoint with a newly transported shift. I did not cite a finite-coefficient or bounded-below adjunction here.

Step 3 uses the actual statement of `prop-sfb-module-left-derived-upper-star-comp`: the ambient derived compositor is induced by the ordinary module-object compositor. `lem-sfb-exact-derived-natural-iso` gives the degreewise representative of a derived natural isomorphism, and `lem-sfb-exact-derived-composition` gives the precise exact-composition factorization, not a pullback theorem with extra hypotheses. Their exactness hypotheses were checked in step 1. The factorization node also explicitly respects shifts. I checked the degree-$r$ comparison at $M[n]$: it is the component at $M^{r+n}$; the signs in both differentials are $(-1)^n$. This proves the shift square directly, including negative integers. Inverting and composing those squares gives the stated $\theta$ square. There is no missing new lemma here: the argument is the degreewise equality in the cited universal-property factorizations, in 1279 characters.

Step 4 uses only the adjunction laws in `sk-def-sfb-module-derived-pushpull`. I checked all types: $A=P_gG_pK$ belongs to the category on $Y'$, $FA$ and $C=P_{g'}K$ to that on $X'$, and $a:FA\to C$. The counit naturality equation is at this arrow $a$, and the cancellation is $\varepsilon'_{FA}F\eta'_A=1_{FA}$. This gives the exact equation in the item, without a reversed mate or an assumption that the square is cartesian. It is an elementary two-line adjunction calculation, not a new node restating the clause.

Step 5 uses the statement of `lem-weil-pbc-commshift-nattrans-comp-whisker`, whose clauses explicitly allow composition and both whiskerings. Steps 2 and 3 supply the three compatible factors. Applying the rule at each fixed $[n]$ gives the displayed integer-shift equation. Naturality is simply composition and whiskering of natural transformations. No acyclicity or base-change isomorphism theorem is being used.

Step 6 writes out the connecting square. The first equality is naturality at $w:M\to K[1]$, the second is the $n=1$ equation from step 5. The image connecting maps are exactly $\chi^1\Phi(w)$ and $\chi^1\Psi(w)$; their distinguishedness came from step 1, so this step does not silently drop the signs or the shift comparison. The elementary calculation matches the morphism-of-triangles definition in `def-weil-triangulated-category`.

Step 7 uses `det-def-sfb-base-change-morphism-bc`, whose statement has the same three ordered arrows and explicitly permits noncartesian squares. I compared its formula with the ambient one after setting $f=p$, $f'=p'$. Its premise of restricted pushforwards is supplied only at this step. `sk-def-sfb-bounded-constructible` explicitly says identities, composition and morphisms are the ambient ones, and `def-weil-triangulated-subcategory` gives inherited shifts and triangles. All intermediate objects are in the chosen subcategories by the preservation assumptions for the four pullbacks and two pushforwards. The restricted adjunction and compositor are assumed to be their actual restrictions, so equality of the three factors proves equality of the composite components; no unspecified isomorphism is used. This explains also the corrected conditional final sentence.

I tested the identity square (the mate cancels by the same triangle identity), the zero input and zero coefficient ring, and shifts $n=0,1,-1$. No division, nonzero-object or positive-degree condition occurs. The counit argument also works for any noncartesian commutative square; it uses only $\theta$, not a geometric isomorphism assertion. For the restriction step I checked that preservation of objects alone does not change the adjunction: the separate restriction hypothesis is essential and retained. The square-zero-ring example above tests the one ambiguous endpoint and is the only statement clarification. No non-elementary step is longer than 2000 characters, and no clause has been moved into a new node. B1–B9 are vacuous for new nodes; B10 and C1–C8 were addressed by the source/attachment search, the verbatim statement citations, the cycle check and declared tools. D1–D5 are addressed by the actual cancellation, degreewise and connecting-square arguments. E1–E6 were checked by the typed arrows, exactness/resolution hypotheses, integer signs and full-subcategory restriction; E7 prompted the explicit statement clarification above.

The off-unit uses in `split_report.tool_uses` are generic input facts about exact module pullback, ambient derived functors, the canonical adjunction, composition and full subcategories. None replaces the proper-base-change unit's finite/integral/rational route. That unit does not prove these categorical tools. Mathlib and Lean-closed tools need no additional route exception. I changed no maintainer-owned fields, wrote no Lean and ran no compiler or local DAG/preflight check.

## Validation

The server `review_split` check passed on the initial seven-step split. Final delivery validation is recorded below after the required dry run.

The required `deliver.py Q32 lem-sfb-derived-exchange-exact-normalization --no-push` exited 0 and printed `OK (not pushed)` at `ec7048752ee`, with server preflight passed. The final split has seven steps (longest 1279 characters), 17 distinct proof dependencies, 19 verbatim citation entries, zero new nodes and zero new Mathlib leaves. The final push invokes the same preflight again.


## Validation by Q38

The first required server dry run exited 0 and printed OK (not pushed) at e961ec7016d. After that check I made the two child statements explicitly cite the coefficient-sheaf, module-object and derived-category definitions, cited the ordinary compositor definition, and quantified K in the square equation. The statement and search questions are otherwise unchanged; a final dry run follows these clarity repairs. No local DAG checker was run.
