# Stage-1 repair: lem-a1-finite-weil-sections-decomposition

## Files written

- lem-a1-finite-weil-sections-decomposition: statement unchanged; four-step assembly of two new work packages.
- lem-a1-finite-geometric-sections-and-point-orbits: statement, unsplit; no Mathlib match.
- lem-a1-proper-weil-iterate-germ-formula: statement, unsplit; no Mathlib match.
- citations.json records every assembly citation. searches.jsonl retains the real msearch results.

## Attachments

None. The project source search by blueprint tag and concept found no exact finished declaration under WeilConjectures/. Both rational and Qbar statements in Sheaf.Paper.A1FiniteWeilSectionsDecomposition have sorry proofs. I read them as retained statement material, not attachments. No Lean files were written and no compiler was run.

## WANTED

None. The required sources are available locally.

## Fault and repair

The released repair note of 2026-10-22 requires at least two comparable statement-only nodes and an assembly of at most 3000 characters. The sandbox initially had only brief markers, so I read the current live item and its released keep_plan order, and copied the live statement, statement dependencies, citations, earlier Mathlib searches, and Lean metadata. There was no retained split/report to dry-run before editing. The two new arguments are independently available: neither depends on the other, and neither restates the full item. The first has no Weil structure at all; the second allows any proper scheme, all cohomology degrees, and has no finite-stalk decomposition or dimension assertion. Both are deliberately unsplit, with empty proof and proof_deps. Their intended proof material follows below, outside the node statements.

The parent blueprint's arithmetic-invariants formula was already corrected before this repair. For Spec F_q with a rank-one Weil sheaf of Frobenius -1, arithmetic invariants vanish but geometric H_c^0 has dimension one. I preserve the corrected item verbatim; this repair introduces no new statement dispute and changes neither the chapter nor unit route. The item is not the key unit node, so the unit record is untouched.

## Unfinished work

The new nodes are intentionally statement-only for parallel stage-1 workers; no proof is claimed in Lean. Every old argument is assigned below. The only parent-level calculation retained is the inverse of a finite block permutation, an explicit assembly argument.

## Review by NY

I read Stacks 03QP, etale-cohomology.tex, proposition-finite-higher-direct-image-zero (1), including its actual geometric restriction-map formula and proof using finite strictly henselian factors. It neither requires reducedness nor takes arithmetic invariants. I read Deligne Weil II (1.1.3), printed p.150, for rationalization and the common finite field stage, (1.1.7), pp.150-151, for geometric versus arithmetic Frobenius, (1.1.10)-(1.1.13), pp.151-152, for Weil structures and the degree-normalized local operator, and (1.1.14), p.153, for the cohomology action. These sources support the new finite-evaluation package and proper-Weil-iterate package respectively; their more explicit formulas are marked as agent extractions in source.place. No prohibited SGA route is used.

For assembly step 1 I opened the complete statement of lem-a1-finite-geometric-sections-and-point-orbits: it explicitly supplies finite point sets, the embedding count, cyclic permutation, the return equality, finite-dimensionality and the specified natural germ isomorphism. Its hypotheses ask only for a finite Z_0 and a constructible rational/common-stage sheaf, both supplied by the unchanged item; forgetting the Weil structure is legitimate. For step 2 I read lem-weil-pbc-finite-proper and its exact statement that a finite morphism is proper, then the new proper-Weil-iterate statement: its r=1 formula has input Tz and output z, and its coefficient is an isomorphism. After H^0 it gives the correct T inverse block permutation. For step 3 the same new statement explicitly identifies the coefficient at a returning point with the local degree-r operator; step 1 provides precisely the scheme-map return g^d z=z h^d. I checked all three factors against the full displayed definition in def-weil-local-frobenius-trace, including the order of composition. Step 4 writes the inverse block map and verifies both composites componentwise. Every cited statement has a verbatim quotation in citations.json; no assembly step uses a cited proof in place of its statement.

I also opened the existing finite-direct-image, proper coincidence, finite-morphism permanence, closed-point residue field, finite-field Galois Frobenius, transport naturality, integral pullback composition, semilinear germ, and transport-isomorphism statements that supply the retained proof plans below. In particular the finite-direct-image statement supplies natural rational/common-stage germ evaluation, whereas the existing semilinear-germ theorem has no Weil structure and supplies only the transport identity; the new proper package must still prove the naturality induction with theta. The pullback comparisons in all formulas are the scalar localizations of the specified integral system. A rational Weil isomorphism need not preserve an invertible lattice, so the retained induction does not reduce theta to such a lattice map.

Small cases checked: the empty scheme gives empty point sets and zero cohomology; Spec F_q gives one point and the given stalk automorphism; Spec F_{q^2} has two geometric points swapped by T and returns after two steps; Spec(F_q[epsilon]/epsilon^2) has one geometric point and shows why reducedness is unnecessary. Zero sheaves give zero blocks, whose unique maps are still linear isomorphisms. A rank-one sheaf with nonunit l-adic Weil scalar is allowed: the rational formulas use no integral invertibility. For the proper package r=1 is exactly the defining global composite, and for a returning point the displayed coefficient is precisely the three-arrow local definition. These checks preserve the semilinear return rather than the false equality g^d z=z.

I checked delivery-errors B-E: the new statements introduce all their own fields, schemes, coefficients and maps; definition owners are cited, no proof sketches occur in them, searches were actually run with msearch, blueprint ancestry points to the current parent display, and no attachment is asserted from a sorry. The report below compares shared-source and near-duplicate candidates. No new node points to the item, no new proof is hidden in a >2000-character parent step, and the original statement and statement dependencies are byte-for-byte unchanged. The former off-unit generic tools occur only in the retained plans for the unsplit work packages, not as new parent proof edges; the earlier accepted tool metadata is retained, without adding any tool exemption.

## Retained arguments and assignment

The following are the original seven steps, verbatim, so the two future workers receive every detail and none is lost to shortening. Steps 1-3 belong to the finite geometric sections and point orbits node (2290 characters of original argument). Steps 4-6 belong to the proper Weil iterate germ formula node (2836 characters). Step 7 is preserved as the parent's explicit inverse block assembly, and both workers may use its concluding zero-space check. Sources and full original citation lists are copied with each step.

### Original step 1 — lem-a1-finite-geometric-sections-and-point-orbits

By [lem-weil-pbc-finite-morphism-permanence](a), the geometric base change $a_Z$ is finite. The finite structure morphism is proper by [lem-weil-pbc-finite-proper]. Use its identity compactification; [lem-pod-proper-coincidence-frobenius] gives the natural identification $R\Gamma_c(Z,M)\simeq R\Gamma(Z,M)$, including the specified transports. Apply [lem-zl-finite-adic-direct-image] to $a_Z:Z\to s$ and its geometric point $\operatorname{id}_s$. Its finite indexing set $P_{\operatorname{id}_s}$ is $Z(k)=\operatorname{Hom}_k(s,Z)$, and its restriction-map formula gives $e:H_c^0(Z,\mathcal G)\simeq\bigoplus_{z\in Z(k)}\mathcal G_z$. Its naturality is for all morphisms of the underlying constructible sheaves, so also for morphisms of Weil sheaves. No assertion about $|Z_0|$ or dimensions is used yet.

Cited nodes: lem-weil-pbc-finite-proper, lem-pod-proper-coincidence-frobenius, lem-zl-finite-adic-direct-image, lem-weil-pbc-finite-morphism-permanence.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-a1-finite-boundary-weights.proof.md", "place": "First sentence and displayed evaluation formula, corrected geometric-stalk interpretation"}.

### Original step 2 — lem-a1-finite-geometric-sections-and-point-orbits

For a closed point $x$ of $Z_0$, finite type follows from finiteness of its structure morphism [def-weil-finite-integral-morphism], and [lem-kun-closed-point-field](a) gives a finite residue extension of positive degree $d_x$. By [def-weil-geometric-point], its lifts are the $k_0$-embeddings $\kappa(x)\hookrightarrow k$. The finite-field Galois theorem [lem-sfb-finite-field-galois-frobenius] says this extension is separable and Galois, with its $d_x$ automorphisms the powers of $c\mapsto c^q$; after one embedding, all embeddings are obtained by those powers. Hence $|P_x|=d_x\geq1$. The projection from the finite set $Z(k)$ of step 1 onto $|Z_0|$ is surjective, so $|Z_0|$ is finite. Write $h=\operatorname{Spec}(\gamma)$, $g=g_Z$, and $T(z)=gz h^{-1}$ using [def-weil-frobenius-detailed]. This source reparametrization makes $T(z)$ a $k$-point. On residue-field embeddings it is composition with $\gamma^{-1}$, so $T$ acts on each $P_x$ in a cycle of length $d_x$; in particular $g^{d_x}z=z h^{d_x}$.

Cited nodes: def-weil-finite-integral-morphism, lem-kun-closed-point-field, def-weil-geometric-point, lem-sfb-finite-field-galois-frobenius, def-weil-frobenius-detailed.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-a1-finite-boundary-weights.proof.md", "place": "First sentence and displayed evaluation formula, corrected geometric-stalk interpretation"}.

### Original step 3 — lem-a1-finite-geometric-sections-and-point-orbits

Regroup the finite sum of step 1 by the fibres $P_x$. For the underlying degree-zero complex $M=\operatorname{For}\mathcal G$, [def-weil-local-frobenius-trace] interprets $\mathcal G_z$ as $\mathrm H^0(\operatorname{Fib}_s(Lz^*M))$ at a common finite coefficient-field stage and states that this is finite-dimensional. A finite direct sum of these spaces is finite-dimensional, so $V$ is finite-dimensional. Scalar extension from that stage to $\Qlb$ preserves this assertion.

Cited nodes: def-weil-local-frobenius-trace.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-a1-finite-boundary-weights.proof.md", "place": "First sentence and displayed evaluation formula, corrected geometric-stalk interpretation"}.

### Original step 4 — lem-a1-proper-weil-iterate-germ-formula

Work at a common field stage $E$, and put $C=R\Gamma_c(Z,-)$, $P=Lg^*$, $P_r=L(g^r)^*$. By [def-weil-global-geometric-frobenius], $F=C(\theta)\tau_{c,M}$. The transports are natural in every underlying derived morphism by [def-weil-frobenius-cohomology-transport]. Before replacing $P^r$ by $P_r$, induction gives
$$F^r=C(\theta\circ P\theta\circ\cdots\circ P^{r-1}\theta)\circ\tau_{c,P^{r-1}M}\circ\cdots\circ\tau_{c,M}.$$
The base $r=1$ is the definition. For the induction step, expand $F\circ F^r$ and move $\tau_{c,M}$ past the morphism $C(\theta\circ\cdots\circ P^{r-1}\theta)$ by naturality; the new sheaf-map factor is $\theta\circ P(\theta\circ\cdots\circ P^{r-1}\theta)$. Under the associative comparison of [lem-pod-integral-pullback-composition], rationalized as in the local-operator definition, this is $\theta^{[r+1]}$ of [def-weil-local-frobenius-trace]. Thus
$$F^r=C(\theta^{[r]})\circ\tau^{[r]}_{c,M},$$
where $\tau^{[r]}$ is the iterated transport of [lem-a1-proper-sections-semilinear-germs]. This induction uses no assertion about reduction of a rational Weil isomorphism to an invertible lattice map.

Cited nodes: def-weil-global-geometric-frobenius, def-weil-frobenius-cohomology-transport, lem-pod-integral-pullback-composition, def-weil-local-frobenius-trace, lem-a1-proper-sections-semilinear-germs.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-a1-finite-boundary-weights.proof.md", "place": "First sentence and displayed evaluation formula, corrected geometric-stalk interpretation"}.

### Original step 5 — lem-a1-proper-weil-iterate-germ-formula

Let $z_r=T^rz$. Apply [lem-a1-proper-sections-semilinear-germs] to $Z_0,M,r,z$. The naturality of the derived germs, defined by the counit in that lemma, applied to $\theta^{[r]}:P_rM\to M$, and the identity of step 4 give
$$e_zF^r=\mathrm H^0\!\left(\operatorname{Fib}_s(Lz^*\theta^{[r]})\circ\operatorname{Fib}_s(b_{r,z,M})\circ I_{Lz_r^*M}^{[r]}\right)e_{z_r}.$$
Here $b_{r,z,M}$ uses $g^rz=z_rh^r$; the lemma explicitly identifies evaluation after the specified compact-support exchange and point transport with this composite. For $r=1$ all three maps in parentheses are isomorphisms: the Weil structure is an isomorphism, $b_{1,z,M}$ is a pullback-composition comparison, and point transport is invertible by [lem-weil-frobenius-cohomology-transport-iso](1). Thus the only nonzero block in output stalk $z$ is the isomorphism from input stalk $Tz$. Consequently $F$ preserves each $V_x$ and permutes its stalk summands in the cycle $T^{-1}$. All formulas extend from the common stage to $\Qlb$.

Cited nodes: lem-a1-proper-sections-semilinear-germs, lem-weil-frobenius-cohomology-transport-iso.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-a1-finite-boundary-weights.proof.md", "place": "First sentence and displayed evaluation formula, corrected geometric-stalk interpretation"}.

### Original step 6 — lem-a1-proper-weil-iterate-germ-formula

Fix $x$ and $z\in P_x$, and take $r=d_x$ in step 5. Step 2 gives $z_r=z$ and the equality of scheme maps $g^rz=zh^r$. Consequently the coefficient of $e_z$ in that formula is
$$\mathrm H^0\!\left(\operatorname{Fib}_s(Lz^*\theta^{[r]})\circ\operatorname{Fib}_s(b_{r,z,M})\circ I_{Lz^*M}^{[r]}\right).$$
The three arrows, in this order, are the final stalk map, middle composition comparison, and initial iterated point transport in the displayed definition of $F_{x,z}$ in [def-weil-local-frobenius-trace]. They use the same specified pullback-composition comparisons; in particular the return is $g^rz=zh^r$, not $g^rz=z$. The coefficient therefore is $F_{x,z}$ by that definition, proving $e_zF^{d_x}=F_{x,z}e_z$.

Cited nodes: def-weil-local-frobenius-trace.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-a1-finite-boundary-weights.proof.md", "place": "First sentence and displayed evaluation formula, corrected geometric-stalk interpretation"}.

### Original step 7 — parent assembly step 4

A permutation of a finite collection of summands, with an isomorphism on every block, is invertible: use the inverse permutation and the inverse stalk maps. Conjugating by $e$ proves that $F$ is an automorphism of $V$. The naturality of $e$ was obtained in step 1. For empty $Z_0$ both sides are zero and this is the unique automorphism of the zero space.

Cited nodes: .

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-a1-finite-boundary-weights.proof.md", "place": "First sentence and displayed evaluation formula, corrected geometric-stalk interpretation"}.

## Search results and duplicate audit

Whole-DAG searches used 03QP, geometric lifts, finite geometric sections, semilinear, Frobenius orbit, iterated transport, and the exact blueprint tag. Whole-blueprint searches with blueprint_refs.py for finite Weil sections, Frobenius transport, finite geometric, semilinear, geometric lifts, global Frobenius powers and 03QP found no exact statement. Existing rational finite direct image and semilinear germs are retained as black-box inputs for the future splits, not recreated. Actual Mathlib hits were read: SpecToEquivOfField (ResidueField.lean:346) describes scheme points by residue embeddings but neither evaluates constructible sheaves nor proves the orbit cycle; finite-fibre instances only give finiteness; ring Frobenius/isocrystal identities are different objects. Both new nodes have two semantic phrasings, LeanSearch, Loogle and source grep recorded exactly as run.

## Not duplicates

lem-a1-finite-geometric-sections-and-point-orbits vs lem-sbc-closed-coefficient-source-transition-iso: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns For a closed immersion i:Z→T and a sheaf G on Z, the canonical source transition with coefficient i_*G is an isomorphism in every degree q.. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-sbc-closed-coefficient-target-transition-iso: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns For a Cartesian square Y→T over X→S, a closed immersion i:Z→T, and the corresponding Cartesian square YZ→Z, the canonical target transition is an isomorphism with coefficient i_*G.. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-zl-finite-compactification-stalk-return: that statement assumes finite Weil presentations of an R0 compactification pushforward and constructs jointly injective evaluations intertwining return operators; this package assumes no Weil structure, constructs an isomorphism for all finite geometric sections, and counts all point orbits.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-fd-finite-etale-adic-cohomology: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Finite etale direct image and ordinary adic cohomology. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-trf-finite-base-strict-localization: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Finite base change of strict localizations along a finite morphism. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-trf-derived-sections-finite-pushforward-modules: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Derived sections through finite pushforward for module sheaves. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs sk-lem-geo-finite-boundary: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Detection by a proper direct image. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-zl-finite-adic-direct-image: finite adic direct image gives the rational restriction-map isomorphism for arbitrary finite maps, but does not count closed-point lifts over finite fields, identify the moving-point cycles, or assert finite-dimensional compact sections with this closed-point indexing; the old finite-image application is retained in the report for the future worker.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-a1-finite-weil-sections-decomposition: the new package has no Weil structure, global F, block permutation on sheaves, or local return operator; it isolates original steps 1-3 as expressly required by the re-split order.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-a1-finite-etale-weil-fibre-comparison: that statement compares a finite-etale pushforward stalk with a fibre over a closed target point and its relative Weil structure; this package allows a nonreduced finite scheme, has no Weil structure and proves closed-point geometric orbit indexing.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-finite-pushforward-unit-edge-compatibility: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Base-changed edge maps carry the unit of a composite to the pullback. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-finite-split-pieces-cofinal: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Split pieces compute each fibre stalk. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs sk-lem-pbc-finite: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Finite morphisms. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-finite-surjective-unit-mono: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns The unit along a finite surjective morphism is a monomorphism. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-sets-finite-pushforward-stalk-map-bijective: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Restriction map bijectivity assuming finite fibre. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-sets-finite-pushforward-stalk-fiber-finite: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Finite geometric fibre of a finite morphism. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs g1-finite-pushforward-pullback-comparison: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns FinitePushforwardPullbackComparison. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-finite-pushforward-cohomology: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Finite direct image does not change etale cohomology (edge map). It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-finite-split-sections-product: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Sections on split neighbourhoods are products of piece sections. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-finite-stalk-formula-restriction: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns The finite stalk formula is given by the restrictions of germs. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-sets-finite-pushforward-stalk: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Stalk of a finite direct image of an etale sheaf of sets. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs g1-finite-pushforward-cohomology-comparison: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns FinitePushforwardCohomologyComparison. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-finite-split-neighbourhoods-cofinal: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Cofiltered split neighbourhoods compute the base stalk. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs g1-finite-pushforward-coefficient-control: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns FinitePushforwardCoefficientControl. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-sets-pushforward-stalk-strict-henselization: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Stalk of a direct image of sets as sections over the strict henselization. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-sepclosed-finite-extension-unique-embedding: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns A finite extension of a separably closed field is separably closed and embeds uniquely into an algebraically closed field. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-curve-assertions-dense-open: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns The eight curve assertions and restriction to a dense open. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-weil-pbc-curve-assertions-finite-pushforward: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns The eight curve assertions pass to finite direct images. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-asd-supported-kummer-scalar-source: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Derived scalar extension of a closed supported constant sheaf. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-asd-supported-kummer-scalar-derived-units: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Derived universal properties of supported scalar maps. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-asd-supported-kummer-scalar-maps: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Normalized supported scalar maps. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-fin-finite-direct-image-counit-epi: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns The finite direct-image counit is epimorphic for module sheaves. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-pur-compact-point-source-normalization: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Section-one normalization of compact cohomology of a closed rational point. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-finite-geometric-sections-and-point-orbits vs sk-lem-curve-finite-support: the new package includes rational/common-stage canonical compact evaluation together with closed-point embedding counts and the semilinear cyclic orbit, with no Weil structure; the existing statement concerns Finite-support sheaves and finite maps. It does not state this combined finite-field indexing and normalized evaluation result.

lem-a1-proper-weil-iterate-germ-formula vs lem-a1-proper-sections-semilinear-germs: the existing theorem concerns M with no Weil structure and the identity e_z^(P_r M) tau^[r] = Fib(b) I e_(T^r z); the new statement adds theta, proves the actual power of the global Weil operator, and identifies the resulting returning-point coefficient with the local Weil operator. The existing theorem remains a proof-plan input.

lem-a1-proper-weil-iterate-germ-formula vs lem-trf-rational-global-frobenius-powers: that theorem assumes a rationalized integral object with ctf reductions and specified direct transports and has no germ formula. The new theorem uses the proper-scheme counit germ for an arbitrary rational/common-stage Weil complex, the iterated degree-one transports, and an explicit moving-point/local-return identity.

lem-a1-proper-weil-iterate-germ-formula vs lem-trf-compact-weil-cocycle-endomorphism-recurrence: that statement is finite-torsion, strict-Weil and direct-transport recurrence, without point germs; the new package is rational/common-stage, permits any rational Weil isomorphism, and has moving-point coefficients.

lem-a1-proper-weil-iterate-germ-formula vs lem-trf-compact-frobenius-transport-composition: this is finite-coefficient direct-transport composition with no Weil structure; the new package must combine rational theta iterates with counit evaluation and local-return normalization.

lem-a1-proper-weil-iterate-germ-formula vs lem-trf-frobenius-transport-induction: that is an abstract categorical comparison of direct and iterated transports and has no Weil map, germ, or local Frobenius. It does not supply the new statement.

lem-a1-proper-weil-iterate-germ-formula vs lem-a1-lisse-sections-stalk-evaluation: the existing result assumes lissity, gives finitely many jointly injective evaluations in ordinary H0, and only a closed-point return identity. The new package allows bounded constructible complexes and all moving geometric points, supplies the derived power and germ identities, and makes no finite-family injectivity assertion.

lem-a1-proper-weil-iterate-germ-formula vs lem-zl-weil-constant-extension-frobenius: that concerns lisse sheaves, scalar extension of the finite base field and cohomological/local conjugacy; it does not state this proper derived germ coefficient formula for general constructible Weil complexes.

lem-a1-finite-geometric-sections-and-point-orbits vs lem-a1-proper-weil-iterate-germ-formula: the first package is finite-scheme geometry plus degree-zero evaluation with no Weil structure; the second is proper-scheme derived Weil-operator evaluation with no finite-point or evaluation-isomorphism conclusion.
