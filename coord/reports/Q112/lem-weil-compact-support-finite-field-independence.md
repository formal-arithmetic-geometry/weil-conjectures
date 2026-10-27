# Q112 repair: lem-weil-compact-support-finite-field-independence

Files written, all in `dag/nodes/sec-smooth-purity/`:

- `lem-weil-compact-support-finite-field-independence.json`: repaired split; its statement, statement dependencies, imported fields and Lean record are retained.
- `lem-weil-compact-support-normalized-scalar-isomorphisms.json` (A): statement-only existence and normalization; the returned statement and its real search records are retained unchanged; no Mathlib match.
- `lem-weil-compact-support-normalized-scalar-descent.json` (B): statement-only unit and tower equations for the prescribed normalized maps, with every pair-category, inverse and independence clause removed; no Mathlib match.
- `lem-weil-common-stage-inverse-representatives.json` (C): statement-only generic lifting of a specified isomorphism and its inverse to one stage, including eventual inverse equations; no Mathlib match.

`citations.json` contains a verified verbatim statement quotation for every node cited by every item step. Reports, original arguments and queries from the returned attempt are retained in the sandbox. `returned-report.md` is the historical report, not the present review; its superseded two-node design is replaced by this report. No attachments. WANTED: none. Nothing required for this stage-1 split remains unfinished. A, B and C are deliberately unsplit obligations for later workers, with empty proofs and proof dependencies. No Lean was written, compiled or built.

## Repair of every returned point

The returned two-node design was not a valid redistribution. I compared all sandbox node fields with the current repository item and the returned copies. The live item still has the original four steps and the released 4531-character re-split order. Only proof, proof dependencies, proof origin and split report differed in the returned item; the statement and Lean record agree. I ran the required dry run before changing the existing split: it exited OK at `21a3eace5c7`. That mechanical success did not resolve the mathematical return.

1. D1/D2 and unequal distribution: A is preserved. B now asserts only the unit and tower equations; it contains no output pair, descended functor, representative-independence or parent conclusion. C separately states the generic inverse-representative fact. The item constructs its own comparison by applying the descended functor to the given gamma and gives the two inverse cancellations explicitly. Thus none of A, B, C restates the requested independence of compact-support values. A constructs specified maps, B proves equations for those maps, C lifts specified arrows in arbitrary diagrams; all are independently stated work items. Their lengths reflect their hypotheses, not an allocation of the whole argument to B.

2. C5 generic descent: item step 2 now directly cites `lem-sbc-coherent-pair-functor-descent`, with an explicit `split_report.tool_uses` declaration. The source's `prop-weil-pbc-descent-functors` route is realized by its already declared generic tool, not a second compact-support descent theorem. The PBC proposition itself quantifies the different PBC coefficient categories. I do not assert an unproved equivalence with the present raw categories. The generic theorem quantifies arbitrary additive stage categories and therefore gives its very same formula on the actual framework stages. Its identity/composition and representative-independence statements carry precisely the old steps 3–4's generic work.

3. The old one-stage inverse clause is isolated as C, independent of compact support or scalar-comparison beta maps. It remembers the actual classes gamma and gamma inverse, not just existence of an unrelated isomorphism of the lifted objects. Its optional prescribed representatives clause explicitly forces the two original inverse representatives to satisfy their equations after enlargement. This is the generic finite-equation argument of the original step 2.

4. C5 omitted duplicate candidate: I opened `lem-pur-compact-support-integral-coefficient-comparison` and its specified domain and tower equation. The Not duplicates section now compares both A and B against it, and also compares B with its stricter composition auxiliary. The existing result is valuable source material but cannot be specialized to arbitrary K0 and all bounded constructible inputs: its hypotheses fix the algebraic closure of a finite field, separated schemes and the uniform finite-Tor domain. No argument silently drops those hypotheses.

The final assembly has four short steps, 2096 characters altogether, and the longest is 694 characters. The complete old four-step argument is reproduced below without shortening. Its normalized existence lives in A; its normalized beta coherence lives in B; its simultaneous inverse lifting lives in C; its transport/naturality cancellation and equality-of-representatives conclusion live in the existing generic descent theorem, which the item now cites. The item itself retains the explicit finite-stage inverse cancellation and the application to the specified presentations.

## Sources and searches read

I read `GOAL.md`, the three levels in SETUP, the worker brief, stage 1, the chapter and unit records, the released repair note and sections B–E of delivery-errors in both retained versions. The chapter/unit route is unchanged. This item is not the unit's key statement, so no unit realization file is edited.

For the item and A/B I read the whole master node and the current main-20261015 statement/proof under `sec-six-functors-basics/sk-thm-sf-pf-field/`. Their proof paragraph is identical: finite scalar compatibility, then descent of functors. I retained the exact normalized strict-tower construction in A after reading the statements of `def-weil-compact-support-finite-action`, `def-weil-compact-support-coefficient-action`, `def-weil-mixed-reduction-unit`, `def-weil-integral-scalar-extension`, `def-weil-rationalization-karoubi` and `def-weil-integral-rational-qbar-compact-support`. The full homotopy-category normalization, including the prescribed Roos map, is part of the given construction for B. Equality of arbitrary derived maps is not inferred merely from equality of cohomology or of finite reductions.

For C I read the finite common-stage principle in `literature/blueprint/slopmaster2/src/version/sketch/32_smooth_base_change.tex`, lines 1340–1353: any finite list of equations holds after some further coefficient extension. I read the pseudocone functor proposition and pair universal property in `42_qbarl_triangulated_colimit.tex`, around lines 810–854, and the whole statement of `lem-sbc-coherent-pair-functor-descent`. C is an agent-stated generic isolation of the finite common-stage argument; the blueprint does not supply a named generic inverse lifting node. No SGA source is used. No Stacks tag is claimed for these complete varying-coefficient assertions: none of the source paragraphs supplies such a tag.

I searched the whole DAG for the two new coefficient assertions and for inverse representatives, eventual inverse equations, `exists_iso_toStage` and common-stage isomorphisms. I ran blueprint_refs searches including `inverse representative`, `common-stage isomorphism`, `normalized scalar`, `compact-support coefficient`, `inverse` and `common-stage`, and read the close candidate statements discussed below. The ancestor is the item itself, with empty via list. The new inverse-representative id was absent. The returned A/B searches were read from searches.jsonl and their original outputs; A's question is unchanged, so its queries were not fabricated or repeated. B's narrower question and C's new question each received two distinct semantic phrasings, Loogle, LeanSearch and source grep through the authorized msearch command. Extra targeted grep of CategoryTheory for StageSystem/PairCategory/inverse representatives found zero hits. The exact commands and actual outcomes are preserved in the node records and searches.jsonl. Earlier invalid NatIso queries remain recorded as unavailable.

I read the meaningful candidates: Mathlib `Algebra/Category/ModuleCat/ChangeOfRings.lean:954–1008` gives ordinary module scalar units/associators, and `ModuleCat/Pseudofunctor.lean:31–71` packages those into an ordinary module pseudofunctor. Neither constructs or proves equations for these normalized derived compact-support mates. `CategoryTheory/MorphismProperty/Limits.lean:628–650` says a colimit of isomorphisms is an isomorphism within one category; it does not lift an isomorphism in a category-valued colimit to stage arrows. `CategoryTheory/Limits/Indization/Category.lean:291` presents an arbitrary Ind arrow as a natural transformation of diagrams; it neither concerns the pair category nor gives the prescribed inverse equations. Filtered cocone/sup/span lemmas provide only the common-upper-bound ingredient. Thus no new node is a Mathlib leaf.

I also searched the project source for the item tag and concept. No project declaration under WeilConjectures states the item. The recorded `lean/Sheaf/Paper/CompactSupportFiniteFieldIndependence.lean` theorem ends in sorry at line 89. The generic upstream `CategoryTheory.StageSystem.exists_iso_toStage` at `WeilConjectures/CategoryTheory/StageSystem/Restrict.lean:81–102` is sorry-free, but its statement gives only a Nonempty isomorphism between lifted objects, with no equality to the specified gamma and no prescribed representative property. Its proof is useful future material for C, not a declaration stating C. I did not attach its weaker statement as the stronger new node. No compiler was invoked.

## Not duplicates

lem-weil-compact-support-normalized-scalar-isomorphisms vs lem-fix-operation-reduction: the existing broad commutation assertion does not state the full prescribed tensor-unit universal property and chosen derived-limit normalization; A constructs integral comparisons with these required identifications.

lem-weil-compact-support-normalized-scalar-isomorphisms vs lem-finite-compact-support-scalar-comparison: the existing result uses quotients within one coefficient field and positive m <= n; A varies finite coefficient fields and constructs completed integral comparisons with the chosen reduction normalization.

lem-weil-compact-support-normalized-scalar-isomorphisms vs lem-pur-finite-free-compact-scalar: the existing finite-ring result does not construct normalized completed integral comparison maps or identify their raw rationalizations.

lem-weil-compact-support-normalized-scalar-isomorphisms vs lem-pur-compact-support-integral-coefficient-comparison: the existing c is on D^b_ctf over the fixed global finite-field datum, with separated source/target schemes and finite-free cofinal reductions A_(E,n) to A_(F,en); A is for arbitrary K0 and the framework D^b_c functors, with the specified same-index mixed tensor-unit and fixed Roos reduction normalization. The former cannot discharge the latter under the item's hypotheses.

lem-weil-compact-support-normalized-scalar-descent vs lem-pur-compact-support-integral-coefficient-comparison: the existing node indeed gives identity and tower coherence, but for the fixed finite-field datum and finite-Tor domain with its c comparisons. B proves those equations for the prescribed framework normalization on arbitrary K0 and all its D^b_c inputs, not by dropping those extra hypotheses or assuming c equals beta.

lem-weil-compact-support-normalized-scalar-descent vs lem-pur-compact-support-strict-scalar-composition: that auxiliary assumes the same finite-field/finite-Tor and finite-free retained-tower setting. B concerns the arbitrary-field framework functors, mixed-unit normalization and their raw rationalizations. Its coherence cannot be obtained by directly specializing that narrower theorem.

lem-weil-compact-support-normalized-scalar-descent vs lem-sbc-coherent-pair-functor-descent: B concludes the unit/tower hypotheses for prescribed comparisons; the generic theorem assumes those hypotheses and concludes descent. B now contains none of the generic theorem's conclusions. The item explicitly cites the generic theorem as a tool.

lem-weil-compact-support-normalized-scalar-descent vs prop-weil-pbc-descent-functors: the PBC proposition assumes coherent comparisons on its PBC categories and concludes descent. B proves coherence of framework compact-support comparisons, without asserting descent. The generic categorical core of the PBC proposition is reused by the item.

lem-weil-compact-support-normalized-scalar-descent vs lem-cbc-rational-compact-support-coefficient-coherence: the latter works with the completed/raw PBC categories, compact-support base-change square and its exchange normalization; B concerns the specified framework scalar comparisons. No equivalence of these coefficient categories is assumed.

lem-weil-common-stage-inverse-representatives vs lem-sbc-common-stage-inverse-through-karoubi: that node assumes an inverse at a raw stage and propagates it through two Karoubi layers and a compatible natural transformation. C starts with a specified isomorphism of the raw pair category and lifts its two arrows to a stage; it assumes no inverse at an initial stage and has no Karoubi layers.

lem-weil-common-stage-inverse-representatives vs lem-weil-pbc-distinguished-diagram-lifting: the existing result lifts finite diagrams/equations and triangles of the PBC categories of a noetherian finite-dimensional scheme, with specified exact structures. C applies to arbitrary additive category diagrams with no scheme and no triangulation, and remembers the prescribed inverse representatives. Its genericity cannot be obtained by specializing the PBC geometric assertion.

lem-weil-common-stage-inverse-representatives vs lem-pur-common-stage-finite-hom-lifting: that node concerns Hom bijections of fully faithful geometric restriction families over the fixed finite-field datum; C assumes no restriction family or full faithfulness and concludes eventual inverse equations for a specified pair-category isomorphism.

lem-weil-common-stage-inverse-representatives vs lem-sbc-coherent-pair-functor-descent: the existing statement defines the pair categories and functor descent from coherent functors. It does not state that a specified pair-category isomorphism and its prescribed inverse representatives become literal inverses at one stage. C isolates that finite-equation lifting argument requested in the return.

There is no new same-Stacks-tag pair: the new nodes carry no asserted Stacks tag. These searches reused the close-node list and actual query results of the returned attempt and added the omitted integral-comparison candidate. No second descent or functor.mapIso node is created.

## Review by Q112

I checked each item step against the actual cited statements, with the sources and all three new statements open. The hypotheses remain K0 any field, ell invertible in K0, finite-type X and Y, separated finite-type K0-morphism f, a fixed coefficient algebraic closure, E contained in L, and the two specified representing isomorphisms. No properness, smoothness, geometric finite-field structure or finite-Tor assumption was added. One fixed compactification is used throughout. The statements and formulas are in the actual derived categories and raw Hom localizations.

Step 1 uses A exactly for existence, invertibility and normalization of the integral b and rational beta; B exactly for the displayed unit/tower equations, not for any independence assertion; and scalar-extension-composition exactly for the scalar associator and identity compatibility. The beta direction is T^Y G_A to G_B T^X, which makes all three factors of the later formula type-correct. A remains a substantial construction problem. B requires A's full fixed realization, not an arbitrary family of isomorphisms with equal reductions. The new B is restricted to equations only, as the return asks.

Step 2 uses the generic descent theorem's stated functor formula and stated independence of field and representative. Its hypotheses were checked: the rational stages are additive from rationalization; their transition functors are additive; the finite compact-support functors retain additivity by finite-action's integral linearity and Hom tensor construction; the scalar associators are the canonical ones. Identity transitions in the generic statement are literal identities, whereas framework scalar extension has a canonical unit. The assembly explicitly normalizes this: T'_(B/A)=T_(B/A) for proper inclusions and T'_(A/A)=1; use the original units to identify T' and T, and conjugate each comparison/associator by those identifications. At repeated indices the unit laws cancel those identifications; the usual coherent tensor associators give the pentagon. In the representative formula the same endpoint units cancel, recovering the original beta conjugation. There is no changed coefficient category or Karoubi envelope. Only the additive part of descent is needed for the item, so no unproved shift/exactness assertion is taken from a definition. The stated generic theorem is a declared tool use carrying the blueprint's descent-of-functors step.

Step 3 uses C exactly for u,v representing this gamma and its inverse with both inverse equations at the same stage; it does not suppose the two presentations are already isomorphic over L. The auxiliary M0 can contain any prescribed initial field. It applies to the same normalized diagram as step 2, and the unit conjugations carry its equations back to the literal framework representatives. The functor of step 2 then supplies the maps w and z. The two explicit cancellations use only natural-isomorphism inverses and functoriality. The compact-support definition's statement identifies the endpoints with the two requested displayed values. I verified their source and target: b_E starts at T^Y_(M/E)G_EK_E, G_M(u) goes to G_MT^X_(M/L)K_L, and b_L inverse ends at T^Y_(M/L)G_LK_L.

Step 4 is elementary after step 2: apply the already defined functor to the fixed arrow alpha_L inverse alpha_E. Its stated representative independence gives precisely independence from the auxiliary stage/maps. The cocycle is the written cancellation of alpha_B and its inverse, transported by functoriality. No new compact-support node asserts the parent conclusion. Each uses entry has a verbatim statement quote in citations.json. Proof dependencies equal the union of uses. No non-elementary fact about arbitrary category-valued filtered colimits is silently imported from a set-valued colimit theorem.

For C, the source finite common-stage principle confirms the intended argument: represent the two given arrows, transport them to one upper field; use equality of each composite class with an identity to obtain two further equality witnesses; dominate both witnesses and any M0 to make both equations hold literally. Transition functors and associator conjugations preserve the equations. This is several separate lifts/equality witnesses, not a claim that a transition functor is faithful. Its full generic statement is deliberately separate per the explicit return instruction. The existing sorry-free exists_iso_toStage theorem lacks equality to the given arrows in its conclusion, so it is not an attachment for C's stronger statement.

Small cases: with E=L or repeated tower fields, B's unit equation gives the expected unit-normalized comparison and the inverse cancellation still works. Zero objects and empty schemes impose no nonzero/nonempty hypothesis. C allows nonfaithful transitions and enlarges the field before the inverse equations; it does not force them at M0. For an identity gamma the equations allow identity representatives, but an arbitrary initially prescribed representative may need enlargement, which C permits. Ramification is handled by the actual induced quotient map O_A/(varpi_A^(n+1)) to O_B/(varpi_B^(n+1)): the inclusion exists because varpi_A^(n+1) belongs to varpi_B^(n+1)O_B. No same-exponent finite-flat assertion is used. The map normalization is the entire homotopy-category specification, so no equality of derived maps is justified just by equal finite cohomology maps.

I checked delivery-errors B–E against these files. The new nodes introduce their own objects, retain definitions via stated dependencies, and are statement-only. Neither scalar existence nor scalar coherence is an elementary two-line consequence; the inverse lifting is retained as an independent generic obligation because the return explicitly requests it. No new statement reproduces the parent or one of its output independence clauses. All non-elementary assembly inputs are cited, and the generic off-unit tool is declared. The long historical proof is handoff material below; no current step exceeds 2000 characters. The remaining mechanical checks are the prescribed server dry run and delivery.

## Handoff: complete original argument retained verbatim


### Returned step 1

For $Z=X,Y$, write $T^Z_{B/A}$ for the rational scalar extension of [def-weil-rationalization-karoubi], and write $F_A=Rf_{!,A}$ for the rational compact-support operation of [def-weil-integral-rational-qbar-compact-support]. Use the coefficient comparisons of [lem-fix-operation-reduction], on the stated bounded constructible domains, to obtain natural isomorphisms
$$\beta_{B/A}:T^Y_{B/A}F_A\xrightarrow{\sim}F_BT^X_{B/A}.$$
Here only finite extensions of coefficient fields are used; the notation $-\otimes_A\Qlb$ will subsequently mean a pair in the common-stage category. Let $a^Z_{N,M,A}:T^Z_{N/M}T^Z_{M/A}\xrightarrow{\sim}T^Z_{N/A}$ be the scalar-extension associator of [lem-weil-scalar-extension-composition]. The compatibility with tensor associativity asserted in [lem-fix-operation-reduction] gives the equation
$$\beta_{N/A,K}=F_N(a^X_{N,M,A,K})\circ\beta_{N/M,T^X_{M/A}K}\circ T^Y_{N/M}(\beta_{M/A,K})\circ(a^Y_{N,M,A,F_AK})^{-1}.$$
The identity-extension comparison is the corresponding unit map. These are comparisons for the actual completed-integral scalar extensions followed by raw Hom scalar localization, rather than for the ambient derived category of discrete $\Qlb$-module sheaves.

Cited statements: def-weil-rationalization-karoubi, def-weil-integral-rational-qbar-compact-support, lem-fix-operation-reduction, lem-weil-scalar-extension-composition.

### Returned step 2

In the common-stage category of [def-weil-algebraically-closed-coefficients], let $\gamma=\alpha_L^{-1}\alpha_E:(E,K_E)\xrightarrow{\sim}(L,K_L)$. Represent $\gamma$ and $\gamma^{-1}$ over common finite coefficient fields, then enlarge to a finite $M\supset L$ on which both compositions are identities. This is possible because equality of two morphism representatives means equality after a further finite extension, and a compositum dominates the finitely many fields needed for the two equalities. With the associators of [lem-weil-scalar-extension-composition] inserted in the transport maps, we therefore have inverse maps
$$u:T^X_{M/E}K_E\xrightarrow{\sim}T^X_{M/L}K_L,\qquad v=u^{-1}$$
at this single stage. No isomorphism $T^X_{L/E}K_E\cong K_L$ at $L$ is assumed: the supplied common-stage identification may require enlarging $L$.

Cited statements: def-weil-algebraically-closed-coefficients, lem-weil-scalar-extension-composition.

### Returned step 3

Define at stage $M$
$$w_M=\beta_{M/L,K_L}^{-1}\circ F_M(u)\circ\beta_{M/E,K_E}:
T^Y_{M/E}F_EK_E\longrightarrow T^Y_{M/L}F_LK_L.$$
Define $z_M=\beta_{M/E,K_E}^{-1}\circ F_M(v)\circ\beta_{M/L,K_L}$. Then $z_Mw_M=\beta_{M/E,K_E}^{-1}F_M(vu)\beta_{M/E,K_E}=1$, and $w_Mz_M=\beta_{M/L,K_L}^{-1}F_M(uv)\beta_{M/L,K_L}=1$. Passing to morphism classes in [def-weil-algebraically-closed-coefficients] preserves these equations, since its composition is represented at one common stage. Thus $[M,w_M]$ is an isomorphism from $(E,F_EK_E)$ to $(L,F_LK_L)$. By [def-weil-integral-rational-qbar-compact-support], these are precisely the two objects displayed in the statement. This uses the finite-stage functors and the coefficient comparisons of [lem-fix-operation-reduction], without identifying the coefficient categories with a different ambient sheaf category.

Cited statements: def-weil-algebraically-closed-coefficients, def-weil-integral-rational-qbar-compact-support, lem-fix-operation-reduction.

### Returned step 4

It remains to verify that the isomorphism is canonical relative to $\alpha_E,\alpha_L$. If $M\subset N$, the common-stage transport of $u$ is
$$u_N=a^X_{N,M,L,K_L}\circ T^X_{N/M}(u)\circ(a^X_{N,M,E,K_E})^{-1}$$
by [def-weil-algebraically-closed-coefficients] and [lem-weil-scalar-extension-composition]. For $A=E,L$, abbreviate $x_A=a^X_{N,M,A,K_A}$, $y_A=a^Y_{N,M,A,F_AK_A}$, $b_A=\beta_{M/A,K_A}$ and $c_A=\beta_{N/M,T^X_{M/A}K_A}$, and put $S=T^Y_{N/M}$. Step 1 says $\beta_{N/A,K_A}=F_N(x_A)c_AS(b_A)y_A^{-1}$. Hence substitution of $u_N=x_LT^X_{N/M}(u)x_E^{-1}$ gives
$$w_N=y_LS(b_L)^{-1}c_L^{-1}F_N(T^X_{N/M}u)c_ES(b_E)y_E^{-1}.$$
Naturality of $\beta_{N/M}$ at the map $u:T^X_{M/E}K_E\to T^X_{M/L}K_L$ is precisely
$$F_N(T^X_{N/M}u)c_E=c_LS(F_Mu).$$
Substituting this equality cancels $c_L^{-1}c_L$ and gives
$$w_N=y_LS(b_L^{-1}F_M(u)b_E)y_E^{-1}=a^Y_{N,M,L,F_LK_L}\circ T^Y_{N/M}(w_M)\circ(a^Y_{N,M,E,F_EK_E})^{-1}.$$
Consequently $w_N$ represents the same morphism as $w_M$. For two representatives of the fixed morphism $\gamma$, choose a further stage where their transports agree, as in the equality clause of [def-weil-algebraically-closed-coefficients]; the displayed formula makes their output representatives equal there. This proves independence of every auxiliary stage and representative. Identity input comparisons give identity output comparisons, and composable comparisons give composable outputs, because in the product $\beta^{-1}F(v)\beta\,\beta^{-1}F(u)\beta$ the middle factors cancel and $F(v)F(u)=F(vu)$. This is the descent argument in the imported proof, written within the present pair categories.

Cited statements: def-weil-algebraically-closed-coefficients, lem-weil-scalar-extension-composition, lem-fix-operation-reduction.

