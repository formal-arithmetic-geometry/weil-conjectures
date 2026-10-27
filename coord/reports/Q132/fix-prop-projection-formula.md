# Worker report

## Files written

- `dag/nodes/sec-six-functors/fix-prop-projection-formula.json`: same statement, nine assembly steps; 2431 proof characters.

- `lem-sf-concrete-integral-projection-cone`: statement, unsplit; no Mathlib match found. Source and blueprint provenance are recorded; proof and proof_deps are empty.
- `lem-sf-concrete-projection-field-descent`: statement, unsplit; no Mathlib match found. Source and blueprint provenance are recorded; proof and proof_deps are empty.
- `lem-sf-concrete-projection-reduction-square`: statement, unsplit; no Mathlib match found. Source and blueprint provenance are recorded; proof and proof_deps are empty.
- `lem-sf-projection-compatible-triangle-assembly`: statement, unsplit; no Mathlib match found. Source and blueprint provenance are recorded; proof and proof_deps are empty.
- `lem-sf-projection-integral-coherence-realization`: statement, unsplit; no Mathlib match found. Source and blueprint provenance are recorded; proof and proof_deps are empty.
- `lem-sf-projection-refinement-descent`: statement, unsplit; no Mathlib match found. Source and blueprint provenance are recorded; proof and proof_deps are empty.
- `lem-sf-projection-weil-tensor-domain-bridge`: statement, unsplit; no Mathlib match found. Source and blueprint provenance are recorded; proof and proof_deps are empty.

## Attachments

None. The upstream WeilConjectures search found generic projection helpers but no declaration proving the complete item. In the live module `lean/Sheaf/Paper/CompactSupportProjectionFormula.lean`, `compactSupportProjectionFormula` at line 111 ends in `sorry` at line 136. It is not a finished attachment. Its finite/coefficient and Weil declarations likewise do not justify bypassing this stage-1 repair.

## Wanted literature

None. The current blueprint and the Stacks source needed here are present. No SGA source is used.

## What was wrong and what changed

The return asks to distribute the 16,792-character concrete argument, keep the statement unchanged, add at least five comparable statement-only tasks, and keep the assembly under 3,000 characters. This repair creates seven tasks, roughly 1,800–2,330 characters apiece. A proposed eighth task was removed after the source-tag search found the existing general ringed-topos composition identity `lem-sfb-ringed-projection-tensor-composition`. The assembly cites that statement directly. The original fifteen paragraphs are reproduced verbatim below, with their destinations; nothing was silently discarded. Finite witnessed invertibility remains a direct application of the existing finite projection theorem, and proper coincidence and inversion of an equivariant isomorphism remain explicit assembly steps.

The sandbox initially contained only dispatcher marker files, with no node, report, citations or previous search log. I copied the live item whose fifteen step lengths match the returned entry. Its maintainer-owned fields, Lean records, inherited route error and existing source statements were retained. No repository or launcher file was written, and no compiler, Lake or build tool was run.

The inherited route error remains material: `def-sf-datum` assumes projection invertibility (A3) and coefficient compatibility (A5). Its finite-Tor input domain also omits the allowed finite-level first input A/(t) over A=R/(t²). The concrete operation datum of this item does not assume the desired theorem. Thus the abstract adic/field/coherence statements requiring that stronger datum cannot replace this argument. This is a preserved earlier correction, not a new change to the target statement.

## Work remaining

The seven new nodes deliberately have no proofs. Their seven independent arguments are the stage-1 work made available to other workers. This delivery supplies the parent assembly, not a Lean proof or an axiom audit.

## Not duplicates

lem-sf-concrete-projection-reduction-square vs prop-sf-pf-reduction: the existing node assumes the axiom-bearing def-sf-datum and asserts invertibility equivalence; the new node identifies the actual concrete mate square, its two vertical composites and the tensor Tor domain without that datum.
lem-sf-concrete-projection-reduction-square vs lem-fix-compact-support-coefficient-change: that node gives the compact-support coefficient arrow and counit compatibility, not the full tensor/pullback projection square and its domain computation.
lem-sf-concrete-projection-reduction-square vs lem-sf-pf-coefficient-realization-transport: that generic statement assumes all invertible primitive comparisons on a closed domain; the new statement verifies the finite-Tor concrete domain and identifies the actual comparisons.
lem-sf-concrete-integral-projection-cone vs thm-sf-pf-adic: the latter assumes def-sf-datum and directly concludes an isomorphism; the new statement supplies complete endpoints, uniform bounds and the actual reduced cone, leaving the finite theorem and Nakayama to the parent.
lem-sf-concrete-integral-projection-cone vs lem-pur-compact-support-completed-projection-coherence: that statement is for the completed ordinary direct-image adjunction over constant coefficients; this task includes the concrete compact-support open factor, completed coefficient category and constructible/uniform-Tor cone domain.
lem-sf-concrete-projection-field-descent vs thm-sf-pf-field: the existing statement assumes the axiom-bearing datum and concludes field invertibility; the new task identifies concrete localization/scalar maps and their inverse representatives conditional on an integral inverse, with the tower cocycle.
lem-sf-concrete-projection-field-descent vs lem-pur-compact-support-scalar-projection-identification: the latter treats integral scalar extensions between separated schemes with a fixed compactification; the new task includes raw rationalization and common-stage morphism-class independence and allows nonseparated structure morphisms.
lem-sf-concrete-projection-field-descent vs lem-sf-pf-coefficient-realization-transport: the existing lemma is conditional on supplied comparison data; the new task applies actual localization and field comparisons, verifies cocycles and identifies inverse representatives.
lem-sf-projection-refinement-descent vs lem-sf-proper-open-projection-mate: that statement gives the local square identity for gamma; the new task substitutes the specified theta, verifies the full constructible witness domain with arbitrary K, and descends via the cocycle.
lem-sf-projection-refinement-descent vs lem-pur-system-compactification-pf-substitution: that statement requires separated schemes and normalized finite-Tor system inputs; the new finite-level descent permits nonseparated structure morphisms and arbitrary bounded constructible first input, and only reuses the local system equality.
lem-sf-projection-compatible-triangle-assembly vs lem-sf-composition-projection-mate: the latter assumes the compatible triangle and its normalized compositor; this task constructs such a triangle under the actual finite-type hypotheses and identifies that mate with the independently fixed compact-support compositor on its witnessed domain.
lem-sf-projection-integral-coherence-realization vs lem-sf-integral-compactification-system-realization: that node constructs c_V conditional on intermediate bounds; this task verifies those bounds for the projection/composition/refinement expressions and identifies their actual integral coherence maps.
lem-sf-projection-integral-coherence-realization vs lem-pur-system-level-projection-formula-coherence: the latter is a composition equation before limit on separated schemes; this task verifies full intermediate bounds and identifies the completed integral projection, refinement, proper/open, and nested-composition equations, allowing nonseparated structure morphisms.
lem-sf-projection-weil-tensor-domain-bridge vs lem-wf-tensor-completion-frobenius: that statement supplies Frobenius compatibility once the tensor models are identified; this task verifies coefficient-category and reduction identifications and all constructible operation-output domains before using the conditional Weil-operations theorem.
lem-sf-projection-weil-tensor-domain-bridge vs lem-fix-weil-operations: that node assumes preservation on the underlying domains; the new task supplies those domains and compares the actual ordinary/completed tensor conventions.
lem-sf-projection-refinement-descent vs lem-weil-pbc-etale-open-proper-interchange: the existing statement is an etale bounded-below functor isomorphism for a Cartesian open base-change square; the new statement is the projection/refinement commuting equation on pro-etale constructible inputs, allowing a non-Cartesian refinement.
lem-sf-projection-refinement-descent vs lem-sfb-exact-compactification-unit-composition: the existing statement compares exact-sheaf-functor derived units with a compact-support compositor; it has no tensor, projection component or refinement projection square.
lem-sf-projection-refinement-descent vs lem-sfb-exact-compactification-unit-refinement: the existing statement normalizes a derived unit for an exact sheaf functor along compactification comparison; it does not compare the projection mate at K and at its tensor input.
lem-sf-projection-refinement-descent vs lem-sfb-proper-open-tower-derived-unit: the existing statement is a chain-homotopy comparison between single and successive K-injective derived units on etale sites; it does not give the projection/refinement equation or the arbitrary-first-input pro-etale witness domain.
lem-sf-projection-refinement-descent vs lem-sfb-proper-open-tower-single-unit-formula: the existing statement spells out a localized K-injective single-unit representative; it contains no projection maps or tensor/refinement compatibility.
lem-sf-projection-refinement-descent vs lem-sfb-proper-open-tower-successive-unit-formula: the existing statement spells out a successive-unit representative under hypotheses on a chosen comparison Gamma; it contains no projection square or compactification-independent projection transformation.
lem-sf-projection-refinement-descent vs def-coef-semilinear-proper-open-mate: this defines a semilinear proper/open mate without invertibility or pasting assertions; the new statement gives the projection identity for the specified refinement and its constructible descent domain.
lem-sf-projection-refinement-descent vs def-sf-etale-support-compositor: this defines the canonical etale support compositor from a proper/open tower; it explicitly asserts no further coherence and gives no tensor/refinement projection equation.
lem-sf-projection-refinement-descent vs def-sf-semilinear-proper-open-comparisons: this defines the intrinsic clopen proper/open comparisons and ordinary compositors, without the tensor/projection refinement equation; the new statement substitutes those normalized maps into that equation.
lem-sf-projection-refinement-descent vs lem-sf-ambient-proper-open-pasting: the existing statement proves horizontal and vertical pasting of Gamma itself on ambient ordinary/system categories, but does not compare projection maps or descend them on the full constructible tensor domain.
lem-sf-projection-refinement-descent vs lem-sf-composition-projection-mate: the existing statement relates projections for two composable morphisms using an already chosen compatible triangle; the new statement concerns changing a compactification of a single morphism and verifies its full finite constructible first-input domain.
lem-sf-projection-refinement-descent vs lem-sf-native-weil-open-proper-interchange: the existing statement is an interchange isomorphism in native derived Weil-sheaf categories over algebraically closed coefficients; the new statement is a finite ordinary pro-etale projection/refinement equation, not an equivariant functor interchange.

The refinement source inherits Tags 0F7B and 0F7G from its former step 9; the same-tag comparisons above were read and checked after the first dry run listed them. The proposed 0B56 node was removed as a duplicate. Its existing replacement is cited. The main-20261015 blueprint proof is the common source of the remaining seven tasks, and their provenance names the specific former concrete steps. All-chapter blueprint searches and whole-DAG statement/tag searches were read; same_as is empty because no blueprint node states these technical assertions without the additional datum/domain restrictions above.

## Review by Q132

I read the main-20261015 statement and proof of fix-prop-projection-formula, its chapter and sk-rem-sf-pf-done unit, the complete returned fifteen-step proof, and delivery-errors B–E. I compared the relevant current node statements, not just their proof discussions. The item statement is unchanged, including K arbitrary at finite level, L finite Tor, the restriction to proper maps for ordinary direct image, and the finite-field-model hypothesis for Weil restriction. The source proof gives the finite/reduction/adic/field/pro-etale/coherence/Weil route; the inherited concrete proof repairs its conditional-framework gap. For the counit argument I read Stacks Tag 0B56, sites-cohomology equation-projection-formula-map at lines 13660–13680. For the finite compactification formula I read more-etale lemma-projection-formula-Rf-lower-shriek (Tag 0GL5): its proof factors through proper projection and open tensor. No duality or purity theorem is needed here.

For each new statement I checked its exact scope against that source route and its assigned old paragraphs. The reduction task is exactly the two-sided mate square in old step 3, with both inputs finite Tor so that compact-support comparison applies to the tensor input. The integral-cone task is old step 4: residue-Tor, constructible preservation, triangle closure and exact derived reduction establish endpoints and cone, rather than selecting a lift from its reductions. The field task is old step 5 and the higher-coefficient part of step 6: localization uses integral representatives of underlying objects, and a common finite field represents both maps and inverses; it never reduces a field object. The refinement task is old steps 8–9, keeping the clopen normalization for a non-Cartesian refinement and the witness check for arbitrary K. The compatible-triangle task is old step 10, including its Noetherian/qcqs verification and etale/pro-etale comparison maps. The realization task is old step 11, with the uniform bounds supplied by old step 4; it transports an equality of actual system maps, not evaluated maps. The Weil bridge is old step 13 and the domain check in step 14: finite affine covers give Noetherianity, finite type gives finite dimension, ell is invertible, and the comparison preserves Frobenius and actual reductions. These are seven separate statements, not one renamed copy of the target.

Assembly step 1 uses def-exchange-projection for the proper counit/open tensor formula and def-fix-six-functor-datum for the operations; both state exactly those data, so fixing their name is elementary. Step 2 uses clause (ii) of lem-sf-proetale-constructible-origin to choose bounded etale representatives, clause (ii) of lem-sf-comparison-tor-amplitude to reflect the Tor interval of L, and the last clauses of lem-weil-finite-compact-projection-formula to obtain invertibility of precisely this witnessed pro-etale component. No Tor condition on K was smuggled in. Step 3 cites the new reduction task for precisely its displayed square. Step 4 cites the new cone task for completeness and identification of the actual reduction, and sk-lem-pe-derived-nakayama for detection of an isomorphism between complete complexes. The cone reduction is only an isomorphism test, never a faithfulness claim. Step 5 cites the field-descent task for the localized map, its inverse and tower comparisons.

Assembly step 6 now cites the existing lem-sfb-ringed-projection-tensor-composition, whose statement actually displays pi_(gf)=Rg_*(pi_f) pi_g with no boundedness or invertibility assumption. Its ringed-topos scope includes ringed diagram sites. The new refinement task provides the theta substitution and witnessed descent; this replaces the attempted duplicate counit node. Step 7 takes the canonical alpha and parenthesization assertion from the new triangle task and the actual total-limit conjugacy from the new realization task. Step 5 already carries equalities to fields. Step 8 uses the defining proper-coincidence identification for the identity-open compactification from def-fix-six-functor-datum and the explicit PF composite from def-exchange-projection. Substitution is elementary. Step 9 uses the new Weil bridge to establish the domain hypotheses of lem-fix-weil-operations, whose statement explicitly makes projection equivariant; def-wf-weil-category supplies the commuting-morphism condition. The inverse equation is written out and is elementary once those citations have supplied invertibility and equivariance. All citations are represented by verbatim statement text in citations.json.

I checked the small cases and the hypotheses where they matter. For the reduction square m=n gives identities; at n=1 its Tor claim is over the residue field. K=A/(t) over A=R/(t²) is deliberately excluded only from the finite reduction-comparison task, while finite invertibility and refinement still permit it. In the cone task K=0 or L=0 gives the zero cone, and an identity morphism gives the tensor identity. For scalar descent identity fields and a two-step field tower must have the same morphism class; choosing an integral lift of a rational Weil isomorphism is never required. In refinement, a compactification with an extra disjoint proper component has a non-Cartesian refinement square: the clopen projection retains the identity on the image and is zero on that extra component. The triangle task includes identity maps and empty source; finite type over k is enough for Noetherian/qcqs even when the structure morphism is not separated. Realization handles zero inputs and nested compact supports with one uniform finite interval enlarged as necessary, not all n separately. For the Weil bridge the tensor unit and zero object give the expected Frobenius maps, and finite-type geometric fibres satisfy the Noetherian finite-dimensional comparison hypotheses.

Mathlib searches were run through msearch.py, separately for each of the eight initially proposed tasks (the duplicate was subsequently dropped). For each retained task I read a LeanFinder query, an independently worded LeanSearch query, Loogle and grep output, retained verbatim in mathlib_searches. The primitive comp_counit_app and mappingCone_triangle_distinguished hits are useful pieces, but do not state these concrete compact-support tasks in one line. The apparent Frobenius hit in CategoryTheory/Monoidal/Closed/Functor.lean defines a Cartesian-product adjunction map, not geometric Frobenius compatibility of completed sheaf tensors. I read its hypotheses and the adjunction comp_counit_app source. Two broad Loogle patterns reported unknown identifiers; those responses are recorded as returned, and the successful semantic searches and source grep supply the actual search evidence. No unrun search or service failure is reported as a mathematical absence result.

The return has one substantive instruction, repeated in its attribution. It is repaired by seven fresh unsplit statement-only nodes, each cited by the parent, and an assembly shorter than 3,000 characters. Proofs of the fresh tasks are intentionally left to separate workers; their full motivating arguments, original sources and old dependency lists are preserved below. I also corrected an escaped TeX control character found during the JSON inspection and removed the duplicate counit task before delivery. The preliminary server check_dag passed with only pre-existing off-route advisories. The required final dry run is run after this signed report; its result is recorded in the validation paragraph when it exits. The first dry run required the twelve explicit 0F7B source-tag distinctions now written above; I opened all their statements and added the differences, preserving the actual source tags.

## Original arguments and extraction map

The following paragraphs are copied verbatim from the current returned proof, including all formerly cited dependencies. They preserve the work for the next workers; they are not proof fields on the statement-only nodes.

### Former step 1

Owner: lem-sf-concrete-projection-reduction-square; assembly step 1.

Use the operation datum [def-fix-six-functor-datum] and fix the projection transformation of [def-exchange-projection]. For a compactification $f=pj$, its component is the projection map of $Rp_*$ at $(j_!K,L)$ followed by $Rp_*$ of $j_!K\otimes^LLp^*L\cong j_!(K\otimes^LLf^*L)$. At finite coefficients $Rf_!^c=Rp_*j_!$ is [def-compact-support-direct-image-detailed]; at the integral, rational and algebraically closed stages use precisely the completed, localized and common-stage functors of [def-weil-integral-rational-qbar-compact-support]. Thus throughout the proof PF means this specified natural transformation, rather than an arbitrary isomorphism with the same endpoints.

Cited statements: def-fix-six-functor-datum, def-exchange-projection, def-compact-support-direct-image-detailed, def-weil-integral-rational-qbar-compact-support.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md; Proof, first sentence; statement, projection transformation and coefficient stages.

### Former step 2

Owner: existing lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude, lem-weil-finite-compact-projection-formula; assembly step 2.

Let $\Lambda=A_{E,n}$. By [lem-sf-proetale-constructible-origin], choose bounded constructible etale representatives $K_0,L_0$ with witnesses $\nu_X^*K_0\cong K$, $\nu_Y^*L_0\cong L$. The converse direction of [lem-sf-comparison-tor-amplitude] transfers the finite Tor interval of $L$ to $L_0$; $L_0$ is bounded below because it is bounded. Now [lem-weil-finite-compact-projection-formula] applies to $f,K_0,L_0$ and its witnessed pro-etale realizations. It says exactly that the component of the transformation in step 1 is invertible and natural in $K,L$. No finite Tor condition on $K$ is needed here.

Cited statements: lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude, lem-weil-finite-compact-projection-formula.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md; Proof, first sentence: finite coefficient formula, with intrinsic pro-etale objects supplied witnesses.

### Former step 3

Owner: lem-sf-concrete-projection-reduction-square.

For $1\le m\le n$, assume $K,L$ are in the finite-Tor domains and write $\rho_T(-)=-\otimes^L_{A_{E,n}}A_{E,m}$ on each scheme. For the tensor input, [lem-sf-pullback-tor-amplitude] preserves the Tor interval of $L$, and [lem-sf-tensor-ctf](ii) gives finite Tor amplitude for $K\otimes^LLf^*L$ by adding the two intervals. Thus the compact-support coefficient comparison applies to this input as well as to $K$. The coefficient comparison of [lem-fix-compact-support-coefficient-change] is an isomorphism for the compact-support direct image, and [lem-fix-operation-reduction] gives the tensor and pullback comparisons together with preservation of the units and counits used in the mate defining [def-exchange-projection]. Define the comparison $u$ on the source of PF by first applying the tensor comparison and then the compact-support comparison to $K$, and define $v$ on its target by applying the compact-support comparison to $K\otimes^LLf^*L$ and then the tensor and pullback comparisons. Expanding the two composites through a compactification $f=pj$, the proper factor is the transpose of the same counit composite (the counit identity in [lem-fix-compact-support-coefficient-change]), while the open factor is the same extension-by-zero tensor map after coefficient change. Hence $v\circ\rho(\operatorname{PF}_{n})=\operatorname{PF}_{m}\circ u$. This is an equality of the specified mate composites, so it does not use an axiom asserting that PF is invertible. The finite formula [lem-weil-finite-compact-projection-formula] supplies invertibility at both levels.

Cited statements: lem-fix-compact-support-coefficient-change, lem-fix-operation-reduction, def-exchange-projection, lem-weil-finite-compact-projection-formula, lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md; Proof, repaired concrete step 3.

### Former step 4

Owner: lem-sf-concrete-integral-projection-cone.

Work integrally with the actual projection component $u:S\to T$ specified in step 1, not a lift chosen from its reductions. The objects $K,L$ are derived complete and have uniformly bounded constructible reductions by [def-weil-derived-complete-integral-detailed]. By [lem-coef-integral-residue-tor] their reductions have uniform finite Tor intervals. By [lem-pur-integral-operations-preserve-constructible], $Lf^*L$, $K\widehat\otimes^LLf^*L$, and $S=(Rf_!K)\widehat\otimes^LL$ are integral constructible; here [lem-sf-integral-compact-support-constructible] first supplies $Rf_!K$ and also supplies $T=Rf_!(K\widehat\otimes^LLf^*L)$. Thus both endpoints of $u$ are derived complete. Apply the integral clause of [lem-fix-operation-reduction]: its comparisons identify $S_n,T_n$ with the finite projection endpoints, and its preservation of units, counits and tensor comparisons identifies the reduction of the actual composite $u$ with $\operatorname{PF}_{f,K_n,L_n}$. That finite map is invertible by [lem-weil-finite-compact-projection-formula]. The cone of $u$ remains in the complete constructible category by [lem-weil-integral-constructible-triangulated] (rotate its cone triangle to use the stated extension closure). Its first reduction is zero. The isomorphism-detection clause of [sk-lem-pe-derived-nakayama] therefore proves $u$ invertible. This proves invertibility of the specified map itself and its reduction square; it does not construct a map from an incoherent family, or deduce equality of maps from conservativity.

Cited statements: def-weil-derived-complete-integral-detailed, lem-coef-integral-residue-tor, lem-pur-integral-operations-preserve-constructible, lem-sf-integral-compact-support-constructible, lem-fix-operation-reduction, lem-weil-finite-compact-projection-formula, lem-weil-integral-constructible-triangulated, sk-lem-pe-derived-nakayama.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md; Integral reconstruction sentence: concrete reduction of the canonical map and derived Nakayama.

### Former step 5

Owner: lem-sf-concrete-projection-field-descent.

The raw localization [def-weil-rationalization-karoubi] has the same objects as the integral category, so choose integral representatives of the two rational inputs. The rational operations and transformations are the localized integral ones by [def-weil-derived-pullback-tensor-hom], [def-weil-integral-rational-qbar-compact-support] and [def-exchange-projection]. Apply localization to the map and its inverse from step 4. For an extension of finite coefficient fields use the scalar-comparison clause of [lem-fix-operation-reduction]: it commutes with the operations and preserves the units, counits and tensor associators defining PF, so it identifies extension of this very component with the component over the larger field. Exactness of the extension functor is [lem-weil-scalar-extension-exact-triangulated]; preservation of an inverse also follows simply from functoriality. For algebraically closed coefficients choose one common finite field for both inputs and the map, as in [def-weil-algebraically-closed-coefficients]. The supplied comparisons in [def-exchange-projection] satisfy the identity and tower cocycle. Hence enlarging the field gives the same morphism class, and the finite-stage inverse gives its inverse class. This proves the field formulas and their scalar compatibility without an axiomatized projection theorem.

Cited statements: def-weil-rationalization-karoubi, def-weil-derived-pullback-tensor-hom, def-weil-integral-rational-qbar-compact-support, def-exchange-projection, lem-fix-operation-reduction, lem-weil-scalar-extension-exact-triangulated, def-weil-algebraically-closed-coefficients.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md; Field-passage sentence: localization and canonical scalar comparisons.

### Former step 6

Owner: lem-sf-concrete-integral-projection-cone; lem-sf-concrete-projection-field-descent; assembly step 2.

For finite coefficients, [lem-sf-proetale-constructible-origin] gives an étale-origin witness for every bounded constructible pro-étale input, and [lem-sf-comparison-tor-amplitude] transfers the finite-Tor interval to the étale representative. The finite projection lemma [lem-weil-finite-compact-projection-formula] explicitly includes the pro-étale realizations with these witnesses, so it gives invertibility of the actual pro-étale PF component, including arbitrary finite-level $K$ and finite-Tor $L$. At the integral stage, the pro-étale operations and their reduction maps are the ones in the tower definition [def-weil-integral-rational-qbar-compact-support], and step 4 identifies their inverse-limit map with PF. Rationalization and common-stage scalar extension then give the field stages by step 5. Thus no abstract pro-étale projection axiom or replacement of the completed coefficient system by a discrete étale one is used.

Cited statements: lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude, lem-weil-finite-compact-projection-formula, def-weil-integral-rational-qbar-compact-support.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md; Proof, repaired concrete step 6.

### Former step 7

Owner: lem-sfb-ringed-projection-tensor-composition.

We establish the finite coherence identities before imposing constructibility. Write $P_u=Lu^*$, $R_u=Ru_*$ and $\pi_u$ for the counit-defined map of [def-exchange-projection]. Under the adjunction-normalized direct-image compositor [lem-weil-derived-direct-image-composition], the identity to prove for composable $u,v$ is $\pi_{vu;M,N}=R_v(\pi_{u;M,P_vN})\,\pi_{v;R_uM,N}$, with the pullback and tensor identifications inserted. Transpose both sides under $P_uP_v\dashv R_vR_u$. By [lem-weil-pbc-mate-pasting] its counit is $\varepsilon_u\circ P_u\varepsilon_vR_u$. Both transposes are therefore the composite from $P_uP_v(R_vR_uM\otimes N)$ to $M\otimes P_uP_vN$ which first distributes the two pullbacks over tensor, then applies $P_u\varepsilon_{v,R_uM}$ to the first factor, and finally $\varepsilon_{u,M}$ to that factor. Naturality of the tensor-pullback comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] moves the middle counit across that comparison. The two iterated tensor comparisons agree: on flat-term K-flat models [lem-pc-kflat-resolution] both send a local pure tensor to the same pure tensor, and their total-complex differentials have the same signs. The adjunction bijection now gives the equality. The same calculation with an identity adjunction gives the identity constraint. Iterating this fixed counit composite proves equality of all parenthesizations. These identities require no Tor hypothesis on $M$ and no invertibility of $\pi_u$.

Cited statements: def-exchange-projection, lem-weil-derived-direct-image-composition, lem-weil-pbc-mate-pasting, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-pc-kflat-resolution.

Source: literature/stacks-project/sites-cohomology.tex; Tag 0B56, equation-projection-formula-map; composition-adjunction counit calculation.

### Former step 8

Owner: lem-sf-projection-refinement-descent.

At a finite coefficient level, the normalized proper/open comparison in any commutative proper/open square satisfies the projection identity of [lem-sf-proper-open-projection-mate]. Its clopen-projection normalization includes non-Cartesian refinement squares. The same cited statement gives this identity for intrinsic semilinear-system maps before evaluation; [lem-sf-integral-compactification-system-realization] identifies their finite evaluations with the canonical finite maps. No Tor or boundedness hypothesis is used in this local mate identity.

Cited statements: lem-sf-proper-open-projection-mate, lem-sf-integral-compactification-system-realization.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md; Proof, repaired concrete step 8.

### Former step 9

Owner: lem-sf-projection-refinement-descent.

For a refinement $u:c_1\to c_2$, use precisely $\theta_u=R_{p_2}(\gamma_u^{-1})c_{p_2,u}$ of [def-sf-refinement-comparison-isomorphism]. Step 7 makes the direct-image compositor commute with projection. Step 8, applied to $r=\mathrm{id}_X$, $k=j_1$, $i=j_2$, $p=u$, makes $\gamma_u$ and its inverse commute with the open tensor/projection maps. Substitute these two identities in the defining composite of $\theta_u$; they give
$$\theta_{u,K\otimes Lf^*L}\operatorname{PF}^{c_1}_{f,K,L}
=\operatorname{PF}^{c_2}_{f,K,L}(\theta_{u,K}\otimes1).$$
The comparison cocycle and common refinements of [prop-compactification-coherence-detailed] extend this equality to arbitrary compactifications. Its witnessed domain applies: [lem-sf-pullback-tor-amplitude] gives bounded constructible finite-Tor $Lf^*L$, and [lem-sf-tensor-ctf](i), with that as the finite-Tor factor and the symmetry of tensor, gives bounded constructibility of $K\otimes^LLf^*L$ even for arbitrary bounded constructible $K$. [lem-sf-proetale-constructible-origin] gives witnesses for $K$ and for the bounded constructible tensor appearing in the finite formula [lem-weil-finite-compact-projection-formula]. No finite Tor assumption on $K$ was used in either local identity. Hence the specified finite PF descends independently of compactification on the full domain of the item.

Cited statements: def-sf-refinement-comparison-isomorphism, prop-compactification-coherence-detailed, lem-sf-proetale-constructible-origin, lem-weil-finite-compact-projection-formula, lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf.

Source: literature/stacks-project/more-etale.tex; Tags 0F7B and 0F7G: refinement normalization and tensor compatibility.

### Former step 10

Owner: lem-sf-projection-compatible-triangle-assembly.

For composable $f,g$ between finite-type $k$-schemes, all schemes are Noetherian and qcqs: apply [lem-weil-pbc-finite-type-over-noetherian] over the spectrum of the field, then [lem-weil-pbc-locally-noetherian-quasi-separated]. Choose a compactification $Y\xhookrightarrow{i}\overline Y\xrightarrow{s}Z$ of $g$ and use [lem-weil-pbc-compatible-compactification-triangle] to obtain $X\xhookrightarrow{j}V\xhookrightarrow{b}\overline X$ with $q:V\to Y$, $p:\overline X\to\overline Y$ proper, $f=qj$ and $pb=iq$ cartesian; the compactification schemes are again of finite type over the field. Its normalized comparison $\alpha_{g,f}$ is that of [lem-amb-unbounded-compact-support-comparisons] and, at finite pro-etale level, of [lem-cbc-strict-tower-proper-open-calculus]; under the counit-normalized direct-image comparison [lem-weil-pbc-comparison-direct-image-canonical-mate], the open comparison [lem-cbc-proetale-extension-zero-comparison] and open composition [lem-cbc-extension-zero-composition] it is the canonical compositor of [thm-sf-comp-composition]. The finite-level counit-mate calculation [lem-sf-composition-projection-mate] gives the displayed equation relating $\alpha_{g,f}$ and the three specified projection maps for arbitrary $K,L$, and gives the same equality of actual semilinear-system maps before evaluation. The associative compositor in [thm-sf-comp-composition] then identifies all three-fold parenthesizations.

Cited statements: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-compatible-compactification-triangle, lem-sf-composition-projection-mate, lem-amb-unbounded-compact-support-comparisons, lem-cbc-strict-tower-proper-open-calculus, lem-weil-pbc-comparison-direct-image-canonical-mate, lem-cbc-proetale-extension-zero-comparison, lem-cbc-extension-zero-composition, thm-sf-comp-composition.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md; Proof, repaired concrete step 10.

### Former step 11

Owner: lem-sf-projection-integral-coherence-realization.

Use the coherent system operations and realization isomorphisms $c_V$ of [lem-sf-integral-compactification-system-realization]. The proper/open and composition projection identities hold as actual system equalities by [lem-sf-proper-open-projection-mate] and [lem-sf-composition-projection-mate]; the counit calculation of step 7 applies in these same ringed diagram categories. Their refinement consequence is the substitution of step 9. For the integral inputs, step 4 supplies the common Tor and constructibility bounds required for every intermediate expression in $c_V$. Apply the total-limit functor and the canonical direct-image comparison of [prop-weil-pbc-direct-image-limits], with $A=\mathcal O_E$, $I=(\varpi_E)$; its finite perfect quotients are the usual two-term DVR resolutions. The $c_V$ isomorphisms intertwine units, counits, tensor, composition and proper/open maps, including nested compact support. Conjugating the system equalities by $c_V$ therefore gives the asserted integral equations for the specified maps. The coefficient comparisons of [lem-fix-operation-reduction] and the localized/common-stage functors of [def-weil-derived-pullback-tensor-hom, def-weil-integral-rational-qbar-compact-support] preserve these equations at the field stages. No equality is inferred from finite evaluation or from conservativity.

Cited statements: lem-sf-integral-compactification-system-realization, prop-weil-pbc-direct-image-limits, lem-fix-operation-reduction, def-weil-derived-pullback-tensor-hom, def-weil-integral-rational-qbar-compact-support, lem-sf-proper-open-projection-mate, lem-sf-composition-projection-mate.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md; Integral coherence sentence, repaired concrete step 11.

### Former step 12

Owner: assembly step 8 (proper identity-open specialization).

If $f$ is proper, choose the compactification with $j=\operatorname{id}$ and $p=f$ in [def-weil-integral-rational-qbar-compact-support] and [def-exchange-projection]. By the defining proper-coincidence identification in [def-fix-six-functor-datum] (equivalently the finite compact-support definition), $Rf_!$ is $Rf_*$. The projection component is then exactly the direct-image projection mate for $p$. Its invertibility follows by applying the finite, integral-tower, and scalar-extension arguments of steps 2--5 to this proper morphism; no direct-image projection formula is asserted for a nonproper morphism.

Cited statements: def-fix-six-functor-datum, def-weil-integral-rational-qbar-compact-support, def-exchange-projection, lem-weil-finite-compact-projection-formula.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md; Proof, repaired concrete step 8.

### Former step 13

Owner: lem-sf-projection-weil-tensor-domain-bridge.

For finite-type geometric fibres $W\in\{X,Y\}$ of a fixed finite-field model, a finite affine cover of $W$ has finitely generated $k$-algebras as coordinate rings, which are Noetherian by [lem-wf-affine-noetherian-components]; with [lem-kun-dimension-finite-type] this verifies the Noetherian finite-dimensional hypotheses of [lem-weil-pbc-integral-stratified-perfect-characterization], and $\ell\ne p$ is invertible on $W$. That theorem identifies the integral constructible category used by [def-wf-weil-category] with the completed category in the six-functor conventions. The canonical ordinary/completed tensor comparison and its completion unit are supplied by [lem-fix-constructible-tensor-completion] and [def-weil-pbc-intrinsic-completion]. The technical Frobenius-compatibility of this comparison is exactly [lem-wf-tensor-completion-frobenius], while [def-wf-tensor-product] defines the target tensor map. The preservation nodes [lem-pur-integral-operations-preserve-constructible] and [lem-sf-integral-compact-support-constructible] keep all operation outputs in these domains. Thus the six-functor tensor is canonically identified with the Weil tensor, compatibly with Frobenius, before applying the equivariance result in step 14.

Cited statements: lem-wf-affine-noetherian-components, lem-kun-dimension-finite-type, lem-weil-pbc-integral-stratified-perfect-characterization, def-wf-weil-category, lem-fix-constructible-tensor-completion, def-weil-pbc-intrinsic-completion, lem-wf-tensor-completion-frobenius, def-wf-tensor-product, lem-pur-integral-operations-preserve-constructible, lem-sf-integral-compact-support-constructible.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md; Item proof step 13, canonical tensor model and Frobenius compatibility.

### Former step 14

Owner: lem-sf-projection-weil-tensor-domain-bridge; existing lem-fix-weil-operations; assembly step 9.

For the Weil assertion impose the finite-field model stated in the corrected statement, and let the inputs carry Weil structures. At $E$-coefficients choose integral representatives of the underlying objects only, to apply the preservation assertions of step 13; the Weil isomorphisms remain morphisms in the rational category. No integral lift of a Weil isomorphism is required. At $\overline{\mathbf Q}_\ell$ choose a common finite coefficient field for the two Weil objects, as in [def-wf-weil-category]. The preceding step verifies that the pullback, tensor and compact-support functors have bounded constructible outputs in precisely these coefficient categories. Now [lem-fix-weil-operations] applies to $f_0$ and its geometric fiber $f$: these underlying operations carry their canonical Weil structures and the specified projection transformation is equivariant. Read the tensor Frobenius via [def-wf-tensor-product] and the canonical tensor identification of step 13. Thus, at that finite coefficient field, the underlying projection isomorphism is a morphism between the required Weil objects. The finite-field model is needed for this Weil assertion; the preceding non-Weil projection formula retains its separated finite-type hypotheses.

Cited statements: lem-fix-weil-operations, def-wf-tensor-product, def-wf-weil-category.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md; Weil-equivariance sentence, after checking coefficient models and constructible domains.

### Former step 15

Owner: assembly step 9 (explicit inverse equation).

At the finite coefficient field just chosen, write $u:S\to T$ for the projection component and $\varphi_S,\varphi_T$ for its Weil maps. Step 5 makes $u$ invertible there, and step 14 gives $u\varphi_S=\varphi_T\Phi^*(u)$. Multiply on the left by $u^{-1}$ and on the right by $\Phi^*(u^{-1})$ to obtain $\varphi_S\Phi^*(u^{-1})=u^{-1}\varphi_T$. Thus the inverse is a commuting Weil morphism by [def-wf-weil-category], so $u$ is an isomorphism in the finite-stage Weil category. For algebraically closed coefficients take the class of this inverse at the common finite stage; the definition's composition rule makes its two composites the identity classes. This proves invertibility in the common-stage Weil category itself. The underlying naturality equations are equations of Weil morphisms, so they also prove the asserted naturality after this restriction.

Cited statements: def-wf-weil-category.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md; Weil-equivariance sentence, inverse calculation at a common finite coefficient field.

## Validation

Preliminary server-only `check_dag` passed. The first final dry run stopped at the source-tag duplicate check. All twelve listed comparison statements were opened and distinguished above. The repaired required dry run exited 0: `OK (not pushed) deliver/Q132/fix-prop-projection-formula at 592243ba685: preflight passed`. The preliminary server-only check_dag also passed. No Lean files or compilers were used.

Source-label verification: I also read Stacks `more-etale.tex`, Tag 0F7B (`lemma-shriek-proper-and-open`, lines 2460 ff.) and Tag 0F7G (`lemma-shriek-lqf-and-proper`, lines 2962 ff.). They supply the normalized proper/open and refinement functor comparisons; the tensor compatibility remains the separately cited projection-mate task, not an assertion taken from these functor-only tags.
