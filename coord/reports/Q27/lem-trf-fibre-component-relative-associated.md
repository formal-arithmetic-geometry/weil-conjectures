# Repair delivery: lem-trf-fibre-component-relative-associated

## Files written

- dag/nodes/sec-trace-formula/lem-trf-fibre-component-relative-associated.json: item, split; unchanged statement, three assembly steps.
- dag/nodes/sec-trace-formula/lem-trf-fibre-component-noetherian-affine-chart.json: new statement, unsplit; no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-affine-minimal-prime-stalk-annihilator.json: new statement, unsplit; no exact Mathlib match.
- citations.json: verbatim statement quotes for every use in the three parent steps.
- searches.jsonl: unmodified output log produced by msearch.py.

## Attachments

None for the item or either complete new statement. The exact upstream item tag/name has no hit in lean/WeilConjectures; lean/Sheaf/TraceFormula/FibreComponentRelativeAssociated.lean ends in sorry. The new chart lemma has a useful partial implementation: AlgebraicGeometry.IsAffineOpen.primeIdealOf_mem_minimalPrimes, lean/WeilConjectures/Mathlib/AlgebraicGeometry/Properties.lean:78--93, proves minimality on a GIVEN affine chart, for a generic component point. It does not state local Noetherianity of an arbitrary locally-finite-type fibre or supply the Noetherian chart, so it is not an attachment for the complete new node. Its occurrence in the proof of lem-weil-pbc-generic-finite-morphism-open-neighborhood does not make that node a minimal-prime statement. This partial theorem is an available implementation tool, not newly written Lean. Mathlib's similarly named primeIdealOf_genericPoint instead assumes the entire scheme integral, which need not hold here.

## WANTED

None. All sources used are in literature/stacks-project/. No SGA source is used.

## What was wrong and what changed

The only numbered return is the batch5 re-split instruction: the 3122-character proof must distribute substantial work to at least two new statement-only unsplit nodes, with a parent proof at most 3000 characters. I reconstructed the retained reviewed proof from the current shared node because the sandbox contained only .brief* files, no nodes, report or searches. The mandated initial dry run exited with “no node files”; no previous sandbox work was overwritten. The current shared item is exactly the returned five-step proof (556, 1212, 315, 665, 374 characters). No git command was run in the shared repository.

The first new node takes the complete geometric argument of old steps 1--2 (1768 characters). The second takes the complete algebra/localization/stalk argument of old steps 3--4 (980 characters). These are comparable independent proof tasks. Neither states the parent's associated-point conclusion from a component generic point: one concludes affine-chart minimality, the other starts from an arbitrary minimal affine prime and proves a stalk annihilator. The relative-assassin assembly is still the original elementary old step 5, verbatim. The entire old proof is preserved below to make the handoff reviewable and prevent shortening from concealing omitted work. Only the allowed split fields of the existing node were changed; source, statement, created, blueprint ancestry, Lean and review records were retained from the live read clone.

No statement dispute was found. Flatness is retained in the item, although these two arguments only use local finite type. No Noetherian, reducedness, irreducibility, quasi-compactness or separation condition on the base or total fibre was added.

## Unfinished work

The two new nodes are intentionally unsplit, with empty proof/proof_deps and null proof_origin, as the return requires; subsequent workers can prove them independently. No Lean was written or compiled. Delivery checks are recorded below once run.

## Sources and search assessment

I read Divisors Tags 05AT (definition-relative-assassin), 02OJ (definition-associated), 02OK (lemma-associated-affine-open) and 05AH (lemma-minimal-support-in-ass), including the proofs. The item is the generic-component case of 05AH on the fibre, followed by the union in 05AT. For the first new node I read Morphisms Tags 01T4 (lemma-base-change-finite-type) and 01T6 (lemma-finite-type-noetherian), Properties Tag 01OV (definition-noetherian), and Algebra Tag 00ES (lemma-irreducible) with its closure/minimal-prime argument. For the second I read Algebra Tags 05BV (lemma-ass-minimal-prime-support) and 05BZ (lemma-localize-ass), Divisors 02OK and 02OJ, and Schemes Tag 01HV (lemma-spec-sheaves), especially clause (6) identifying the structure-sheaf stalk with the localization. Tags and labels were verified in literature/stacks-project/tags/tags. The source text really allows the nonreduced and multicomponent case; 05AH explicitly warns that a Noetherian hypothesis cannot simply be removed.

Before creating either node I searched the whole DAG by generic/minimal prime, affine/associated point and all relevant tags, and ran tools/blueprint_refs.py searches for minimal prime, associated point, generic point, 00ES, 05AH, 02OK, Noetherian affine, annihilator and component generic. No blueprint statement gives either new conjunction. The ancestor command gives lem-trf-local-term-locality. I read its current main-20261015 file and the sk-i-curve-zero unit and sec-trace-formula chapter. This is still the inherited component-closure input in the nearby-cycle/specialization branch; no chapter/unit route was replaced. The new from.via lists prepend the current item to its existing via list.

Every Mathlib query recorded in the new nodes was run through the required msearch.py command, and the log was read. Both nodes have two distinct semantic phrasings plus Loogle and grep. The chart searches find LocallyOfFiniteType.isLocallyNoetherian and the locally-Noetherian pullback instances, which cover the first half only; PrimeSpectrum.zeroLocus_minimalPrimes and vanishingIdeal_irreducibleComponents describe Spec A but do not perform the component-point affine-neighbourhood passage. The relevant source at Mathlib/AlgebraicGeometry/Noetherian.lean:239--264 and Mathlib/RingTheory/Spectrum/Prime/Topology.lean:1260--1289 was read. The genericPoint_eq_bot_of_affine and primeIdealOf_genericPoint results in Mathlib/AlgebraicGeometry/FunctionField.lean:108--145 require domains/integral schemes, so are insufficient for reducible/nonreduced fibres. The upstream theorem mentioned above addresses just minimality. For the second node, Mathlib has the algebraic minimalPrimes_annihilator_subset_associatedPrimes result (already the existing DAG leaf), affine prime/point maps, and localization ingredients, but no scheme-level associatedPoints interface or the displayed stalk-annihilator conclusion as a single specialization. LeanSearch for the second node returned a rate-limit service-unavailable response; that entry is recorded as unavailable, never as a negative search result. Successful LeanFinder, Loogle and grep results remain separate. All prior item searches were preserved rather than rewritten.

## Review by Q27

I checked the return against the actual new statements and the original five arguments, not merely their lengths. Parent step 1 cites only lem-trf-fibre-component-noetherian-affine-chart. I opened its statement and checked that it returns the SAME fibre T, an affine open containing this y, a Noetherian section ring A and the minimal corresponding prime. Its assumptions are exactly local finite type and the parent's component/generic-point data; it does not require the base to be Noetherian. Parent step 2 cites only lem-trf-affine-minimal-prime-stalk-annihilator: that statement really supplies the annihilator in O_(T,y), as well as associated-point membership. Its Noetherian and minimality assumptions come from step 1; no conclusion is being imported from a dependency's proof. Parent step 3 cites def-pc-scheme-fibre. I opened its statement: it explicitly identifies the fibre projection topologically with f^(-1)(t). Together with the union definition IN THE ITEM, this proves membership using the same index t and the image of y. citations.json quotes exactly those three statements.

I also opened every statement used by the retained arguments handed to the new nodes. The fibre definition is the residue-field base change, lem-weil-pbc-lft-base-change explicitly preserves LOCAL finite type under ANY base change, def-weil-pbc-noetherian-ring is finite generation of ideals, def-weil-affine-spectrum includes the one-point spectrum of a field, pqf-def-locnoeth is a cover by Noetherian affine rings, and pqf-lem-locnoeth-lft requires only a locally Noetherian target. Thus old step 1 is valid without hypotheses on S. For old step 2, lem-weil-pbc-affine-open-spec-points really identifies y with a prime via an isomorphism onto the affine open. The definitions of generic point and irreducible component give closure{y}=C and maximal irreducibility; the smaller-prime contradiction below proves minimality rather than assuming T integral. For old step 3, lem-weil-pbc-noetherian-minimal-prime-associated states the exact annihilator equality for a minimal prime of a Noetherian ring. For old step 4, lem-weil-pbc-associated-prime-localization-depth-zero states that the extended prime is an annihilator in A_p, and clause (c) of lem-weil-pbc-affine-open-stalk-localization is a RING isomorphism A_p -> O_(T,y). The explicit transport below preserves/refects rb=0, and local-ring maximal ideals correspond; def-sc-associated-points then gives the desired interpretation. I did not cite a definition as a substitute for the localization theorem. These existing algebraic and affine-input statements are Mathlib leaves and are reused, not recreated. The annotation in def-sc-associated-points still has the pre-existing source-tag typo 02OZ versus 02OJ; its statement is correct and the dependency was not edited.

Small-case checks: an empty fibre has no component point y, so the chart statement is vacuous there. For Spec K, A=K, p=0, w=1 works. For K[e]/(e^2), p=(e) is minimal and Ann(e)=(e); both lemmas retain this nilpotent example. For K[u,v]/(uv), either minimal prime (u) or (v) is allowed; no irreducibility is assumed, and localization gives a field at either generic point. For K[x,y]/(x^2,xy), the embedded associated prime (x,y) does not invalidate the argument for the component prime (x): Ann(y)=(x). The second new statement assumes a minimal prime, and does not falsely assert that every point of a Noetherian chart is associated. An affine chart with y in it cannot have the zero ring, so no nonempty point was smuggled into Spec 0. A base S with non-Noetherian local rings is allowed because all finite-type/Noetherian work is on the residue-field fibre. I checked that neither new statement needs flatness and that its omission there is harmless since the parent's hypotheses are untouched.

B1--B10: new nodes have statements only, introduce all objects and assumptions, cite their actual notions, use ordinary single TeX escapes, give verified Stacks tags/labels, have truthful logged searches and full blueprint provenance. Neither is marked Mathlib or given invented Lean evidence. C1--C8: every non-elementary parent use has the matching cited statement, every quote is verbatim, and the children have no edges back to the parent (blueprint ancestry is provenance only). D1--D5: the two nodes expose distinct geometric and algebra-to-stalk tasks, neither simply repeats an item clause under the item's hypotheses, and no old argument was deleted. E1--E7: the hypotheses, fibre and stalk objects, annihilator transport, non-Noetherian base and small cases were checked explicitly above. Parent proof steps are all below 2000 characters, and the whole parent proof is below 3000 characters. There are no hidden long steps left in the assembly. No permission or extra agent was needed.

## Full retained arguments and assignment to new nodes

The following texts are copied without shortening from the reviewed node used as the repair base. They are handoff material in the report, not proof steps in the new statement-only nodes.

### Old step 1: lem-trf-fibre-component-noetherian-affine-chart

Put $T=X_t$ and $K=\kappa(t)$. By the fibre definition, $T\to\operatorname{Spec}K$ is the base change of $f$ along $\operatorname{Spec}K\to S$. The locally-finite-type base-change lemma therefore makes this morphism locally of finite type. A field has only the ideals $(0)$ and $(1)$, both finitely generated, so $K$ is Noetherian and its one-point spectrum is locally Noetherian. Applying the locally-Noetherian finite-type lemma gives that $T$ is locally Noetherian. Neither this argument nor the remaining steps require any Noetherian hypothesis on $S$.

Existing inputs: def-pc-scheme-fibre, lem-weil-pbc-lft-base-change, def-weil-pbc-noetherian-ring, def-weil-affine-spectrum, pqf-def-locnoeth, pqf-lem-locnoeth-lft.

### Old step 2: lem-trf-fibre-component-noetherian-affine-chart

Let $B$ be the component of $T$ with generic point $y$. Choose from the locally Noetherian affine cover an affine neighbourhood $U=\operatorname{Spec}A$ of $y$ with $A$ Noetherian, and let $\mathfrak p\subset A$ be its prime corresponding to $y$ under the affine-open point identification. We check directly that $\mathfrak p$ is minimal. In the Zariski topology $\overline{\{\mathfrak p\}}=V(\mathfrak p)$: a closed set $V(I)$ contains $\mathfrak p$ exactly when $I\subseteq\mathfrak p$, so every such closed set contains $V(\mathfrak p)$. Also $B\cap U=\overline{\{y\}}^{\,U}=V(\mathfrak p)$; the equality of closures follows because $U$ is an open neighbourhood of $y$. If a prime $\mathfrak q\subsetneq\mathfrak p$ existed, its point $z\in U$ would specialize to $y$, since $\mathfrak p\in V(\mathfrak q)$. Thus the closure of $z$ in $T$ contains $B$. That closure is irreducible (a singleton is irreducible, and its closure remains irreducible directly by the closed-set definition), so maximality of the component $B$ makes it equal to $B$. But $z\notin B\cap U=V(\mathfrak p)$ because $\mathfrak p\nsubseteq\mathfrak q$, a contradiction. This proves minimality without assuming $T$ irreducible or reduced.

Existing inputs: pqf-def-locnoeth, lem-weil-pbc-affine-open-spec-points, def-weil-affine-spectrum, def-sc-generic-point, def-weil-irreducible-components.

### Old step 3: lem-trf-affine-minimal-prime-stalk-annihilator

Apply the Noetherian minimal-prime associated-prime lemma to $A$ and $\mathfrak p$. Step 1 and the choice in Step 2 give precisely its Noetherian hypothesis; Step 2 gives its minimal-prime hypothesis. It supplies $a\in A$ with $\operatorname{Ann}_A(a)=\mathfrak p$. Thus $\mathfrak p$ is an associated prime of $A$.

Existing inputs: lem-weil-pbc-noetherian-minimal-prime-associated.

### Old step 4: lem-trf-affine-minimal-prime-stalk-annihilator

The associated-prime localization lemma, applied to this Noetherian ring $A$ and its associated prime $\mathfrak p$, says that the maximal ideal $\mathfrak pA_{\mathfrak p}$ is associated to $A_{\mathfrak p}$. By the affine-open stalk-localization theorem, the germ map identifies $\mathcal O_{T,y}$ with $A_{\mathfrak p}$. Under this ring isomorphism maximal ideals correspond, and an annihilator equality corresponds because $rb=0$ is preserved and reflected by a ring isomorphism. Consequently the maximal ideal of $\mathcal O_{T,y}$ is the annihilator of an element of that ring. By the definition of associated points, $y\in\operatorname{Ass}_T(\mathcal O_T)$.

Existing inputs: lem-weil-pbc-associated-prime-localization-depth-zero, lem-weil-pbc-affine-open-stalk-localization, def-sc-associated-points.

### Old step 5: parent step 3 (unchanged)

In the union defining $\operatorname{Ass}_{X/S}(\mathcal O_X)$ in the statement, take the index $s=t$. The preceding step places $y$ in its summand $\operatorname{Ass}_{X_t}(\mathcal O_{X_t})$. Regard this point as a point of $X$ by the fibre projection, whose underlying map identifies $X_t$ with $f^{-1}(t)$. Thus $y\in\operatorname{Ass}_{X/S}(\mathcal O_X)$, as required.

Existing inputs: def-pc-scheme-fibre.

## Not duplicates

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-closed-component-stalk-calculus: shared tag 00ES; the existing statement starts with a globally Noetherian ambient scheme and a closed subscheme, and identifies components of a reduced closed subscheme through a point with minimal primes in its ambient stalk. It neither proves local Noetherianity of a locally-finite-type residue-field fibre nor produces a Noetherian affine chart at its component generic point; its reduced-component clause cannot be applied to an arbitrary nonreduced fibre. The new chart lemma allows an arbitrary base and nonreduced fibre and concludes minimality in the chart section ring, so is not a special case.


lem-trf-fibre-component-noetherian-affine-chart vs lem-sbc-flat-composite-fibre-dimension-at-point: shared tag(s) 01T6; the existing statement concerns Pointwise fibre dimension is additive for a flat first morphism; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sbc-composite-fibre-local-models: shared tag(s) 01T6; the existing statement concerns Local models of the fibres of a composite; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs pqf-def-locnoeth: shared tag(s) 01T6; the existing node defines Locally Noetherian schemes; it does not assert the fibre chart/minimality theorem.

lem-trf-fibre-component-noetherian-affine-chart vs sk-thm-sf-pf-proetale: shared tag(s) 01T6; the existing statement concerns Projection formula: the pro-étale realization; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-verdier-preservation-strata: shared tag(s) 01T6; the existing statement concerns Constructible preservation before biduality; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-package-base-change-domain-realization: shared tag(s) 01T6; the existing statement concerns Geometric and coefficient-domain realization of base change; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-open-roos-unit-adjunction: shared tag(s) 01T6; the existing statement concerns Roos completeness, actual open completion units and the complete adjunction; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-native-weil-pullback-star-preservation: shared tag(s) 01T6; the existing statement concerns Bounded constructible preservation for native Weil pullback and ordinary direct image; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs sk-lem-sf-open-ctf: shared tag(s) 01T6; the existing statement concerns Extension by zero preserves the finite-Tor constructible category; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-boundary-etale-adjunction-restriction: shared tag(s) 01T6; the existing statement concerns Finite-dimensional compactifications and bounded-below restriction of etale adjunctions; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-adic-qbar-constructible-realization: shared tag(s) 01T6; the existing statement concerns Evaluation-compatible realization of common-stage coefficients as native adic modules; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-native-weil-constructible-abelian: shared tag(s) 01T6; the existing statement concerns Abelian ambient category and weak Serre constructible native Weil sheaves; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs cor-pur-smooth-admissibility: shared tag(s) 01T6; the existing statement concerns Smooth morphisms satisfy the preservation clauses; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-locally-finite-adic-compact-support-sums: shared tag(s) 01T6; the existing statement concerns Coproduct preservation of actual adic compact supports on the constructible localizing hull; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-locally-closed-closure-adjoint-realization: shared tag(s) 01T6; the existing statement concerns Closure compactification realizes the immersion adjoint and its bounds; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-finite-duality-closed-comparison: shared tag(s) 01T6; the existing statement concerns Closed exceptional comparison under site comparison; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-proper-open-tensor-compatibility: shared tag(s) 01T6; the existing statement concerns Tensor compatibility of the normalized proper/open interchange; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-composition-projection-mate: shared tag(s) 01T6; the existing statement concerns Normalized compact-support composition satisfies the projection mate identity; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-open-tensor-quotient-augmentation: shared tag(s) 01T6; the existing statement concerns Open reduction towers and the strict augmented tensor square; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-etale-generic-direct-image-exchange: shared tag(s) 01T6; the existing statement concerns Generic direct-image exchange over an arbitrary algebraically closed base; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-etale-generic-exchange-algclosed: shared tag(s) 01T6; the existing statement concerns Geometric-generic closed-support and internal-Hom exchange over arbitrary algebraically closed fields; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-affine-proper-square-stratified-module: shared tag(s) 01T6; the existing statement concerns Affine proper squares and global stratified module refinement; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-fix-projection-compactification-comparison: shared tag(s) 01T6; the existing statement concerns Projection transformations of two compactifications agree under the refinement comparison; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-derived-weil-tensor-hom-adjunction: shared tag(s) 01T6; the existing statement concerns Native derived-Weil tensor preserves bounded constructible complexes; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-etale-smooth-stratified-ctf: shared tag(s) 01T6; the existing statement concerns Smooth-stratum finite-Tor devissage over an arbitrary algebraically closed field; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-continuous-adic-proper-base-change-restriction: shared tag(s) 01T6; the existing statement concerns Proper base change under locally closed restriction for continuous adic module sheaves; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-constructible-exceptional-adjunction-coefficients: shared tag(s) 01T6; the existing statement concerns Constructible exceptional adjunction and its coefficient comparisons without an ambient datum; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-immersion-weil-local-behavior: shared tag(s) 01T6; the existing statement concerns Exact immersion operations and local Frobenius on Weil stalks; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-extension-by-zero-punctual: shared tag(s) 01T6; the existing statement concerns Extension by zero is exact and preserves punctual weights; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-spectrum-irreducible-nilradical-prime: shared tag(s) 00ES; the existing statement concerns Irreducibility of an affine spectrum is equivalent to primality of the nilradical; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-bertini-prescribed-point-smooth-system: shared tag(s) 01T6; the existing statement concerns Prescribed-point high-degree systems with smooth hypersurfaces; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-bertini-sections: shared tag(s) 01T6; the existing statement concerns Sections vanishing on a closed subscheme; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-geometric-irreducibility-finite-separable-test: shared tag(s) 00ES; the existing statement concerns Geometric irreducibility can be tested on finite separable extensions; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-geometric-irreducibility-transcendental: shared tag(s) 00ES; the existing statement concerns Geometric irreducibility and purely transcendental extensions; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-geometric-irreducibility-subalgebra-colimit: shared tag(s) 00ES; the existing statement concerns Geometric irreducibility is preserved by subalgebras and directed colimits; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-bertini-finite-cover-transverse-component: shared tag(s) 00ES; the existing statement concerns A transverse codimension-two witness for an immersive system on a finite cover; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-irreducible-fibre-dimension-lower-bound: shared tag(s) 01T6; the existing statement concerns Lower bound for fibres of an irreducible finite-type scheme; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-bertini-irreducible-member: shared tag(s) 01T6; the existing statement concerns Geometrically irreducible general member of a linear system; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-linear-incidence-irreducible: shared tag(s) 00ES; the existing statement concerns Irreducibility of an affine linear incidence hypersurface; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-finite-type-fibre-component-lower-bound: shared tag(s) 00ES; the existing statement concerns Dimension lower bound for each rational closed-fibre component of a finite type algebra map; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-tw-lisse-rational-realization: shared tag(s) 01T6; the existing statement concerns Lisse realization of the rationalized constructible heart, with tensor and point normalization; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-a1-smooth-lisse-integral-lattice: shared tag(s) 01T6; the existing statement concerns Global integral lattices for lisse sheaves on smooth geometric fibres; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs prop-wf-weil-sheaf-representation-equivalence: shared tag(s) 01T6; the existing statement concerns The lisse sheaf–representation equivalence; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-rp-determinant-weights-agree: shared tag(s) 01T6; the existing statement concerns Rank-one purity discharges the finite-determinant hypotheses; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-a1-normal-etale-components-clopen: shared tag(s) 01T6; the existing statement concerns Clopen irreducible components of an etale scheme over a normal base; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-a1-geometric-cover-component-qc-proper: shared tag(s) 01T6; the existing statement concerns Quasi-compact proper components of a connected geometric covering; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs sk-thm-rationality: shared tag(s) 01T6; the existing statement concerns Rationality of the zeta series; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-zl-general-condensed-weil-realization: shared tag(s) 01T6; the existing statement concerns Condensed realization of a finite-stage Weil complex and its Frobenius operators; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-fd-finite-ring-compact-support-finiteness: shared tag(s) 01T6; the existing statement concerns Compact-support finiteness for arbitrary finite rings and a finite-type target; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-fd-rational-coefficient-category-comparison: shared tag(s) 01T6; the existing statement concerns Comparison of the framework and PBC rational coefficient systems; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-etale-coordinate-intersection-geometry: shared tag(s) 01T6; the existing statement concerns Regular coordinate intersections and their etale transport; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-psi-constructibility-descent: shared tag(s) 01T6; the existing statement concerns Proper-surjective descent of constructibility on a vanishing topos; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-log-regular-sharp-chart: shared tag(s) 01T6; the existing statement concerns Charts modeled on the sharp characteristic of a log regular scheme; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-valuation-exceptional-closed-image-criterion: shared tag(s) 01T6; the existing statement concerns Closed-image exceptional components detect stability; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-section-local-dualizing-comparisons: shared tag(s) 01T6; the existing statement concerns Local shifted dualizing lines and normalized section-chart comparisons; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-riemann-zariski-local-colimit: shared tag(s) 01T6; the existing statement concerns Valuation ring as the filtered colimit of centre local rings; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-semistable-marked-base-change: shared tag(s) 01T6; the existing statement concerns Arbitrary base change of semistable marked curves and fibrewise stability; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-flat-relative-associated-specialization: shared tag(s) 01T6; the existing statement concerns Specialization of a relative associated point at a flat fibre-component generic point; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-generic-fibre-points-smooth: shared tag(s) 01T6; the existing statement concerns Smoothness at generic points of geometrically reduced fibres; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-stacks-nodal-closed-subcurve: shared tag(s) 00ES; the existing statement concerns Stacks lemma for a reduced closed subcurve of a nodal curve; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-finite-monoid-stalk-data-spreading: shared tag(s) 01T6; the existing statement concerns Finite monoid data and equations spread from an etale stalk; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-fppf-local-qf-neighbourhood: shared tag(s) 01T6; the existing statement concerns A flat finitely presented morphism has a locally quasi-finite neighbourhood over every image point; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-stable-modification-stability-locus: shared tag(s) 01T6; the existing statement concerns Constructible stable locus and dense isomorphism open for a spread modification; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-stratified-product-coherent-conservative: shared tag(s) 01T6; the existing statement concerns Finite stratified oriented products form a coherent conservative cover; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-hilbert-samuel-near-normal-cone: shared tag(s) 01T6; the existing statement concerns Normal-flat normal cone and linear vertex at a Hilbert--Samuel near point; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-proper-base-change-coherent-conservative: shared tag(s) 01T6; the existing statement concerns Proper surjective base change is coherent and conservative on vanishing topoi; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-nearby-compact-tensor-coherence: shared tag(s) 01T6; the existing statement concerns Tensor and compact-support coherence before duality; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-oriented-proper-image-constructibility: shared tag(s) 01T6; the existing statement concerns Proper source direct image on vanishing topoi; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-conductor-smooth-base-change: shared tag(s) 01T6; the existing statement concerns The conductor ideal of normalization commutes with smooth pullback; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-reduced-curve-normalization-genus: shared tag(s) 01T6; the existing statement concerns Normalization formula for the arithmetic genus of a reduced proper curve; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-dejong-arbitrary-base-marked-semistable: shared tag(s) 01T6; the existing statement concerns Marked semistable alteration over an arbitrary excellent base; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-marked-controlled-blowup-charts: shared tag(s) 01T6; the existing statement concerns Controlled transforms in smooth marked blowup charts; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-proetale-composition-tower-normalization: shared tag(s) 01T6; the existing statement concerns Pro-etale composition on a compatible tower has the open-adjoint normalization; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-normalization-singular-skyscraper: shared tag(s) 01T6; the existing statement concerns Normalization quotient is supported at singular points; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-nodal-contraction-euler-defect: shared tag(s) 01T6; the existing statement concerns Euler defect of contracting a nodal subcurve to a smooth point; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-fine-log-stalk-chart-spreading: shared tag(s) 01T6; the existing statement concerns Spreading a given chart of a fine log stalk; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-finite-dominant-fibre-purity: shared tag(s) 01T6; the existing statement concerns Purity of fibres under a finite dominant integral cover; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-finite-surjective-ample-reflection: shared tag(s) 01T6; the existing statement concerns Ampleness descends and ascends along finite surjective morphisms; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-flat-fibre-component-closure-dimension: shared tag(s) 01T6; the existing statement concerns Dimension of fibres in a fibre-component closure inside a flat family; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-proper-field-invertible-coherent: shared tag(s) 01T6; the existing statement concerns Noetherianity and coherence of invertible modules on a proper scheme over a field; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-section-rees-noetherian-geometry: shared tag(s) 01T6; the existing statement concerns Noetherian smooth Rees geometry for a closed section; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-proper-birational-curve-finite: shared tag(s) 01T6; the existing statement concerns A proper birational morphism of integral curves is finite; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-curve-euler-tensor-generic-rank: shared tag(s) 01T6; the existing statement concerns Euler characteristic of an invertible twist on an integral proper curve; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-etale-component-coordinate-identification: shared tag(s) 01T6; the existing statement concerns Étale local identification of regular boundary components with coordinate hyperplanes; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-nodal-curve-normalization-euler: shared tag(s) 01T6; the existing statement concerns Euler characteristic of a nodal curve from its normalization; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-functorial-log-blowup-etale-descent: shared tag(s) 01T6; the existing statement concerns Etale descent of finite functorial log blowup procedures; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-etale-completed-local-ring-iso: shared tag(s) 01T6; the existing statement concerns Etale local invariance at a point with algebraically closed residue field; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-fibre-component-relative-associated: shared tag(s) 01T6, 00ES; the parent concludes fibre-associated and relative-assassin membership, whereas this node constructs the Noetherian affine minimal-prime chart and has no associated-point conclusion.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-dnc-generic-local-system-devissage: shared tag(s) 01T6; the existing statement concerns Finite-cover exact sequence for a local system on the complement of a divisor; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-nodal-contraction-normalization-branches: shared tag(s) 01T6; the existing statement concerns Normalization branches at a nodal contraction boundary; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-nodal-pair-projective-resolution: shared tag(s) 01T6; the existing statement concerns Resolution of a nodal curve over a smooth normal-crossings pair; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-flat-dense-generic-fibre-pure-dimension: shared tag(s) 01T6; the existing statement concerns Pure dimension of fibres of a flat family with dense pure-dimensional generic fibre; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-excellent-base-generic-curve-preparation: shared tag(s) 01T6; the existing statement concerns Generic smooth curve and etale boundary preparation over an excellent base; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-dnc-principal-generic-smooth-reduction: shared tag(s) 00ES; the existing statement concerns Generic smooth coordinate reduction for a principal divisor; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-nc-coordinate-max-stratum: shared tag(s) 01T6; the existing statement concerns Coordinate description of the maximal branch stratum; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-finite-birational-nodal-connected-iso: shared tag(s) 01T6; the existing statement concerns A finite birational map to a nodal curve with connected fibres is an isomorphism; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-smooth-rational-point-completion: shared tag(s) 01T6; the existing statement concerns Completion at a rational point of an essentially smooth local map; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-degree-weighted-irreducible-components: shared tag(s) 01T6; the existing statement concerns Degree as a multiplicity-weighted sum over integral components; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-j2-affine-cover: shared tag(s) 01T6; the existing statement concerns The J-2 property passes from an affine open cover to every affine open; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-nodal-geometric-fibres-reduced: shared tag(s) 01T6; the existing statement concerns Nodal geometric curve fibres are geometrically reduced; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-valuation-domain-fibre-dimensions: shared tag(s) 00ES; the existing statement concerns Equidimensional closed fibre of a finite type domain over a valuation ring; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-nodal-points-reduced-algebraically-closed: shared tag(s) 01T6; the existing statement concerns A curve with only smooth points and nodes over an algebraically closed field is reduced; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-birational-curve-quasifinite: shared tag(s) 01T6; the existing statement concerns A dominant morphism of integral curves with finite generic extension is quasi-finite; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-proper-composition-site-transport: shared tag(s) 01T6; the existing statement concerns Site comparison preserves compact-support composition with a proper factor; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-field-extension-component-local-dimension: shared tag(s) 01T6; the existing statement concerns Component dimensions after a field extension from local dimensions; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-stable-modification-stability-field-descent: shared tag(s) 01T6; the existing statement concerns Semistability and geometric stability are invariant under field extension; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-normal-crossings-strictification: shared tag(s) 01T6; the existing statement concerns Strictification of a normal crossings boundary; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-base-modification-comparison-fibre-image: shared tag(s) 01T6; the existing statement concerns Finite image of a projection fibre under a proper comparison after modifying the base; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-open-fixed-square-domains: shared tag(s) 01T6; the existing statement concerns Finite-type domains for an open restriction of the fixed square; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-normal-topologically-noetherian-components: shared tag(s) 00ES; the existing statement concerns Normal schemes with Noetherian underlying space have open integral components; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-nearby-cycle-sheaf-finiteness: shared tag(s) 01T6; the existing statement concerns Standard nearby-cycle constructibility and vanishing for a constructible sheaf on the generic fibre; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-riemann-zariski-finite-refinement: shared tag(s) 01T6; the existing statement concerns Valuation neighbourhoods and common finite Riemann--Zariski refinement; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-nodal-family-etale-source-locality: shared tag(s) 01T6; the existing statement concerns Nodal curves are etale local on the source; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-nodal-normalization-adjunction: shared tag(s) 01T6; the existing statement concerns Normalization adjunction for a component of a nodal curve; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-curve-degree-tensor-additive: shared tag(s) 01T6; the existing statement concerns Degree is additive on tensor products of invertible modules on proper schemes of dimension at most one; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-finite-etale-marking-sections: shared tag(s) 01T6; the existing statement concerns Splitting a finite etale marking into disjoint sections after alteration; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-nodal-subcurve-boundary: shared tag(s) 01T6; the existing statement concerns Reduced nodal subcurves and their reduced boundary intersection; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-trf-valuation-normalized-graph-model: shared tag(s) 01T6; the existing statement concerns Normalized graph image as an intermediate valuation-curve model; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pc-euler-characteristic-well-defined: shared tag(s) 01T6; the existing statement concerns Well-definedness of the Euler characteristic; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pc-vanishing-above-dim: shared tag(s) 01T6; the existing statement concerns Vanishing above the dimension of a curve; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pc-curve-local-scalar-principal-parts: shared tag(s) 01T6; the existing statement concerns Scalar extension and semilocal principal parts on a smooth curve; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pc-coherent-support-proper-higher-direct-image: shared tag(s) 01T6; the existing statement concerns Coherent higher direct images with proper support; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pc-noetherian-perfect-direct-image: shared tag(s) 01T6; the existing statement concerns Perfect direct image over a Noetherian base; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs det-lem-stratified-lattice-trace: shared tag(s) 01T6; the existing statement concerns Pushing a lattice down a finite étale cover by the trace; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-common-regular-surface-resolution: shared tag(s) 01T6; the existing statement concerns Common point-blowup resolution of regular proper surfaces; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-dm-open-finite-etale-permanence: shared tag(s) 01T6; the existing statement concerns Open substacks and finite etale decorations of a smooth finite-diagonal stack; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-proper-dc-preserves-continuous: shared tag(s) 01T6; the existing statement concerns Proper direct image preserves bounded constructible complexes (finite extension E); it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-proper-pair-radicial-preparation: shared tag(s) 01T6; the existing statement concerns Proper normal pair preparation over a radicial constant extension; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-integral-general-lfp-hom-finiteness: shared tag(s) 01T6; the existing statement concerns Complete residue witness for internal Hom of integral general-lfp complexes; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs det-thm-sf-ctf-stability-direct-images: shared tag(s) 01T6; the existing statement concerns Pullback, tensor product and direct images on $\Dctf$ at all coefficient stages; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-ample-curve-two-section-pencil: shared tag(s) 01T6; the existing statement concerns Orbit-separated two-section pencils from an ample power; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-general-lfp-adic-input-witness: shared tag(s) 01T6; the existing statement concerns General-lfp integral inputs have complete constructible residue witnesses; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs det-cor-sf-direct-image-ctf-open-tor: shared tag(s) 01T6; the existing statement concerns Scalar projection formula and the Tor bound for an open immersion; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-snc-boundary-parameter-criterion: shared tag(s) 00ES; the existing statement concerns Local parameter criterion for a strict normal crossings boundary; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-nodal-trait-rational-domination: shared tag(s) 01T6; the existing statement concerns Rational geometric fibres dominate modifications of a nodal trait curve; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs sk-lem-proper-heart-bound: shared tag(s) 01T6; the existing statement concerns A uniform bound for proper direct image; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-git-orbit-closure-dimension: shared tag(s) 01T6; the existing statement concerns Semistable orbit closures and algebraic orbit dimensions; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs det-prop-scalar-six-ctf: shared tag(s) 01T6; the existing statement concerns Extension of scalars preserves $\Dctf$; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-adic-proper-localizing-adjunction-comparison: shared tag(s) 01T6; the existing statement concerns Adic proper adjunction comparison on the two constructible localizing presentations; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-proper-curve-bundle-pullback-degree: shared tag(s) 01T6; the existing statement concerns Degree of an invertible sheaf pulled back along a proper curve map; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-separated-space-dimension-one-scheme: shared tag(s) 01T6; the existing statement concerns Separated algebraic spaces of dimension at most one over a field are schemes; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-finite-type-noetherian-spectrum: shared tag(s) 00ES; the existing statement concerns Finite type algebras preserve Noetherian spectra; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-semilinear-equivariant-chow-modification: shared tag(s) 01T6; the existing statement concerns Semilinear equivariant projective Chow modification; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-adic-localizing-exceptional-bounded: shared tag(s) 01T6; the existing statement concerns Cohomological boundedness of the localizing exceptional object; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-quasifinite-compact-support-exact: shared tag(s) 01T6; the existing statement concerns Quasi-finite compact support is exact and agrees with compactifications; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-point-blowup-fibre-defects: shared tag(s) 01T6; the existing statement concerns Geometric fibre defects in regular surface point blowups; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-tame-radical-curve-normalization: shared tag(s) 01T6; the existing statement concerns Smooth normalization of a tame radical cover of a marked curve; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-lattice-subquotient-filtration: shared tag(s) 01T6; the existing statement concerns Integral lattice subquotients of a lisse extension by zero; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-finite-etale-normal-generic-components: shared tag(s) 01T6; the existing statement concerns Generic fields and normalization components of a finite etale cover; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-log-smooth-composition-strict-base-change: shared tag(s) 01T6; the existing statement concerns Composition and strict base change in logarithmic smoothness; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-etale-source-adjunction-line: shared tag(s) 01T6; the existing statement concerns Etale source locality of the canonical relative adjunction line; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-persistent-node-normalization: shared tag(s) 01T6; the existing statement concerns Finite normalization at persistent nodes over an arbitrary trait; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-proper-formal-curve-algebraization: shared tag(s) 01T6; the existing statement concerns Algebraization of proper flat formal curves over a power-series ring; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-semistable-log-pluricanonical-lattices: shared tag(s) 01T6; the existing statement concerns Invariance of logarithmic pluricanonical lattices of semistable models; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs det-thm-restriction-local: shared tag(s) 01T6; the existing statement concerns Local factorization of $f^!$ on an affine chart; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-locally-closed-generator-tensor-intersection: shared tag(s) 01T6; the existing statement concerns Tensor comparison for locally closed finite-free generators; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-projective-fibre-product-closed-model: shared tag(s) 01T6; the existing statement concerns Finite projective-space embeddings of a fibre product and its closed models; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-dc-tensor-preserves: shared tag(s) 01T6; the existing statement concerns $\otimes^{\mathrm L}$ preserves bounded constructible complexes ($\ell$-adic $\Lambda$); it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-equivariant-flat-curve-preparation: shared tag(s) 01T6; the existing statement concerns Equivariant projective flat preparation of a generic curve; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-transverse-tame-open-shriek-exchange: shared tag(s) 01T6; the existing statement concerns Transverse tame boundary exchange of open direct image and extension by zero; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs det-thm-restriction-glue: shared tag(s) 01T6; the existing statement concerns Gluing constructibility of $f^!K$ and restricting the adjunction; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sfb-finite-quotient-normal-proper: shared tag(s) 01T6; the existing statement concerns Normality and properness of an existing finite geometric quotient; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs pqf-lem-locnoeth-lft: shared tag(s) 01T6; the existing leaf concludes local Noetherianity assuming it on the target; the new node handles an arbitrary base by residue-field base change and supplies a minimal-prime affine chart at the specified component point.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-birational-curve-degree-invariance: shared tag(s) 01T6; the existing statement concerns Birational pullback preserves line-bundle degree on proper integral curves; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-finite-generic-dominant-parts: shared tag(s) 00ES; the existing statement concerns Dominant reduced parts of finite-generic schemes are alteration objects; etale families; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-qbar-dual-recollement: shared tag(s) 01T6; the existing statement concerns Verdier-compatible open and closed recollement for arbitrary-field adic coefficients; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-noetherian-log-pair-strict-resolution: shared tag(s) 01T6; the existing statement concerns Strict boundary resolution of an excellent Noetherian log regular pair; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-equivariant-projective-envelope: shared tag(s) 01T6; the existing statement concerns An equivariant homogeneous projective envelope; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-finite-affine-direct-image-support-bound: shared tag(s) 01T6; the existing statement concerns Artin's affine support estimate for the direct image at finite coefficients; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-excellent-quasiprojective-normalized-blowup: shared tag(s) 01T6; the existing statement concerns Normalized blowups preserve quasi-projectivity over an excellent affine base; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-normal-surface-exceptional-curves: shared tag(s) 01T6; the existing statement concerns Finite exceptional-curve data for a normal excellent surface modification; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-ordinary-smooth-orientation: shared tag(s) 01T6; the existing statement concerns Ordinary etale smooth purity with diagonal normalization; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-alteration-cover-closed-fibre-shrink: shared tag(s) 01T6; the existing statement concerns Dimension-inductive gluing of local regular alteration covers; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-local-system-finite-cover-germ-action: shared tag(s) 01T6; the existing statement concerns Monodromy of a local system on germs over a finite etale neighbourhood; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-log-smooth-composition-strict-base-change: shared tag(s) 01T6; the existing statement concerns Composition and strict base change in logarithmic smoothness; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-integral-etale-chart-flatification: shared tag(s) 01T6; the existing statement concerns Simultaneous generically finite flatification over integral etale charts; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-noetherian-local-domain-open-infinite: shared tag(s) 00ES; the existing statement concerns Nonempty opens in a high-dimensional Noetherian local domain are infinite; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-generic-fibre-finiteness-criterion: shared tag(s) 01T6; the existing statement concerns Generic residue extensions and finite generic fibres; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-low-base-constructible-internal-hom: shared tag(s) 01T6; the existing statement concerns Constructible internal Hom over a regular base of dimension at most one; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-a1-lisse-sections-stalk-evaluation: shared tag(s) 01T6; the existing statement concerns Finite stalk detection and Frobenius compatibility for lisse global sections; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-equivariant-marked-nodal-alteration: shared tag(s) 01T6; the existing statement concerns Galois equivariant marked nodal alteration with birational quotients; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-componentwise-normalization-affine-charts: shared tag(s) 00ES; the existing statement concerns Affine charts of componentwise normalization; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-noetherian-affine-line-unit: shared tag(s) 01T6; the existing statement concerns Ordinary finite-coefficient affine-line unit over a Noetherian base; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-separable-stable-modification-flat-pair: shared tag(s) 01T6; the existing statement concerns Separable stable modification of a flat marked curve; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-noetherian-supported-product-calculus: shared tag(s) 01T6; the existing statement concerns Supported products and Cartier interchange on ordinary etale sites; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-local-ordinary-point-blowups-globalize: shared tag(s) 01T6; the existing statement concerns Globalizing ordinary point-blowup towers from finitely many local schemes; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-qbar-generic-duality-model: shared tag(s) 01T6; the existing statement concerns Generic lisse local form of the relative dualizing complex; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-henselian-component-dimension: shared tag(s) 00ES; the existing statement concerns One-dimensional components and strict henselization; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-torsion-torsor-descent: shared tag(s) 01T6; the existing statement concerns Torsors under torsion local systems are local systems; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-surface-point-blowup-geometry: shared tag(s) 01T6; the existing statement concerns Regularity and projectivity of a point blowup on a regular surface; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-generically-finite-quasifinite-over-dimension-one: shared tag(s) 00ES; the existing statement concerns Generic algebraicity gives quasi-finiteness over a point of local dimension at most one; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-dominant-part-coreflection: shared tag(s) 01T6; the existing statement concerns Reduced dominant closure and its functorial properties; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-proper-generic-curve-preparation: shared tag(s) 01T6; the existing statement concerns Compactification and inseparable preparation of a marked relative curve; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-adic-closed-constructible: shared tag(s) 01T6; the existing statement concerns Closed tensor structure and internal-Hom finiteness for adic constructible complexes; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-finite-compact-support-fibre-support-bound: shared tag(s) 01T6; the existing statement concerns Fibre support bound for compactly supported higher direct images at finite coefficients; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-normal-projective-compactification: shared tag(s) 01T6; the existing statement concerns Normal projective compactification over a complete trait; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-rational-stratum-integral-models: shared tag(s) 01T6; the existing statement concerns Filtration quotients with genuine completed integral models; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-regular-log-smooth-monomial-chart: shared tag(s) 01T6; the existing statement concerns Monomial etale charts of regular log-smooth schemes over a trait; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-polynomial-closed-fibre-components: shared tag(s) 00ES; the existing statement concerns Equidimensionality after polynomial extension and localization; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-constructible-subset-closure-dimension: shared tag(s) 01T6; the existing statement concerns Dimension of a constructible subset and its closure over a field; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-per-completion-component-dimension: shared tag(s) 00ES; the existing statement concerns One-dimensional components and completion; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-proper-reduced-algclosed-global-sections-product: shared tag(s) 01T6; the existing statement concerns Global functions on a proper reduced scheme over an algebraically closed field; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-spec-topological-krull-dimension-ring: shared tag(s) 00ES; the existing statement concerns The topological Krull dimension of the spectrum is the Krull dimension of the ring; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-chow-noetherian: shared tag(s) 01T6; the existing statement concerns Chow's lemma over a Noetherian base; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-constructible-module-noetherian-descent: shared tag(s) 01T6; the existing statement concerns A constructible sheaf of $\Lambda$-modules on a qcqs scheme is the inverse image of one on a Noetherian scheme; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-good-curves-boundary-quasifinite: shared tag(s) 01T6; the existing statement concerns Quasi-finite boundary of fibrewise nonempty opens in good curve compactifications; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-chow-finite-type: shared tag(s) 01T6; the existing statement concerns Chow's lemma for separated morphisms of finite type over a qcqs base; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-finite-type-over-noetherian: shared tag(s) 01T6; the existing statement concerns A scheme of finite type over a Noetherian scheme is Noetherian (Stacks 01T6); it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs thm-chow-lemma: shared tag(s) 01T6; the existing statement concerns Chow's lemma; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-open-relative-line-principal-geometry: shared tag(s) 01T6; the existing statement concerns Principal-open geometry of an open relative affine line; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-thickening-systems-dictionary: shared tag(s) 01T6; the existing statement concerns Systems of coherent modules on the thickenings X_n are coherent formal modules on X; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-etale-lisse-open-relative-line-constructibility: shared tag(s) 01T6; the existing statement concerns Lisse coefficients on an open relative affine line over an integer model; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs thm-weil-pbc-stein-inputs: shared tag(s) 01T6; the existing statement concerns The two classical inputs of Stein connectedness; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-spec-irreducible-closed-subsets-primes: shared tag(s) 00ES; the existing statement concerns Closures of points and irreducible closed subsets of the spectrum of a ring; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-dimension-at-point-components: shared tag(s) 00ES; the existing statement concerns Dimension at a point of a finite type affine scheme from its irreducible components; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-stein-finite-fibres-residue-fields: shared tag(s) 01T6; the existing statement concerns Finite fibres and residue extensions of the affine Stein factor; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-closed-point-dimension-local-ring: shared tag(s) 00ES; the existing statement concerns Dimension at a closed point of a finite type algebra over a field is the dimension of the local ring; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-spec-irreducible-components-minimal-primes: shared tag(s) 00ES; the existing leaf describes components of a GIVEN Spec A; the new node also proves residue-field fibre local Noetherianity, finds a Noetherian affine neighbourhood and identifies the generic component point there.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra: shared tag(s) 00ES; the existing statement concerns A quasi-finite cover of affine n-space has dimension at most n; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-finite-algebra-noetherian: shared tag(s) 01T6; the existing statement concerns A module-finite algebra over a Noetherian ring is Noetherian; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-generic-fibre-localization-domain-irreducible: shared tag(s) 00ES; the existing statement concerns The generic fibre of a domain over a domain is an irreducible spectrum; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-graded-finiteness-cohomology: shared tag(s) 01T6; the existing statement concerns Cohomology of a finite type graded module over f^*B~ is a finite B-module; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs prop-compactification-coherence-detailed: shared tag(s) 01T6; the existing statement concerns Compactification coherence; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pur-closed-finite-adjoint-counit-transport: shared tag(s) 01T6; the existing statement concerns Closed finite exceptional adjoint and counit on classical inputs; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-kun-kunneth-via-0f1n: shared tag(s) 01T6; the existing statement concerns Compatibility of the Kunneth map with the projection-formula variant; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sp-smooth-admissible-coordinate-cover: shared tag(s) 01T6; the existing statement concerns A finite admissible coordinate cover over the original base; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-amb-etale-adjoint-locality: shared tag(s) 01T6; the existing statement concerns Etale localization of the ambient adjoint; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-fin-normalization-extends-cover: shared tag(s) 01T6; the existing statement concerns Extending a finite cover by normalization; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-fix-compactification-completed-realization: shared tag(s) 01T6; the existing statement concerns Completed proper/open realization and its projection normalization without a Tor bound; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-cbc-compactification-geometry-fibre-bound: shared tag(s) 01T6; the existing statement concerns Finite-type ambient geometry and a common geometric-fibre dimension bound; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pur-etale-exceptional-constant-tensor: shared tag(s) 01T6; the existing statement concerns Constant-coefficient tensor calculus for the finite etale exceptional adjoint; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pur-compact-top-localization: shared tag(s) 01T6; the existing statement concerns Top compact-support cohomology: dimension bound, dense restriction and cover presentation; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-amb-unbounded-proper-open-interchange: shared tag(s) 01T6; the existing statement concerns Unbounded torsion-coefficient proper/open interchange with its canonical maps; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-integral-direct-image-constructible: shared tag(s) 01T6; the existing statement concerns The integral derived direct image of a constructible complex along a finite-type morphism is constructible; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs thm-exc-curve-open-dimension-general: shared tag(s) 01T6; the existing statement concerns Open direct-image dimension on arbitrary curves; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-integral-compact-support-constructible: shared tag(s) 01T6; the existing statement concerns The integral compact-support direct image of a constructible complex is constructible; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pur-noetherian-etale-section-specialization: shared tag(s) 01T6; the existing statement concerns Normalized section specialization for ordinary etale dualizing complexes over a Noetherian base; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-class-compact-support-comparison: shared tag(s) 01T6; the existing statement concerns On the coefficient class the compact-support functor is computed on the étale site; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pur-finite-universal-smooth-trace: shared tag(s) 01T6; the existing statement concerns The finite smooth trace is the scalar extension of the prime-power trace; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-amb-etale-compact-comparisons: shared tag(s) 01T6; the existing statement concerns The etale compact-support comparisons; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-kun-finite-type-local-dimension: shared tag(s) 01T6; the existing statement concerns Finite local dimension for finite type schemes over a field; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-weil-pbc-irreducible-lisse-strata: shared tag(s) 01T6; the existing statement concerns Irreducible lisse strata; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs det-sp-tower-gamma: shared tag(s) 01T6; the existing statement concerns Tower orientation and tower purity isomorphism; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-kun-geometric-reduced-perfect: shared tag(s) 01T6; the existing statement concerns Geometric reducedness over a perfect field; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pur-closed-supported-cup-vanishing: shared tag(s) 01T6; the existing statement concerns Restriction to a closed support detects the zero action on supported cohomology; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sf-finite-proetale-pushforward-constructible: shared tag(s) 01T6; the existing statement concerns Intrinsic finite-coefficient constructibility under nonseparated finite-type pushforward; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs prop-sf-open-closed-triangle-all-stages: shared tag(s) 01T6; the existing statement concerns The open–closed triangle at every coefficient stage; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-kun-0f1h-sep-reduction: shared tag(s) 01T6; the existing statement concerns Reduction to a separably closed ground field; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pur-finite-coefficient-adjoint-comparisons: shared tag(s) 01T6; the existing statement concerns Finite-coefficient exceptional adjunction and coefficient mates over an arbitrary field; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pur-quasifinite-flat-weighted-trace: shared tag(s) 01T6; the existing statement concerns Weighted sum on etale sheaves for a quasi-finite flat morphism; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-kun-0f14b: shared tag(s) 01T6; the existing statement concerns Kunneth formula, one proper factor, $\kunZn$-coefficients; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs fin2-lem-lisse-trivialized-finite-etale: shared tag(s) 01T6; the existing statement concerns Finite etale trivialization of a lisse sheaf; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs thm-amb-p1-decomposition: shared tag(s) 01T6; the existing statement concerns The projective-line calculation before purity; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-kun-finite-closed-subscheme: shared tag(s) 01T6; the existing statement concerns Closed subsets consisting of closed points; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs def-asd-compactifiable: shared tag(s) 01T6; the existing node defines Compactifiable morphism; it does not assert the fibre chart/minimality theorem.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pur-etale-closed-chart-exceptional-preservation: shared tag(s) 01T6; the existing statement concerns Exceptional inverse image on a closed affine-space chart; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-fin-compact-bounded-and-base-change: shared tag(s) 01T6; the existing statement concerns Compact direct images needed by the generic argument; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-fin-generic-curve-model: shared tag(s) 01T6; the existing statement concerns A generic curve model with finite comparison boundary; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pur-affine-line-support-geometry: shared tag(s) 01T6; the existing statement concerns Finite-type and Noetherian geometry of the affine-line support pair; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pur-etale-support-map-compatibility: shared tag(s) 01T6; the existing statement concerns Etale proper-support normalization intertwines exchange and projection; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-cbc-integral-compact-support-uniform-restriction: shared tag(s) 01T6; the existing statement concerns Integral compact-support image preserves uniform constructibility; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sc-support-dimension-union: shared tag(s) 01T6; the existing statement concerns A sheaf supported in low dimension is a filtered union; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-kun-dimension-finite-type: shared tag(s) 01T6; the existing statement concerns Finiteness of the dimension of a finite type scheme; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-pur-rational-weil-naturality-mate: shared tag(s) 01T6; the existing statement concerns Rational smooth purity naturality and Frobenius mate identification; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-fibre-component-noetherian-affine-chart vs lem-sc-dim-one-ample-invertible: shared tag(s) 01T6; the existing statement concerns A separated finite-type scheme of dimension at most one has an ample invertible sheaf; it does not give a Noetherian affine minimal-prime chart at a prescribed generic component point of a locally-finite-type fibre.

lem-trf-affine-minimal-prime-stalk-annihilator vs lem-trf-fibre-component-relative-associated: shared tag(s) 02OK, 05BV; the parent concludes fibre-associated and relative-assassin membership, whereas this node starts with an arbitrary minimal prime on a Noetherian chart and concludes a stalk annihilator; it has no morphism, component or relative-assassin data.

lem-trf-affine-minimal-prime-stalk-annihilator vs lem-trf-generic-cm-locus-field: shared tag(s) 05BV; the existing statement concerns Dense Cohen–Macaulay locus in a finite type algebra over a field; it does not give the maximal-ideal annihilator in the stalk at an arbitrary point with a minimal Noetherian affine coordinate prime.

lem-trf-affine-minimal-prime-stalk-annihilator vs lem-sc-hilbert-embedded-points-affine-removal: shared tag(s) 05BV; the existing statement concerns Removing embedded primes from a finite module; it does not give the maximal-ideal annihilator in the stalk at an arbitrary point with a minimal Noetherian affine coordinate prime.

lem-trf-affine-minimal-prime-stalk-annihilator vs lem-weil-pbc-noetherian-minimal-prime-associated: shared tag(s) 05BV; the existing algebra leaf gives Ann_A(a)=p in the chart ring; the new node proves Ann_(O_(T,y))(w)=m_y after localization and the affine-stalk identification, on an arbitrary ambient scheme.

lem-trf-affine-minimal-prime-stalk-annihilator vs lem-weil-pbc-cm-local-maximal-chain-length: shared tag(s) 05BV; the existing statement concerns Maximal chains of primes in a Cohen–Macaulay local ring have length the dimension; it does not give the maximal-ideal annihilator in the stalk at an arbitrary point with a minimal Noetherian affine coordinate prime.

lem-trf-affine-minimal-prime-stalk-annihilator vs lem-weil-pbc-associated-prime-power-quotient: shared tag(s) 05BV; the existing statement concerns A prime minimal over an associated prime plus (x) is associated to M/x^nM for some n; it does not give the maximal-ideal annihilator in the stalk at an arbitrary point with a minimal Noetherian affine coordinate prime.

lem-trf-affine-minimal-prime-stalk-annihilator vs lem-weil-pbc-minimal-support-prime-associated: shared tag(s) 05BV; the existing algebra leaf gives an associated prime of a finite module; it has no scheme stalk, local-ring maximal ideal identification or associated POINT conclusion.

lem-trf-affine-minimal-prime-stalk-annihilator vs lem-weil-pbc-cm-module-good-sequence-element-nonzerodivisor: shared tag(s) 05BV; the existing statement concerns An element good with respect to a maximal regular sequence of a Cohen–Macaulay module is a nonzerodivisor; it does not give the maximal-ideal annihilator in the stalk at an arbitrary point with a minimal Noetherian affine coordinate prime.

lem-trf-affine-minimal-prime-stalk-annihilator vs lem-weil-pbc-depth-le-dim-associated-prime: shared tag(s) 05BV; the existing statement concerns The depth of a module is at most dim(R/p) for every associated prime p; it does not give the maximal-ideal annihilator in the stalk at an arbitrary point with a minimal Noetherian affine coordinate prime.

## Delivery validation

The required deliver.py --no-push completed with OK (not pushed), server preflight passed, at 71369bcc1c1 on 2026-10-22. The item statement and all maintainer-owned metadata compare unchanged against the live read clone; changed fields are proof, proof_deps, proof_origin and split_report only. The three proof steps are 438, 349 and 374 characters (1161 total). Both new nodes have status unsplit, empty proof/proof_deps and null proof_origin. Every step use has a verbatim citation quote. Earlier preparatory attempts exited for absent node files and for a report still being generated; both conditions were repaired before the successful dry run. No dry-run process is left active. Final push follows a fresh dry run including this report update.


## Landing return repair (2026-10-22)

The return at branch head 9bdd992d6d1 is a landing/promotion refusal, not a mathematical rejection. I retained the delivered node files, report, citations and searches. After verifying that no deliver.py process was active, I ran the mandated initial dry run; it exited successfully with `OK (not pushed)` at 10101ec071b. The delivery tool rebuilt the retained split on the current origin/sheaf-dag rather than reusing the returned head. I read the current return entry and the released stage-1 repair note; the latter still requires two new statement-only proof tasks and a short assembly.

Compared with the current shared item, the retained item differed only in proof, proof_deps, proof_origin and split_report. Its statement, statement dependencies, source, blueprint ancestry, searches, Lean information and maintainer review fields agreed. Neither proposed child id exists in the current shared DAG. I re-read the statements of all current inputs retained in the old-argument handoff: def-pc-scheme-fibre, lem-weil-pbc-lft-base-change, def-weil-pbc-noetherian-ring, def-weil-affine-spectrum, pqf-def-locnoeth, pqf-lem-locnoeth-lft, lem-weil-pbc-affine-open-spec-points, def-sc-generic-point, def-weil-irreducible-components, lem-weil-pbc-noetherian-minimal-prime-associated, lem-weil-pbc-associated-prime-localization-depth-zero, lem-weil-pbc-affine-open-stalk-localization and def-sc-associated-points. Their current statements still supply exactly the hypotheses and conclusions described in Review by Q27. The associated-point definition retains its known source-tag typo, without changing its mathematical statement.

I adjusted parent step 3 to name the fibre projection i_t and its image point i_t(y) explicitly. This makes the fibre point versus total-space point distinction visible and matches the existing Lean signature's image sets. The argument is image membership followed by union membership at index t, with the homeomorphism onto f^{-1}(t) taken verbatim from def-pc-scheme-fibre. The citation quote remains valid; no new lemma or search question is introduced. Parent steps 1 and 2 still use precisely the two child statements quoted in citations.json, whose hypotheses are checked in the existing review. Both children remain unsplit and proof-free; every old argument remains preserved in the handoff section. I re-read the logged search results rather than repeating unchanged queries. I also rechecked the upstream partial minimal-prime theorem and the item's Sheaf declaration, whose proof still ends in sorry, so there is no new complete attachment.

For this repair I reopened the Stacks source statements for 05AT, 02OJ, 02OK, 05AH, 01T4, 01T6, 00ES, 05BV, 05BZ and 01HV. The chart and stalk conclusions, including nonreduced and reducible examples, remain faithful to these sources. The three proof uses have exact statement quotes; neither child cites its parent as a dependency; no long non-elementary assembly step hides another argument. The final validation following this report update is run before push. This repair changes the explicit projection argument and the repair report as well as rebasing the delivery; it is not an unchanged re-push.


## Latest landing-return repair (returned head dac3aba47ef, 2026-10-22)

This entry supplements the earlier landing-return repair, which concerned head 9bdd992d6d1. The current coord/returns/Q27.md entry instead identifies dac3aba47ef (12:09 UTC) and repeats the landing/promotion refusal. The retained sandbox has been continued, including its two child statements, every old proof argument, report, verbatim citation file and logged search results. The mandatory first dry run in this repair exited with OK (not pushed) at 799ad0c94d1, rebuilding the delivery on the current server DAG. No direct git command was run and no repository or launcher file was edited.

I compared the current shared item field by field with the retained item: only proof, proof_deps, proof_origin and split_report differed. The statement, statement dependencies, source, blueprint, Lean information, created and reviewed metadata still agree. Neither child id is present in the current shared DAG. I re-read the latest released keep_plan repair note, which still requires at least two comparable statement-only children and an assembly of at most 3000 characters. These requirements remain satisfied. This is a fresh adjustment to the retained split and its report, not an unchanged re-push.

### Review by Q27 of the current return

I reopened the statements of both child nodes and all current inputs of the retained five-step argument: def-pc-scheme-fibre, lem-weil-pbc-lft-base-change, def-weil-pbc-noetherian-ring, def-weil-affine-spectrum, pqf-def-locnoeth, pqf-lem-locnoeth-lft, lem-weil-pbc-affine-open-spec-points, def-sc-generic-point, def-weil-irreducible-components, lem-weil-pbc-noetherian-minimal-prime-associated, lem-weil-pbc-associated-prime-localization-depth-zero, lem-weil-pbc-affine-open-stalk-localization and def-sc-associated-points. Their statements still provide the precise inputs described in the original Review by Q27: arbitrary base change preserves local finite type; a fibre over a field is locally Noetherian; its generic component point gives a minimal prime on a Noetherian affine neighbourhood; this prime is an annihilator, remains one after localization, and the localization is the scheme stalk. I also reread def-pc-scheme, def-weil-finite-type-morphism and def-weil-flat-morphism. The hypotheses have not changed. In particular neither child presupposes that the fibre is reduced or irreducible, and the ambient scheme in the stalk lemma need not be locally Noetherian away from the given affine open.

For step 1, the first child's actual conclusion supplies local Noetherianity, U containing y, the section ring A and minimal p_y, under exactly the local-finite-type/component/generic-point data in the parent. For step 2, the second child's actual conclusion supplies a stalk element with maximal-ideal annihilator and the first assertion. These are statements quoted in citations.json, not constructions borrowed from their proofs. For step 3, I replaced the previous prose image argument by explicit witnesses: for x=i_t(y), y proves image membership and t proves membership in the union of the images. The current fibre-definition statement says verbatim that the first projection is a homeomorphism onto f^{-1}(t); it identifies this x with the point denoted y in the parent's final assertion. This change keeps the original statement intact while making the two ambient point spaces and the union convention explicit. The original five steps remain in the old-argument handoff; the report's earlier descriptions of a verbatim final assembly step are historical and are superseded by this repair.

For the item I reread Divisors 05AH, 05AT and 02OJ. For the chart child I reopened Morphisms 01T4 and 01T6 and Algebra 00ES; the latter identifies closures and components in Spec A, and the retained closure/maximality argument justifies passage to the affine neighbourhood. For the stalk child I reopened Algebra 05BV and 05BZ, Divisors 02OK and Schemes 01HV. The forward implication of 02OK requires only an affine open of an arbitrary scheme, which agrees with this child's hypotheses; the algebraic application uses the explicitly Noetherian A. The existing associated-point definition's source-tag typo remains reported, without changing its mathematical definition. No forbidden source is used.

I repeated the attachment check in lean/WeilConjectures by the item's tag and the relative-assassin/fibre-component concepts: no complete project theorem appeared. The item declaration in lean/Sheaf/TraceFormula/FibreComponentRelativeAssociated.lean still ends in sorry, and the upstream primeIdealOf_mem_minimalPrimes theorem still covers only the minimality clause on a given affine chart. I read the retained searches.jsonl results and kept the unchanged questions and records; no new node or Mathlib query is claimed in this repair.

The original small cases remain valid: empty fibre is vacuous; Spec K uses w=1; K[e]/(e^2) uses the minimal prime (e) and w=e; K[u,v]/(uv) allows either component; K[x,y]/(x^2,xy) has Ann(y)=(x) at the component prime despite the embedded associated point. Each proof use still has a verbatim statement quote, each unsplit child is proof-free, and no assembly step exceeds 2000 characters. The projection/union argument is elementary image and union membership and creates no new lemma. A final dry run after these edits precedes the push.


## Repair of the landing return at d040b1010eb (2026-10-23)

I continued the retained sandbox, including the prior report, both unsplit children, all five old arguments, citations.json and searches.jsonl. The return asks for rebasing onto the current DAG and re-reading changed citations after a side-completion promotion refusal. The mandatory initial dry run was run before editing; it exited with a new duplicate-tag diagnostic naming lem-sfb-closed-component-stalk-calculus. I opened that full node and added the precise 00ES distinction under Not duplicates. It assumes a globally Noetherian ambient scheme, uses a closed subscheme and a reducedness hypothesis for its component clause, and concludes a stalk-ideal bijection. The chart child assumes none of those extra conditions, produces local Noetherianity by the residue-field fibre, and concludes minimality of a prime in the affine section ring. No new node or search question is introduced by this repair.

I compared the retained parent with the current shared DAG field by field: only proof, proof_deps, proof_origin and split_report differed. I rebuilt the sandbox parent from that current node and reapplied only those four split fields. Both child ids are still absent from the current shared DAG. The delivery tool, as required, builds a fresh commit on the server's current DAG rather than using the returned branch base. This repair also changes the assembly argument and the duplicate assessment; it is not an unchanged re-push.

### Current return review by Q27

I reopened every current node statement used in the old-argument handoff and every statement dependency of the children: def-pc-scheme, def-weil-flat-morphism, def-weil-finite-type-morphism, def-pc-scheme-fibre, def-sc-generic-point, def-weil-irreducible-components, def-sc-associated-points, def-weil-affine-spectrum, def-weil-pbc-noetherian-ring, pqf-def-locnoeth, lem-weil-pbc-lft-base-change, pqf-lem-locnoeth-lft, lem-weil-pbc-affine-open-spec-points, lem-weil-pbc-noetherian-minimal-prime-associated, lem-weil-pbc-associated-prime-localization-depth-zero and lem-weil-pbc-affine-open-stalk-localization. Their current statements supply the same hypotheses and conclusions described in the original review; no stale identifier or missing conclusion was found. In particular the base-change lemma allows arbitrary base change, local Noetherianity is required only of Spec kappa(t), and the stalk-localization statement supplies a ring isomorphism, not merely a module or set identification. The associated-point definition still has its reported source-tag typo 02OZ versus 02OJ; its mathematical statement is correct and is outside my edit scope.

I reread the item against Divisors 05AH (lemma-minimal-support-in-ass), 05AT (definition-relative-assassin), and 02OJ (definition-associated). For the chart child I read Morphisms 01T4 (lemma-base-change-finite-type), 01T6 (lemma-finite-type-noetherian), Properties 01OV (definition-noetherian), and Algebra 00ES (lemma-irreducible). For the stalk child I read Algebra 05BV (lemma-ass-minimal-prime-support), 05BZ (lemma-localize-ass), Divisors 02OK (lemma-associated-affine-open) and Schemes 01HV (lemma-spec-sheaves). These exact source statements cover arbitrary nonreduced and reducible fibres; local finite type over a field, rather than Noetherianity of the original base, provides the needed Noetherian hypothesis. All original chart, minimality, localization and annihilator arguments remain intact in the retained handoff above.

Step 1 now explicitly chooses the affine U and defines A as O_T(U), matching the chart child's actual conclusion. Step 2 applies the second child to this same T,U,y,A, so its Noetherian and minimality hypotheses are exactly those just obtained; the child's actual statement gives both the maximal-ideal annihilator witness and associated-point membership. Step 3 distinguishes the fibre point y from x=i_t(y) in X; y is the witness for membership in the image at t, and t is the witness for the union. The current fibre-definition statement gives exactly the required homeomorphism onto f^{-1}(t). This is an elementary image/union argument. The current citations.json covers all three uses with verbatim portions of these statements; it was checked against both child statements and the current fibre definition. There are no hidden non-elementary facts or long proof steps in this assembly.

I reread the actual logged Mathlib results, keeping the successful searches and the unavailable LeanSearch result separate. The questions and child statements have not changed, so I did not repeat or invent queries. The live WeilConjectures tree still has no exact item tag or relative-associated-point theorem; the Sheaf item still ends in sorry and is not an attachment. The current blueprint searches for Noetherian affine and stalk annihilator return no statement of either complete child, and the ancestor remains lem-trf-local-term-locality. The existing unit and chapter route and blueprint metadata are preserved.

The empty-fibre case is vacuous; Spec K has annihilator witness 1; K[e]/(e^2) has witness e at its minimal prime; K[u,v]/(uv) admits either component; and K[x,y]/(x^2,xy) has Ann(y)=(x) despite its embedded prime. These checks still rule out inadvertently assuming reducedness, irreducibility or absence of embedded points. Neither new child assumes flatness, while the parent's original flatness hypothesis is retained. Both children remain statement-only with no proof or proof dependencies. Checks B through E were repeated against these statements and sources, particularly C1/C4 and the new duplicate diagnostic. No Lean, compiler, repository file or launcher file was written. Procedural correction for this session: one early diagnostic mistakenly included read-only git status/log commands in the shared repository; they made no mutation, and all subsequent comparisons use direct file reads and the required delivery tool.

Final validation follows this report update; only one deliver.py invocation will be active at a time.
