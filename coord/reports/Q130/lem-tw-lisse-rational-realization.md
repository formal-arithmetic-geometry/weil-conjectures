# Repair of lem-tw-lisse-rational-realization by Q130

## Files written

- Item: statement unchanged; seven-step assembly of six new nodes and existing infrastructure.
- lem-tw-lisse-localization-restriction: statement; unsplit, no Mathlib match; source Lemma 6.8.2, Definitions 6.8.3 and 6.8.8; source restriction and exact scalar localization in Proposition 6.8.14(2).
- lem-tw-lisse-lattice-heart-lift: statement; unsplit, no Mathlib match; source Lemma 6.8.13, Proposition 6.8.4(6), Proposition 6.8.11(3); rationalized lattice lifting in Proposition 6.8.14(2).
- lem-tw-lisse-tensor-pullback-realization: statement; unsplit, no Mathlib match; source Remark 6.8.15, tensor and ordinary module pullback; agent specification of completion-map normalization.
- lem-tw-lisse-scalar-comparison-coherence: statement; unsplit, no Mathlib match; source Lemma 6.8.2, Proposition 6.8.14(1), Remark 6.8.15; agent specification of quotient-diagram coherence and finite scalar comparisons.
- lem-tw-lisse-point-sections-realization: statement; unsplit, no Mathlib match; source Lemma 6.8.12, Proposition 6.8.14(2) at a geometric point, Remark 6.8.15; agent specification of point normalization.
- lem-tw-lisse-point-transport-realization: statement; unsplit, no Mathlib match; source Remark 6.8.15, point automorphism pullback; agent specification of restriction/coprojection normalization and its iterates.

## Attachments

None. The item tag has no match in WeilConjectures/. Sheaf.Paper.LisseRationalRealization.lisse_rational_realization is a sorry theorem (line 258), not a completed upstream attachment. The search of the upstream source for rational/lisse realization gives unrelated tangent/cotangent and final-theorem references.

## WANTED

None. Read the local Bhatt–Scholze PDF pages 58–62 (the 6.8 coefficient section), together with the current blueprint lem-tw-dual-negation and its unit/chapter. The comparison normalizations not explicit in that paper remain agent formulations, identified as such in each source.place. No SGA source or trace route is used.

## What was wrong and what is repaired

The released repair note requests work distribution: the previous 12182-character proof was too large. There was no retained sandbox node/report/search log, only dispatcher marker files. The copied current live node is the returned 13-step proof with its earlier reviews and Lean metadata; no previously completed sandbox work was discarded. The original statement, statement dependencies, blueprint provenance and module ownership are unchanged. Six nodes now expose separate arguments, with empty proof/proof_deps and null proof_origin. At least four were required. The existing constructible Hom comparison is reused rather than duplicated. The parent assembly contains 2232 characters; no step exceeds 2000 characters.

## Unfinished work

The six new statement-only nodes are deliberately unsplit for independent workers. No Lean was written or compiled. Their source arguments are preserved below, not hidden inside their statements.

## Not duplicates

- lem-tw-lisse-localization-restriction vs lem-per-rational-module-realization-functor: reuse its exact scalar functor and cohomology assertion; the new work is its specified pro-etale slice restriction and rational-lisse image, including charts not assumed finite type.
- lem-tw-lisse-localization-restriction vs lem-per-continuous-rational-derived-realization: the latter is phrased for the PBC category and does not identify the sf lisse predicate and the strict-limit restriction normalization. It is not used to bypass the returned route.
- lem-tw-lisse-lattice-heart-lift vs lem-weil-pbc-lisse-e-constructible-integral-lattice: the existing result supplies only a constructible lattice; the new statement asserts the heart and specified local rationalized-isomorphism lifts for every choice.
- lem-tw-lisse-lattice-heart-lift vs lem-weil-pbc-lisse-lattice-etale-local: the existing result supplies locally free integral lattices on charts, not lifts between a global constructible lattice and those chart lattices in the rationalized heart.
- lem-tw-lisse-tensor-pullback-realization vs lem-zl-rational-realization-tensor-comparison: that comparison assumes separatedness, is tensor-only and is expressed through a PBC category equivalence; here arbitrary maps and the specific eta/chi degree-zero normalization are required.
- lem-tw-lisse-tensor-pullback-realization vs lem-tw-ordinary-completed-integral-pullback: that is an integral completion comparison, not its scalar-localization square and its lisse degree-zero tensor/pullback normalization.
- lem-tw-lisse-scalar-comparison-coherence vs lem-weil-finite-free-completed-scalar-comparison: the latter is one integral scalar-completion map; the new statement asserts simultaneous rational scalar/tensor/pullback diagrams and their exact normalization.
- lem-tw-lisse-scalar-comparison-coherence vs lem-sfb-ringed-derived-monoidal-comparisons: the latter concerns ordinary derived functors; the new assertion identifies the completed operations and strict quotient diagrams with these functors.
- lem-tw-lisse-point-sections-realization vs lem-weil-point-sections-scalar-extension: the existing result is finite integral coefficient extension, not inversion of a uniformizer, rational fibre identification and tensor normalization.
- lem-tw-lisse-point-sections-realization vs lem-zl-point-realization-coefficient-comparison: the latter has pulled-back condensed target coefficients and a different target realization; it does not state this ordinary localized-sheaf sections map.
- lem-tw-lisse-point-transport-realization vs lem-weil-point-automorphism-restriction-natural: that lemma asserts naturality of integral restriction/coprojection, not agreement of completed kappa with the ordinary unit after rational realization or iterates.
- lem-tw-lisse-point-transport-realization vs lem-real-lisse-path-fibres: etale paths on smooth connected schemes are a different construction, and that node depends on the item, so citing it would be circular.

Whole-DAG keyword/source searches and blueprint_refs searches for lisse, lisse heart, 6.8.13, 6.8.14, rationalized, localization realization, point transport, scalar extension and slice restriction found these comparison candidates. Definitions of normalization merely define the conditions; they do not prove them. New ids were checked absent before creating files. No new node carries a Stacks tag.

## Mathlib searches and reading

Each new node has its own plain-language semantic search, a second phrasing, Loogle, grep, and LeanSearch; exact queries and responses are in its record and searches.jsonl. All returned successfully. The scalar Loogle query CategoryTheory.MonoidalFunctor returned unknown identifier; a subsequent SheafOfModules.pullbackObjFreeIso query was run and read. Loogle/general semantic hits were free, freeHomEquiv, pullback, pullbackComp, pullbackObjFreeIso and sections/unitHomEquiv. Read Mathlib/Algebra/Category/ModuleCat/Sheaf/Free.lean:30–105, PullbackContinuous.lean, PullbackFree.lean and Sheaf.lean. These give ordinary module operations, without constructible completed/rational comparison. Read Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean:40–90: it defines continuous Z_l coefficients and cohomology, not the rational heart equivalence. AdicCompletion/AsTensorProduct.lean:80–145 concerns ordinary ring/module completion, not sheaf towers and their normalized operations. Other semantic hits concern Zariski structure sheaves, etale algebra localization, integral closures, or arbitrary abstract derived localization, not these assertions. No exact match or one-line specialization was found.

## Review by Q130

I read Bhatt–Scholze Lemma 6.8.2 for the completed/continuous ring identity, Definitions 6.8.3 and 6.8.8 for the target category, Proposition 6.8.4(6) and Lemma 6.8.13 for the two different lattice assertions, Proposition 6.8.11(3) for constructibility of degree-zero integral sheaves, Lemma 6.8.12 and Proposition 6.8.14(2) for Hom localization, and Remark 6.8.15 for the ordinary ringed pullback formula. The item has no stronger global lisse-lattice assertion. The new lattice node preserves that distinction. The new operation, scalar, sections and transport statements isolate the explicit agent normalization arguments of the old proof, not purported verbatim theorems of the PDF.

Assembly step 1 uses pqf-lem-locnoeth-lft for local noetherianity, lem-kun-dimension-finite-type for dimension, continuous-coefficients-immersion-restriction for the ring identity, and lem-tw-lisse-localization-restriction for exactness/restriction and the local lisse image. Their statements, not their proof constructions, are what is used. Finite type supplies quasi-compactness; no separatedness is invoked. Quasi-compact etale charts over a noetherian scheme meet the noetherian finite-dimensional hypotheses.

Assembly step 2 uses the stratified-perfect characterization to identify sf and PBC integral categories, the actual Hom formula in lem-per-constructible-rational-hom-comparison for full faithfulness, lem-tw-lisse-localization-restriction for degree-zero sheaves and lem-tw-lisse-lattice-heart-lift for local lifts and essential image. The existing Hom theorem explicitly uses the same quotient coefficient rings and actual scalar-extension map; its integral category agrees by the cited characterization. The new lattice statement includes both a constructible global N and locally free chart M_i, membership in the integral category, the specified lift and its inverse. No proof of a cited node is mined for extra objects.

Assembly step 3 uses precisely the derived isomorphisms and degree-zero/basis formulas in lem-tw-lisse-tensor-pullback-realization. Its statement introduces the coefficient square, chi and eta rather than relying on an unspecified isomorphism. There is no flatness assumption on a scheme map; finite local freeness of the lisse sheaf is what removes derived tensor. Step 4 uses the diagrams and simultaneous quotient normalizations expressly asserted in lem-tw-lisse-scalar-comparison-coherence, including scalar towers and sign +1 in degree zero.

Assembly step 5 uses the derived sections-localization map, its cohomology normalization and tensor/unit assertion in lem-tw-lisse-point-sections-realization, together with the map for x from lem-tw-lisse-tensor-pullback-realization. Sections exactness is confined to s=Spec(k); the statement does not claim exact sections on general X. Step 6 uses the kappa-to-unit equality, fraction formula, naturality and all iterates stated in lem-tw-lisse-point-transport-realization. The source and target are successive pullbacks, not a mistakenly identified fixed point object. Step 7 uses the explicit common-field representative/equality rule in def-weil-algebraically-closed-coefficients and the scalar compatibilities in lem-tw-lisse-scalar-comparison-coherence, lem-tw-lisse-point-sections-realization and lem-tw-lisse-point-transport-realization. Taking one compositum per finite diagram and applying these equalities is the elementary descent step.

I opened each of these cited statements and copied verbatim statement text to citations.json. The older infrastructure statements used in the retained arguments were also inspected: their noetherian/finite-dimensional hypotheses are supplied in assembly step 1; the scalar-localization Hom lemma requires bounded-below targets and countable Hom continuity, supplied for constructible objects by the existing compactness node. The point fibre equivalence gives finite-dimensionality, not a monoidal assertion, so the retained point argument explicitly checks tensor on finite sums of units.

Small cases checked: empty X and rank zero give zero sheaves and empty bases; disconnected X allows variable finite ranks; torsion lattices may vanish after localization without contradicting full faithfulness of the rational category; E=E′ gives the completeness/unit maps; identity pullback has the unit formula; h=id and zero transport iterations give identities. Arbitrary h may act on the base field, so no k-linearity was added. None of the parent or new statements was weakened. I checked B–E of delivery-errors against these files: statement-only children, self-contained objects, definition dependencies, no duplicate or circular re-labelling of the whole item, exact cited conclusions, no missing non-elementary assembly step, correct coefficient categories and derived-form isomorphisms. The human re-split order explicitly requests moving separate arguments into statement-only children; six balanced tasks replace the single oversized task.

## Allocation of the original argument (verbatim)

This is the full returned argument, retained as handoff material. Child node statements contain no proof. Steps 1–3 belong to lem-tw-lisse-localization-restriction (the Hom-localization part of step 2 is already lem-per-constructible-rational-hom-comparison). Step 4 belongs to lem-tw-lisse-lattice-heart-lift; steps 5–6 to lem-tw-lisse-tensor-pullback-realization; steps 7–8 to lem-tw-lisse-scalar-comparison-coherence; steps 9–10 to lem-tw-lisse-point-sections-realization; steps 11–12 to lem-tw-lisse-point-transport-realization. Step 13 remains the elementary common-stage assembly, using lem-tw-lisse-scalar-comparison-coherence for finite scalar coherence.

### Original step 1

A field is noetherian (its only ideals are $0$ and the unit ideal). Apply [pqf-lem-locnoeth-lft] to the structure map of $X$ and use its quasi-compactness, part of finite type, to see that $X$ is noetherian. By [lem-kun-dimension-finite-type] it has finite Krull dimension. Its underlying noetherian space has every open quasi-compact, so $X$ is qcqs even without separatedness. The same statements apply to $X'$ and to quasi-compact etale charts of either. The coefficient identifications of [lem-weil-pbc-continuous-coefficients-immersion-restriction] identify $\widehat R_X$ with the continuous integral coefficient sheaf and $E_X$ with its sheaf localization. Thus the lattice and continuity results cited below concern exactly these rings.

Cited statements: pqf-lem-locnoeth-lft, lem-kun-dimension-finite-type, lem-weil-pbc-continuous-coefficients-immersion-restriction. Source: Lemma 6.6.10(1), Lemma 6.8.2; Stacks Tag 01T6, morphisms-lemma-finite-type-noetherian.

### Original step 2

Put $B=\widehat R_X$, $t=\varpi$ and $F(K)=B[1/t]\otimes_B^LK$. Localization is exact: sectionwise localization is flat by [lem-weil-pbc-localization-flat] and preserves kernels, while module sheafification is exact by [lem-weil-pbc-ringed-site-module-sheafification-exact]; hence localization of an exact sheaf sequence is exact after sheafification. It follows that $H^i(FK)=H^i(K)[1/t]$. For integral constructible $K$, [lem-weil-pbc-integral-constructible-bounded-below-compactness] supplies bounded-below coproduct continuity of global derived Hom. Taking $H^0$ gives the Hom continuity hypothesis of [lem-weil-pbc-scalar-localization-derived-hom] (cohomology of a direct sum of module complexes is the direct sum of cohomology, since cycles and boundaries have finite support). Apply that lemma to bounded integral constructible $K,L$. It gives
$$\operatorname{Hom}(K,L)\otimes_RE\cong\operatorname{Hom}_{D(E_X)}(FK,FL),\quad u\otimes a\mapsto aF(u).$$
The same lemma gives identity and composition compatibility. By [def-weil-rationalization-karoubi] these are precisely the Hom groups of the raw rationalization, so $F$ descends to a fully faithful functor with exactly the prescribed arrow formula.

Cited statements: lem-weil-pbc-localization-flat, lem-weil-pbc-ringed-site-module-sheafification-exact, lem-weil-pbc-integral-constructible-bounded-below-compactness, lem-weil-pbc-scalar-localization-derived-hom, def-weil-rationalization-karoubi. Source: Lemma 6.8.12 and Proposition 6.8.14(2), full faithfulness.

### Original step 3

Restriction to a site slice commutes with sheaf tensor by [lem-sfb-localized-site-tensor-restriction], and with the strict derived limit by [lem-sp-slice-restriction-strict-derived-limit]. Thus it also commutes with the coefficient localization and the completed coefficient constructions used here. The sheaf-site interpretation of a weakly etale chart is [lem-weil-proetale-weakly-etale-localization]. On an object of the lisse source, restrict its given local isomorphism with a finite sum of the coefficient unit and apply $F$. By [lem-weil-constant-coefficient-objects-constructible] the unit is represented by $B[0]$, whose image is $E_X[0]$. Consequently $FK$ is locally finite free in degree zero. This also identifies the lisse heart with a full subcategory of ordinary sheaves: morphisms between complexes concentrated in degree zero in a derived category are their sheaf morphisms. The standard heart is [def-weil-constructible-heart], with the cohomological standard classes of [def-weil-constructible-standard-tstructure]; exact localization carries both classes into their ordinary cohomological counterparts.

Cited statements: lem-sfb-localized-site-tensor-restriction, lem-sp-slice-restriction-strict-derived-limit, lem-weil-proetale-weakly-etale-localization, lem-weil-constant-coefficient-objects-constructible, def-weil-constructible-heart, def-weil-constructible-standard-tstructure. Source: Definitions 6.8.3 and 6.8.8; restriction of the localization realization.

### Original step 4

Conversely let $L\in\operatorname{Loc}(X,E_X)$. By [lem-weil-pbc-lisse-e-constructible-integral-lattice] there is a constructible integral sheaf $N$ with $N[1/t]\cong L$. By [lem-weil-pbc-integral-stratified-perfect-characterization], $N[0]$ is an integral constructible derived-complete object, so its rationalization is in the standard heart. To verify that this object is lisse, use [lem-weil-pbc-lisse-lattice-etale-local] and refine its etale cover by quasi-compact charts $Y_i$. It gives integral finite locally free $M_i$ with $M_i[1/t]\cong L|_{Y_i}$. The same stratified-perfect characterization puts $M_i[0]$ in the integral constructible category. Step 2 on the noetherian finite-dimensional $Y_i$ lifts the specified isomorphism $N[1/t]|_{Y_i}\cong M_i[1/t]$ and its inverse uniquely to the rationalized category. The lifts are inverse because their composites realize to identities and realization is faithful. Each $M_i$ is pro-etale locally a finite free coefficient module, hence these local lifts give the required local isomorphisms for the rationalization of $N$. Together with Step 3 and Step 2 this proves the equivalence and its exact Hom normalization; it never asserts that $L$ has a globally lisse integral lattice.

Cited statements: lem-weil-pbc-lisse-e-constructible-integral-lattice, lem-weil-pbc-integral-stratified-perfect-characterization, lem-weil-pbc-lisse-lattice-etale-local, def-weil-constructible-standard-tstructure. Source: Lemma 6.8.13 and Proposition 6.8.4(6); essential image in Proposition 6.8.14(2).

### Original step 5

For integral representatives $M,N$, the specified map $\chi_{M,N}$ of [lem-fix-constructible-tensor-completion] identifies the ordinary ambient derived tensor with the completed tensor used by [def-weil-derived-pullback-tensor-hom]. Apply scalar localization and the ordinary ringed-topos monoidal comparison of [lem-sfb-ringed-derived-monoidal-comparisons] to obtain
$$F(M\widehat\otimes_R^LN)\cong FM\otimes_{E_X}^LFN.$$
For lisse inputs the right side is ordinary sheaf tensor in degree zero: on a basis chart, tensoring with a finite free module is a finite direct sum of the identity functor, hence exact. Exactness and vanishing of the higher tensor cohomology are local statements about sheaves, so this calculation suffices. The map sends $e_i\otimes e_j$ to the corresponding pure tensor. The unit comparison is multiplication $E_X\otimes_BE_X\to E_X$, with $1\otimes1\mapsto1$.

Cited statements: lem-fix-constructible-tensor-completion, def-weil-derived-pullback-tensor-hom, lem-sfb-ringed-derived-monoidal-comparisons. Source: Remark 6.8.15, tensor; ordinary/completed tensor comparison.

### Original step 6

For an arbitrary scheme map $f:X'\to X$, apply [lem-tw-ordinary-completed-integral-pullback] to identify completed integral pullback with $P_fK=B_{X'}\otimes^L_{f^{-1}B_X}f^{-1}K$. The two paths of ordinary derived scalar extension around the ring square $f^{-1}B_X\to B_{X'}$, $f^{-1}E_X\to E_{X'}$ are canonically the same, by the composition and monoidal comparisons of [lem-sfb-ringed-derived-monoidal-comparisons]. Consequently
$$F_{X'}(Lf_E^*K)\cong E_{X'}\otimes^L_{f^{-1}E_X}f^{-1}(F_XK).$$
For lisse $K$, $f^{-1}(F_XK)$ is locally finite free over $f^{-1}E_X$, so the displayed tensor is ordinary and in degree zero. On pulled-back bases the comparison is $1\otimes e_i\mapsto e_i$. Both the new integral comparison and ordinary ringed-topos composition apply to all scheme maps, so no $k$-linearity or separatedness hypothesis has entered.

Cited statements: lem-tw-ordinary-completed-integral-pullback, lem-sfb-ringed-derived-monoidal-comparisons, def-weil-derived-pullback-tensor-hom. Source: Remark 6.8.15, explicit ringed pullback formula.

### Original step 7

For $E\subset L$ finite, [lem-weil-finite-free-completed-scalar-comparison] identifies the integral transition functor with ordinary derived change of completed coefficient rings via its specified quotient-cone map $\chi_{L/E,K}$. Localizing this isomorphism gives the ordinary extension of continuous field coefficients on realized objects, with $e_i\otimes b\mapsto b e_i$. The comparison is natural on integral arrows; the formula in Step 2 extends it to all rationalized arrows. The scalar-operation comparisons of [lem-pur-integral-operations-scalar-extension] therefore identify the field extensions of the tensor and pullback comparisons of Steps 5 and 6 with the same comparisons over $L$.

Cited statements: lem-weil-finite-free-completed-scalar-comparison, lem-pur-integral-operations-scalar-extension, lem-sfb-ringed-derived-monoidal-comparisons. Source: Lemma 6.8.2 and Remark 6.8.15; finite coefficient extension.

### Original step 8

Check that these are the specified coherent comparisons. The completed tensor associators, unitors and symmetry are the limits of the finite total-complex maps by [lem-pur-completed-operation-tower-substitution]. The normalized integral pullback composition and its scalar compatibility are those realized from simultaneous quotient diagrams in [lem-trf-integral-pullback-comparison-realization]. The maps $\chi$ in Steps 5 and 7 and $\eta$ in Step 6 use those same quotient maps, with zero shifted-product component. Thus they intertwine these finite diagrams before realization. On the ordinary side [lem-sfb-ringed-derived-monoidal-comparisons] supplies the corresponding monoidal and composition laws. Alternatively, after realizing lisse inputs every resulting diagram is checked on a common local basis: associativity sends $(e_i\otimes e_j)\otimes e_k$ to $e_i\otimes(e_j\otimes e_k)$, symmetry interchanges the two basis vectors, units multiply by $1$, and successive pullbacks send a basis vector to the same basis vector. The scalar maps send it to $e_i\otimes b$, with successive scalars multiplied. Both paths therefore agree on generators, then on all sections by linearity and the sheaf axiom. All objects here are in degree zero, so the symmetry sign is $+1$. This proves the requested naturality, identity, composition and coherence assertions.

Cited statements: lem-pur-completed-operation-tower-substitution, lem-trf-integral-pullback-comparison-realization, lem-sfb-ringed-derived-monoidal-comparisons. Source: Remark 6.8.15; quotient-diagram normalization and pure-tensor verification.

### Original step 9

Put $s=\operatorname{Spec}k$. By [lem-weil-point-proetale-sections-exact], sections of any coefficient module sheaf on $s$ are exact. The continuous-coefficient identification of Step 1 gives $B_s(s)=R$ and $E_s(s)=E$, because a continuous function on the one-point space $|s|$ is its value. For any integral constructible $C$ at $s$, the canonical sections-localization map
$$\Gamma(s,C)\otimes_RE\longrightarrow\Gamma(s,FC)$$
is an isomorphism: apply Step 2's Hom-localization result with $K=B_s$ and $L=C[q]$ for every $q$. The unit $B_s$ is constructible by [lem-weil-constant-coefficient-objects-constructible], and $\operatorname{Hom}(B_s,C[q])=H^q\Gamma(s,C)$ by exact sections and evaluation at $1$. These Hom identifications are exactly the cohomology maps of the displayed canonical map; [lem-weil-pbc-unbounded-derived-iso-cohomology] proves invertibility. Combining it with Step 6 for $x:s\to X$ identifies the rational point fibre defined in [def-weil-finite-coefficient-point] with sections of the ordinary pullback. All maps used are natural in $C$ and $K$.

Cited statements: lem-weil-point-proetale-sections-exact, lem-weil-constant-coefficient-objects-constructible, lem-weil-pbc-scalar-localization-derived-hom, lem-weil-pbc-unbounded-derived-iso-cohomology, def-weil-finite-coefficient-point. Source: Lemma 6.8.12 and Proposition 6.8.14(2), on a geometric point.

### Original step 10

For lisse point objects the fibre in Step 9 is a finite-dimensional vector space: [lem-weil-point-fibre-equivalence] places it in $D^b_{\mathrm{fd}}(E)$, and exact localization and sections put its cohomology in degree zero. Choose a finite basis of this space. Full faithfulness of the point fibre functor in [lem-weil-point-fibre-equivalence] lifts its basis isomorphism to an isomorphism of the point object with a finite sum of units. Hence the sections-tensor comparison and the fibre-tensor comparison are the same map: on these finite sums both send $e_i\otimes e_j$ to $e_i\otimes e_j$, and send the unit $1$ to $1$. Naturality removes the choice of basis. This verifies tensor and unit compatibility of Step 9, including rank zero.

Cited statements: lem-weil-point-fibre-equivalence, def-weil-finite-coefficient-point, lem-weil-point-proetale-sections-exact. Source: Definition 6.8.3 and Remark 6.8.15; finite free point calculation.

### Original step 11

Let $h:s\to s$ be a scheme automorphism. By [lem-weil-proetale-isomorphism-inverse-image], $h^{-1}$ is an exact equivalence commuting with coefficient limits and colimits, with structure map induced by the finite coefficient maps. Use the restriction-and-coprojection construction of [def-weil-frobenius-point-transport] with $h$ in place of $g_s$. Its integral comparison $\kappa$ is the quotient-cone map of [def-weil-inverse-image-pullback-comparison]. Under the normalized $\eta_h$ of Step 6 it becomes the ordinary module unit $z\mapsto1\otimes z$: both maps into every quotient are the reduction followed by that unit, and both have zero shifted-product component. Under Step 9, a localized section $z/t^n$ is consequently sent to
$$t^{-n}\bigl(1\otimes\operatorname{ins}(\operatorname{res}_h z)\bigr).$$
Restriction and the inverse-image colimit coprojection commute with multiplying by $t$ and with the coefficient maps. This is exactly restriction, then coprojection, then the ordinary module unit applied to the localized section. Thus the point-transport maps themselves agree under realization, rather than only being conjugate by an arbitrary fibre isomorphism. The calculation is natural in sheaf maps and coefficient extensions.

Cited statements: lem-weil-proetale-isomorphism-inverse-image, def-weil-frobenius-point-transport, def-weil-inverse-image-pullback-comparison, lem-tw-ordinary-completed-integral-pullback. Source: Remark 6.8.15; explicit point-transport normalization of the item.

### Original step 12

The equality for iterates follows by induction: for zero iterations both sides are identities; if the identification intertwines the first $r$ transport factors, compose that equation with the one-factor equation of Step 11 applied to the $r$-fold pulled-back object. Step 8's pullback composition law identifies the resulting source and target. Every tensor and scalar compatibility persists under this composition.

Cited statements: . Source: Point-transport normalization; induction on the number of factors.

### Original step 13

Finally use [def-weil-algebraically-closed-coefficients]. An object, a morphism, or a finite diagram in the common-stage category is represented over a finite field after taking a compositum. Apply Steps 2-12 there and then extend scalars to $\Qlb$ where the fibre definition requires it. Step 7 and Step 8 identify the results after any further finite extension. Equal representatives therefore yield equal maps, and inverse maps remain inverse at larger stages. This gives the stated common-stage lisse assertions and all tensor, pullback, fibre and point-transport compatibilities for $\Sh_c(X,\Qlb)$.

Cited statements: def-weil-algebraically-closed-coefficients, def-weil-finite-coefficient-point. Source: Proposition 6.8.14(1); common finite coefficient stage.

## Delivery validation

The required dry run exited successfully: `OK (not pushed) deliver/Q130/lem-tw-lisse-rational-realization at c4d75ad2407: preflight passed`. The server ran preflight including the required DAG and split review; no local compiler or forbidden local checker was run. The six new statements range from 2494 to 3325 characters (their repeated self-contained coefficient setup accounts for about 1400 each); no single child takes over the parent theorem. The parent statement is byte-for-byte unchanged, and the full returned argument above remains available for the next workers. A final record-only refinement adds the already-run successful Loogle replacement to the scalar-coherence node, explicitly labels its earlier unknown-identifier query invalid, and leaves every mathematical statement and dependency unchanged.
