# Stage-1 repair: lem-pur-composition-comparison-scalar-compatibility

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-composition-comparison-scalar-compatibility.json: item, split; statement unchanged; three assembly steps totaling 1902 characters.
- dag/nodes/sec-smooth-purity/lem-pur-rational-normalized-purity-diagrams.json: statement, unsplit; no Mathlib match; no proof steps or proof dependencies.
- dag/nodes/sec-smooth-purity/lem-pur-iterated-purity-scalar-pasting.json: statement, unsplit; no Mathlib match; no proof steps or proof dependencies.
- citations.json: verbatim conclusion paragraphs for every new citation in each assembly step.
- report.md: this repair, search assessment, source review and the complete returned argument with its work allocation.

## Attachments

None. I searched the project source for the exact blueprint tag and for purity, scalar and composition terminology. Smooth/Transport.lean only proves preservation of derived completeness. Smooth/Reduction.lean proves finite-coefficient purity squares from supplied constituent compatibilities, not the normalized rational exceptional composition equation. Smooth/Rational.lean:57–100 explicitly describes its theorem as E-stage packaging with assumed tower compatibility; it neither constructs the actual compositor nor proves the equation here. These declarations do not attach this item or either extracted node.

## WANTED

None. The new lemmas are agent extractions of the existing blueprint argument, not attributions of the full normalized comparison assertions to a missing source. No new SGA source is used.

## Return repaired and retained work

The sandbox contained only dispatcher marker files, with no delivered JSON, report or searches.jsonl. I read the current repository's returned item and preserved it verbatim in returned-node.json before editing. Its six proof steps are reproduced below, including every formula, source dependency and naturality explanation. The live copy matches the six step lengths in the return. The delivery tool rebases the split-owned fields onto current origin and retains maintainer-owned records; no git command was run in the shared repository.

The return demanded at least two comparable statement-only arguments and an assembly of at most 3000 characters, without shortening away the old argument. New node lem-pur-rational-normalized-purity-diagrams takes old steps 1–3 (2590 characters): lattice domains, localization of the actual integral composition identity, and rationalization of the counit-normalized purity square and its coefficient coherences. New node lem-pur-iterated-purity-scalar-pasting takes old steps 4–5 (1917 characters): the ordered Tate/shift compositor square and the horizontal pasting calculation using both purity squares. Old step 6 remains the cancellation argument in the item. Each extracted node introduces its objects independently; neither asserts the item's equation comparing the actual exceptional compositor with scalar extension. In particular, the second node never mentions that exceptional compositor. These are separate proof tasks, not two clauses that restate the conclusion. Their mathematical workload is comparable. Extraction of these formerly inline arguments is expressly required by the human's re-split instruction, including the formerly elementary-marked tensor and pasting calculations.

## Source and search assessment

For the item and both new nodes I read main-20261015/blueprint/sec-smooth-purity/sk-thm-purity-transport/prop-pur-rational-purity-trace-coherence.md and its .proof.md, the corresponding adic-reconstruction-trace-coherence statement and proof, and thm-pur-rational-and-qbar-purity.proof.md. The ancestor proof says that the integral coherence diagrams are transported along the same exact functors. New node lem-pur-rational-normalized-purity-diagrams states the particular transported diagrams with the normalization and domain details that old steps 1–3 had supplied. New node lem-pur-iterated-purity-scalar-pasting states the two intermediary squares needed to paste this diagram; its concrete tensor and naturality arguments are the extracted old steps 4–5, reproduced below. This is the unit's Step 3 route. I read dag/chapters/sec-smooth-purity.json, dag/units/sk-thm-purity-transport.json and the three levels in SETUP.md; no chapter/unit route is changed.

Whole-DAG keyword searches and blueprint_refs.py searches for purity scalar, composition comparison, rational purity, purity composition and twist scalar located the existing general transport and coherence nodes. I read the closest statements and distinguished them below. The ancestor command gives prop-pur-rational-purity-trace-coherence, so both new nodes use that blueprint ancestor, via the current item, and specify the exact old steps in from.place. No blueprint node states either complete extracted result independently; same_as is empty.

The item's prior Mathlib searches are retained unchanged and their recorded results were read. Each new node has two distinct semantic phrasings, Loogle queries and source greps run through msearch.py and recorded from searches.jsonl. Both LeanSearch calls returned rate-limit errors and are marked unavailable. LeanFinder's normalized-diagram queries returned scheme normalization/localization results, not constructible purity. Its pasting queries returned ordinary scheme module pullback composition, pseudofunctor associativity, and pullback of free sheaves. Loogle's purity/rational query had no hits; the localization query found liftNatTrans, natTrans_ext and comp_liftNatTrans; these formal transport tools do not establish the finite-Tor domains, identify the supplied integral purity family with the actual composition map, or supply the normalized coefficient maps. The whisker/naturality query found generic bicategorical naturality, and pullbackComp found categorical limit comparisons. Such results do not give the specified Tate-twisted derived compositor or its scalar square. I read the supplied signatures and the local localization source. The source greps found no purity/exceptional comparison in CategoryTheory or AlgebraicGeometry; the broad Tate.*comp query's hits were incidental English text, also read. Neither new node is a one-line specialization of these hits, so both remain unsplit, with mathlib_match null.

## Not duplicates

lem-pur-rational-normalized-purity-diagrams vs prop-pur-adic-reconstruction-trace-coherence: the existing proposition transports finite diagrams to the integral stage; the new lemma puts the actual integral diagrams on the raw rational categories, verifies their lattice domains and states their rational counit-normalized scalar equations.
lem-pur-rational-normalized-purity-diagrams vs thm-pur-rational-and-qbar-purity: the existing theorem supplies the rational purity isomorphism, not its equation with the actual exceptional compositor and the specified scalar square.
lem-pur-rational-normalized-purity-diagrams vs lem-pur-adic-purity-scalar-naturality: this is the integral normalized family and its scalar square; the new lemma also verifies rational domains and transports the integral exceptional composition identity. The scalar square alone is an input, not a new duplicate.
lem-pur-rational-normalized-purity-diagrams vs prop-weil-pbc-rational-transport: the latter extends supplied linear functors and transformations; it does not identify the geometric normalized diagrams or establish their domains.
lem-pur-rational-normalized-purity-diagrams vs prop-pur-rational-purity-trace-coherence: this is the blueprint ancestor which the item realizes; the new lemma supplies only rationalized input equations, not the scalar compatibility of the actual exceptional compositor asserted by the item or the full ancestor's trace/base-change coherence.
lem-pur-iterated-purity-scalar-pasting vs lem-pur-coefficient-pullback-coherence: the existing statement concerns inverse-image comparisons for a supplied ringed-site scalar presentation. The new node concerns the canonical completed, rational, Tate-twisted and shifted smooth compositor together with the horizontal purity transformation.
lem-pur-iterated-purity-scalar-pasting vs lem-pur-normalized-pullback-composition-transport: the existing result realizes a fixed-coefficient whole-system pullback compositor through the limit; it does not state a coefficient-extension square for shifted Tate twists or iterated purity.
lem-pur-iterated-purity-scalar-pasting vs lem-weil-integral-twist-scalar-coherence: the latter is the successive-field scalar associator for a single twist; the new lemma is the two-geometric-map twisted compositor square and horizontal purity pasting over rational categories.
lem-pur-iterated-purity-scalar-pasting vs def-pur-composition-comparisons: the existing node defines finite-coefficient maps only; it proves neither of the new rational scalar equations.
lem-pur-iterated-purity-scalar-pasting vs lem-pur-smooth-exchange-scalar-compatibility: that result concerns a Cartesian base-change square and the actual exceptional exchange; the new lemma concerns two composable smooth maps and the pure-model compositor, with no exceptional compositor or exchange in its conclusions.
lem-pur-iterated-purity-scalar-pasting vs det-prop-scalar-six-exceptional: the existing proposition is on Loc(D_ctf) in the standing six-functor datum and directly treats exceptional composition. The new lemma is on the raw rational constructible categories and treats the twisted pullback and horizontally composed purity maps only.

## Review by Q68

I read delivery-errors.md B–E in full and checked the actual new statements against the sources and the returned proof. Both new nodes are complete statements with the primes, finite coefficient fields, separated finite-type schemes, two smooth relative dimensions, rational categories, functors and every comparison introduced. They have no proof steps, no proof_origin and no proof_deps; their intended arguments appear only in this report. I preserved the item's statement, including the actual counit-normalized b and transported integral c. No statement dispute or source correction was needed.

Assembly step 1 cites lem-pur-rational-normalized-purity-diagrams. I checked its statement gives exactly c gamma_gf = q u, the square b T(gamma) = gamma a, naturality, the coefficient unit/associator/shift equations, and the integral finite-Tor domain check. I read the old inputs: finite-type-over-noetherian applies over the field k; dimension-finite-type supplies finite dimension; the raw rational category has precisely integral objects; integral-stratified-perfect-characterization identifies its completed integral notion with the purity category; integral-residue-tor gives D_c = D_ctf with a uniform interval. These hypotheses hold on X,Y,Z over both E and L. Relative-dimension permanence explicitly permits empty schemes and gives d+e. The integral reconstruction proposition transports the finite composition formula, whose displayed direction is c gamma_gf = q u. Rational-transport extends the given exact linear natural transformations, not arbitrary choices of endpoint isomorphisms. The integral scalar-naturality statement supplies the adjoint-transpose definition and the full comparison square; rationalization is the additional work assigned to the first node. I checked the current blueprint_update of rational-and-qbar-purity and used its E-stage interpretation, not a Karoubi envelope.

Assembly step 2 cites lem-pur-iterated-purity-scalar-pasting. Its statement gives exactly A T(u_E) = u_L a_gf and beta T(q_E) = q_L A. In the retained argument, scalar-extension's statement expressly says pullback comparisons respect composition, successive coefficient extensions and shifts. Integral-operations-scalar-extension supplies the natural pullback/tensor comparisons and their successive-extension equations. Twists-detailed defines the nonnegative twists from the same rank-one root-of-unity line and the zero twist as the unit. Thus the extracted tensor calculation preserves the ordered e+d factors and uses the same coefficient multiplication on both routes, including zero exponents; even shifts do not introduce a sign. The second old calculation uses the normalized purity square twice. I checked the naturality move for gamma_f at b_g and the naturality move for a_f at gamma_g have the displayed intermediate domains. The second new node includes both the tensor argument and the pasted naturality argument, so neither is hidden in the assembly.

Assembly step 3 cites both new nodes. I checked each verbatim quotation in citations.json includes precisely the equations it uses. Both required arrows have source T_X G_gf,E K and target G_f,L G_g,L T_Z K. After precomposing with T_X gamma_gf,E, the two displayed chains end at q_L u_L a_gf. Cancellation is legal because gamma and its functorial image are isomorphisms. Every other equality is functoriality, substitution or associativity; no uncited comparison theorem is used in this step. Naturality and the unit/tower/shift identifications are conclusions of the new lemmas and remain part of the extracted work, as in the full old argument below. Each assembly step is below 2000 characters and the total is below 3000.

I tested E=L (all coefficient maps reduce to identities), d=0 and e=0 (zero tensor powers are units), f or g an identity, K=0, and empty schemes. The formulas retain their types and reduce to the corresponding unit or zero equations. No assumption of an E-linear arbitrary lift being coherent from equal reductions alone was introduced: the family remains the simultaneous specified integral family, with the actual transported compositor, throughout. No new node cites the item or its blueprint ancestor as a dependency, and both have the same unit as the item, so the assembly introduces no route detour or cycle.

## Complete retained argument and allocation to future workers

The following text is copied without shortening from the returned live node. It records what must be proved in the two unsplit tasks and what remains in the assembly. These are report material, not proof steps in the new node files.

### Original step 1, assigned to lem-pur-rational-normalized-purity-diagrams

Check the coefficient domains before transporting maps. The schemes are noetherian by [lem-weil-pbc-finite-type-over-noetherian] applied over the field $k$, finite-dimensional by [lem-kun-dimension-finite-type], and have $\ell$ invertible since $\ell\ne p$. The raw rational category [def-weil-pbc-rational-category] has exactly the integral objects as its objects. By [lem-weil-pbc-integral-stratified-perfect-characterization] these lattices are objects of the derived-complete category used by integral purity, and [lem-coef-integral-residue-tor] puts every lattice in its uniform finite-Tor subcategory. These assertions apply over both $E$ and $L$ and on $X,Y,Z$. By [lem-sbc-smooth-relative-dimension-permanence], $gf$ is smooth of dimension $d+e$. Thus the integral and rational comparisons for $f,g,gf$ have the asserted domains.

Cited nodes: lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type, def-weil-pbc-rational-category, lem-weil-pbc-integral-stratified-perfect-characterization, lem-coef-integral-residue-tor, lem-sbc-smooth-relative-dimension-permanence.
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-purity-transport/prop-pur-rational-purity-trace-coherence.proof.md; Composition-coherence transport paragraph; unit sk-thm-purity-transport Step 3.

### Original step 2, assigned to lem-pur-rational-normalized-purity-diagrams

For $R=E,L$ let $u^R_K:H_{gf,R}K\xrightarrow{\sim}H_{f,R}H_{g,R}K$ be the canonical pullback-composition, twist-addition and shift comparison. Put $q^R_K=\gamma_{f,R,G_{g,R}K}\circ H_{f,R}(\gamma_{g,R,K})$. The integral composition-coherence assertion of [prop-pur-adic-reconstruction-trace-coherence], with the direction fixed by [thm-pur-composition-coherence], is $c^R_K\gamma_{gf,R,K}=q^R_Ku^R_K$ before rationalization. Here, as in the statement, use the transported integral purity and composition maps, not arbitrary lifts with the same reductions. Apply the functor and natural-transformation extension of [prop-weil-pbc-rational-transport]. A functor preserves the composite and equality, so this same equation holds over $R$, for every lattice and hence every rational object. These are the purity maps of [thm-pur-rational-and-qbar-purity]. In particular this equation identifies the actual specified $c^R$; we have not defined a replacement for it by conjugation.

Cited nodes: prop-pur-adic-reconstruction-trace-coherence, thm-pur-composition-coherence, prop-weil-pbc-rational-transport, thm-pur-rational-and-qbar-purity.
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-purity-transport/prop-pur-rational-purity-trace-coherence.proof.md; Composition-coherence transport paragraph; unit sk-thm-purity-transport Step 3.

### Original step 3, assigned to lem-pur-rational-normalized-purity-diagrams

Write $a_{h,K}:T_{\mathrm{source}(h)}H_{h,E}K\to H_{h,L}T_{\mathrm{target}(h)}K$ for the rationalized pullback/twist scalar comparison. Rationalize the natural purity square of [lem-pur-adic-purity-scalar-naturality] by [prop-weil-pbc-rational-transport]. It gives, for $h=f,g,gf$,
$$b_{h,K}T(\gamma_{h,E,K})=\gamma_{h,L,TK}a_{h,K}.$$
It also supplies naturality of these maps and their unit, successive-extension and shift equations. The comparison used here is the specified counit-normalized map
$$b_{h,K}:T_{\mathrm{source}(h)}G_{h,E}K\xrightarrow{\sim}G_{h,L}T_{\mathrm{target}(h)}K,$$
namely the transpose of the compact-support coefficient comparison followed by the counit. Thus no independent choice of an isomorphism between the two exceptional functors is being made.

Cited nodes: lem-pur-adic-purity-scalar-naturality, prop-weil-pbc-rational-transport.
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-purity-transport/prop-pur-rational-purity-trace-coherence.proof.md; Composition-coherence transport paragraph; unit sk-thm-purity-transport Step 3.

### Original step 4, assigned to lem-pur-iterated-purity-scalar-pasting

Set $A_K=H_{f,L}(a_{g,K})a_{f,H_{g,E}K}$. The pullback comparisons of [prop-weil-pbc-scalar-extension] respect composition. With twists and shifts inserted they give
$$A_KT_X(u^E_K)=u^L_{T_ZK}a_{gf,K}.$$
The additional twist check is explicit: by [def-coefficient-twists-detailed], a nonnegative twist is a tensor power of the same roots-of-unity object with its coefficient ring extended. Both routes preserve the ordered $e+d$ twist factors and multiply the coefficient factors in their original order. On pure tensors they send $((v\otimes s)\otimes t)$ to $v\otimes st$; balancing gives equality, including when either tensor power is zero. These are the natural pullback/tensor comparisons of [lem-pur-integral-operations-scalar-extension], followed by rationalization. Reassociation of the shifts also agrees: $2d$ and $2e$ are even, so moving a twist past either shift contributes sign $+1$. This proves the displayed equation by the defining tensor maps and the cited pullback-composition compatibility.

Cited nodes: prop-weil-pbc-scalar-extension, def-coefficient-twists-detailed, lem-pur-integral-operations-scalar-extension.
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-purity-transport/prop-pur-rational-purity-trace-coherence.proof.md; Composition-coherence transport paragraph; unit sk-thm-purity-transport Step 3.

### Original step 5, assigned to lem-pur-iterated-purity-scalar-pasting

Suppress composition symbols, and object subscripts only where the functors determine them. From source $T_XH_{f,E}H_{g,E}K$ the calculation is
$$\begin{aligned}
\beta_KT_X(q^E_K)
&=G_{f,L}(b_{g,K})b_{f,G_{g,E}K}T_X(\gamma_{f,E,G_{g,E}K})T_XH_{f,E}(\gamma_{g,E,K})\\
&=G_{f,L}(b_{g,K})\gamma_{f,L,T_YG_{g,E}K}a_{f,G_{g,E}K}T_XH_{f,E}(\gamma_{g,E,K})\\
&=\gamma_{f,L,G_{g,L}T_ZK}H_{f,L}(b_{g,K})H_{f,L}T_Y(\gamma_{g,E,K})a_{f,H_{g,E}K}\\
&=\gamma_{f,L,G_{g,L}T_ZK}H_{f,L}(\gamma_{g,L,T_ZK})H_{f,L}(a_{g,K})a_{f,H_{g,E}K}\\
&=q^L_{T_ZK}A_K.
\end{aligned}$$
The second line is Step 3's square for $f$ at $G_{g,E}K$. In the third line, naturality of $\gamma_{f,L}$ moves $G_{f,L}(b_g)$ across it, and naturality of $a_f$ moves $T_XH_{f,E}(\gamma_g)$ across $a_f$. The fourth line applies Step 3's square for $g$ inside $H_{f,L}$. These are substitution, naturality and preservation of composition by a functor.

Cited nodes: (elementary calculation using previous steps).
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-purity-transport/prop-pur-rational-purity-trace-coherence.proof.md; Composition-coherence transport paragraph; unit sk-thm-purity-transport Step 3.

### Original step 6, assigned to lem-pur-composition-comparison-scalar-compatibility

Precompose the required equation with the isomorphism $T_X(\gamma_{gf,E,K})$. Its left side becomes
$$\beta_KT_X(c^E_K\gamma_{gf,E,K})
=\beta_KT_X(q^E_K)T_X(u^E_K)
=q^L_{T_ZK}A_KT_X(u^E_K)
=q^L_{T_ZK}u^L_{T_ZK}a_{gf,K}.$$
Its right side becomes, by Step 3 and then Step 2,
$$c^L_{T_ZK}b_{gf,K}T_X(\gamma_{gf,E,K})
=c^L_{T_ZK}\gamma_{gf,L,T_ZK}a_{gf,K}
=q^L_{T_ZK}u^L_{T_ZK}a_{gf,K}.$$
Cancel the common precomposition isomorphism. Every expression is a composite of natural transformations, so these component equalities give equality of natural transformations. For the unit, successive-extension associators and shifts, substitute the comparison equations of Steps 3 and 4 into the same calculation. Both sides then have the same ordered factors with the same tensor associators; naturality moves each comparison through these factors, and cancellation gives the same equality. Thus all identifications are the specified ones.

Cited nodes: (elementary calculation using previous steps).
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-purity-transport/prop-pur-rational-purity-trace-coherence.proof.md; Composition-coherence transport paragraph; unit sk-thm-purity-transport Step 3.

## Unfinished work

The two extracted nodes are deliberately unsplit and await independent stage-1 workers; this is the requested work distribution. No Lean was written and no compiler, Lake, or local DAG/preflight check was run. Required remote dry-run and delivery results are recorded after they complete.
