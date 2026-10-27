## Worker report

Files written:

- dag/nodes/sec-trace-formula/lem-trf-quotient-system-mixed-coherence.json: item, statement unchanged, five-step assembly of 2312 characters.
- dag/nodes/sec-trace-formula/lem-trf-sequence-scalar-generator-interchange.json: statement, unsplit, no Mathlib match. Carries the ordinary mixed, scalar-unit and scalar-tower generator calculations and their strict diagram compatibility.
- dag/nodes/sec-trace-formula/lem-trf-ringed-kflat-word-comparison-descent.json: statement, unsplit, no Mathlib match. Carries simultaneous resolving models, counit normalization, comparison descent and equality detection for finite words of ringed pullbacks.
- report.md and citations.json: the signed review and verbatim statement citations.

Attachments: none. The search by the item tag and by integralQuotientMixedCoherence in lean/WeilConjectures gives no declaration of the item. The recorded Sheaf/Paper/QuotientSystemMixedCoherence.lean:490 theorem has `sorry` at line 492. Its scalar associator and unitor helpers are proved but do not prove the main mixed or geometric equations. A proof landing metadata field therefore does not justify ATTACH.

WANTED: none. All documents used are available locally.

What required repair: coord/repair-notes/lem-trf-quotient-system-mixed-coherence.json is released and expressly requests a re-split of the 8409-character proof into at least two comparable independent statement-only tasks, with assembly at most 3000 characters. This specific human instruction overrides the ordinary prohibition on splitting an already reviewed item and on extracting its ordinary clauses. The statement, definitions, route and target were not changed. The original eight steps are preserved below with an allocation of every argument. New nodes have no proof, proof dependency or proof sketch inside their statements. The generic descent node assumes the ordinary transformations and relations; it does not assert this item's mixed equation. The scalar node proves only ordinary strict-system equations; it does not assert their derived validity. Neither replaces the item alone.

What remains: proofs of the two new statement-only nodes are intentionally left to the queue. No Lean file was written, and no compiler, Lake or build tool was run.

## Review by Q70

I read the chapter record sec-trace-formula and unit sk-thm-trace-transport, SETUP's three blueprint levels, GOAL, the current main-20261015 prop-trf-karoubi-independence.proof.md final sentence, the item's complete original proof, and the maintainer's released re-split note. The blueprint sentence is transport of Frobenius under the common-stage isomorphism, not an independent purity or trace route. This item supplies the coherence used by its integral-comparison parent; it is not the unit's key statement, so no unit realization field changes.

For the item and the scalar-generator node I read sites-cohomology.tex Tag 0D6D (lemma-derived-pullback-composition), including its proof, and the full statement of def-trf-integral-comparison-sequence-systems. The latter fixes precisely the adjunction mate, kappa, multiplication associator and unit used here, and explicitly asserts their vertical and horizontal naturality. Stacks does not verbatim state the three mixed equations: their source is marked as an agent expansion, and the original calculations are retained below. For the generic descent node I read Tags 06YS (lemma-K-flat-resolution), 0G7E (lemma-pullback-K-flat), 06YY (lemma-derived-base-change), and 0D6D in sites-cohomology.tex. 06YS resolves arbitrary unbounded complexes with flat terms; 0G7E preserves BOTH K-flatness and flat terms under arbitrary ringed pullback; 06YY computes the chosen derived pullback on that class; 0D6D reuses the same representative after pullback. They do not require flat structural ring maps. The new node's finite-word and transformation descent is the explicit agent generalization of these facts, not attributed verbatim to Stacks.

I opened each statement cited by the new assembly:

1. def-coef-ringed-sequence-site gives actual module sheaves on the small ringed sequence site, not an abstract tower in a derived category. def-trf-integral-comparison-sequence-systems supplies direct image, its left adjoint, and the compositor mate. lem-trf-adjoint-composition-coherence states the needed associativity of LEFT comparisons when the RIGHT comparisons are coherent natural isomorphisms. Its hypothesis is checked here by ordinary fibre-product pasting: either triple nesting sends (u,w,z) to the identical unnested tuple. The direction in the item is the inverse of that lemma's left comparison, which gives exactly c rather than its inverse. This reuse avoids creating a duplicate geometric-compositor node. It is declared as a generic tool in split_report.
2. The identity comparator is specifically the adjunction-unit identification from the operations definition. Equality of mates follows from the adjunction bijection. Induction on the length and binary assembly is explicit: at a composite junction use the triple equality from Step 1, with zero and one arrows as identity bases. The definition states naturality in the vertical and horizontal arrows, so this is an elementary assembly of that definition and Step 1, not an uncited extra comparison lemma. No strict equality of differently parenthesized functors is claimed; the canonical functor associators and equality identifications are understood.
3. The scalar-generator statement contains, verbatim, each of the three ordinary equalities used in this step, plus compatibility with BOTH kinds of sequence arrow and arbitrary cochain differentials. The new statement introduces E,L,M, all schemes, all ordinary functors and directions. Its ordinary scope is essential: it makes no unjustified claim that nonflat scalar extension is exact or already derived. Comparing generators means using the two adjunction bijections on all local sections, not assuming arbitrary sections are single global pure tensors.
4. The finite-word descent statement supplies precisely one whole-system resolution, preservation at every intermediate word, invertible composite counits, the displayed normalization of derived transformations, preservation of whiskering and pasting, and equality detection on those models. Its edge hypothesis is checked separately for the two cases here: geometric maps are the ringed maps from the sequence-system definition, and coefficient change is ringed pullback on the IDENTITY underlying topos with its actual quotient ring map. No smallness, exactness or normalization hypothesis is imported from a different category. The operations definition says its chosen derived maps are these normalized localizations, so the descent theorem applies to the specified maps, not arbitrary isomorphisms.
5. def-weil-abstract-derived-category states that Q is localization at quasi-isomorphisms; therefore Qp is invertible. The naturality and cancellation displayed in the step give equality on C from equality on P. This is elementary category theory, with no assumption that realization or evaluation is faithful.

I checked B1-B7 of delivery-errors on both new nodes. Each is a self-contained proposition, with all data quantified; brackets name the notions actually defined by their statement dependencies; TeX is single-escaped at the string level; the sources identify the Stacks tags AND labels; neither statement contains a proof or appeal to a tag for its meaning. Definitions of K-flatness, flat terms, module complexes and ringed morphisms are named where the generic node uses them. Source and search comparisons against the nearest existing statements are listed below. The recorded Mathlib queries are copied from searches.jsonl, including their actual hit lists. Both semantic phrasings were read, as were PullbackContinuous.lean:165-210, ModuleCat/ChangeOfRings.lean:984-1015 and Functor/Derived/LeftDerived.lean:74-110. Mathlib gives individual pullback/adjunction/scalar laws and the abstract left-derived lift API; it does not by one specialization provide these entire-diagram statements. No service was recorded as unavailable when it returned hits.

Small cases: n=1, zero modules and zero complexes, E=L, L=M, and E=L=M preserve every displayed source and target. For a ramified extension of ramification index e, inclusion sends varpi_E^n into varpi_L^(en), contained in varpi_L^n since e>=1, so the actual maps A_E,n -> A_L,n exist. Their possible nonflatness is harmless to the ordinary balanced tensor calculations; the derived node uses K-flat replacement rather than exactness of scalar extension. Empty words give the identity and empty geometric strings give the inverse-image unit; singleton words give their chosen universal counit. Arbitrarily long but finite words are handled by induction, never an infinite resolution diagram. General unbounded K is allowed by 06YS; no stalk, point, finite Tor, constructibility or normalization assumption is added. On a one-object ringed site the scalar generator equations reduce to balanced module tensor identities, and the generic model formula reduces to the usual derived tensor normalization. No new statement failed these checks.

Corrections during review: I initially considered a third geometric-coherence node, then rejected it because the existing adjoint-composition-coherence already supplies its substantive three-map argument. That work is cited rather than duplicated. I kept the whole-system K-flat preservation hypothesis (flat terms as well as K-flatness) and explicitly included composite counits, so the generic descent node does not silently assume that unrelated levelwise resolutions form a strict system. I removed only the old prose progress annotation about the main Lean proof obligation; it is not a mathematical argument. All assembly steps are below 2000 characters; both long old arguments are allocated explicitly below. No source-error or statement-dispute was found.

## Proof allocation and preserved arguments

The ordinary scalar task receives original Step 1's determining adjunction/tensor test and Steps 3-5's three computations. Original Step 6's vertical/horizontal naturality and cochain argument applies both to this task and to the geometric assembly. The generic descent task receives original Steps 7-8's resolving class, preservation, counit normalization, associator/unitor existence and uniqueness, localization and cancellation. Original Step 2's geometric triple law reuses the existing general adjoint theorem; its finite-string induction and units remain explicit in assembly Steps 1-2. Thus none of the old work is replaced by a vaguer assertion.

The following is the previous proof text, retained as work instructions for the new tasks and to make the allocation reviewable. It is outside the new unsplit node statements. The references here are historical proof instructions, not additional citations of the new assembly.

### Original step 1

Work in the ringed sequence site of [def-coef-ringed-sequence-site], not in the category of towers in a derived category. Its module sheaves are the strict quotient-semilinear systems in the statement. The geometric maps leave the positive index fixed; scalar change is change of its ring sheaf along the compatible maps $A_{E,n}\to A_{L,n}$. By [def-trf-integral-comparison-sequence-systems], the ordinary comparison maps are the indicated adjunction mates and balanced tensor maps. The adjunct of the geometric compositor on a local section $x$ is the successive unit $\gamma_h\gamma_k(x)$: applying the two adjunction bijections to the mate of fibre-product pasting gives exactly the composite unit. The identity mate gives $\gamma_{\mathrm{id}}(x)=x$ after the unit identification. In the computations below, equality on these unit sections determines a map out of an inverse image by the adjunction bijection; equality on $1\otimes x$ determines a scalar-linear map out of scalar extension by its tensor adjunction. Thus these tests determine the whole sheaf maps, without assuming that arbitrary sections are globally pure tensors.

### Original step 2

First check geometric coherence on module systems. For three composable scheme maps, either composite of compositors takes the unit section of the composite inverse image to $\gamma_{f_1}\gamma_{f_2}\gamma_{f_3}(x)$. The two underlying fibre-product pastings both send a nested tuple to the same tuple with its three entries, so these are the same section under the canonical base-change identifications. The determining adjunction test of Step 1 proves associativity. Inserting an identity inserts $\gamma_{\mathrm{id}}$, hence leaves this expression unchanged and proves the two unit equations. For an arbitrary finite string, define its comparison by the successively composed units. Induction on the length of a parenthesized string, using the three-map equality at the last junction, identifies every parenthesization with that comparison; the length-zero and length-one cases are the identity units. Equal scheme morphisms induce the same base-change functor and coefficient map; the same adjunction mate therefore gives equal comparisons after these canonical identifications.

### Original step 3

For the mixed square use the source generator $1\otimes\gamma_{kh}(x)$ of $S_{L/E,Z}U_{kh,E}C$. The left side first gives $1\otimes\gamma_h\gamma_k(x)$, then $\gamma_h(1\otimes\gamma_k(x))$, then $\gamma_h\gamma_k(1\otimes x)$. The right side gives $\gamma_{kh}(1\otimes x)$ and then $\gamma_h\gamma_k(1\otimes x)$. Here all units carry their prescribed coefficient field, and the constant coefficient sections are identified by the canonical coefficient inverse-image map. The formulas are those of [def-trf-integral-comparison-sequence-systems]. The adjunction and scalar-linearity test of Step 1 therefore proves the displayed mixed geometric equation as an equality of ordinary system maps.

### Original step 4

For identity scalar change, start with $1\otimes\gamma_f(x)$. The composite $U_{f,E}(e_Y)\kappa_f^{E/E}$ sends it to $\gamma_f(1x)=\gamma_f(x)$, and $e_XU_{f,E}$ sends it to the same section. For a general coefficient $s$, linearity gives $\gamma_f(sx)=s\gamma_f(x)$ under the constant coefficient identification. The determining test of Step 1 proves the scalar unit equation, including equality fields and the identity scheme map.

### Original step 5

For the scalar tower equation start with $c\otimes(b\otimes\gamma_f(x))$ in $S_{M/L,X}S_{L/E,X}U_{f,E}C$. On the left the inner $\kappa$ and then the outer $\kappa$ give $\gamma_f(c\otimes(b\otimes x))$; applying $U_{f,M}(\alpha_Y)$ gives $\gamma_f(cb\otimes x)$. On the right $\alpha_XU_{f,E}$ gives $cb\otimes\gamma_f(x)$ and $\kappa_f^{M/E}$ gives $\gamma_f(cb\otimes x)$. Products here use the given inclusion $L\subset M$, exactly as in the associator formula of [def-trf-integral-comparison-sequence-systems]. Balance over $A_{L,n}$ identifies the coefficients $cb$, so this calculation is valid without flatness of any quotient-ring map. Applying the determining test proves the tower equation. It also covers $E=L$, $L=M$, and $E=L=M$.

### Original step 6

The calculations above are on whole strict systems. To spell out restriction compatibility, let $r$ be a vertical restriction and $q$ a horizontal transition from level $m$ to $n\le m$. Each inverse-image unit is natural, so $r\gamma_f(x)=\gamma_f(rx)$ and $q\gamma_f(x)=\gamma_f(qx)$ under the coefficient restrictions. A scalar tensor restricts as $r(b\otimes x)=r(b)\otimes r(x)$ and transitions as $q(b\otimes x)=q(b)\otimes q(x)$. The quotient coefficient maps are ring homomorphisms, hence $q(cb)=q(c)q(b)$; also $r(cb)=r(c)r(b)$. Consequently restriction of the common answers in Steps 3--5 is respectively $\gamma_h\gamma_k(1\otimes qx)$, $\gamma_f(qs\,qx)$, and $\gamma_f(qc\,qb\otimes qx)$, and applying the comparison after transition gives exactly these answers. Replace $q$ by $r$ for the vertical equations. The geometric formulas in Step 2 commute with $r$ and $q$ by the same unit naturality. Every sequence-site arrow is a composite of vertical and horizontal arrows, so these checks cover every arrow. Termwise application to a complex also commutes with its differential by naturality in the input module; the maps have degree zero and introduce no Koszul sign.

### Original step 7

For an arbitrary unbounded input choose one flat-term K-flat resolution on its entire ringed sequence site by [lem-pc-kflat-resolution]. This resolves the strict system as a single ringed-site module complex, rather than choosing unrelated resolutions at each level. By [lem-weil-pbc-ringed-topos-kflat-pullback], every ordinary geometric pullback and every scalar extension of this complex is again K-flat with flat terms: scalar extension is the special case with identity underlying topos and the actual quotient ring-sheaf map. Repeated application proves the assertion for every intermediate expression in the finite diagrams of Steps 2--5. The sites are the small sequence sites of [def-coef-ringed-sequence-site], and the geometric and coefficient ringed maps are those of [def-trf-integral-comparison-sequence-systems]; thus the cited preservation theorem applies with its actual hypotheses. By [lem-pur-derived-change-of-rings], the scalar functors and their resolution comparisons are computed on these models and are independent of the chosen K-flat resolution. The geometric functor is exact as specified in [def-trf-integral-comparison-sequence-systems], so its termwise action computes its derived functor. Accordingly the stipulated derived comparison components are precisely the localizations of the cochain maps checked above. The derived scalar associator is constructed as the universal left-derived lift of the ordinary tensor associator. On a flat-term K-flat resolution its component is invertible: the first scalar extension remains K-flat by lem-pur-kflat-change-of-rings-independent, so all three model counits are invertible. Naturality across resolution quasi-isomorphisms gives invertibility everywhere. The derived scalar unit is the uniqueness isomorphism between the given derived scalar model and the identity, using the localized ordinary multiplication unitor as counit. For uniqueness of both comparisons, equality on K-flat inputs extends to all inputs by naturality and cancellation of the resolution isomorphisms. These two existence-and-uniqueness assertions are proved in Lean; the combined mixed-coherence theorem retains its original proof obligation.

### Original step 8

Apply the localization of [def-weil-abstract-derived-category] to the equal cochain maps of Steps 2--6 on the simultaneous model of Step 7. A functor takes equal arrows to equal arrows, so all desired equations hold at that model. If $a,b:F\Rightarrow G$ denote the two derived composites of any equation and $p:P\to C$ is the chosen resolution, naturality gives $a_C F(Qp)=G(Qp)a_P$ and $b_C F(Qp)=G(Qp)b_P$. Since $Qp$ is invertible and $a_P=b_P$, cancellation gives $a_C=b_C$. This proves equality for every input and, since the comparisons are natural, equality of natural transformations. Step 6 shows these are equalities localized from the full quotient diagrams before any realization. The resolution and preservation theorems apply to unbounded complexes and arbitrary ring maps. No step used normalization, a bound on cohomology or Tor-amplitude, or flatness of $A_{E,n}\to A_{L,n}$; hence all the stated unrestricted assertions follow.

## Not duplicates

These splits were compared with whole-DAG keyword/tag searches, blueprint_refs searches for pullback coherence, scalar composition, inverse-image composition, mixed, tensor-generator, K-flat comparisons and finite words, and the project source searches by tags and notions. In particular the existing general adjoint-composition node is reused, and the existing resolving-class and localization results will be available when splitting the generic descent task. The source-collision pairs requested by the delivery check follow; sharing a background Stacks tag does not assert the same normalized comparison theorem.

lem-trf-sequence-scalar-generator-interchange vs lem-trf-quotient-system-mixed-coherence: parent asserts derived mixed and finite-string geometric coherence; the new scalar task is only its ordinary generator argument, specifically extracted under the re-split note, and cannot prove the derived clause alone.

lem-trf-sequence-scalar-generator-interchange vs lem-pe-kflat-scalar-tower-realization: existing theorem computes an augmented scalar-reduction tower and its units, not the three ordinary geometric/scalar interchange equations.

lem-trf-sequence-scalar-generator-interchange vs lem-sbc-pullback-comparison-comp: existing theorem is a coefficient comparison for a degree-zero sheaf and two geometric squares; there is no whole-sequence scalar unit/tower assertion.

lem-trf-sequence-scalar-generator-interchange vs lem-sf-open-exchange-roos-restriction: existing theorem is a completed open exchange and Roos restriction; the new node is ordinary scalar/geometric interchange before completion.

lem-trf-sequence-scalar-generator-interchange vs lem-sf-scalar-pullback-composition: existing theorem gives geometric-composition compatibility at one fixed constant-ring map on scheme sites; it does not give scalar unit/tower equations for strict varying-ring systems.

lem-trf-sequence-scalar-generator-interchange vs lem-pur-factorized-pullback-square-pasting: existing theorem pastes pullback squares for factored endomorphisms at one finite constant ring; it has no scalar extension unit/tower equations.

lem-trf-sequence-scalar-generator-interchange vs lem-sf-semilinear-compositor-coherence: existing theorem gives geometric pullback/direct-image/open compositors at fixed ring systems, without scalar-changing mixed comparisons.

lem-trf-sequence-scalar-generator-interchange vs def-sf-semilinear-proper-open-comparisons: existing definition specifies geometric, proper and open mates, not theorems for coefficient-changing tensor squares.

lem-trf-sequence-scalar-generator-interchange vs def-zl-pbc-finite-raw-scalar-comparison: existing definition compares normalized and embedding scalar extension at field stages, not ordinary strict quotient-system interchange.

lem-trf-sequence-scalar-generator-interchange vs def-zl-finite-regular-coefficient-comparisons: existing definition specifies regular finite coefficient objects and a compositor; it does not assert these scalar-changing coherence equations.

lem-trf-sequence-scalar-generator-interchange vs lem-trf-derived-pullback-coherence: existing theorem is geometric associativity with one constant finite ring, not scalar unit or scalar tower compatibility.

lem-trf-sequence-scalar-generator-interchange vs def-trf-integral-comparison-realization-models: existing definition chooses normalized realization interfaces; the new theorem is an ordinary pre-realization tensor-generator calculation.

lem-trf-sequence-scalar-generator-interchange vs lem-pe-kflat-roos-representative-invariance: existing theorem is Roos representative invariance, not scalar/geometric interchange.

lem-trf-sequence-scalar-generator-interchange vs lem-pe-two-term-reduction-cohomology: existing theorem computes a specific two-term coefficient complex.

lem-trf-sequence-scalar-generator-interchange vs lem-pe-restricted-kflat-tensor-identification: existing theorem identifies scalar-first and scalar-last tensor models after restriction, not geometric or scalar coherence equations.

lem-trf-sequence-scalar-generator-interchange vs def-pe-integral-presentation-encoding: existing node is coefficient presentation data, not ordinary interchange equations.

lem-trf-sequence-scalar-generator-interchange vs lem-sfb-ringed-finite-free-resolution-tensor: existing theorem is tensor computation from a finite-free resolution.

lem-trf-sequence-scalar-generator-interchange vs lem-pe-integral-reduction-transition-comparison: existing theorem compares integral quotient transitions under encodings.

lem-trf-sequence-scalar-generator-interchange vs lem-pe-integral-normalized-restriction-squares: existing theorem constructs integral restriction encodings.

lem-trf-sequence-scalar-generator-interchange vs lem-sbc-derived-scalar-extension-counit-shift: existing theorem gives coherent shifts of derived scalar extension.

lem-trf-sequence-scalar-generator-interchange vs lem-sbc-koszul-tensor-derived-tower: existing theorem compares a fixed Koszul tensor tower.

lem-trf-sequence-scalar-generator-interchange vs lem-pur-coefficient-pullback-coherence: existing theorem concerns supplied Comparisons data and balanced units/associators but does not give the geometric mixed-composition equation or its actual strict quotient-system normalization.

lem-trf-sequence-scalar-generator-interchange vs lem-weil-pbc-site-derived-tensor-descent: existing theorem concerns tensor bifunctor descent, not these ordinary mixed equations.

lem-trf-sequence-scalar-generator-interchange vs lem-sfb-multivariable-derived-calculus: existing theorem concerns abstract localization calculus, not the ordinary strict-system generator equations.

lem-trf-sequence-scalar-generator-interchange vs lem-sp-exact-derived-transformation-pasting: existing theorem derives supplied ordinary equations; it does not establish the new ordinary equations.

lem-trf-sequence-scalar-generator-interchange vs lem-weil-pbc-ringed-topos-kflat-pullback: existing theorem is K-flat preservation for one ringed pullback.

lem-trf-ringed-kflat-word-comparison-descent vs lem-trf-quotient-system-mixed-coherence: parent proves particular geometric/scalar equations; the new general theorem starts with ordinary transformations/relations and provides their normalized ringed-site descent, without proving those ordinary relations.

lem-trf-ringed-kflat-word-comparison-descent vs lem-pe-kflat-roos-representative-invariance: existing theorem needs exact countable products and identifies augmented Roos cones; no such products or cones occur in the new finite-word descent theorem.

lem-trf-ringed-kflat-word-comparison-descent vs lem-pe-two-term-reduction-cohomology: existing theorem computes two cohomology groups and transitions for a specific two-term complex, not arbitrary word models.

lem-trf-ringed-kflat-word-comparison-descent vs lem-pe-restricted-kflat-tensor-identification: existing theorem gives a restricted scalar-first tensor comparison for one resolution, not arbitrary finite ringed-site words and pasting.

lem-trf-ringed-kflat-word-comparison-descent vs def-pe-integral-presentation-encoding: existing node is a definition of supplied integral presentation data, not a theorem about derived word models.

lem-trf-ringed-kflat-word-comparison-descent vs lem-pe-kflat-scalar-tower-realization: existing theorem identifies one augmented scalar tower; the new theorem handles finite words of general ringed pullbacks and natural transformations between them.

lem-trf-ringed-kflat-word-comparison-descent vs lem-sfb-ringed-finite-free-resolution-tensor: existing theorem assumes a specified bounded-above finite-free resolution of a sheaf; the new theorem allows arbitrary unbounded complexes and ringed pullback words.

lem-trf-ringed-kflat-word-comparison-descent vs lem-pe-integral-reduction-transition-comparison: existing theorem is one normalized integral transition equation under encoding hypotheses, not a finite-word descent theorem.

lem-trf-ringed-kflat-word-comparison-descent vs lem-pe-integral-normalized-restriction-squares: existing theorem constructs ordinary encoding restriction squares, with no derived word conclusion.

lem-trf-ringed-kflat-word-comparison-descent vs lem-sbc-pullback-comparison-comp: existing theorem is a fixed degree-zero coefficient comparison, not general unbounded finite-word K-flat counit descent.

lem-trf-ringed-kflat-word-comparison-descent vs lem-sbc-derived-scalar-extension-counit-shift: existing theorem constructs counit-compatible shifts for one scalar map; the new node handles independent ringed sites and finite words/pastings, with no shift-structure assertion.

lem-trf-ringed-kflat-word-comparison-descent vs lem-sbc-koszul-tensor-derived-tower: existing theorem uses a specific strict dual Koszul tower; the new statement is not a consequence of that fixed-object comparison.

lem-trf-ringed-kflat-word-comparison-descent vs lem-sf-open-exchange-roos-restriction: existing theorem uses complete objects, open exchanges and Roos realization; the new theorem has no completion or realization hypothesis or conclusion.

lem-trf-ringed-kflat-word-comparison-descent vs lem-sf-scalar-pullback-composition: existing theorem gives one particular scalar/pullback equation, not resolving models and descent for arbitrary ringed-site words.

lem-trf-ringed-kflat-word-comparison-descent vs lem-pur-factorized-pullback-square-pasting: existing theorem is one geometric endomorphism pasting equation, not a general model comparison theorem.

lem-trf-ringed-kflat-word-comparison-descent vs lem-sf-semilinear-compositor-coherence: existing theorem gives geometric compositor equations, not derived scalar word models for arbitrary structural ring maps.

lem-trf-ringed-kflat-word-comparison-descent vs def-sf-semilinear-proper-open-comparisons: existing definition specifies proper/open comparison data, not simultaneous K-flat computation or transformation descent.

lem-trf-ringed-kflat-word-comparison-descent vs def-zl-pbc-finite-raw-scalar-comparison: existing definition specifies field-stage coordinate comparison, not general ringed-site finite-word resolving models.

lem-trf-ringed-kflat-word-comparison-descent vs def-zl-finite-regular-coefficient-comparisons: existing definition specifies finite regular objects/compositors, not unbounded generic comparison descent.

lem-trf-ringed-kflat-word-comparison-descent vs lem-trf-derived-pullback-coherence: existing theorem proves a particular geometric associativity equation; the new theorem provides the generic resolving-model transfer mechanism.

lem-trf-ringed-kflat-word-comparison-descent vs def-trf-integral-comparison-realization-models: existing definition describes chosen completed realization interfaces, not existence or coherence of finite-word K-flat descent.

lem-trf-ringed-kflat-word-comparison-descent vs lem-pur-coefficient-pullback-coherence: existing theorem proves two particular coherence laws for given coefficient comparisons, not generic finite-word resolving models.

lem-trf-ringed-kflat-word-comparison-descent vs lem-weil-pbc-site-derived-tensor-descent: existing theorem supplies resolving-class localization and bifunctor extension on one ringed site; it does not identify composite counits for words crossing distinct ringed sites.

lem-trf-ringed-kflat-word-comparison-descent vs lem-sfb-multivariable-derived-calculus: existing theorem assumes left derivability structures and functors inverting the relevant arrows; the new theorem establishes the concrete K-flat flat-term word models and their composite counit normalization for ringed pullbacks.

lem-trf-ringed-kflat-word-comparison-descent vs lem-sp-exact-derived-transformation-pasting: existing theorem assumes every edge exact; the new node includes nonflat scalar extension, which need not be exact.

lem-trf-ringed-kflat-word-comparison-descent vs lem-weil-pbc-ringed-topos-kflat-pullback: existing theorem supplies preservation for one edge only; the new node additionally identifies composite universal counits and descends arbitrary natural transformations and their pastings.


lem-trf-ringed-kflat-word-comparison-descent vs def-a1-integral-completed-tower-pullback-universes: existing definition specifies integral reduction and a single tower pullback pair; the new theorem proves simultaneous finite-word models and transformation descent on arbitrary ringed sites.

lem-trf-ringed-kflat-word-comparison-descent vs lem-a1-principal-koszul-strict-replacement: existing theorem constructs the explicit principal Koszul replacement of a reduction tower; the new theorem has neither principal ideal nor Koszul objects and proves finite-word comparison descent.

lem-trf-ringed-kflat-word-comparison-descent vs lem-per-proetale-scalar-slice-comparison: existing theorem is a single scalar/slice restriction comparison; the new theorem proves normalized transformation descent and whiskering for arbitrary finite words of ringed pullbacks.

lem-trf-ringed-kflat-word-comparison-descent vs def-pc-derived-tensor-cohomology-vanishes: existing node defines a tensor-cohomology vanishing predicate for a sheaf second factor; it proves no word-model or transformation descent theorem.

lem-trf-ringed-kflat-word-comparison-descent vs def-pc-derived-tensor-complex-cohomology-vanishes: existing node defines tensor-cohomology vanishing with a complex second factor; it does not supply composite derived counits or word comparisons.

lem-trf-ringed-kflat-word-comparison-descent vs def-pc-kflat-complex: existing node defines K-flatness and resolutions; the new theorem proves existence, preservation and normalized descent. The new statement cites this definition.

lem-trf-ringed-kflat-word-comparison-descent vs def-sc-bounded-flat-shift-representative: existing node defines a bounded-flat shifted representative predicate; the new theorem has arbitrary unbounded inputs and a transformation-descent conclusion.

lem-trf-ringed-kflat-word-comparison-descent vs def-sc-derived-tensor-augmentation: existing node defines data expressing one derived tensor augmentation; it gives no existence theorem or finite-word counit normalization.

lem-trf-ringed-kflat-word-comparison-descent vs def-sc-flat-telescope-stage-map: existing node defines flat telescope stage-induced morphisms; no telescope is involved in the new theorem about finite ringed-pullback words.

lem-trf-ringed-kflat-word-comparison-descent vs lem-pc-bounded-above-flat-kflat-site: existing theorem makes bounded-above flat complexes K-flat; the new theorem resolves arbitrary unbounded complexes and identifies universal word counits and transformations.

lem-trf-ringed-kflat-word-comparison-descent vs lem-pc-bounded-above-flat-tensor-acyclic: existing theorem proves bounded-above tensor acyclicity; the new theorem neither assumes boundedness nor concludes only acyclicity, but gives arbitrary ringed-word comparison descent.

lem-trf-sequence-scalar-generator-interchange vs def-a1-proper-sections-germ-and-moving-point: existing definition specifies proper germs and moving Frobenius points at integral/rational stages; the new node proves ordinary whole-system coefficient-changing identities and has no properness or Frobenius data.

lem-trf-sequence-scalar-generator-interchange vs def-per-derived-hom-pullback: existing definition gives maps on shifted Hom groups for a geometric composite at fixed coefficients; the new node proves mixed geometric/scalar equations of ordinary strict-system transformations.

lem-trf-sequence-scalar-generator-interchange vs lem-pod-constant-comparison-module-localization: existing theorem identifies localization of one fixed finite-coefficient compositor; the new theorem gives scalar-changing mixed, unit and tower identities before localization.

lem-trf-sequence-scalar-generator-interchange vs lem-pod-finite-system-pullback-coherence: existing theorem gives geometric associativity for one fixed coefficient sequence; it has no extension-of-scalars mixed square, scalar unit, or coefficient-tower equation.

lem-trf-sequence-scalar-generator-interchange vs lem-pod-integral-pullback-composition: existing theorem gives composition and associativity after completed integral realization in bounded constructible categories; the new node concerns ordinary uncompleted systems with changing coefficients.

lem-trf-sequence-scalar-generator-interchange vs def-pbc-successive-derived-scalar-normalization-data: existing definition is a data type, explicitly not existence of normalization; it does not prove ordinary inverse-image/scalar interchange for the actual sequence operations.

lem-trf-sequence-scalar-generator-interchange vs def-weil-pbc-actual-finite-coefficient-transport: existing definition constructs completed coefficient maps and scalar transport; it does not assert the three ordinary strict-system identities.

lem-trf-sequence-scalar-generator-interchange vs def-weil-pbc-derived-direct-image-composition: existing definition specifies derived direct-image conjugate compositors for bounded-below abelian sheaves; the new ordinary module-system theorem concerns scalar-changing inverse images.

lem-trf-sequence-scalar-generator-interchange vs def-weil-pbc-derived-square-iso: existing definition localizes an exact geometric square at fixed coefficients; the new theorem proves three ordinary changing-coefficient equations with all quotient transitions.

lem-trf-sequence-scalar-generator-interchange vs def-weil-pbc-normalized-scalar-restriction: existing definition specifies a completed ringed scalar/pullback comparison and its counit normalization; it does not assert geometric-composition, scalar-unit or coefficient-tower coherence on strict quotient diagrams.

## Dry-run repairs

The first packaging dry run listed additional same-tag candidates in the server snapshot order. I opened each listed statement and added the pairwise distinctions above. None supplies the new theorem: most are definitions or a single fixed tensor/pullback computation. In particular finite-system-pullback-coherence covers geometry at fixed coefficients and is not the scalar-changing generator theorem. No mathematical statement or proof changed in this repair.
