# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-mv-exchange-triangles.json`: statement retained; six-step split, canonical signs and connecting maps retained; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-elementary-shriek-exact.json`: statement-only lemma, elementary-square exact sequence of exact left adjoint endofunctors; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-etale-sum-pullback.json`: statement-only lemma, arbitrary structural-ring pullback of etale sum extension, normalized by summands and counits, including K-flat preservation; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-derived-adjoint-ses-mates.json`: statement-only general homological lemma, right-adjoint SES triangle and compatibility of its canonical boundary with enhanced left-resolution comparisons; no Mathlib match.
- `citations.json`: every step/use pair is certified by the full verbatim statement read from the referenced node. No claim in this certificate comes from a node's proof alone.

## Attachments

None. Searches of the project's WeilConjectures source by the exact blueprint tag, relative Mayer–Vietoris, elementary distinguished squares, exchange triangles, and the existing scheme MV modules found no declaration stating the arbitrary algebraic-space elementary-square assertion. Scheme Zariski open-cover declarations have different objects and hypotheses. No compiler, Lake or build was run.

## Wanted sources

None. All source material used is present locally. No SGA source was used.

## Findings and corrections

The item's statement is retained. Stacks spaces-perfect Tag 08JK gives the relative triangle by the K-injective short exact sequence; Tag 0DKH uses a diagram including its connecting square without explaining it. The split supplies a concrete route to that square: compare the whole left resolution diagrams, then use the signed Hom/cone adjunction result, and identify each right component by its transpose. It does not infer the last square from only the first two squares, and does not replace the canonical boundary by one selected by TR3.

The left exact sequence uses 08GV, not a new node restating the item's derived triangle. The general adjoint-sequence node is not the item or one of its clauses: it has arbitrary abelian categories, exact functors, adjoints and an explicit resolution-diagram hypothesis, with no algebraic spaces or base-change geometry. The etale sum comparison isolates the additional geometric compatibility needed to verify that hypothesis. Its proof ideas below are preserved for the next splitter; they are deliberately not inserted as proof steps or proof dependencies in statement-only nodes.

The existing `blueprint.from.node` is null because the inherited created-item chain has a broken ancestor; `tools/blueprint_refs.py ancestor` prints None. The inherited exact place and via list are retained; the new nodes prepend this item to that via list. Whole-blueprint keyword searches and the current latest blueprint's direct-image proof were read. There is no matching blueprint statement; this is a supporting Stacks-module calculation within the inherited proper-direct-image prerequisite, not a change to the constructible coefficient route.

## Arguments retained for the new nodes

For the elementary-square sequence, read 08GV and 08GN in spaces-perfect.tex and 03DI/03DJ in sites-modules.tex. At a geometric point over U, the T-lifts are exactly the V-lifts, and the sequence is the graph inclusion x -> (sum x,-x), followed by addition. Outside U there is one V-lift and no T-lifts, and the last map is an identity. These computations give exactness with the displayed signs and allow arbitrarily many V-lifts. The same argument applies after arbitrary base change, since the complement's reduced support has a unique V-lift there. No reducedness of a scheme-theoretic base change of E is asserted.

For etale sum pullback, read the sheafified lift-indexed sums in 03DI and the fibre sums in 0710 and 08GU; compare with the K-flat pullback construction of 06YY and 0G7E. The comparison sends b tensor a local summand to the corresponding base-changed summand with coefficient b. Tensor products and direct sums commute; the geometric fibres of Z_1 and Z over corresponding points agree. Evaluation and nested-slice counits sum these same summands, so the comparison preserves both. Flat terms are preserved because their stalks are direct sums of flat modules. The projection formula for etale sum extension, checked on those same stalk sums, identifies j_!P tensor A with j_!(P tensor j^*A); exact restriction and exact j_! then show K-flat preservation. A flat-term K-flat resolution computes both sides of the derived comparison. This supplies arbitrary structural-ring base change, rather than using a constant-finite-coefficient etale-shriek lemma with unverified hypotheses.

For the adjoint-sequence result, read derived.tex 0152, 09T5, and 0A8D, including the cone formula and chain-adjunction normalization. For an injective I, testing the proposed right sequence by Hom(M,-) identifies it with Hom(E_0 M,I) -> Hom(E_1 M,I) -> Hom(E_2 M,I); injectivity makes this exact. Each H_iI is injective since E_i is exact; the sequence therefore splits. The H_i preserve K-injectives by their exact left adjoints. Applying F preserves a degreewise split sequence. Its SES boundary uses the cone projection quasi-isomorphism, not an arbitrary triangle completion. Termwise chain adjunction commutes with the Hom differential d(u)=d u-(-1)^degree(u)u d. Applying it to the cone defining 0152 identifies the left and right connecting maps with their usual opposite-Hom signs. A map of the whole left resolution diagrams commutes with both the cone projection and inclusion. Transposing these equations gives the corresponding right SES boundary equation. Quasi-isomorphisms of diagrams can be inverted, so the equation descends and is resolution independent. The node expressly assumes such a map of diagrams; bare commutation of two squares in a triangulated category is insufficient.

## Review by Q116

I read spaces-perfect.tex Tag 08JK (lemma-unbounded-relative-mayer-vietoris), the induction diagram in 0DKH (lemma-single-complex-base-change), and 08GV (lemma-exact-sequence-lower-shriek), with the source's injective-resolution argument. The statement keeps arbitrary unbounded structure-sheaf module complexes; the optional QCoh notation imposes no QCoh condition. I did not silently substitute constant coefficients or schemes for algebraic spaces.

Step 1 uses the elementary-square sequence node for exactly its short exact sequence and signs, the etale sum node for the specified exact adjunction, and the canonical module-functor definition for restriction/direct image. Their statements contain these data. The finite-sum adjunction and the composite adjunction are the explicit formal compositions of the displayed Hom bijections.

Step 2 uses the generic small-ringed-site resolution theorem for both existence and injectivity in every degree; generic localized restriction for K-injectivity after restriction; chart calculus for the normalized derived adjunction and compositors; and the new adjoint-sequence lemma for the split image sequence, naturality, and its SES boundary. I checked the site is small in the stipulated universes and that etale restrictions are actual slice restrictions. The composition comparison is used only for its stated units/counits normalization. No claim is taken from the proof of chart calculus alone.

Step 3 uses the ringed-topos pullback node's explicit assertion that the functor is exact and computed on flat-term K-flat resolutions. A finite biproduct is preserved by additivity, and the shift is the functor's own canonical comparison. It does not require flatness of g.

Step 4 uses etale sum pullback for K-flat preservation and evaluation/overlap counits, chart calculus for associative pullback composition, the elementary-square sequence for the actual maps, ringed K-flat preservation for f^*P, and the flat-quotient sheaf tensor SES lemma for exactness after structural-ring tensor. I initially left this last use implicit; the self-review corrected it by citing the existing node, rather than merely citing the definition of flatness. The quotient is f^*P in each degree and is flat; all sites stay within the specified universes. Thus this step verifies the whole resolution-diagram hypothesis and does not assume arbitrary pullback is exact on all module sheaves.

Step 5 uses the adjoint-sequence lemma for its exact mate formula and boundary equation, then etale sum pullback's counit normalization and chart calculus's counit-preserving compositors to identify the components. Transposing twice explicitly gives the displayed f_Z counit followed by phi restricted to Z'. This checks the connecting square for the named gamma components, not an unknown completion. Step 6 merely substitutes those identified components into the already obtained equation; it is elementary.

For each new node I checked B1–B9: all objects and hypotheses are introduced, sources carry actual tags/labels, data and notions are given inline or by definition references, searches are executed through msearch.py and recorded literally, and proof/proof_deps remain empty. I read the generic Mathlib MayerVietorisSquare short complex (lines 228–266), the free-module pullback comparison (PullbackFree lines 118–143), the slice adjunctions (PushforwardContinuous lines 342–365), and Triangulated/Adjunction line 60. They do not give the new statements in one specialization. Two semantic phrasings were searched for every new node. The extra third adjoint query was also read; it returns derived adjunction normalization, not the SES-mate comparison.

Small cases checked: U=X permits arbitrary etale V with arbitrarily many lifts and gives the split graph/addition complex, U=empty forces V=X and gives an identity, V=empty forces U=X, and the empty space/zero complex gives zero triangles. For sum pullback, h=id gives the identity summand comparison, empty Z gives zero, a disjoint etale cover gives arbitrary direct sums, and a nonflat quotient of rings still has the tensor/sum comparison (no general exactness of h^* is claimed). For the general homological node, E_2=0 or E_1=E_0 gives the zero or identity triangles, a split sequence gives zero boundary, and a nonsplit left sequence is allowed because the right sequence splits only on injective terms. The comparison hypothesis explicitly excludes three unrelated objectwise isomorphisms. No non-elementary proof step exceeds 2000 characters; no hidden long-step exception is used.

## Unfinished work

None in this one-level split. The three new nodes intentionally remain statement-only for future workers. The independent maintainer review remains separate from this author's signature.

## Not duplicates

Same-source-tag matches below were read as statements. A shared general construction tag (notably 06YY) is distinguished from the asserted specialized compatibility. The closest comparisons are spelled out first.

lem-sfb-space-relative-mv-exchange-triangles vs lem-pc-rf-mv-triangle-naturality: existing schemes with affine bases, qcqs f, QCoh complexes and a two-open cover; this item uses arbitrary algebraic spaces, an elementary etale square and all unbounded modules with canonical boundaries.

lem-sfb-space-etale-sum-pullback vs lem-pur-etale-sum-exchange-counit: existing constant finite coefficients and separated finite-type etale maps of Noetherian schemes; new arbitrary structural-ring tensor pullback on algebraic spaces without those hypotheses.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-complex-ses-triangle: existing naturality for a map of SES complexes; new adjunction identification and right-boundary compatibility from a whole left resolution diagram.

lem-sfb-space-elementary-shriek-exact vs def-a1-finite-adic-open-section-data: existing Finite adic open extension and fibre data; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-cbc-completed-finite-exchange-coordinates: existing Fixed finite coordinates for completed-ring open exchange; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-cbc-completed-strict-open-exchange: existing Canonical completed-ring strict open exchange; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-cbc-finite-comparison-models: existing Representative models and normalization of finite comparisons; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-coef-semilinear-derived-calculus: existing Ordinary derived semilinear calculus interfaces; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-pd-proetale-section-module-functors: existing Normalized tensor structures on existing pro-etale section-module functors; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-pd-section-derived-realization: existing Canonical derived section-module realization; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-pd-section-derived-tensor-data: existing Canonical derived section-module tensor data; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-pd-section-module-operations-data: existing Existing section-module operations and pure-tensor data; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-pur-ringed-open-extension-on-complexes: existing Termwise sheafified ringed slice extension on cochain complexes; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-pur-sequence-site-open-data: existing Ordinary open-extension data for the ringed sequence site; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-sf-completed-open-strict-mate-data: existing Canonical strict open mate and its scalar and completed endpoints; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-sf-etale-open-scalar-data: existing Canonical ordinary and derived open scalar comparison data; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-sf-finite-open-tensor-operations: existing Canonical finite open tensor and pullback operations; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-sf-integral-open-operations: existing Pinned integral open coefficient and operation presentation; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-sf-integral-open-reduction-comparison-data: existing Normalized integral open tensor and reduction comparison data; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-sf-localized-strict-tensor-comparison-data: existing Normalized cochain computation data for localized strict tensor towers; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-sf-open-normalization-data: existing Geometric and operation data for open tensor normalization; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-sf-semilinear-proper-open-comparisons: existing Canonical semilinear proper/open compositors and intrinsic clopen comparison; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-sfb-adic-residue-lift-comparisons: existing The coefficient comparisons and actual finite-reduction Hom tower; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-sp-open-coefficient-unit-iso: existing Open coefficient isomorphism normalized by the open unit; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-sp-semilinear-constant-ring-operations: existing Constant-ring semilinear system operations and normalized evaluation mates; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-sp-varying-ring-operations: existing Canonical geometric operations on varying-ring systems; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-sp-varying-ring-proper-open-arrows: existing Intrinsic varying-ring clopen proper/open arrows; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-weil-extension-by-zero-presheaf: existing The extension-by-zero presheaf of a module on a localized ringed site; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-weil-pbc-extension-by-zero: existing Extension by zero for open immersions; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-weil-pbc-integral-model-open-closed-basic: existing Concrete supported functors and ordinary rationalization; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-weil-pbc-local-coefficient-localization: existing Coefficient localization and local section multiplication on a ringed site; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs def-weil-pbc-ringed-derived-restriction: existing RingedDerivedRestriction; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-cbc-completed-finite-scalar-exchange: existing Completed-to-finite scalar compatibility of ordinary open exchange; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-cbc-completed-open-strict-mate-identification: existing Completed open exchange agrees with the actual constant-coefficient strict mate; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-cbc-completed-ring-strict-finite-exchange: existing Strict finite open exchange over completed coefficient rings; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-cbc-completed-support-intermediate-tower: existing Intermediate compact-support reduction tower and exchange substitution; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-cbc-extension-zero-stratified-perfect: existing Extension by zero preserves stratified perfect local models; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-cbc-finite-open-exchange-scalars: existing Finite open exchange commutes with coefficient restriction and tower transitions; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-cbc-localized-extension-zero-linear-derived: existing Module extension by zero is linear on the unbounded derived category; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-cbc-normalized-finite-comparison-existence: existing Existence of the two normalized finite comparisons; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-cbc-open-extension-zero-etale-adjunction-agreement: existing Open-immersion and etale extension by zero have the same adjunction; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-cbc-open-localized-counit-comparison: existing Open localized finite pullback is the pulled-back extension counit; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-cbc-ringed-open-scalar-adjunction: existing Scalar restriction and the sheafified slice-extension adjunction; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-cbc-ringed-open-scalar-limit-coherence: existing Ringed open extension, scalar restriction and normalized strict limits; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-cbc-tower-adjunction-realization: existing Constant coefficients and derived adjunctions on strict pro-etale towers; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-pc-inverse-image-open-free-sheaf: existing Inverse image of a represented open free abelian sheaf; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-pc-open-embedding-sheaf-pullback-injectives: existing Open embedding sheaf pullback preserves injectives; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-pc-open-extension-derived-unit-isiso: existing OpenExtensionDerivedUnitIsIso; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-pc-open-free-restriction-hom: existing Restriction of morphisms from the image-open free sheaf; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-pc-open-inverse-image-injectives: existing Open inverse image preserves injective abelian sheaves; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-pc-open-restriction-data: existing Degree-zero restriction data in the cartesian open-subscheme square; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-pc-open-restriction-ext-bijective: existing Bijectivity of the constructed open-restriction Ext maps; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-pc-scheme-module-free-yoneda-iso: existing Free Yoneda sheaves agree with extension by zero of the localized unit; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-pd-section-derived-open-adjunction-normalization: existing Section equivalence identifies the canonical derived open adjunction; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-pur-clopen-common-compact-support: existing Shared compactification and finite clopen compact-support summands; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-pur-compact-support-scalar-shift-normalization: existing Canonical shifts of scalar proper/open mates and scalar limit maps; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-pur-sequence-site-open-extension: existing Geometric and levelwise open extension on ringed sequence sites; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-pur-site-restriction-module-adjunction-exact: existing Restriction and extension by zero for modules on a localized site; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sc-module-extension-by-zero-unit-epi: existing The chosen open-extension adjunction unit is epic; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sc-module-extension-by-zero-unit-isiso: existing The chosen open-extension adjunction unit is invertible; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sc-module-extension-by-zero-unit-mono: existing The chosen open-extension adjunction unit is monic; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-canonical-open-restriction-model: existing Canonical open restriction on augmented quotient models; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-cbc-slice-tensor-generator-coherence: existing Generator-normalized slice tensor isomorphisms and their strict coefficient coherence; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-open-extension-scalar-restriction-coherence: existing Coherent finite scalar restriction for sheafified and derived open extension; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-open-operation-models: existing Open operation comparisons with fixed tensor models and right square; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-semilinear-clopen-unit-projector: existing Clopen system projection is the specified direct-image unit; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-semilinear-evaluation-derived-adjunction: existing Derived evaluation factors through the normalized constant diagonal; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-site-finite-projective-lift: existing exists local lift overMap from finiteFree; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-site-finite-projective-section: existing exists local section overMap of finiteFree retract; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-site-perfect-derived-restriction-iso: existing overFunctor derivedRestrictionIso; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-site-perfect-lower-model: existing exists strictPerfect lower model; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-site-perfect-opcycles-retract: existing exists local retract opcycles of perfect tor; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-site-perfect-opcycles-retract-transport: existing transport slice retract; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-site-perfect-overmap-additive: existing sitePerfectOverMap additive; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-site-perfect-overmap-comp: existing sitePerfectOverMapComp; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-site-perfect-overmap-exact: existing overMap exact ofUniverses; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-site-perfect-package-map: existing StrictPerfectCoefficientPackageOnSite.map; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-site-perfect-restriction-additive: existing sitePerfectOverFunctor additive; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-site-perfect-restriction-exact: existing overFunctor exact ofUniverses; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sf-site-perfect-upper-model: existing exists strictPerfect upper model; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sfb-coefficient-heart-locally-closed-extension: existing Exact locally closed coefficient extension through the scheme-theoretic closure; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sfb-exact-open-closed-unbounded-calculus: existing Unbounded support calculus from exact abelian open/closed localization data; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sfb-internal-open-extension-disjoint-vanishing: existing Disjoint pullback of internal module extension by zero vanishes; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sfb-locally-closed-extension-coherence: existing Restriction and composition for locally closed extension by zero; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sfb-locally-closed-module-extension-coherence: existing Normalized locally closed extension on module sheaves; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sfb-open-filtration-successor: existing Natural quotient for two nested open module pieces; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sfb-proetale-identified-open-closed: existing Exact open and closed extensions with identified inverse-image coefficients; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sfb-proetale-identified-supported-reconstruction: existing Normalized supported reconstruction for actual tensor pullbacks; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sfb-proetale-locally-closed-extension: existing Pointwise exact locally closed extension; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sfb-ringed-slice-scalar-unit: existing Normalized slice tensor comparison preserves coefficient scalar action; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sfb-ringed-slice-tensor-constraints: existing Normalized slice tensor comparison preserves associators; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sp-module-extension-zero-independent-ring: existing Exact module extension by zero with an independent ring universe; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sp-slice-restriction-strict-derived-limit: existing Slice restriction commutes with total derived inverse limit of strict towers; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sp-subterminal-module-local-calculus: existing Intersection and local detection calculus for subterminal module slices; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sp-supported-constructible-origin-comparison: existing Supported constructible etale origin and its unbounded coefficient tensor comparison; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sp-unbounded-open-counit-site-transport: existing Unbounded degreewise open adjunctions and actual site-comparison counits; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sp-varying-ring-cartesian-comparison-lift-relabelling: existing The cartesian open comparison on varying-ring systems relabels lifts; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-sp-varying-ring-open-unit-coherence: existing Exact localization and identity unit law for varying-ring open extension; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-trf-topos-complement-module-stalks: existing Module support, adjunctions and stalks for complementary subtopoi; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-affine-free-finite-stalk-generation: existing Finite affine free maps generating one module stalk; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-continuous-constructible-supported: existing Constructibility of supported continuous modules; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-continuous-extension-scalar-change: existing Ordinary scalar change commutes with continuous extension by zero; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-continuous-module-localization: existing Localization for the actual continuous module functors; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-element-presheaf-extension: existing Direct-sum computation and left exactness of presheaf element extension; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-etale-graph-section-extension-map-linear: existing The presheaf map from the etale sum presheaf to direct image is linear over the constant sheaf of rings; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-extension-by-zero-adjunction: existing Extension by zero is left adjoint to restriction (étale site); new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-extension-by-zero-exact: existing Extension by zero is exact (étale site); new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-free-etale-module-shriek-comparison: existing Free representable module sheaves are etale extensions by zero; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-free-sheaf-derived-sections: existing Free sheaf shifted Hom computes derived module global sections; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-free-sheaf-flat: existing The sheafified free presheaf on a representable with flat coefficients is flat (j_{X!} of a constant flat sheaf is flat); new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-free-yoneda-presheaf-module: existing Morphisms out of the free presheaf of modules on a representable are sections; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-integral-model-open-closed-pieces: existing Integral open and closed pieces remain constructible and rationalize to the localization sequence; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-proetale-ringed-open-closed: existing Ringed pro-etale open-closed localization; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-ringed-slice-extension-preserves-exact: existing Ringed-slice extension preserves exactness; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-sheaf-free-separator: existing The coproduct of the sheafified free presheaves on representables with coefficients in a separator is a separator of the sheaf category; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-site-extension-by-zero-exact: existing Extension by zero on a localized site is exact; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-site-extension-by-zero-presheaf-adjoint: existing The sheafified direct-sum presheaf is left adjoint to restriction to a localized site; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-site-restriction-exact: existing Restriction to a localized site is exact; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-site-restriction-injectives: existing Extension by zero and restriction on a localized site; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-zariski-etale-pushed-resolution: existing Local vanishing gives the pushed injective-resolution augmentation as a quasi-isomorphism; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-zariski-etale-pushed-resolution-finite-limits: existing Finite-limit preservation for the pushed resolution; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-zariski-etale-pushed-resolution-quasi-iso: existing Quasi-isomorphism of the pushed resolution augmentation; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-zariski-extension-by-zero-adjunction: existing Extension by zero of abelian Zariski sheaves is a left adjoint of restriction to an open; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs lem-weil-pbc-zariski-extension-by-zero-exact: existing Extension by zero of abelian Zariski sheaves is exact; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs new-lem-amb-closed-support-hom-sequence: existing Underived closed-support Hom sequence on injective sheaves; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs new-lem-sc-nested-slice-extension-stalks: existing Nested slice extension stalk maps; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs new-localized-restriction-extension-exists-universes: existing Exact extension adjoint for localized restriction with independent coefficient universe; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs new-open-embedding-sheaf-pullback-adjunction: existing Extension by zero adjunction for open embeddings; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs new-open-embedding-sheaf-pullback-preserves-monomorphisms: existing Open embedding sheaf pullback preserves monomorphisms; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs new-over-pullback-adjunction-mono: existing Extension by zero adjunction preserving monomorphisms; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-elementary-shriek-exact vs new-over-pullback-preserves-injectives: existing Restriction to a slice Grothendieck site preserves injective abelian sheaves; new geometric (+,-)/(+,+) exact module-endofunctor sequence for arbitrary elementary squares, including base changes is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-a1-finite-adic-open-section-data: existing Finite adic open extension and fibre data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-a1-integral-completed-tower-pullback-universes: existing Integral completed strict-tower interfaces at independent universes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-cbc-completed-finite-exchange-coordinates: existing Fixed finite coordinates for completed-ring open exchange; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-cbc-completed-strict-open-exchange: existing Canonical completed-ring strict open exchange; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-cbc-derived-pair-exchange-normalization: existing Representative normalization for abstract derived functor pairs; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-cbc-finite-comparison-models: existing Representative models and normalization of finite comparisons; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-cbc-regular-quotient-cone-basic: existing The strict scalar cone and coefficient restriction; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-coef-compact-support-reduction-maps: existing Canonical quotient maps and completed-coefficient derived reductions; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-coef-compact-support-tensor-comparison: existing Universal coefficient tensor presentations and canonical compact-support coefficient map; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-coef-graded-linear-category: existing Graded linear categories and graded linear functors from dg categories; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-coef-ringed-sequence-site: existing Canonical ringed sequence site for the coefficient quotient tower; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-coef-semilinear-derived-calculus: existing Ordinary derived semilinear calculus interfaces; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-coef-semilinear-system-models: existing Generic strict semilinear system constructions and representative normalization; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-fix-proper-etale-origin-scalar-data: existing Canonical scalar, tensor and direct-image comparisons at etale origins; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pbc-successive-derived-scalar-normalization-data: existing Normalized presentation data for successive derived scalar extensions; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pd-proetale-section-module-functors: existing Normalized tensor structures on existing pro-etale section-module functors; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pd-section-derived-realization: existing Canonical derived section-module realization; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pd-section-derived-tensor-data: existing Canonical derived section-module tensor data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pd-section-module-operations-data: existing Existing section-module operations and pure-tensor data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pe-integral-presentation-encoding: existing Specified integral coefficient presentation encoding; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-per-scalar-extension-unit: existing Canonical identity scalar-extension unit; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-change-of-rings-complex: existing Termwise change of rings of a cochain complex; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-constant-coefficient-inverse-image-data: existing Constant-coefficient algebraic inverse-image and derived-pullback data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-derived-constant-pullback-comparison: existing Canonical derived constant-sheaf pullback comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-derived-tensor-pullback-normalization: existing Normalization predicate for the existing derived tensor pullback comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-etale-scalar-pullback-iso: existing Canonical derived scalar and pullback isomorphism; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-finite-compact-support-scalar-data: existing Finite and ramified compact-support coefficient arrows; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-finite-scalar-coordinate-data: existing Normalized finite scalar coordinates on modules and strict towers; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-open-coefficient-normalizations: existing Exact-pullback and open-unit coefficient normalizations; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-operation-scalar-transport: existing Pure-tensor and derived-counit normalized operation scalar transport; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-ringed-open-extension-on-complexes: existing Termwise sheafified ringed slice extension on cochain complexes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-sequence-adjoint-resolution-data: existing Resolution data for the coefficient sequence projection; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-sequence-site-open-data: existing Ordinary open-extension data for the ringed sequence site; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-strict-quotient-completion-data: existing Strict quotient reduction towers and their canonical completion data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-strict-quotient-expressions: existing Strict quotient expressions with actual horizontal transitions; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-system-horizontal-reduction-adjoints: existing Ordinary and cochain horizontal reduction adjoints of semilinear systems; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-pur-vector-purity-scalar-single: existing Canonical scalar comparison on degree-zero coefficient sheaves; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-completed-coefficient-free-cell: existing Completed-coefficient finite free cells and canonical reduction maps; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-completed-open-strict-mate-data: existing Canonical strict open mate and its scalar and completed endpoints; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-etale-open-scalar-data: existing Canonical ordinary and derived open scalar comparison data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-finite-open-tensor-operations: existing Canonical finite open tensor and pullback operations; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-integral-comparison-system-data: existing Simultaneous normalized integral realization data and comparison predicates; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-integral-hom-reduction-comparison: existing Canonical integral internal Hom reduction comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-integral-open-operations: existing Pinned integral open coefficient and operation presentation; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-integral-open-reduction-comparison-data: existing Normalized integral open tensor and reduction comparison data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-localized-strict-tensor-comparison-data: existing Normalized cochain computation data for localized strict tensor towers; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-open-normalization-data: existing Geometric and operation data for open tensor normalization; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-open-semilinear-tensor-model-data: existing Simultaneous semilinear open tensor model data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-ordinary-integral-derived-pullback: existing Ordinary unbounded total derived integral pullback; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-ringed-derived-adjoint-lift-data: existing Data of a normalized derived adjoint lift of a ringed-topos morphism; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-semilinear-proper-open-comparisons: existing Canonical semilinear proper/open compositors and intrinsic clopen comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-strict-tensor-reduction-termwise: existing Ordinary strict tensor reduction and termwise functors; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sf-unrestricted-reduction-complex-constructions: existing Unrestricted reduction complexes and canonical comparison constructions; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sfb-adic-residue-lift-comparisons: existing The coefficient comparisons and actual finite-reduction Hom tower; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sfb-constant-completion-coefficient-data: existing Constant completion coefficient objects and scalar-extension data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sfb-derived-change-of-rings-cochain-model: existing Derived change-of-rings cochain presentation; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sfb-integral-quotient-coefficients: existing Canonical integral uniformizer quotient coefficient maps; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sfb-integral-quotient-projection-map: existing Integral quotient internal projection arrow; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sfb-internal-derived-scalar-comparisons: existing Normalized internal derived scalar comparison interface; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sfb-internal-section-scalar-pullback-comparison-data: existing Internal to section scalar and pullback comparison data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sfb-quotient-system-projection-data: existing Normalized coefficient-system scalar and projection presentation; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sfb-quotient-system-scalar-data: existing Universal normalized coefficient-system scalar model; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sfb-scalar-restriction-tensor-comparison-data: existing Canonical internal scalar restriction and tensor comparison maps; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sfb-section-scalar-tensor-normalization-data: existing Localized section restriction and scalar tensor normalization; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sfb-space-derived-tensor-pullback: existing Canonical derived tensor pullback on algebraic spaces; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sp-coefficient-scalar-representatives: existing Canonical scalar-extension arrows on cochain representatives; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sp-constant-quotient-projection: existing The canonical single-quotient reduction projection; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sp-constant-reduction-models: existing Coupled universal models for strict constant-coefficient reduction; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sp-constant-scalar-pullback-comparison: existing Canonical constant-coefficient scalar extension, direct image and pullback comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sp-et-proet-coefficient-transport: existing Fixed presentation transport of the recorded intrinsic reduction comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sp-finite-free-direct-image-data: existing Normalized scalar models and canonical coefficient comparison data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sp-finite-scalar-realization-presentations: existing Canonical finite scalar realization presentations; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sp-open-coefficient-unit-iso: existing Open coefficient isomorphism normalized by the open unit; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sp-open-scalar-operations: existing Constant-ring pro-etale scalar and open operations and their canonical comparisons; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sp-proetale-scalar-mate-identifications: existing Normalized pro-etale scalar-to-tensor and coefficient-pullback identifications; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sp-semilinear-constant-ring-operations: existing Constant-ring semilinear system operations and normalized evaluation mates; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sp-varying-ring-operations: existing Canonical geometric operations on varying-ring systems; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-sp-varying-ring-proper-open-arrows: existing Intrinsic varying-ring clopen proper/open arrows; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-trf-realized-pullback-comparisons: existing Constructible and rational forms of normalized integral pullback comparisons; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-trf-singleton-site-operations: existing Punctual ringed-site operations and normalized comparison predicates; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-extension-by-zero-presheaf: existing The extension-by-zero presheaf of a module on a localized ringed site; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-integral-derived-reduction: existing Derived reduction of integral complexes modulo powers of the uniformizer; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-pbc-common-quotient-pullback-data: existing Normalized common-quotient pullback comparison data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-pbc-constant-coefficient-scalar-extension: existing Constant coefficient scalar extension on a site; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-pbc-derived-normalization-arrows: existing Canonical derived coefficient normalization arrows; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-pbc-derived-reduction-model-data: existing Derived reduction model data and normalized complex comparisons; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-pbc-extension-by-zero: existing Extension by zero for open immersions; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-pbc-integral-model-open-closed-basic: existing Concrete supported functors and ordinary rationalization; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-pbc-koszul-reconstruction-models: existing The fixed Koszul and quotient reconstruction models; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-pbc-local-coefficient-localization: existing Coefficient localization and local section multiplication on a ringed site; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-pbc-normalized-origin-scalar-comparisons: existing Canonical quotient scalar-extension unit and associator; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-pbc-reduction-augmentation: existing Normalized augmentation of the completed reduction tower; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-pbc-ringed-derived-restriction: existing RingedDerivedRestriction; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-pbc-successive-derived-quotient-data: existing Normalized presentations of derived coefficient extension; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-weil-pbc-system-scalar-model: existing Normalized ordinary and derived scalar model data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-zl-condensed-scalar-realization: existing Canonical derived scalar realization for a commutative condensed ring; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-zl-derived-change-of-rings-model: existing Canonical derived change-of-rings cochain model; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs def-zl-ring-derived-scalar-extension: existing Derived restriction and extension of scalars for ordinary modules; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-a1-adic-scalar-flat-reduction-model: existing Adic scalar data and normalized flat reduction complexes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-a1-finite-pullback-strict-tower-comparison: existing Natural finite pullback comparison of strict reduction towers; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-a1-pulled-koszul-tower-chain-comparison: existing Ordinary pullback of principal Koszul towers and target augmentation; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-a1-quotient-tensor-scalar-tower-comparison: existing The total tensor quotient tower and ordinary scalar reduction agree with their units; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-amb-etale-sum-stalks: existing Geometric stalks of etale sum extension; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-asd-supported-kummer-scalar-derived-units: existing Derived universal properties of supported scalar maps; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-asd-supported-kummer-scalar-maps: existing Normalized supported scalar maps; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-completed-finite-scalar-exchange: existing Completed-to-finite scalar compatibility of ordinary open exchange; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-completed-open-kflat: existing Completed-coefficient open extension preserves flat-term K-flat models; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-completed-open-strict-mate-identification: existing Completed open exchange agrees with the actual constant-coefficient strict mate; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-completed-ring-strict-finite-exchange: existing Strict finite open exchange over completed coefficient rings; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-completed-support-intermediate-tower: existing Intermediate compact-support reduction tower and exchange substitution; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-extension-tensor-comparison-independent: existing Normalized scalar-extension tensor comparison in independent universes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-extension-zero-stratified-perfect: existing Extension by zero preserves stratified perfect local models; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-finite-open-exchange-scalars: existing Finite open exchange commutes with coefficient restriction and tower transitions; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-localized-extension-zero-linear-derived: existing Module extension by zero is linear on the unbounded derived category; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-normalized-finite-comparison-existence: existing Existence of the two normalized finite comparisons; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-open-extension-zero-etale-adjunction-agreement: existing Open-immersion and etale extension by zero have the same adjunction; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-open-localized-counit-comparison: existing Open localized finite pullback is the pulled-back extension counit; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-regular-quotient-cone-chain: existing Strict scalar cone augmentation and invariance; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-regular-quotient-cone-quasi-iso: existing Principal quotient cone quasi-isomorphism for every K-flat; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-regular-quotient-flat-sequence: existing Normalized principal quotient exact sequence on a flat module; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-ringed-open-scalar-adjunction: existing Scalar restriction and the sheafified slice-extension adjunction; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-ringed-open-scalar-limit-coherence: existing Ringed open extension, scalar restriction and normalized strict limits; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-cbc-tower-adjunction-realization: existing Constant coefficients and derived adjunctions on strict pro-etale towers; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-coef-dgcat-cell-comparison-functors: existing Comparison dg functors for freely contracting a formal cone; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-coef-dgcat-cone-word-normal-form: existing Old-object word generation after freely contracting a formal cone; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-coef-dgcat-equivalence-cell-calculus: existing Coherent homotopy-equivalence cell: realization, pushout and lifting; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-coef-dgcat-finite-limit-sketch-signature: existing Finite-limit sketch signature for small R-linear dg categories; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-coef-dgcat-formal-cone-enlargement: existing Strict dg Yoneda embedding and the formal cone enlargement; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-coef-dgcat-free-cell-calculus: existing Free dg-category presentations and arrow-word filtrations; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-coef-dgcat-sketch-model-identification: existing Models of the dg-category sketch are dg categories; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-coef-etale-tensor-model-comparison: existing Unique flat-model normalization of the étale scalar tensor comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-coef-exact-sections-reduction-unit: existing Exact sections identify principal derived reduction with the actual scalar-extension unit; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-coef-semilinear-operations-existence: existing Geometric and coefficient operations on a fixed semilinear system calculus; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-coef-semilinear-system-existence: existing Ordinary semilinear system calculus and cartesian internal Hom; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-coef-sequence-projection-derived-adjunction: existing Derived adjunction of a ringed sequence projection; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-derived-adjoint-cochain-counit: existing The chosen derived-adjunction counit on cochain representatives; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-derived-right-exact-tensor-comparison: existing Normalized tensor comparison for a right exact strong monoidal functor; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-exc-proetale-constant-support-projection: existing Constant-coefficient projection for compact support; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-exc-unbounded-coefficient-pullback-model: existing Unbounded coefficient comparison on flat-term K-flat inverse-image models; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-fix-reduction-open-etale-origin: existing Bounded etale witnesses for finite reduction and open extension; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-fix-tensor-pullback-square: existing Tensor inverse-image comparisons commute around an open square; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-geo-cartier-coeff-extension: existing Derived scalar extension of a closed supported constant sheaf; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-geo-cartier-exponent-independence: existing Modulus change of the derived quotient and torsion identifications; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pc-inverse-image-open-free-sheaf: existing Inverse image of a represented open free abelian sheaf; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pc-open-embedding-sheaf-pullback-injectives: existing Open embedding sheaf pullback preserves injectives; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pc-open-extension-derived-unit-isiso: existing OpenExtensionDerivedUnitIsIso; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pc-open-free-restriction-hom: existing Restriction of morphisms from the image-open free sheaf; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pc-open-inverse-image-injectives: existing Open inverse image preserves injective abelian sheaves; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pc-open-restriction-data: existing Degree-zero restriction data in the cartesian open-subscheme square; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pc-open-restriction-ext-bijective: existing Bijectivity of the constructed open-restriction Ext maps; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pc-scheme-module-free-yoneda-iso: existing Free Yoneda sheaves agree with extension by zero of the localized unit; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pd-module-ringed-topos-derived-comparison: existing Module-object and ringed-topos derived tensor comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pd-section-derived-open-adjunction-normalization: existing Section equivalence identifies the canonical derived open adjunction; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pd-section-derived-representative-square: existing Actual internal derived tensor arrow on resolving representatives; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pe-integral-normalized-restriction-squares: existing Normalized finite restriction squares for the integral coefficient presentation; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pe-integral-reduction-transition-comparison: existing Quotient transitions under normalized integral coefficient comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pe-kflat-roos-representative-invariance: existing K-flat representative invariance of augmented scalar-extension Roos cones; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pe-kflat-scalar-tower-realization: existing K-flat realization of the augmented derived scalar-extension tower; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pe-restricted-kflat-tensor-identification: existing Restricted scalar-first K-flat tensor models identify derived scalar extensions; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pe-two-term-reduction-cohomology: existing Cohomology and quotient maps of a two-term integral coefficient complex; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-per-localized-pullback-tensor-normalization: existing Two localization-normalized derived pullback tensor identifications; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-per-proetale-scalar-slice-comparison: existing Normalized scalar extension comparison on a pro-etale slice; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-per-rational-scalar-balanced-localization: existing Balanced localization and raw fraction comparison for finite coefficients; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pod-derived-reduction-sheaf-resolution-independence: existing Independence of the sheaf K-flat resolution after exact point sections; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pod-point-extension-kflat: existing K-flatness of the point extension of a flat-term module complex; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pod-point-sections-derived-reduction-cone: existing Multiplication-cone component; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pod-point-sections-derived-reduction-homology: existing Homology exact-sections component; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pod-point-sections-derived-reduction-iso: existing Derived point-section comparison component; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pod-principal-derived-tensor-cone: existing Derived principal quotient tensor is the scalar multiplication cone; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pod-principal-quotient-quasi-iso: existing Principal quotient preserves quasi-isomorphisms on regular complexes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pod-principal-reduction-comparison: existing Descent of exact-sections principal reduction through derived roofs; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pod-principal-reduction-flat-comparison: existing Invertibility of the principal reduction comparison on flat models; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pod-scalar-reduction-cochain-comparison: existing Cochain and homotopy presentations of scalar reduction agree; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-algebra-diagram-pullback-extension-coherence: existing Derived scalar-extension/pullback comparison agrees with the ambient strict-diagram tensor map; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-change-of-rings-acyclic-kflat: existing Extension of scalars of acyclic K-flat complexes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-change-of-rings-kflat-quasi-iso: existing Termwise change of rings preserves quasi-isomorphisms between K-flat complexes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-change-of-rings-tensor-acyclic: existing Change of rings of a universally tensor-acyclic complex; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-change-of-rings-tensor-comparison: existing Natural comparison of restricted scalar extension and sheaf tensor; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-clopen-common-compact-support: existing Shared compactification and finite clopen compact-support summands; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-clopen-derived-scalar-compositor: existing Clopen derived scalar comparison and its normalized compositor; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-coefficient-pullback-comparison: existing Canonical inverse-image coefficient comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-compact-support-scalar-shift-normalization: existing Canonical shifts of scalar proper/open mates and scalar limit maps; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-completed-coefficient-completion-roos-transport: existing The normalized completion Roos triangle under completed coefficient transport; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-completed-line-derived: existing Derived finite reductions of a completed coefficient line are ordinary reductions; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-derived-change-of-rings: existing Derived change of rings along a morphism of sheaves of rings, computed by K-flat resolutions; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-etale-scalar-flat-kflat-comparison: existing Native flat-term K-flat étale complexes in scalar coordinates; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-etale-scalar-pullback-existence: existing Existence of normalized derived scalar/pullback comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-etale-scalar-pullback-uniqueness: existing Uniqueness of normalized derived scalar/pullback comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-external-rhom-evaluation-naturality: existing Four-variance naturality of the external evaluation transpose; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-finite-derived-comparison-normalization: existing K-flat normalization and coefficient coherence of the finite derived comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-integral-ambient-operation-models: existing Ambient completion presentations for integral pullback and tensor; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-integral-object-pullback-line: existing Completed inverse image of an integral line with a slice basis; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-integral-operations-well-defined: existing The towers defining integral pullback and completed tensor product are invariant under change of K-flat resolution; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-kflat-change-of-rings: existing Change of rings preserves K-flat complexes with flat terms; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-kflat-change-of-rings-all-independent: existing Change of rings preserves all K-flat complexes with independent coefficient universe; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-kflat-change-of-rings-independent: existing Change of rings preserves K-flat complexes with flat terms in independent universes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-normalized-scalar-comparison-realization: existing Normalized realization of scalar comparisons on quotient systems; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-quotient-expression-kflat-normalization: existing Simultaneous K-flat normalization of strict quotient expressions; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-quotient-expression-strict-kflat-towers: existing Prescribed strict quotient-expression towers, cocycles and system K-flatness; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-quotient-operation-adjoint-factorizations: existing Tensor and pullback transition adjunct factorizations on prescribed K-flat complexes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-quotient-system-flat-models: existing Strict flat quotient systems compute simultaneous tensor and geometric inverse image; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-relative-external-power-regrouping: existing Regrouping and finite-Tor domains of relative external powers; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-ringed-coefficient-change-normalization: existing Normalized coefficient changes and their naturality; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-ringed-coefficient-derived-presentation-exists: existing Existence of a normalized derived coefficient presentation; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-ringed-derived-pullback-linear: existing Derived ringed-topos pullback preserves compatible central scalars; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-scalar-tensor-pullback-normalization: existing Scalar/tensor pullback normalization on a K-flat representative; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-sequence-kflat-comparison-shifts: existing K-flat quotient-projection comparison and coherent shifts; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-sequence-site-completion-projection: existing Constant/limit ringed sequence projection and coherent reduction; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-sequence-site-open-extension: existing Geometric and levelwise open extension on ringed sequence sites; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-sheaf-ring-derived-hom-comparison: existing Compatibility of the derived scalar-extension adjunction with homotopy Hom representatives; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-site-restriction-module-adjunction-exact: existing Restriction and extension by zero for modules on a localized site; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-system-cochain-tensor-reduction: existing Cochain scalar-adjoint tensor formula for strict systems; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-system-ordinary-tensor-reduction: existing Ordinary scalar-adjoint tensor formula for strict systems; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-pur-varying-ring-tensor-comparison: existing Normalized tensor comparison for one varying-ring inverse image; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sbc-derived-coefficient-map-descent: existing Descent of a termwise coefficient map through a resolving counit; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sbc-derived-scalar-extension-counit-shift: existing Counit-compatible shift structure of derived change of rings on a site; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sbc-scalar-extension-counit-properties: existing K-flat computation and triangulatedness of a specified scalar-extension counit; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sc-module-extension-by-zero-unit-epi: existing The chosen open-extension adjunction unit is epic; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sc-module-extension-by-zero-unit-isiso: existing The chosen open-extension adjunction unit is invertible; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sc-module-extension-by-zero-unit-mono: existing The chosen open-extension adjunction unit is monic; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-boundary-bounded-tensor-comparison: existing Bounded tensor preparation for the boundary direct-image comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-canonical-open-restriction-model: existing Canonical open restriction on augmented quotient models; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-cbc-slice-tensor-generator-coherence: existing Generator-normalized slice tensor isomorphisms and their strict coefficient coherence; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-coefficient-cochain-tensor-curry: existing Componentwise coefficient cochain currying; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-coefficient-tensor-curry-normalization: existing Normalization of coefficient tensor currying; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-completion-unit-finite-projection: existing Projection of the completion unit is the finite scalar-extension unit; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-derived-complete-legacy-comparison: existing Intrinsic and K-flat augmented-tower derived completeness agree; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-etale-tor-flat-pullback-model: existing Etale finite-Tor flat models with their termwise geometric pullback; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-integral-line-tensor-comparison-representative: existing K-flat line tensor models and finite balancing; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-open-extension-scalar-restriction-coherence: existing Coherent finite scalar restriction for sheafified and derived open extension; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-open-operation-models: existing Open operation comparisons with fixed tensor models and right square; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-open-pullback-support: existing Derived pullback preserves open support; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-open-quotient-completion-unit-comparison: existing Open strict quotient comparison and actual completion-unit normalization; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-open-restriction-completeness: existing Completeness and the actual completion unit after ordinary open restriction; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-reduction-pull-finite-evaluation: existing Finite evaluation respects the specified reduction/pullback comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-scalar-pullback-composition: existing Composition coherence of normalized scalar/pullback comparisons; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-scalar-tensor-comparison-transport: existing Transport of normalized scalar tensor comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-semilinear-clopen-unit-projector: existing Clopen system projection is the specified direct-image unit; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-semilinear-evaluation-derived-adjunction: existing Derived evaluation factors through the normalized constant diagonal; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-site-finite-projective-lift: existing exists local lift overMap from finiteFree; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-site-finite-projective-section: existing exists local section overMap of finiteFree retract; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-site-perfect-derived-restriction-iso: existing overFunctor derivedRestrictionIso; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-site-perfect-lower-model: existing exists strictPerfect lower model; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-site-perfect-opcycles-retract: existing exists local retract opcycles of perfect tor; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-site-perfect-opcycles-retract-transport: existing transport slice retract; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-site-perfect-overmap-additive: existing sitePerfectOverMap additive; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-site-perfect-overmap-comp: existing sitePerfectOverMapComp; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-site-perfect-overmap-exact: existing overMap exact ofUniverses; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-site-perfect-package-map: existing StrictPerfectCoefficientPackageOnSite.map; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-site-perfect-restriction-additive: existing sitePerfectOverFunctor additive; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-site-perfect-restriction-exact: existing overFunctor exact ofUniverses; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sf-site-perfect-upper-model: existing exists strictPerfect upper model; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-coefficient-heart-locally-closed-extension: existing Exact locally closed coefficient extension through the scheme-theoretic closure; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-complete-integral-residue-functor: existing Exact residue reduction on the triangulated category of complete integral complexes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-constant-module-kflat: existing Constant realization preserves flat-term K-flat complexes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-constant-realization-derived-scalar-extension: existing Derived constant realization commutes with derived scalar extension; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-derived-section-scalar-transport: existing Localization transport of the normalized scalar adjunction; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-divisible-extension-derived-reduction: existing Derived reduction of an extension by a divisible sheaf; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-exact-open-closed-unbounded-calculus: existing Unbounded support calculus from exact abelian open/closed localization data; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-exact-right-adjoint-kflat-representative: existing K-flat representative transpose for exact-right derived adjunctions; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-flat-term-kflat-functor: existing Flat-preserving colimit functors preserve flat-term K-flat complexes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-integral-coefficient-square-normalization: existing Normalized constant-to-integral coefficient square and flat K-flat pullback; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-integral-hom-comparison-normalization: existing The normalized integral Hom reduction presentations give the same morphism; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-internal-open-extension-disjoint-vanishing: existing Disjoint pullback of internal module extension by zero vanishes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-internal-scalar-mate-transitivity: existing Successive internal coefficient mates and normalized scalar units; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-internal-scalar-pullback-normalization: existing Normalized internal scalar extension and geometric pullback; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-kflat-scalar-comparison-normalization: existing Representative and adjunction normalization of scalar pullback comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-locally-closed-extension-coherence: existing Restriction and composition for locally closed extension by zero; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-locally-closed-module-extension-coherence: existing Normalized locally closed extension on module sheaves; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-open-filtration-successor: existing Natural quotient for two nested open module pieces; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-proetale-identified-open-closed: existing Exact open and closed extensions with identified inverse-image coefficients; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-proetale-identified-supported-reconstruction: existing Normalized supported reconstruction for actual tensor pullbacks; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-proetale-locally-closed-extension: existing Pointwise exact locally closed extension; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-ringed-derived-adjoint-lift: existing Normalized ordinary and derived adjoint lifts of ringed-topos morphisms; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-ringed-site-point-kflat-resolution: existing K-flat resolution with K-flat stalk; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-ringed-slice-scalar-unit: existing Normalized slice tensor comparison preserves coefficient scalar action; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-ringed-slice-tensor-constraints: existing Normalized slice tensor comparison preserves associators; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-scalar-extension-kflat: existing Scalar extension preserves all K-flat sheaf complexes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-successive-derived-quotient-normalization: existing Successive derived scalar extensions agree with direct quotient extension; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sfb-topos-scalar-mate-transitivity: existing Transitivity of canonically normalized coefficient mates on sheaf topoi; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-bounded-flat-coefficient-site-square: existing Bounded-flat coefficient/site square with its canonical derived comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-cofinal-quotient-kflat-bisystem: existing Simultaneous K-flat realization of a commuting two-family scalar diagram; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-constant-perfect-quotient-projection: existing Perfect projection for one constant quotient; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-etale-counit-scalar-model: existing Common K-flat representatives for the two etale coefficient-counit composites; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-finite-free-scalar-models: existing Existence of normalized actual-restriction scalar models; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-finite-free-scalar-shift: existing The normalized scalar counit commutes with shifts and scalar extension is triangulated; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-koszul-quotient-strict-resolution-bridge: existing Strict Koszul to quotient comparison on one K-flat resolution; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-module-extension-zero-independent-ring: existing Exact module extension by zero with an independent ring universe; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-restricted-scalar-tensor-cohomology-comparison: existing Underlying cohomology comparison for K-flat scalar extension; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-scalar-associator-conjugate: existing Right conjugate of the normalized scalar associator; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-slice-restriction-strict-derived-limit: existing Slice restriction commutes with total derived inverse limit of strict towers; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-strict-coefficient-tensor-descent: existing Strict coefficient tensor complexes descend through K-flat localization; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-subterminal-module-local-calculus: existing Intersection and local detection calculus for subterminal module slices; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-supported-constructible-origin-comparison: existing Supported constructible etale origin and its unbounded coefficient tensor comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-supported-scalar-tor-interval: existing Supported scalar tensor interval and reflection to an arbitrary etale origin; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-unbounded-open-counit-site-transport: existing Unbounded degreewise open adjunctions and actual site-comparison counits; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-varying-ring-cartesian-comparison-lift-relabelling: existing The cartesian open comparison on varying-ring systems relabels lifts; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-sp-varying-ring-open-unit-coherence: existing Exact localization and identity unit law for varying-ring open extension; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-trf-integral-pullback-reduction-counit: existing K-flat reduction-unit counit calculation for integral inverse image; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-trf-ringed-kflat-word-comparison-descent: existing Simultaneous K-flat word models and normalized comparison descent; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-trf-ringed-scalar-universal-resolution-comparison: existing Universal ring-sheaf scalar extension with normalized resolution comparisons; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-trf-topos-complement-module-stalks: existing Module support, adjunctions and stalks for complementary subtopoi; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-tw-finite-projective-model-pullback: existing Normalized finite-projective constant models under ordinary derived pullback; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-derived-scalar-extension-restriction-adjunction: existing Derived reduction modulo varpi^n is left adjoint to restriction of scalars; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-etale-native-tensor-pullback: existing Native unbounded derived tensor commutes with etale inverse image; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-affine-free-finite-stalk-generation: existing Finite affine free maps generating one module stalk; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-cochain-pullback-tensor-shift: existing The prescribed cochain pullback tensor comparison commutes with both signed shifts; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-common-quotient-insertion-composition: existing Composition normalization of scalar insertion; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-common-quotient-insertion-finite: existing Invertibility of common-quotient reduced insertion; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-common-quotient-insertion-identity: existing Identity normalization of scalar insertion; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-common-quotient-ordinary-insertion: existing Ordinary scalar insertion reduced to common quotients; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-completed-adic-koszul-kflat: existing K-flatness of the actual completed exterior Koszul complexes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-constant-coefficient-scalar-equivalence: existing Bijective constant scalar extension reflects finite lisse cohomology; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-constant-derived-normalization-universal: existing Constant derived realization preserves universal coefficient arrows; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-continuous-constructible-supported: existing Constructibility of supported continuous modules; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-continuous-extension-scalar-change: existing Ordinary scalar change commutes with continuous extension by zero; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-continuous-module-localization: existing Localization for the actual continuous module functors; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-derived-scalar-extension-local-systems: existing Coherent localized derived scalar extension and comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-diagram-kflat-replacements: existing Objectwise K-flat replacements in strict diagram categories; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-element-presheaf-extension: existing Direct-sum computation and left exactness of presheaf element extension; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-etale-graph-section-extension-map-linear: existing The presheaf map from the etale sum presheaf to direct image is linear over the constant sheaf of rings; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-extension-by-zero-adjunction: existing Extension by zero is left adjoint to restriction (étale site); new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-extension-by-zero-exact: existing Extension by zero is exact (étale site); new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-extension-by-zero-stalks: existing Geometric stalks of extension by zero along an open immersion; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-flat-coefficient-reduction-adjunct: existing Finite scalar comparison preserves derived reduction adjuncts; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-flat-common-quotient-reduction-tower: existing Derived common-quotient reduction as a normalized strict tower; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-flat-scalar-restriction-kflat: existing Flat scalar restriction preserves K-flat complexes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-free-etale-module-shriek-comparison: existing Free representable module sheaves are etale extensions by zero; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-free-sheaf-derived-sections: existing Free sheaf shifted Hom computes derived module global sections; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-free-sheaf-flat: existing The sheafified free presheaf on a representable with flat coefficients is flat (j_{X!} of a constant flat sheaf is flat); new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-free-yoneda-presheaf-module: existing Morphisms out of the free presheaf of modules on a representable are sections; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-integral-model-open-closed-pieces: existing Integral open and closed pieces remain constructible and rationalize to the localization sequence; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: existing Derived pullback computes K-flat tensor representatives; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-normalized-derived-isomorphism-section-reduction: existing Normalization-compatible evaluation of actual local Isom sheaves; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-normalized-derived-isomorphism-transport: existing Universal normalization and evaluation of source-site local Isom sheaves; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-normalized-origin-comparison-coherence: existing Comparison reduction respects canonical scalar units and composition; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-proetale-ringed-open-closed: existing Ringed pro-etale open-closed localization; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-pullback-resolving-computation: existing Derived pullback computes on resolving complexes with independent universes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-pulled-reduction-flat-model-formulas: existing Flat-term K-flat models and the specified pulled reduction maps; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-pulled-reduction-normalization-comparison: existing Successive quotient normalizations under the pulled reduction comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-reduction-pullback-derived-tower: existing Normalized derived pullback of a strict coefficient reduction tower; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-ringed-common-quotient-pullback-comparison: existing Common quotient reduction of the geometric scalar comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-ringed-pullback-preserves-kflat: existing Ringed pullback kflat; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-ringed-scalar-pullback-shift-normalization: existing Universal-counit normalization of the ringed scalar/pullback shift square; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-ringed-slice-extension-preserves-exact: existing Ringed-slice extension preserves exactness; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-ringed-topoi-derived-pullback: existing Derived pullback on ringed topoi computed by K-flat resolutions; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: existing Derived tensor comparison for arbitrary ringed topoi; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence: existing Canonical tensor comparison unit existence; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness: existing Canonical tensor comparison unit uniqueness; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-ringed-topos-acyclic-kflat-pullback: existing Ringed-topos pullback in the acyclic K-flat case; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-ringed-topos-kflat-pullback: existing Ringed-topos pullback preserves flat-term K-flat complexes; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-ringed-topos-pullback-adapted-flat-resolution: existing A flat resolution whose ringed-topos pullback is K-flat; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-scalar-extension-unit-triangles: existing Scalar-extension maps form morphisms of distinguished triangles; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-sheaf-free-separator: existing The coproduct of the sheafified free presheaves on representables with coefficients in a separator is a separator of the sheaf category; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-site-derived-tensor-descent: existing Derived tensor and K-flat representative descent on a ringed site; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-site-extension-by-zero-exact: existing Extension by zero on a localized site is exact; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-site-extension-by-zero-presheaf-adjoint: existing The sheafified direct-sum presheaf is left adjoint to restriction to a localized site; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-site-restriction-exact: existing Restriction to a localized site is exact; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-site-restriction-injectives: existing Extension by zero and restriction on a localized site; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-supplied-ringed-topos-kflat-pullback: existing Tensor pullback adjoint to a supplied ringed-topos module direct image; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-zariski-etale-pushed-resolution: existing Local vanishing gives the pushed injective-resolution augmentation as a quasi-isomorphism; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-zariski-etale-pushed-resolution-finite-limits: existing Finite-limit preservation for the pushed resolution; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-zariski-etale-pushed-resolution-quasi-iso: existing Quasi-isomorphism of the pushed resolution augmentation; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-zariski-extension-by-zero-adjunction: existing Extension by zero of abelian Zariski sheaves is a left adjoint of restriction to an open; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-pbc-zariski-extension-by-zero-exact: existing Extension by zero of abelian Zariski sheaves is exact; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-point-derived-sections-tensor-descent: existing Derived descent and K-flat normalization of the ordinary point sections-tensor comparison; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-point-derived-tensor-tower-coherence: existing Ordinary derived scalar associators and point sections-tensor tower coherence; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs lem-weil-sections-scalar-derived-transport: existing Counit-normalized derived transport of coherent exact scalar comparisons; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs new-lem-amb-closed-support-hom-sequence: existing Underived closed-support Hom sequence on injective sheaves; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs new-lem-sc-nested-slice-extension-stalks: existing Nested slice extension stalk maps; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs new-localized-restriction-extension-exists-universes: existing Exact extension adjoint for localized restriction with independent coefficient universe; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs new-open-embedding-sheaf-pullback-adjunction: existing Extension by zero adjunction for open embeddings; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs new-open-embedding-sheaf-pullback-preserves-monomorphisms: existing Open embedding sheaf pullback preserves monomorphisms; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs new-over-pullback-adjunction-mono: existing Extension by zero adjunction preserving monomorphisms; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-space-etale-sum-pullback vs new-over-pullback-preserves-injectives: existing Restriction to a slice Grothendieck site preserves injective abelian sheaves; new arbitrary structural-ring pullback of etale sum extension, with evaluation/overlap counits and K-flat preservation is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs def-coef-reduction-limit-shift-data: existing Normalized coefficient reduction and total-limit shift data; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs def-sfb-identity-open-pullback-comparison: existing Specified identity-open inverse pullback compositor; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs def-trf-coefficient-tower-operations: existing Coefficient tower operations and point sections; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs def-trf-completion-unit-models: existing Ordinary quotient adjunction and normalized derived completion models; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs def-trf-point-reduction-units: existing Canonical scalar-extension units and exact restriction/sections identity at a point; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-asd-derived-counit-k-injective-termwise: existing Derived counit on a K-injective representative; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-cbc-cochain-augmentation-descent: existing Descent of an augmentation through its universal cochain counit; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-cbc-cochain-derived-adjunction: existing Normalized derived adjunction for a specified cochain left derived pair; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-coef-derived-tower-counit-projections: existing Derived constant/limit adjunction with its actual projection counit; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-coef-dg-derived-quillen-calculus: existing Enhanced derived adjunction and monoidal Quillen calculus; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-kun-derived-adjoint-square-comparison: existing Canonical right-derived comparison respects an exact adjoint square; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pc-cone-short-exact-quasi-iso: existing The canonical cone projection of a short exact sequence is a quasi-isomorphism; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pc-derived-adjoint-functors: existing Derived functors of adjoint functors are adjoint; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pc-derived-adjunction-normalization-unique: existing Uniqueness of an adjunction with a fixed representative Hom formula; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pc-derived-base-change-unit-compatibility: existing Derived mate compatibility with the right-derived unit; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pc-derived-functor-termwise-split-ses-triangle: existing Right derived functors identify triangles of termwise split K-injective sequences; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pc-original-counit-adjunction-transport: existing Original-counit transport of the normalized scheme pullback adjunction; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pd-section-derived-pushpull-normalization: existing Section equivalence and canonical derived push-pull adjunctions; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-adjunction-evaluation-composition: existing Evaluation and composition of normalized adjunction mates; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-adjunction-mate-transpose: existing Transpose formula for a general mate square; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-adjunction-transition-coherence: existing Transition coherence for evaluation mates; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-cochain-adjunction-compatibility: existing Normalized derived Hom formulas on cochain complexes; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-cochain-homotopy-derived-comparison: existing Comparison through the homotopy quotient; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-comparison-unit-injective-model: existing Injective-resolution representative of the derived etale/pro-etale comparison unit; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-derived-mate-comparison: existing Cochain representative formula for normalized derived mates; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-evaluation-transition-mate: existing Iterated Hom formula for the transition mate; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-exact-restriction-composition: existing Exact restriction compositors and their localization formulas; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-extension-evaluation-comparison: existing Evaluation comparison for derived left extensions; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-global-hom-evaluation-model: existing A-linear evaluation-normalized global derived Hom model; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-normalized-adjunction-composition: existing Composition and uniqueness of normalized adjunction formulas; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-normalized-left-extension: existing Normalized left extension from a resolving class; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-resolving-class-derived-adjunction: existing Normalized derived adjunction from a resolving class; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-sequence-projection-hom-normalization: existing Sequence projection and normalized whole-system Hom correspondence; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-sheaf-ring-derived-coefficient-adjunction: existing Derived change of rings along a map of ring sheaves is left adjoint to restriction of scalars, with normalized unit and transposes; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-sheaf-ring-derived-hom-comparison: existing Compatibility of the derived scalar-extension adjunction with homotopy Hom representatives; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-derived-subsequence: existing Canonical exact derived subsequence comparisons; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-derived-subsequence-evaluation-composition: existing Subsequence evaluation respects restriction composition; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-derived-subsequence-transition: existing Subsequence evaluation respects derived transitions; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-derived-transition: existing Localization of actual semilinear transitions; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-derived-transition-coherence: existing Derived semilinear transitions compose; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-derived-transition-unit: existing Identity transitions and the canonical derived tensor unit; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-scalar-derived-extension: existing A scalar model as normalized derived extension data; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-selected-derived-composition: existing Canonical composition of derived subsequence extensions; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-selected-derived-composition-evaluation: existing Evaluation of the derived subsequence compositor; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-selected-derived-evaluation: existing Derived evaluation of the subsequence left extension; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-selected-derived-evaluation-index: existing Reindexing the selected derived evaluation comparison; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-selected-derived-extension: existing Deriving the ordinary subsequence extension; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-selected-derived-transition: existing The specified tensor-adjoint selected derived transition; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-single-derived-evaluation: existing Derived singleton evaluation below and above the input level; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-system-single-derived-extension: existing Deriving the ordinary singleton extension; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-pur-unbounded-derived-boundary: existing Unique normalized unbounded derived boundary; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sc-p1-injective-ses-homotopy-boundary-lift: existing Simultaneous homotopy lift of injective SES boundaries; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sc-p1-split-ses-boundary-comparison: existing Comparing cone and degreewise split boundaries; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sc-p1-split-ses-cocycle-boundary: existing Split boundary on a cocycle with an arbitrary lift; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sc-sheaf-algebra-derived-hom-adjunction: existing The constructed algebra-valued derived Hom adjunction; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sc-sheaf-algebra-derived-hom-adjunction-map: existing Derived scalar restriction mapDerivedCategory adjunction; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sf-ambient-adjunction-compositor-normalization: existing Adjunction and resolution normalization of ambient direct-image and open compositors; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sf-completed-augmentation-adjunct: existing The specified completed augmentation is the normalized derived adjunct; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sf-derived-ses-triangle: existing A short exact sequence gives a distinguished triangle in the derived category; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sf-exact-localization-derived-triangle: existing Natural derived triangle of an exact localization sequence; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sf-exact-tower-augmented-counit-evaluation: existing Normalized exact tower augmentation and coherent counit evaluation; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sf-ringed-restriction-exchange-open-descent: existing Normalized ringed restriction exchange and open descent; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sf-triangulated-right-adjoint: existing A shift-compatible right adjoint of a triangulated functor is triangulated; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-cech-augmentation-normalized-naturality: existing Counit normalization and resolution/refinement naturality of the Cech augmentation; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-closed-test-chain-mate-restriction: existing Closed-test chain mate and the normalized derived restriction; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-closed-test-scalar-model-coherence: existing Universal coefficient comparison for closed-test models; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-continuous-qbar-normalized-sheaf-filtration: existing Normalized lisse quotient filtration for continuous algebraic-closure module sheaves; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-derived-cokernel-adjoint-exchange: existing Exact exchange for derived cokernel adjunctions; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-derived-composition-adjunction-normalization: existing Derived composition preserves the specified adjunction normalization; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-derived-section-scalar-transport: existing Localization transport of the normalized scalar adjunction; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-hypercover-derived-unit-chain-squares: existing Derived-unit representatives and cross-site hypercover chain squares; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-identity-open-derived-adjunction-normalization: existing K-injective normalization and derived adjunction at an identity open locus; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-integral-quotient-section-mate-realization: existing Integral quotient scalar and geometric mate realization in section modules; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-normalized-scalar-boundary-naturality: existing Naturality of normalized scalar reduction boundaries; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-reduction-single-cohomology-normalization: existing Cohomology of scalar reduction and signed single-sheaf identifications; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-resolving-derived-adjunction-normalization: existing Derived adjunction normalized by a left resolving class and K-injectives; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-ringed-projection-first-shift: existing The ringed projection mate commutes with shifts in its direct-image input; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-scalar-adjunction-unit-coefficient-normalization: existing Normalized scalar adjunction on K-flat models and the coefficient unit; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-scalar-reduction-unit-triangle: existing Scalar-reduction adjunction unit and multiplication triangle; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sfb-topos-finite-free-counit-comparison: existing Finite-free counit comparison on arbitrary sheaf topoi in specified coordinates; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sp-canonical-right-derived-adjunction-shift: existing Canonical unbounded right-derived adjunctions commute with canonical shifts; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sp-finite-free-scalar-shift: existing The normalized scalar counit commutes with shifts and scalar extension is triangulated; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-sp-subterminal-derived-image-calculus: existing K-injective derived direct-image comparisons for subterminal slices; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-trf-completion-unit-canonical-models: existing Compatible ordinary and derived presentations of the coefficient adjunction; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-trf-continuous-cocontinuous-derived-shriek: existing Unbounded derived lower shriek for continuous and cocontinuous site functors; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-trf-exact-bar-cone-boundaries: existing Exact bar resolutions and cone connecting maps; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-trf-finite-structural-maps-commshift: existing Canonical finite-coefficient structural maps commute with shifts; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-trf-point-reduction-unit-normalization: existing Point coefficient-reduction comparisons are normalized by scalar-extension units; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-adjunction-shift-compatibility-unique: existing Shift isomorphisms compatible with an adjunction: counit from unit, and uniqueness on the right adjoint; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-adjunction-square-shift-mate: existing Shift compatibility passes to the adjunction mate of a square; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-complex-ses-triangle: existing A short exact sequence of complexes gives a distinguished triangle in D(A), functorially; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-derived-adjunction-commshift: existing The unit and counit of the derived adjunction u^{-1} -| Ru_* commute with the shift isomorphisms; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-derived-adjunction-shift: existing Canonical derived ringed-topos adjunction is shift-compatible; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-derived-exchange-triangulated: existing The derived exchange transformation commutes with shifts and maps triangles to morphisms of triangles; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-derived-module-scalar-adjunction: existing Derived scalar restriction for ordinary modules has a left adjoint; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-etale-lisse-filtration-devissage: existing Finite-filtration devissage through a triangulated derived functor; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-exact-functor-ses-triangle-image: existing An exact functor carries the triangle of a short exact sequence to the triangle of the image sequence; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-exact-square-derived-counit: existing Counits in an exact square from normalization on K-injectives; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-formal-exact-projection-mate: existing Formal exact projection mate for specified shift and unit data; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-raw-restricted-resolution-class: existing Raw resolution evaluation has the canonical cocycle class; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-raw-restricted-resolution-naturality: existing Raw evaluation is natural on a prescribed injective resolution; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-raw-restricted-resolution-restriction: existing Etale cohomology pullback on a chosen resolution; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs lem-weil-pbc-ringed-derived-adjunction-independent-universes: existing Derived module inverse image is left adjoint to a supplied derived direct image; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs new-derived-adjunction-compatibility: existing Compatibility of the derived adjunction; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs new-everywhere-defined-derived-functors: existing Everywhere-defined derived functors; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

lem-sfb-derived-adjoint-ses-mates vs prop-weil-pbc-derived-inverse-image-adjunction: existing Derived adjunction of inverse and direct image on D^+; new right-adjoint SES boundary comparison induced by a whole left resolution diagram is additional and not asserted by that statement.

