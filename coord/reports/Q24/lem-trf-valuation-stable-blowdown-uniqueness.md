## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-stable-blowdown-uniqueness.json`: statement corrected as explained below; six-step proof of partial-sequence factorization and unique terminal quotient, status split. No Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-exceptional-contraction-diamond.json`: statement-only, unsplit local geometric lemma about one contraction's structural properties and the commuting square for two distinct exceptional components. No Mathlib match.
- `citations.json`: verbatim extracts from each statement used in each numbered proof step.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` for the exact blueprint tag, blowdown/blow-down and exceptional-component/stable-modification notions. There is no declaration for the item or the new diamond. The wider contraction search found abelian-variety rigidity and unrelated topology/category-theory code, which do not state the curve lemma. The upstream master search likewise found no relevant declaration; upstream sorries were not treated as proofs. No Lean was written or compiled.

## Wanted literature

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, Appendix B, printed pp. 57–58, for both lem-trf-valuation-stable-blowdown-uniqueness and lem-trf-exceptional-contraction-diamond. No local archival PDF was found in the named literature directory. I read the primary PDF online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, especially the paragraph immediately preceding Lemma B.3, B.3 and its proof, and the following absolute-stabilization proviso. No document was downloaded into the shared repository. The induction and the precise local diamond formulation are agent-written; the item's proof_origin says agent.

## Statement corrected

STATEMENT-DISPUTED: the imported lemma with an arbitrary reference map is false. Let P be the unmarked nodal two-gon A union B, two copies of P^1_k meeting transversely at two distinct points, and take C=Spec k and r constant. Both components are exceptional: each has exactly two singular points and is mapped to a point. Collapsing A is the scheme pushout that identifies the two attaching points of B, yielding an irreducible nodal rational curve S_A. This is a semistable curve and has no exceptional component as defined in the item: its only irreducible component is a nodal curve, not a smooth projective line. Collapsing B similarly gives S_B. With pi the first collapse and q the second, pi is nonconstant on B but every composite u q is constant on B. Thus the asserted factorization does not exist. Both sequences have length one and their marking conditions are vacuous. The assumption that a terminal quotient exists as a curve does not remove this example.

Correction: require that the image of every connected component of P under r contain more than one point. This restores the relevant relative condition of Temkin's setup preceding B.3: there the reference map is a proper surjective map between connected curves, so it cannot collapse its whole source. It is the minimal geometric restriction used by the local argument; connectedness, properness over k, and separatedness of the structure maps are still unnecessary. The correction changes no target statement. The original statement and the reason are also retained in split_report.statement_correction for review.

The unique current direct citer is lem-trf-valuation-contracted-component-inclusion. Its Step 3 applies the old lemma with r=f_Omega a_Omega but does not explicitly establish the newly restored noncollapse condition. That caller therefore needs an applicability audit/repair by its owner; it is not edited here. The assertion that its fibre contractions are supplied does not by itself justify the missing hypothesis on their composite reference map. This is an explicit downstream issue, not an assertion that the old application already checks.

## Proof and blueprint audit

The project chapter and unit were read: sec-trace-formula and sk-i-curve-zero. This is an auxiliary node in the recorded stable-modification ancestry of lem-trf-local-term-locality, not a key node of its unit, so no unit realization file was changed. I read the ancestor's blueprint_update for main-20261015: it now proves contracting local terms via Varshavsky's deformation argument. The older semistable-modification branch is historical ancestry retained by the repository. I preserve that ancestry and supply the requested independent Appendix B input; I do not claim the current blueprint_update explicitly contains the old valuation argument, or change the chapter/unit bindings.

The item's actual argument is strong induction on the length n of the given terminal sequence. The induction proves more than existence of a factor map: after any first contraction the remaining factor is itself a sequence of n-1 contractions to the same terminal quotient. This stronger claim is essential to handle subsequent contractions. The distinct-first-component case uses a two-step local diamond, applies induction to the other component after the terminal sequence's first contraction, and reorders that diamond. This is a genuine split: the new lemma handles only two simultaneous local choices, while all sequence-length induction, iteration through an arbitrary q, cancellation and unique-isomorphism arguments remain in the item. There is no new node restating the item's factorization or uniqueness clause.

## Not duplicates

lem-trf-exceptional-contraction-diamond vs lem-trf-valuation-stable-blowdown-uniqueness: the new lemma is a local two-component diamond with structural permanence; the item concerns arbitrary finite sequences to a terminal quotient and contains the induction and uniqueness proof.

lem-trf-exceptional-contraction-diamond vs lem-trf-nodal-exceptional-component-pushout: that existing node supplies one contraction under a proper surjective map to a semistable target with connected fibres and a common dense open. It does not assert the diamond for two supplied contractions over an arbitrary reference scheme; those stronger target hypotheses are unavailable here. Its statement was opened and was not used beyond its actual scope.

lem-trf-exceptional-contraction-diamond vs lem-trf-semistable-modification-fibre-contractions: the latter obtains a finite contraction sequence from a family eta-modification. It gives no commuting square for two different first components or noncollapse permanence for an arbitrary reference map.

lem-trf-exceptional-contraction-diamond vs lem-trf-valuation-contracted-component-inclusion: the latter is a family-level conclusion using the item, not the local diamond; citing it would be circular.

Whole-DAG keyword searches included exceptional components, B.3, blowdown, local diamonds and confluence; I then searched statements to discard the many unrelated exceptional-functor hits. Whole-blueprint searches using tools/blueprint_refs.py for “blowdown”, “exceptional component”, “stable blow”, “exceptional trees”, and “contraction diamond” found no matching blueprint statement. The ancestor command identifies lem-trf-local-term-locality, which is the new node's from.node, and its via list prepends this item. The new id did not exist in the DAG. There is no Stacks-tag duplicate pair: the substantive geometric source is Temkin B.3, not an invented Stacks identification.

The first delivery dry run classified the arXiv number 0707 in the shared PDF filename as a Stacks tag. I opened every listed node; the following comparisons address every reported pair without altering source filenames or the checker.

lem-trf-exceptional-contraction-diamond vs def-trf-birational-quasi-modification: defines a separated generically birational morphism with integral source and reduced target; it states no existence or commutation result for curve contractions.

lem-trf-exceptional-contraction-diamond vs def-trf-centred-valuation: defines a Spec V map with a specified generic centre; it states no exceptional-component contraction fact.

lem-trf-exceptional-contraction-diamond vs def-trf-local-marking-length: defines a local vector-space dimension of marking stalks; it states no contraction or diamond theorem.

lem-trf-exceptional-contraction-diamond vs def-trf-modification: defines a proper morphism with a schematically dense isomorphism open and its generic base-change variant; it states no order-independence or two-component pushout theorem.

lem-trf-exceptional-contraction-diamond vs def-trf-multipointed-curve-modification: defines morphisms of pairs, semistability, eta-modifications and the exceptional-component stability predicate; it supplies the terminology, not the diamond conclusion.

lem-trf-exceptional-contraction-diamond vs def-trf-multipointed-curve: defines the flat finitely presented curve and marking data; it contains no contraction construction or comparison theorem.

lem-trf-exceptional-contraction-diamond vs def-trf-multipointed-eta-modification: defines the proper curve/marking maps and their specified base-change isomorphisms; it contains no two-component local comparison.

lem-trf-exceptional-contraction-diamond vs def-trf-nodal-dualizing-datum: defines regular presentations and normalized dualizing/fundamental-class data; it contains no blowdown or commuting pushout statement.

lem-trf-exceptional-contraction-diamond vs def-trf-projective-line-tree: defines the reduced connected nodal finite incidence-tree predicate; it asserts neither existence of contractions nor a diamond for two supplied contractions.

lem-trf-exceptional-contraction-diamond vs def-trf-rational-rank: defines the rational rank of an abelian group; it is unrelated to nodal-curve contractions.

lem-trf-exceptional-contraction-diamond vs def-trf-schematically-dense-open: defines injectivity of restriction to an open on all structure-sheaf sections; it contains no statement about exceptional components or pushout comparison.

## Mathlib searches

Every new record is from msearch.py and is present in searches.jsonl. I read the returned signatures, including generic valuative criteria, Spec-point extensionality, normalization/coproduct composition identities, Weierstrass minimal-model or variable-change statements, and Matroid.contract_comm. The matroid declaration is about matroids, not nodal schemes; no specialization supplies a scheme pushout or a semistable marked quotient. The second semantic phrasing searches commutation of elementary exceptional P1 contractions and again finds no curve theorem. Loogle for the name fragment “blowdown” has no hits. Source grep in Mathlib/AlgebraicGeometry for exceptional-component, curve-contraction and semistable patterns has no hits. The initial Loogle query with Scheme.Hom returned an unknown-identifier diagnostic, which is recorded as such, not presented as positive evidence. The valid fragment query and both semantic services supplement it. No unavailable service was recorded as no-match.

## Review by Q24

I opened the item, its parent application, the one-component pushout node, the curve and modification definitions, the projective-line chart definition, the affine-spectrum definition and the categorical-colimit definition. I also read Temkin's Appendix B primary text, including the standing relative-map hypotheses before B.3 rather than just its one-line uniqueness statement. For the new lemma, B.3 is motivation and its elementary contraction paragraph supplies the local model; I do not mislabel the precise diamond as a verbatim theorem of Temkin. I tested and corrected the item's false unrestricted version before splitting it.

Step 1 uses exactly def-weil-pbc-category-colimit's unique mediator for compatible cocones, def-sc-p1-standard's affine chart Spec k[t], and def-weil-affine-spectrum's contravariance from k[t] to k. The t=0 point supplies a section of A to Spec k, so agreement on P forces agreement on the second pushout vertex. This proves scheme-morphism cancellation, not merely surjectivity on point sets. The marking map is an isomorphism by the elementary-contraction hypothesis, so the marking component cancels as well. Same-component quotient isomorphisms are the ordinary universal-property calculation. The quotes in citations.json are the actual parts these three definitions state.

Step 2 uses the new local lemma's explicit assertion that the induced reference map has nonpoint image on every connected component. It also uses the colimit definition only to transport a pushout by an isomorphism. I stated the induction invariant including the remaining sequence length, its semistable source, the induced map to C and the same terminal quotient. None of these is borrowed from an uncited proof of another node.

Step 3 is the base case and the same-first-component case of that induction. The source is terminal when n=0, so a first contraction cannot exist. When the first component agrees, the pushout definition and Step 1 supply the quotient isomorphism; composing the given remainder is a length n-1 sequence. No new geometric fact is hidden in “same component”.

Step 4 takes exactly the two elementary arrows j_A and j_B and their equality on P from the new node's statement; its citation quotes both permanence and the diamond. The induction is applied at the smaller length n-1. If n=1 the existence of j_A contradicts the base case, so no negative sequence length is ever used; otherwise w has length n-2 and v=w j_B has length n-1. I checked that the new arrows are pointed maps over C, that their intermediate curve is semistable, and that the first quotient has the noncollapse property needed for induction.

Step 5 repeats the proved single-step assertion, keeping the specified h_i and factoring the specified pi at each stage. It accounts explicitly for q's final isomorphism by composing with e^{-1}; this was not suppressed as a change of representative. Length zero prevents any attempted (n+1)-st contraction. Step 6 uses the cancellation already proved in Step 1, not the false assertion that a surjective scheme map is always an epimorphism. The composites of the two factor maps cancel against their supplied terminal quotients, giving inverse isomorphisms and uniqueness.

For the new local statement I checked the hypotheses against the nodal geometry rather than treating two exceptional components as disjoint. Two different P1 components meet in at most two nodes because each has at most two special points. If they meet twice, their union has no other boundary or marking and is a whole connected component mapped to one point, excluded by the corrected hypothesis. If they meet once, contracting one leaves the other an embedded P1: a second attaching node replaces the old node by its other branch; a lone marked tail moves its sole mark to the attaching point; an unmarked tail removes that node. These cases never increase the other component's special-point count. If they are disjoint, the contractions have disjoint supports. Existence and scheme-level compatibility of the second pushouts, and the one-contraction structural properties, are genuinely geometric content left in the new unsplit lemma; they are not marked elementary in the item. Pushout associativity determines the common double quotient once these local constructions are made. This explains why the node is needed and is smaller than sequence confluence.

Small cases checked: empty marking; disjoint exceptional tails; adjacent components of a chain with a noncontracted component outside it; a one-marked tail; a rational bridge attaching twice to the same nonexceptional component; two adjacent bridges in a cycle of length at least three with a nonconstant reference component; zero-length pi and zero-length q; disconnected source; and the excluded constant two-gon. A bridge may create a self-node on a surviving nonexceptional component, so I did not assume all surviving components globally stay smooth. Only the particular other exceptional component in the diamond is asserted to stay P1; the twice-intersecting two-gon would violate this and is excluded. A finite contraction cannot merge distinct connected components; its proper surjective connected-fibre map gives the permanence assertion in the new node. No genus equality, normality of the reference scheme, source properness over k or nonexistent dense open in a geometric fibre is introduced.

I checked delivery-errors B–E: the one new node is self-contained, statement-only, unsplit, has actual logged searches, genuine blueprint ancestry and single TeX escapes; all uses in the item have verbatim statement quotes; no proof-only construction from a cited node is used; the proof contains the induction instead of moving the item to a new node; and the two-gon counterexample triggered an explicit statement correction and downstream warning. All six proof steps are below 2000 characters. No off-unit statement tool is used: the geometric lemma inherits the item's unit, and the other cited nodes are definitions.

## What remains unfinished

The delivered item has a complete natural-language proof conditional on its one newly stated local geometric lemma, as required for a one-level split. That lemma is deliberately unsplit and joins the stage-1 queue. The existing caller's newly missing noncollapse verification is reported above for maintenance; it is outside this item's authorized files. No other proof work is claimed. The preliminary server review_split check passed; the initial dry run requested the additional source-pair distinctions now recorded under Not duplicates.
