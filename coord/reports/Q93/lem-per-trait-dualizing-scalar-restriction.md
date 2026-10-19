# Stage-1 delivery: lem-per-trait-dualizing-scalar-restriction

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-trait-dualizing-scalar-restriction.json: statement, split into five proof steps; statement unchanged; removed the unused proper-morphism statement dependency.
- dag/nodes/sec-deligne-laumon-a1/lem-per-complete-trait-constructible-biduality.json: new statement-only theorem, unsplit, no Mathlib match.
- citations.json: verbatim statements for all 18 step citations.

The remaining sandbox files are research aids, not proposed repository changes. There is one new node and zero Mathlib leaves.

## Attachments

None. Searched the slopmaster2 WeilConjectures tree for the item id, relative-dualizing/scalar terminology and biduality. Read SixFunctors/Etale/Derived/Dualizing.lean: its constructible preservation and double-dual theorems are field-base statements with sorry, not the present trait-base assertion. The upstream master is reference material, not evidence of a finished proof. No Lean files were written and no compiler was run.

## WANTED

None for the documents used in this split. The ILO volume and Stacks sources are present. The new theorem is the local-biduality input *invoked*, not proved, in ILO XVI Lemma 3.5.9. It remains explicitly unsplit; this delivery does not claim that the ILO paragraph supplies a proof of that whole theorem. Its eventual split must give an independent trait-duality proof, not feed the absolute-purity result back into this argument.

## What was wrong or changed

The imported item was unsplit, but its statement is correct with its stated nonempty-open and integral hypotheses. There is no STATEMENT-DISPUTED and no change to its mathematical statement. Its unused def-weil-proper-morphism edge was removed: the map p_T is quasi-projective, not assumed proper.

The parent proper-degree descent uses this item before proving purity of the target. The tempting existing potential-dualizing route would be circular: regular-unit pinnings use absolute purity, which uses the present proper-degree descent. Instead the new node records the general constructible local-biduality theorem over the complete trait, the input the source actually invokes at XVI p.250. Its conclusion concerns every bounded constructible complex, including on singular X; it does not assert scalar endomorphisms or restriction detection. The item's steps derive those assertions by evaluation, twist cancellation and connected sections.

The chapter and unit records were read and left unchanged. blueprint_refs.py ancestor returned lem-per-artin-gabber-affine-curve; its current proof Step 1 supplies dimension-normalized duality. Filled the precise from.place and retained the inherited ancestry. Whole-blueprint searches for dualizing, scalar, biduality/bidual, local biduality, trait/trait biduality and relative dualizing complex found no trait-based general biduality theorem to reuse. DAG searches by these notions and the source place were also inspected. General tools outside the unit are declared in split_report.tool_uses for maintainer review, without setting tool_uses ourselves.

## Not duplicates

lem-per-complete-trait-constructible-biduality vs lem-per-trait-dualizing-scalar-restriction: the new theorem is constructible biduality for arbitrary quasi-projective X over the trait and arbitrary M in D^b_c, including singular X. The item computes two global endomorphism rings for a regular integral T and proves their restriction map is the identity. Those consequences are proved in the item, not restated in the child.

lem-per-complete-trait-constructible-biduality vs lem-per-potential-local-duality: the latter starts with a pinned potential complex on an excellent scheme. It does not identify the actual ambient p^!A_S without regular pinnings; supplying those through absolute purity here is circular. The new node is specifically the independent relative trait-duality theorem.

lem-per-complete-trait-constructible-biduality vs lem-per-gabber-local-duality-general: the existing theorem likewise assumes a pinned potential dualizing complex. The new theorem supplies duality for p^!A_S without that input or a purity hypothesis.

lem-per-complete-trait-constructible-biduality vs thm-fix-general-biduality: the existing statement assumes a scheme over the fixed algebraic closure of a finite field, not a mixed-characteristic trait.

lem-per-complete-trait-constructible-biduality vs thm-weil-etale-geometric-biduality: the existing theorem has the fixed finite-field geometric base; it cannot be specialized to S.

lem-per-complete-trait-constructible-biduality vs lem-per-potential-scalar-rigidity: the existing result assumes potential pinnings and gives truncated internal scalar endomorphisms. It is neither the independent trait-duality input nor a way to establish those pinnings before purity.

## Mathlib searches

Read every result of the msearch.py calls recorded in searches.jsonl. Ran LeanFinder, Loogle, LeanSearch and Mathlib grep, then a second natural-language phrasing and a second name/grep search. All services ran. The exact query texts and result names/digests are recorded in the item and child; none was invented. Searches for dualizing and bidual returned no Loogle matches; the AlgebraicGeometry grep for Verdier/bidual/dualizingComplex found none. Semantic hits concerned formally etale algebras, condensed modules, matroid/order duality or fractional ideals. None states ordinary etale trait biduality or scalar endomorphisms of its relative dualizing object. Existing historical searches in the item were preserved.

## Review by Q93

I read ILO Expose XVI section 3.5, especially Definition 3.5.4 and Lemmas 3.5.8--3.5.10 on printed pp.248--250. The relevant order is important: Lemma 3.5.9 invokes local biduality for K_Y before Proposition 3.5.7 has established punctual purity of Y. I also inspected the later ILO XVII potential-dualizing statements to check that their stronger generality is not an independent input at this point. The new node isolates the source's general local-biduality input for the complete mixed-characteristic traits of section 3.7. It is a real theorem awaiting a split, with its coefficients, base, actual exceptional functor, evaluation map and constructibility hypotheses stated independently; it contains no proof sketch or proof dependencies.

For Step 1 I opened the new biduality statement, def-weil-pbc-constructible-complexes and lem-sf-ringed-derived-closed-symmetric-monoidal. The first really asserts canonical evaluation-transpose biduality for M=A_T, rather than merely the existence of an object isomorphism. The constant finite module has the required single constructible stratum. The closed tensor-Hom adjunction identifies Hom(A_T,Q) with Q and its evaluation with q tensor a mapping to aq; writing this identifies the biduality map with the scalar map. This corrects the possible gap of using an unspecified equivalence to identify scalars.

For Step 2 I read lem-asd-etale-finite-twist-pullback, which includes negative twists, rank-one local freeness, evaluation compatibility and shifts, not just nonnegative twists. I checked tensor cancellation against the closed symmetric-monoidal statement. The written Hom bijection has inverse tensoring by the dual line and opposite shift. I added the existing lem-galois-yoneda-fully-faithful after noticing that the passage from this natural Hom isomorphism to an object isomorphism needed a citation. This uses exactly full faithfulness on two representables; it does not ask that node for the more general Yoneda evaluation formula with an arbitrary presheaf. Tensoring scalar multiples of the identity preserves the same scalar. The normalization shifts are even, so no sign ambiguity is being suppressed.

For Step 3 I opened the open-is-etale, small-etale-slice and exact internal-Hom restriction statements. The first makes U an object of the correct site, the second identifies the slice with U_et, and the third gives the actual RHom comparison with no perfectness or constructibility hypotheses. I checked Stacks sites-cohomology.tex Tag 08JB (lemma-restriction-RHom-to-U). Thus the argument restricts on T, not by an unwarranted exceptional base-change theorem over S. The twist comparison respects restriction and coefficient evaluation.

For Step 4 I opened lem-pur-rhom-global-sections and the Grothendieck, enough-injectives, degree-zero-resolution and bounded-below-K-injective statements. The global-Hom statement is exactly the Hom group used here. I read Stacks Tag 08JA (lemma-section-RHom-over-U), including its proof with a K-flat source and K-injective target; the degree-zero computation uses Tags 013K, 05TD and 070J as recorded. No assertion that global sections is exact is used: it is only left exact, and the resolution begins in degree zero. The scalar map itself induces the comparison, which is why the resulting bijection is a ring isomorphism. D^+ is a full subcategory of the ambient derived category, as the derived-category definition states.

For Step 5 I opened def-pc-integral-scheme and lem-weil-pbc-constant-module-locally-constant, and read Stacks Tag 03P5 (remark-constant-locally-constant-maps). The module theorem, unlike several finite-field-only constant-H0 siblings, applies to arbitrary schemes and supplies naturality in restrictions. The proof writes out why U is irreducible and why a locally constant function on a nonempty connected space has one value. Finally restriction carries a times identity to a times identity, which proves the required identity square without relying on arbitrary choices of endomorphism-ring identifications.

I checked B--E against the final files: the new node is self-contained and statement-only; its notions are defined or linked; TeX has single backslashes; all searches actually ran; the new input is not one of the two scalar conclusions; every substantive operation in each step is a cited statement, with verbatim quotes in citations.json. No source of the prohibited route is cited. No new node for tensor cancellation, connectedness or degree-zero bookkeeping was introduced: those arguments are written in the item from the cited general statements. Every non-elementary step is shorter than 2000 characters. No chapter or unit record was changed.

Small cases checked: X=S gives Q=A_S in the new theorem; X the closed point gives Q=A(-1)[-2], whose biduality still returns a finite complex. The item for T=S has e_T=0; for T the closed point e_T=-1, and normalization cancels the shift and twist. Negative as well as positive e_T is covered by the signed-twist theorem. A disconnected T would have a product of scalar rings; an empty U would have a zero endomorphism ring. These show why the actual integral and nonempty hypotheses are retained. Singular X is allowed only in the general new biduality input, not silently substituted into the item's regularity convention.

## Unfinished work

None within the one-level split. The new constructible-trait-biduality theorem is intentionally unsplit, as required for new children. It is not marked proved, attached or Mathlib. Validation and direct delivery use the prescribed remote checks.
