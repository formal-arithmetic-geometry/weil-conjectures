# Q82 stage-1 report

Item: lem-sf-perfect-dual-pair-and-tate-stability. This is direct delivery by the dispatched worker, with self-review; no second worker was started. Only stage 1 was performed. The repository and Lean library were read only, and no compiler or build was run.

## Files written

- dag/nodes/sec-six-functors/lem-sf-perfect-dual-pair-and-tate-stability.json: statement; split into eight proof steps. The imported statement is unchanged.
- dag/nodes/sec-six-functors/lem-sf-exact-pairing-tensor.json: statement; Mathlib leaf, CategoryTheory.ExactPairing.tensor, Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean:140, with defining map formulas at lines 225 and 230.
- dag/nodes/sec-six-functors/lem-sf-exact-pairing-symmetric-swap.json: statement; Mathlib leaf, CategoryTheory.BraidedCategory.exactPairing_swap, Mathlib/CategoryTheory/Monoidal/Rigid/Braided.lean:81, with defining maps at lines 82 and 83. Symmetry identifies its inverse braiding with the symmetry used in the statement.
- citations.json contains a verbatim statement quotation for every node cited by each numbered proof step. searches.jsonl retains the actual msearch results. report.md records this review. write_split.py is the sandbox construction script, not a project file.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag and the perfect-dual, exact-pairing, biduality and Tate notions found no declaration proving the complete item. In particular the existing finite étale coefficient-dual declarations cover neither all four coefficient stages nor all the specified canonical maps. Generic project and Mathlib closed-category results are useful ingredients, not an attachment of this item.

## Literature wanted

None.

## Problems found and changes made

The blueprint's final sentence asserts perfect coefficient duals and biduality without supplying the canonical-map argument or the shifted inverse-line calculation. The split now identifies any specified dual pair with the actual internal-Hom dual by counit-compatible uniqueness of right adjoints. It proves invertibility of the transpose defining j_P before computing its explicit inverse. The line argument separately checks finite, completed, raw rational and common-stage categories; it does not replace the completed tensor by ordinary tensor without a comparison.

The two new facts are generic exact-pairing facts, not restatements of geometric clauses of the item. Both are already in Mathlib, so neither receives a further proof or an unsplit obligation. Off-unit theorems are declared as tool uses in split_report. No purity argument or SGA source was introduced.

I retained the searches recorded in searches.jsonl and read their hits. Natural-language searches for tensor duals returned tensor-Hom adjunctions and linear-algebra comparisons; the qualified-name Loogle search and source grep located ExactPairing.tensor and both defining-map lemmas. The symmetric-swap searches directly located exactPairing_swap. An unqualified Loogle name failed to parse and was followed by the qualified name. A file-targeted grep result did not supply usable line attribution, so the directory-targeted grep supplied the checked file and lines. These are actual recorded searches, not reconstructed queries. The item retains its earlier search metadata as well as the Q82 searches. No service failure is represented as evidence of absence.

## Unfinished work

No mathematical obligation of the split is left unaccounted for. New nodes are Mathlib leaves. Formal Lean implementation remains a later stage.

## Not duplicates

lem-sf-exact-pairing-tensor vs lem-sfb-dual-tensor-adjunctions: the existing statement constructs tensor adjunctions from one dual pair; the new leaf constructs an exact pair for the tensor of two pairs, with reversed dual factors and both maps.

lem-sf-exact-pairing-tensor vs lem-pc-dualizable-tensor-hom-equivalences: the existing statement concerns tensor-Hom equivalences in D_QCoh; the new statement concerns arbitrary monoidal categories and tensoring two specified exact pairings.

lem-sf-exact-pairing-symmetric-swap vs prop-sf-dualizable: the existing statement gives site-perfectness of the coefficient internal-Hom dual; the new leaf reverses any specified pair by explicit symmetry formulas in an arbitrary symmetric monoidal category.

Whole-DAG searches for tags 0FFS and 0FN8, the Mathlib declaration names, and tensor/reversed exact-pairing concepts, together with whole-blueprint searches, found no existing statement of either new leaf. The existing adjunction, uniqueness, braiding naturality, site-perfectness and signed-line results were cited rather than recreated. Both new blueprint references point to sk-thm-sf-dual-perfect through this item, and their same_as lists are empty.

## Review by Q82

I read the item's source, literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-dual-perfect/sk-thm-sf-dual-perfect.proof.md, especially its final sentence, and the unit and chapter records. I also read the Tate construction in sec-smooth-purity/sk-prop-an/sk-def-sp-tate-twist-locally-free.proof.md. The proof follows that coefficient-line route. I checked delivery-errors B through E against the actual files, concentrating on hypotheses, canonical maps, hidden non-elementary facts and the distinction between ordinary and completed operations.

For the tensor leaf I read Stacks categories.tex, Tag 0FFS (lemma-tensor-dual), and the construction ExactPairing.tensor in Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean, including tensor_coevaluation and tensor_evaluation. The hypothesis is two specified pairs in any monoidal category, not symmetry or rigidity of all objects. Reversing the order of the dual factors is essential and is present. For the swap leaf I read Stacks Tag 0FN8 (lemma-dual-symmetric) and Mathlib/CategoryTheory/Monoidal/Rigid/Braided.lean: the braiding and its inverse occur on the respective maps. Under symmetric braiding those are precisely the two displayed symmetries. No additional categorical hypothesis is concealed.

I opened the statement of every cited node. The following checks explain what each step takes from them, rather than relying on titles or source tags.

1. sk-def-sf-operations explicitly states the actual tensor/internal-Hom adjunction in clause (i). sk-def-perfect supplies a dual pair. lem-sfb-dual-tensor-adjunctions states the right-tensor adjunction U_P adjoint to U_Q with its specified evaluation. det-sp-unique-right-adjoint gives the counit-compatible comparison of right adjoints. The common left adjoint is right tensor by P; the symmetry converts the displayed left-tensor closed adjunction to this convention. At the unit, counit compatibility is exactly the transpose-of-e equation. This checks a map, not merely existence of an isomorphic object.

2. Transport along that isomorphism gives both triangles by substitution and conjugation, as written. The symmetric-swap leaf then applies to this specified pair. sk-def-perfect interprets this as perfectness. prop-sf-dualizable explicitly treats the actual coefficient internal-Hom dual and all four stages, with site-perfectness as hypothesis; that is assumed for P here. Its conclusion supplies site-perfectness of the actual dual in the required domain. I checked that this tool use does not create a dependency cycle.

3. The same adjunction and uniqueness statements apply to the reversed pair. Its evaluation is e_P composed with symmetry, so the component at the unit is exactly the j_P specified in the item. Nothing about an arbitrary biduality isomorphism is used.

4. lem-sfb-braiding-naturality gives the naturality identity for the actual symmetry. The defining transpose equation for j_P and symmetry squared equal to the identity give e'(1 tensor j_P)=e_P. Substitution into r j_P gives the first dual-pair triangle. Since step 3 already proves j_P invertible, the displayed r is its inverse on both sides. This is an elementary calculation from those formulas, not a new inverse-construction lemma.

5. det-def-sp-tate-twist-locally-free gives local rank-one Tate lines, signed powers and finite locally constant reductions. prop-weil-twist-preserves supplies constructible, finite-Tor and complete domains. lem-pur-line-unbounded-derived-tensor explicitly gives flat-line computation and the basis evaluation formula, so no unproved preservation of quasi-isomorphisms by an arbitrary tensor is assumed. lem-pur-integral-line-reduction-restriction assumes a locally free rank-one completed line with finite locally constant reductions. The Tate construction satisfies both hypotheses on this scheme, since ell differs from its characteristic. Its statement includes evaluation-preserving negative-power comparisons and the comparison with the specified quotient-tower completed tensor. These clauses, not the definition of completion alone, justify the integral evaluation and its inverse.

6. lem-pur-total-tensor-signed-coherence states the summand formula (-1)^(bp), for all integer shifts, and its coherence with associators and symmetry. The line factors are flat and concentrated in degree zero, so the ordinary tensor is the derived tensor by step 5. In degrees -s and s both opposite-shift evaluation multipliers are (-1)^s; the inverse multiplier cancels in each triangle. lem-sf-completed-tensor-shift-right states the actual completed shift comparison, including strict finite reductions and the product-cone shift. Symmetry gives the other tensor variable. Thus this calculation uses the prescribed integral comparison, not an assumed unsigned interchange of shifts.

7. def-weil-rationalization-karoubi states raw rationalization of morphism groups with the same objects, not an idempotent completion. def-weil-algebraically-closed-coefficients states common-finite-stage representatives and eventual equality after extension. lem-pur-completed-line-tensor-coherence provides signed-power scalar comparisons and, crucially, their evaluation equation and tower equation. Tate scalar extension supplies compatible rank-one base changes; twist-preservation has already checked the subcategory condition for rationalization. Finite sums of integral naturality identities prove the rational ones; the common-stage definition and tower equation prove independence of enlargement. Arbitrary P is not asserted to descend as an integral perfect object: its dual pair is handled intrinsically in steps 1 through 4.

8. The two opposite line contractions produce natural inverse tensor functors by associativity. def-weil-site-perfect-complex makes a shifted local unit site-perfect; sk-def-perfect identifies this with dualizability in the statement's convention. def-weil-finite-tor-amplitude and prop-weil-twist-preserves justify the category restrictions: a shift translates the bounding intervals and a twist preserves them. The tensor leaf then supplies the needed pair for a tensor with either line. Applying this to the dual from step 2 proves the final perfectness assertion.

I tested the formulas at the tensor unit and at the zero perfect complex, on an empty scheme, for m=0 and m=1,-1, and for s=0 and s=1,-1. For an odd shift of a rank-one degree-zero line the evaluation and inverse both have the required minus scalar, so the triangle is the identity; in residue characteristic two this scalar is one and the same proof applies. No division by a rank or by two occurs. At n=1 and at nonreduced coefficient rings with n>1, the line arguments use rank-one local bases and flatness, not semisimplicity. The argument for an arbitrary perfect P uses only its specified dual pair, so it does not assume global freeness, a global bounded free resolution, or that every rational object has a chosen integral perfect lattice.

The proof is now eight explicit steps; none exceeds 2000 characters. The comparison and tensor-pairing subclaims have cited theorem statements, while the inverse calculation and interval translation are written out. Every citation has a verbatim quotation in citations.json. I verified that proof_deps is exactly the union of uses and that the two new leaves carry no proof. I retained the imported statement, creation history and blueprint metadata. No statement dispute was needed.
