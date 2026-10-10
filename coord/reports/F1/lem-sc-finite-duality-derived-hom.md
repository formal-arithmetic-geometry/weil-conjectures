Files written:

- `dag/nodes/sec-picard-framework/lem-sc-finite-duality-derived-hom.json` — item, split; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-finite-pushforward-derived-hom-qcoherent.json` — statement-only support node; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-finite-sheafhom-affine-adjoint.json` — statement-only support node; no Mathlib match (generic module analogue found).
- `dag/nodes/sec-picard-framework/lem-sc-finite-twisted-inverse-bounded-below.json` — statement-only support node; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-finite-affine-derived-equivalence.json` — statement-only support node; no Mathlib match.
- `citations.json` — verbatim quotes for all cited statements.

Attachments:

None. I searched the slopmaster2 source for the item tag and for the finite-duality declarations; the available declarations concern the finite-flat curve trace comparison and do not state this derived finite-morphism result without `sorry`.

WANTED:

None. The Stacks source used for the split is represented by the local citation record and the copied source text available in the review checkout.

What was wrong or incomplete in the imported item:

The imported item had an empty proof despite depending on the substantial finite-twisted argument. The returned delivery then introduced two nodes whose statements repeated the item's canonical isomorphism and counit clauses, so Step 2 and Step 3 were circular (D1/C4). I deleted both and replaced them with independent statements for the affine sheaf-Hom adjunction and evaluation counit, boundedness of finite twisted inverse image, and affine derived equivalence. I also added `def-pur-derived-internal-hom` to the quasi-coherence node's `stmt_deps` (B3). The item statement itself was retained unchanged.

## Review by F1

I read the item source as Stacks Tag 0AX2 (lemma-finite-twisted) and Tag 0AX3 (remark-trace-map-finite), including the paragraphs proving pseudo-coherence of $f_*\\mathcal O_X$, preservation of $D^+_{\\mathrm{QCoh}}$, equality of the two right adjoints, and the counit square. I checked that the item hypotheses (finite morphism, Noetherian schemes, and bounded-below quasi-coherent $K$) are exactly the hypotheses used there. I also checked the three new source locations: duality.tex Tags 0AX2/0AX3 for the affine sheaf-Hom adjunction and evaluation, duality.tex Tag 0AX2 for bounded-below $f^!$, and perfect.tex Tag 0AVW for affine derived equivalence.

Step 1 cites `lem-sc-finite-pushforward-derived-hom-qcoherent`; its statement explicitly supplies pseudo-coherence of $f_*\\mathcal O_X$ and membership of derived internal Hom in $D^+_{\\mathrm{QCoh}}(Y)$. Step 2 cites `lem-sc-finite-affine-derived-equivalence`, `lem-sc-finite-twisted-inverse-bounded-below`, and `lem-sc-finite-sheafhom-affine-adjoint`; their statements explicitly supply the equivalence, boundedness, right adjoint, and counit needed for uniqueness of right adjoints. Step 3 cites the same adjunction statement for evaluation and only applies the forgetful functor, which is elementary. Every citation quote is copied verbatim into `citations.json`.

For each new node I searched the DAG and blueprint by finite-duality, affine adjunction, boundedness, and affine-equivalence keywords before creating it; no existing node stated the corresponding fact. Each new node is statement-only, introduces its objects and hypotheses, uses Stacks tag-and-label sources, and records real LeanFinder or Loogle plus Mathlib-source grep searches. The generic module adjunction hits were recorded as generalizations, not Mathlib matches. I tested the formulas on the identity finite morphism and on a finite affine algebra extension; the comparison reduces to the identity and evaluation at $1$ as expected.

I corrected the returned split by putting counit evaluation in the affine-adjunction node itself, so the comparison step explicitly states that the two adjunction isomorphisms match counits. This removes the ill-posed generic representation hypothesis and the relabeling of the item's conclusion.

What I could not finish:

No Lean proof was written, per stage-1 rules. The supporting nodes remain unsplit for later workers.
