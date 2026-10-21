# Q11 stage-1 report: lem-sfb-internal-inflation-graded-cup

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-internal-inflation-graded-cup.json`: statement, split; seven proof steps; no Mathlib match for the full internal condensed-action statement.
- `citations.json`: a literal statement excerpt for each node cited in each proof step.
- `report.md`: this report. `searches.jsonl` is the unmodified log produced by msearch.py; `write_split.py` is a sandbox-only drafting helper.

No new nodes, no new definitions, and no Mathlib leaves. The statement is unchanged. Neither the chapter nor the unit record was modified.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for inflation, laxMonoidal, condensed actions, and graded cup/composition terms. The hits concern other coefficient categories or general monoidal infrastructure, not this declaration with all its clauses. No project declaration states this entire internal condensed-action result. No Lean was written or compiled.

## WANTED

WANTED: a non-SGA reference giving the exact internal condensed-group derived inflation/graded-unit composition normalization, for lem-sfb-internal-inflation-graded-cup. The source node already explicitly requests this reference. The current blueprint direct-images proof is not such a reference: paragraph (3) only invokes direct-image preservation and compactification. Accordingly the proof is explicitly agent-written, with its substantive general ingredients cited as existing DAG nodes. No SGA source was used.

## Problems found and repaired

The imported node had no proof. Its mathematical statement does not require correction. Its formula really needs the order y[p] after x; appealing only to graded commutativity would conceal this issue. Steps 4–7 instead transpose the actual cup product and use unitor naturality to produce this order without reversing the input factors.

The inherited blueprint ancestor is null: `python3 tools/blueprint_refs.py ancestor lem-sfb-internal-inflation-graded-cup` prints None. I preserved the chain and null ancestor, and clarified the precise source place rather than inventing an imported ancestor. Whole-blueprint searches for monoidal, graded, shifted composition, and tensor unit found no statement of this exact item. The recorded unit is inherited infrastructure for paragraph (3); no unit route is replaced. The existing general shift and monoidal nodes are declared as tool uses in split_report, not by editing the maintainer's tool_uses field.

I also made the K-injective existence dependency explicit. Grothendieck abelianness alone was not used as an uncited shortcut for the hypothesis of the canonical adjunction shift theorem: step 2 cites lem-sfb-grothendieck-k-injective.

## Unfinished work

None within this one-level split. The exact literature reference remains wanted, as it was in the input. Existing unsplit inputs are reused, not re-proved or silently treated as finished Lean declarations.

## Not duplicates

No new nodes were created. I searched the whole DAG for tensor/shift, K-flat, graded endomorphism, Yoneda/cup, and monoidal inflation statements and read the candidate statements. In particular the ordinary-module shifted-single-complex nodes lem-sc-module-cup-shifted-unit-tensor and lem-sc-module-cup-shifted-unit-chain-tensor do not apply directly to arbitrary internal ring sheaves. I used the already existing general small ringed-site tensor shift-descent theorem instead. The existing internal restriction calculus gives inflation/invariants and its cup construction but does not state the ordered graded-composition law; it is an input, not an attachment for the item. A traversal of all statement and proof dependencies of every proposed cited node found no path back to the item.

## Review by Q11

I read coord/delivery-errors.md B–E, including the second copy, against the actual statements. I read the item's current source, main-20261015 sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3), the chapter record, and the inherited unit record. The structural assertion is agent-formulated, not a theorem literally present in paragraph (3). I read the local Stacks text sites-cohomology.tex at lemma-symmetric-monoidal-derived (0FPT), lemma-pullback-tensor-product (07A4), and lemma-adjoint (07A6), and more-algebra.tex section-sign-rules (0FNG), particularly the shifted-complex, shift-tensor and flip formulas. I checked the tag-to-label correspondence locally. For the mate step I read Mathlib/CategoryTheory/Monoidal/Functor.lean around rightAdjointLaxMonoidal (line 947) and its tensor-of-counits formula, and Monoidal/NaturalTransformation.lean lines 137–156 for the actual monoidal unit and counit instances. The local blueprint mate proof is the indicated source; the generic theorem is already a Mathlib leaf in the DAG.

Step 1 uses lem-sfb-action-topos-geometric-restriction for its small action-topos presentation, exact trivial pullback, and identity ordinary tensor/unit comparisons; its statement explicitly gives all three. The base coherent profinite site is small under the stated universe convention and has finite limits. Both coefficient ring sheaves are commutative. These are exactly the hypotheses of lem-sf-ringed-derived-closed-symmetric-monoidal and lem-sfb-ringed-derived-monoidal-comparisons. The latter, unlike an arbitrary tensor-existence theorem, explicitly supplies symmetry coherence and the canonical derived adjunction. No assertion about discrete abstract-group representations is substituted for internal group actions.

Step 2 uses lem-sfb-condensed-product-action-inflation for exactness, Grothendieck abelianness, and the specified invariant-inclusion transpose, with the second group trivial. It uses lem-weil-pbc-exact-functor-derived-factorization for the actual termwise functor, triangulated structure and signed shifts. The already constructed ringed projection therefore derives this same exact functor, so the canonical derived adjunction of lem-sfb-ringed-derived-monoidal-comparisons is the required one. The statement of lem-sfb-condensed-derived-restriction-calculus explicitly supplies equivariant-injective computation on bounded-below objects and total derived functors. I checked separately the hypothesis of lem-sp-canonical-right-derived-adjunction-shift: exact additive left adjoint, additive right adjoint, and K-injective resolutions. The latter is supplied by lem-sfb-grothendieck-k-injective, whose statement applies to every complex in a Grothendieck category. This retains the canonical shifts, rather than transporting an arbitrary shift structure.

Step 3 uses the two existing Mathlib leaves lem-sfb-monoidal-adjunction-mates and lem-sfb-monoidal-adjunction-unit-counit. I checked their statements and the actual Mathlib formula: the lax multiplication transposes the inverse strong tensor map followed by the two counits. This is precisely the cup product specified by the item. Applying F to the regular unit multiplication gives a unital algebra by the lax coherence diagrams. The unit transpose is the identity under the specified unit comparison.

Step 4 uses the canonical adjunction shift result for identifying Phi, the actual monoidal counit equation for transposition, and lem-pur-shifted-tensor-morphism-calculus for compatibility of exact ringed pullback with the fixed signed comparison. That last node applies to arbitrary small ringed sites, not only schemes or a Kummer/purity construction; its statement explicitly excludes such extra constructions. Its flat degree-zero input is the regular ring module, whose tensor functor is the identity. Expanding the transpose gives m(f tensor g) on the shifted units, with no remaining unsupported multiplicativity assertion.

Step 5 uses lem-weil-pbc-derived-tensor-shift-descent, whose statement explicitly covers arbitrary morphisms in the localization, inverse quasi-isomorphisms included. This matters because the unit of the action category need not be projective and f need not be a chain map from the literal single complex. The unitors are those in lem-sf-ringed-derived-closed-symmetric-monoidal. The three written equalities are just bifunctoriality, left-unitor naturality, and naturality of second-shift extraction. They give g after f[-q]; none requires a new lemma with independent hypotheses.

Step 6 uses the stated formulas in lem-weil-pbc-total-tensor-integer-shifts: first extraction is unsigned, second extraction contributes (-1)^(n times the first degree), and exchanging extraction orders contributes (-1)^(ab). The corresponding maps are genuinely maps on the derived tensor by lem-weil-pbc-derived-tensor-shift-descent. The only comparison computed on a literal single complex is an isomorphism of shifted copies of the regular unit; that complex is K-flat. Thus the scalar is a sign depending only on p,q and the fixed extraction convention. The arbitrary classes f,g are never computed by an unjustified cochain resolution. Setting either p or q to zero makes every exponent zero. The assertion requests existence of the convention-dependent sign, not an explicit sign for a newly chosen convention, so I did not impose a different normalization.

Step 7 substitutes the preceding calculation and shifts by p+q. I checked the types: f=x[-p]:I[-p] to I, g=y[-q]:I[-q] to I, so g composed with f[-q] shifts to y[p] composed with x. Additivity carries the integer sign through Phi. No fact beyond earlier steps and definitions is introduced in this elementary closing step.

For the B checks there are no new unsplit nodes, hollow definitions, invented tags or new-node search records. The item remains self-contained and unchanged. All five current Mathlib searches were run with the required msearch.py command, and their actual logged results were read and recorded; the source node's older searches were preserved. I tried both an internal-condensed formulation and a general graded-unit formulation. The general mate and graded-object hits cover only ingredients already cited, not the entire item. All services answered normally; no unavailable service was represented as no match.

For C, every cited statement was opened and read, and citations.json copies actual statement substrings. The transposition and naturality steps spell out their arrows; they do not appeal to proofs hidden inside a definition. For D, there is no new node restating a clause, no branch moved into a new input, and no cycle. For E, I tested the trivial group (identity adjunction), the zero ring (zero unit object, no uniqueness of signs needed), p=0 and q=0 (unitors and unsigned comparisons), and p=q=1 (only the possible Koszul sign remains; order still y[1] after x). The calculations never assume a nonzero unit, flatness of arbitrary objects, exactness of invariants, or cochain acyclicity. No step exceeds 2000 characters; the three short formal calculations do not hide a non-elementary sublemma.

## Validation

The preliminary server review_split check passed. The required full deliver.py dry run and direct push are run after this report is written; their definitive outcomes are reported by the delivery command.
