# Stage-1 delivery: lem-sfb-affine-product-algebraic-equivalence

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-product-algebraic-equivalence.json`: statement, split in six steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-line-family-projective-curve-interpolation.json`: new statement only, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-abelian-product-axis-rigidity.json`: new statement only, unsplit; no Mathlib match.
- `citations.json`: one verbatim statement quotation for each cited node in each item proof step.

## Attachments

None. Searched the project's `lean/WeilConjectures/` by blueprint id and affine-product/algebraic-equivalence terminology, also inspected the related source hits in `lean/Sheaf/`. The existing line-algebraic-equivalence definitions and abelian multiplication results do not prove this product assertion. No compiler was run.

## WANTED

WANTED: Guo, *Divisors on coherent schemes and homogeneous spaces*, Proposition 5.2 and Claim 5.2.1, for lem-sfb-affine-product-algebraic-equivalence; its named local PDF is absent. Read the author's March 31 2026 PDF online at the URL already recorded in the item. No file was downloaded into the repository. The actual replacement proof uses the available Milne and Charles–Poonen documents and Stacks sources and is marked agent-written.

## Findings and route

The item statement is unchanged. It is not a formula literally stated in Guo. Guo's Claim 5.2.1 proof, printed pp.12–13, asserts clopenness of a birigidified triviality locus using normal projective compactifications and Picard theory; this item was extracted to make that argument explicit. I read that paragraph online. Normal projective compactifications of high-dimensional smooth affine varieties need not be smooth; using the smooth-projective Picard theorem on them without further work would be invalid. Instead the proof compactifies only the parameter curve. No hypothesis of properness on the affine factors, resolution of singularities in positive characteristic, or SGA input is used.

The latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3), gives the surrounding direct-image context. This worker-created historical branch has `blueprint.from.node = null`, as printed by the required ancestor command: the created-item chain ends at the module-created admissible-direct-image node. I retain that ancestry rather than invent a new imported ancestor, and record the specific context and intermediate items in `from.place` and `from.via`. The current proof stays below the node level and changes no chapter or unit route. The item is not the unit key statement, so no unit record was changed.

The new interpolation lemma is about replacing two fibres of one family; it is independent of product decomposition. Its prospective proof is as follows. A nonempty smooth connected finite-type scheme over an algebraically closed field is integral. If its dimension is zero its two rational points coincide, and use a constant family over the projective line. Otherwise Charles–Poonen Corollary 1.9 (printed p.4, read in the local PDF) supplies an integral curve through the two points, without requiring the original parameter to be quasi-projective. Normalize this curve and choose preimages of the points (their residues are k). Its normalization is smooth over the perfect field k. Milne I Lemma 3.5 supplies a smooth completion, which is projective for curves. Pull the family back to the normalized open curve. The product of the smooth Z with the completed curve is smooth, hence regular and locally Noetherian; regular local rings are UFDs. Stacks Tag 0BD9, `divisors.tex` lemma-extend-invertible-module, extends the line across the missing boundary. Its fibres at the two retained points are unchanged. This argument is retained here as work for the later splitter; the new node itself has no proof or proof dependencies.

The second new lemma is Milne I Theorem 3.4, printed p.18, read directly in the local PDF, with identity as its constant value. It concerns maps into an abelian variety, not Picard decomposition. The theorem explicitly does not require either source factor to be complete. Its proof uses the normalization/completion of curves and their density through a smooth point (Lemmas 3.5–3.6). The new statement preserves smoothness and geometric integrality, and requires both axes to be constant as morphisms. It is not replaced by the ordinary proper-source rigidity lemma.

## Searches

Searched the whole DAG by key notions, Milne Theorem 3.4, Stacks Tag 0BD9, Charles–Poonen, and the proposed node ids; searched the imported blueprint using `tools/blueprint_refs.py search` for algebraic equivalence, algebraically trivial, Picard product, nonsingular varieties, curve interpolation, line bundle family, constant axes, 0BD9, Charles and abelian variety. No existing node states either new lemma. Existing factorial-complement extension is reused conceptually inside the interpolation auxiliary's future proof and is not duplicated. Existing curve Picard, Jacobian, degree constancy and see-saw nodes are used directly in the item.

Ran the mandated msearch command for the item and both new statements, including second natural-language phrasings, Loogle, LeanSearch and Mathlib grep. Raw returned hits are retained in `search-result-*.json`; query/digest records are in `searches.jsonl`. The returned types concern ring Picard classes/tensors, topological trivializations, scheme fibre and Proj constructions, elliptic Weierstrass maps, or biproducts in preadditive categories. None states the geometric results or is a one-line specialization. In particular `biprod.decomp_hom_from` does not apply to arbitrary morphisms of varieties into an abelian variety: schemes are not a preadditive category. An exploratory Loogle query mentioned the unknown identifier `AlgebraicGeometry.IsGroupScheme`; it is not evidence of absence and is omitted from the node's search verdicts. The valid Smooth/IsProper query was also actually run. There are no claimed Mathlib leaves.

## Not duplicates

lem-sfb-line-family-projective-curve-interpolation vs lem-sfb-invertible-extension-factorial-complement: both mention Tag 0BD9, but the existing node extends a given line across an open with factorial boundary local rings; the new node produces a projective curve and a family realizing two given fibres over an arbitrary smooth connected parameter. It additionally needs curve selection, normalization and completion, and is not a specialization of the extension statement.

lem-sfb-line-family-projective-curve-interpolation vs lem-sfb-smooth-dvr-generic-line-extension: both use Tag 0BD9, but the existing statement extends a line from a generic fibre over a DVR; the new one realizes two prescribed closed fibres over a smooth projective curve and does not assume a DVR base.

lem-sfb-line-family-projective-curve-interpolation vs lem-sfb-split-torus-torsor-line-pullback: both use Tag 0BD9, but that node descends lines along a split-torus torsor, with no curve or pair of family fibres; the new node imposes no group or torsor structure.

lem-sfb-line-family-projective-curve-interpolation vs lem-sfb-projective-picard-identity-representability: the existing node's full text also mentions Tag 0BD9 and normal projective extension, but states representability and properties of a projective variety's Picard scheme. The new node states a family realization over a projective curve and asserts no representability.

lem-sfb-abelian-product-axis-rigidity vs lem-sc-rigidity: the existing node requires a proper first source factor and allows a general separated target; the new node allows both factors nonproper but requires an abelian-variety target and both axes constant. Neither statement is a one-line specialization of the other under the item's affine hypotheses.

## Review by Q01

I read the standing stage-1 brief, stages/1-dag.md, SETUP's three levels, GOAL, the item's chapter and unit records, latest blueprint context, and delivery-errors sections B–E. I checked each cited node's actual statement and recorded its verbatim statement in citations.json. In particular I did not use general Picard representability as a substitute for a universal kernel theorem, and did not use the proper-source rigidity lemma on an affine source.

Step 1 uses smooth base change and composition, geometric irreducibility of products and geometric reducedness of smooth schemes, finite-type permanence and rational-point density. All are exactly assertions in the named nodes. Both factors are nonempty by geometric integrality; thus their rational points exist. Affineness identifies their product with the spectrum of the tensor coordinate algebra, so separatedness is available without a missing extra hypothesis. The elementary subgroup reduction treats finite sums and negatives, not merely a single generating family.

Step 2 uses only the interpolation statement; step 1 has checked all hypotheses for Z=T. The new statement explicitly includes smoothness and separatedness of S, allows coinciding endpoints, and has no hidden properness hypothesis on Z. I checked its characteristic-p case: only normalization and smooth completion of a curve over the perfect field k, not higher-dimensional resolution, is used.

Step 3 uses the actual tensor/pullback functoriality and invertibility clauses of lem-weil-pbc-invertible-pullback-tensor. I wrote all four factors, including the basepoint line E_0; omitting that factor would make the axis cancellation incorrect. The cancellation is a few-line tensor identity, so it stays an elementary step.

Step 4 uses degree local constancy, the definition of the degree-zero Picard subfunctor and Jacobian representability by an abelian variety. Connectedness of T gives degree zero globally from the trivial basepoint fibre. Naturality sends both trivial axis families to zero. The new product-axis rigidity lemma has precisely the nonproper smooth source and abelian target needed here; geometric integrality and rational basepoints were checked in step 1. Jacobian representability explicitly identifies k-points with degree-zero invertible-module classes, so alpha=0 does give actually trivial curve fibres. No degree-by-degree substitute for a derived isomorphism occurs anywhere.

Step 5 applies the existing see-saw statement with C as its proper geometrically integral factor and T as its smooth separated finite-type parameter; all its rational curve fibres are actually trivial by step 4. It gives H as pullback from T, so the two endpoint classes agree. I expanded the tensor identity and checked that the E_0 fibres are one-dimensional k-vector spaces and hence trivial after pullback. The extracted factor differences are algebraically trivial using the permitted parameter C itself.

Step 6 explicitly pulls back each defining family and uses tensor-pullback compatibility; it is elementary subgroup algebra and the definition of Picard isomorphism classes. It proves the reverse inclusion and the asserted actual isomorphism, including the case of a zero class or either factor a point.

I tested the Poincare bundle on two affine opens of elliptic curves: its mixed class is generally not algebraically trivial on the whole product, so it is not a counterexample and is not erroneously decomposed by this proof. A genuinely algebraically trivial family difference has zero normalized mixed class by the argument. When the parameter endpoints coincide the interpolation and fibre difference reduce to zero. No new lemma restates the product equality or an item clause: one realizes families, the other is a target-specific morphism rigidity theorem. Both new nodes carry statements only. All six proof steps are shorter than 2000 characters. Cross-unit statements are declared as generic tool uses in split_report; their mathematical role and hypotheses are explained above.

## Unfinished

No required part of the item's split is left unfinished. The two new auxiliary statements are deliberately unsplit, as required for one-level splitting; their future-proof arguments and source places are retained above. The first server dry run passed at 4d9bf7b8f25. Added the actually-run valid Loogle query explicitly to the rigidity node; a fresh dry run and direct push follow this final record correction.
