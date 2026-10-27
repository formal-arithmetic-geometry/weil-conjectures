# Stage-1 delivery: lem-sfb-relative-split-torus-matrix-sheaf

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-split-torus-matrix-sheaf.json — item, statement, now split; no exact Mathlib match.
- citations.json — 15 step/node entries, each quoting the cited statement verbatim.
- searches.jsonl — six genuine searches recorded by msearch.py; earlier searches in the repository item are retained.
- report.md — this report. write_split.py is a sandbox-only reproducibility aid, not a project file.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the item tag and split-torus terminology throughout lean/WeilConjectures, and group-like/Laurent terminology in its GroupScheme directory; no declaration states the item. The field-case node lem-sfb-split-torus-hom-matrices is already split/reviewed, but its field hypothesis excludes arbitrary bases and is not an attachment for this item.

## WANTED

None. All sources actually used are present locally. No SGA source is used.

## What was wrong and what changed

The item had a statement and searches but no proof. The statement is correct and is preserved verbatim, including its arbitrary-base, pointwise operation, base-change and character-sheaf clauses. Milne's field conclusion in Lemma 12.4 cannot simply be quoted over a ring: the coefficients are orthogonal idempotents and need not select a single global exponent. The proof retains the idempotents and partitions the base by their clopen loci. Likewise, the existing Laurent-polynomial definition and group-like-basis leaf assume a field; neither is cited for the arbitrary-ring step. Instead the proof writes the finite-sum algebra and tensor maps and the coefficient equations explicitly.

The blueprint ancestor tool computes null because of the inherited created.item chain; this is retained rather than fabricated. The inherited explicit place and via chain describe the relative-character reconstruction supporting input. Read the latest blueprint sk-thm-sf-ctf-stability/_section.md and its proof as well as the chapter and DAG unit records. This algebraic supporting calculation does not change the direct-image/alteration route, the unit statement or the chapter. The two generic constant-sheaf tools lie in another unit; split_report.tool_uses explains their restricted use. All other geometric proof inputs are Mathlib leaves.

## Not duplicates

No new nodes were created. Searched the entire DAG for group-like, Laurent, orthogonal idempotents, 022U, 00EE and locally constant/constant-sheaf statements and searched blueprint_refs.py for torus, group-like, Laurent, constant sheaf, locally constant, idempotent and split. Reused the existing clopen-idempotent, affine-adjunction, tensor pushout, affine fibre-product, scheme-morphism-gluing and constant-sheaf representation nodes. In particular no ring-generalized replacement of the field group-like node is introduced: its coefficient argument is a short elementary step.

## Mathlib searches

Read all six responses in searches.jsonl. LeanFinder's first query found AffineSpace.homOverEquiv and LocallyConstant operations, not torus group morphisms. Read AffineSpace.lean around lines 145–163: the equivalence specifies arbitrary sections for affine space, with no invertibility or multiplication-preservation condition. LeanSearch returned abstract multiplicative characters, Scheme.Hom and LocallyConstant.instGroup, which do not supply the classification. Loogle for AlgebraicGeometry and torus returned no results. The torus/dagonalizable directory grep returned none. The broader grep found only the rank of finite flat morphisms; read Morphisms/FlatRank.lean around lines 230–235, which is a different locally constant function. The second semantic query returned LaurentPolynomial evaluation formulas; read Algebra/Polynomial/Laurent.lean around its eval₂_T and smeval_T_pow declarations: evaluation of known monomials does not classify group-like elements over disconnected rings. No searches were invented or repeated from an earlier sandbox attempt; the sandbox initially had no split or report.

## Review by NM

I read Milne, Algebraic Groups, Examples 12.1–12.2 and Proposition 12.3 on printed pp.231–232, Lemma 12.4 and its coefficient proof on p.232, and Theorem 12.9(a) and its full-faithfulness proof on pp.233–234. I read Stacks groupoids.tex Example 022U (example-multiplicative-group), algebra.tex Tag 00EE (lemma-disjoint-decomposition), schemes.tex Tag 01I1 (lemma-morphism-into-affine), Tag 01JQ (lemma-fibre-product-affines), and sheaves.tex Tag 00AN (lemma-mapping-property-glue). For the sheaf conclusion I read etale-cohomology.tex Remark 03P5 (remark-constant-locally-constant-maps) and groupoids.tex Example 03YW (example-constant-group). The general-base extensions are marked agent-written; Milne itself states the field results only.

Step 1 cites the tensor-pushout statement, whose clauses (2) and (3) construct and distinguish maps from the tensor product. The inverse monomial maps are written out, so no uncited theorem about tensor bases or multivariable Laurent polynomials is needed. Finitely supported sums and the presentation with inverse variables work even in the zero ring.

Step 2 uses precisely the fibre-product existence/universal property, Spec contravariance, affine tensor-product chart, and natural affine adjunction stated in the four cited nodes. The affine adjunction applies to an arbitrary locally ringed W, not just an affine W. It produces the global integer model and its maps, so there is no hidden gluing-existence theorem. The group identities are checked explicitly on generators. Global W-points are obtained using the global integer model, avoiding any assumption that W or B is affine.

Step 3 uses affine contravariance for the over-A algebra map, the affine tensor-product formula for the product scheme, and the tensor universal property for the induced algebra map. Those cited statements actually give these three operations. The multiplication and identity diagrams are expanded into two equations on each generator. Step 4 is their finite coefficient comparison: diagonal coefficients give idempotence, off-diagonal coefficients give orthogonality, and the counit gives sum one. This is a routine expansion, not an application of the field-only Mathlib leaf.

Step 5 cites the full clopen/idempotent correspondence, which is stated for any commutative ring, and the scheme-morphism-gluing statement, which explicitly includes uniqueness on arbitrary open covers. Orthogonality and sum one prove the partition; localizing at an idempotent sets it to one and kills the others. I checked uniqueness after passing to the nonzero residue field at a point, so exponent uniqueness never assumes A itself is a domain. I use affine refinements of overlaps, not a false assertion that intersections of affine opens are affine. The cited gluing statement then supplies equality of the original maps on the full source.

Step 6 uses Spec to construct the integer monomial maps and the fibre-product universal property to base change them, followed by scheme-morphism gluing on the inverse images of the matrix fibres. This works for an infinite cover, so it does not impose quasi-compactness on B. The multiplication and identity diagrams can be checked on the matching source open covers and the product cover. The inverse correspondence is proved on generators, and the point formula is obtained from Step 2, rather than assumed.

Step 7 expands the exponent sum for composition and the exponent addition for pointwise multiplication. Base change uses the same integer generator maps on the inverse-image open fibres, so it applies to every scheme morphism. Matrix inversion is a map of discrete sets and preserves local constancy; both inverse identities follow from the already proved composition calculation. None of these computations requires a new algebraic-group theorem.

Step 8 cites two existing nodes whose statements I opened in full. The first identifies maps to the coproduct of copies with exactly the clopen partitions/locally constant functions, for every set E and every W over the base. The second says this represented presheaf on the small etale site is the constant sheaf, including its canonical constant sections and sheaf property. Their statements, not a construction hidden in their proofs, give the two identifications used. Taking E=Z^r meets every hypothesis. Naturality follows from Step 7, and addition is checked there, so the conclusion is a sheaf isomorphism with its group operation, not merely an objectwise bijection of sets.

Step 9 checks the degenerate cases explicitly. With r=0, the counit forces the sole coefficient to one; with s=0 there are no output generators. Empty B and the zero ring give singleton Hom sets and empty-domain locally constant functions. On Spec(k×k), e_1 x+(1-e_1)y exhibits two different exponents on its components, showing why the idempotents are necessary. On Spec(k[epsilon]/epsilon^2), the displayed equations force idempotent coefficients, so extra nilpotent terms cannot define a new character. Negative exponents and the characteristic-p power map x↦x^p remain valid. Every step is shorter than 2000 characters. No new statement is false, no imported statement needed correction, and no extra clause was moved into a new node.

## Unfinished work

None for this one-level split. The existing cited nodes retain their own downstream proof obligations. Required server preflight and delivery results are recorded below once the commands complete.
