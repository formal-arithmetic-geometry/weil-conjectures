# Stage-1 delivery: lem-trf-graded-qc-section-algebra-construction

## Files written

- dag/nodes/sec-trace-formula/lem-trf-graded-qc-section-algebra-construction.json: statement item, now split in seven steps; no exact project attachment or Mathlib match found.
- citations.json: 24 entries, one for every step/node citation, checked as literal substrings of the live cited statements.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter record is changed. Sandbox-only helper scripts generated the JSON; searches.jsonl records the prescribed search commands.

## Attachments

None. Searched the live WeilConjectures source for the exact blueprint tag and the graded/quasi-coherent/section-algebra concepts. Read RelativeProj/GradedAlgebraData.lean and its declaration list and inspected RelativeProj/GradedTensor.lean and Rees.lean. GradedAlgebraData defines affine algebra data; Rees constructs one particular graded algebra; neither states the direct image of arbitrary homogeneous modules on an algebraic space, the prescribed chart products, and the topology comparison. Thus none is an attachment to this item.

## WANTED

None. All sources used were present in literature/stacks-project. No prohibited SGA source is used.

## Statement correction

STATEMENT-DISPUTED: the imported wording introduced an algebraic space X over S and a scheme T, but gave T no S-structure. Its cited definition def-trf-algebraic-space defines morphisms as natural transformations between sheaves on Sch/S; f:X -> T is therefore not typed there unless T has an S-structure and f is over S. The correction explicitly says that T is a scheme over S and f is a morphism over S. This supplies the intended ambient data, exactly as in Stacks 0D3C (f:X -> Y a morphism of algebraic spaces over S) and 03M9; it leaves all module, multiplication, quasi-coherence and comparison conclusions intact. It is not a counterexample to their mathematical content. A source/target pair on unrelated Sch/S categories has no hom-set of the specified natural transformations, which is the failed type check. No other statement clause was changed.

## What was missing and what was retained

The imported item had no proof. Its prior Mathlib searches were retained, and new searches through the prescribed msearch.py were run and read: LeanFinder twice with different formulations, LeanSearch, Loogle and source grep. The hits concerned Proj, ordinary scheme module functors, and algebraic graded direct sums. None states this algebraic-space construction with its chart normalization and change of topology. Existing DAG results supply the substantial facts, so no auxiliary nodes are introduced. The proof spells out all products instead of adding nodes that restate the item's clauses.

Read dag/chapters/sec-trace-formula.json, dag/units/sk-i-curve-zero.json and the latest blueprint's lem-trf-local-term-locality.md. The current blueprint node concerns contracting correspondences, whereas this item's inherited provenance is explicitly the historical polarized-descent branch. The report keeps that historical ancestry and identifies the actual section-algebra paragraph in Stacks 0D3C. There is no new route around a unit step. Blueprint searches for graded, section algebra, and quasi-coherent graded found no node stating this item (the normal-bundle direct sum is different), so same_as remains empty.

## Not duplicates

No new node is proposed. Existing results reused include lem-trf-space-qc-separated-quasi-coherent-pushforward, lem-trf-scheme-zariski-etale-quasi-coherent-equivalence, and lem-weil-pbc-quasi-coherent-module-coproduct-closure. The scheme-only line section algebra lem-trf-qcqs-line-section-algebra-evaluation is not the generic algebraic-space/family theorem and is not used to replace it. Its dependency route was read to locate the existing coproduct result.

## Review by Q80

I read Stacks spaces-descent.tex at lemma-descending-property-ample (0D3C), including the paragraph declaring the section algebra quasi-coherent; spaces-morphisms.tex at lemma-pushforward (03M9), the preceding representable-pushforward discussion and the compatible-section proof of lemma-compute-pushforward (03M8); descent.tex at lemma-equivalence-quasi-coherent-limits (06VE), especially coproduct and tensor compatibility; sites-modules.tex at section-tensor-product (03EK), lemma-tensor-product-pullback (03EL) and its bilinear-map proof; and schemes.tex Section 01LA, whose item (3) is closure under direct sums. There are no new nodes whose sources require a separate review.

For Step 1 I opened the cited statements, including def-trf-scheme-algebraic-space, which supplies the representable algebraic-space interpretation of T over S: the space pushforward result really concludes quasi-coherence of the small-etale module direct image under quasi-compact separated hypotheses, and the topology equivalence really gives restriction as inverse and comparisons equal to the identity on opens. This is not an application of a scheme-source theorem to a space. The explicit S-data correction ensures that the required source and target lie in the same algebraic-space category.

For Step 2 I used the actual definition of direct image, which supplies a limit with chart projections and scalar maps, not merely an arbitrary right adjoint. Multiplication is the family with projection mu(pi(s) tensor pi(t)); compatibility follows from the assumed restriction compatibility of mu. Scalar action through a-sharp verifies the balance relation. The sheaf tensor definition and module-sheafification universal property cited in this step supply the extension from these bilinear maps. The unit is specified in the same projections. This is a few-line use of a defined limit, not a hidden base-change theorem.

For Step 3 the same limit statement supplies joint determination by projections. The associativity, ordinary commutativity and two unit laws are the assumed identities in B after each projection. The graded-structure definition states exactly the restriction-compatible bilinear operations now obtained. No assertion that global sections commute with a coproduct is used.

For Step 4 I checked that the coproduct-closure node concerns the categorical coproduct in module SHEAVES on an arbitrary scheme, with only a small index set; it therefore applies to N and the A_d of Step 1 without quasi-compactness of T. The graded-structure definition explicitly provides extension by bilinearity and sheafification, and the sheafification node supplies its universal property. Finite convolution gives the algebra laws, and the quasi-coherent-algebra definition says precisely that quasi-coherence is quasi-coherence of the underlying module. These generic tools are declared in split_report.tool_uses where needed.

For Step 5 the topology-equivalence statement identifies E as tensor pullback; the ringed-topos module-adjunction statement applies to its ringed-site morphism. The left-adjoint-colimit node is used on the discrete small category N, not on a large chart category. Its conclusion identifies the actual cocone E(iota_d), so the isomorphism preserves each summand rather than merely giving an unspecified isomorphism of objects. This avoids confusing an equivalence on quasi-coherent subcategories with ambient preservation of module coproducts.

For Step 6 I checked the cited tensor-pullback node states an underived isomorphism for arbitrary ringed topoi and arbitrary modules, with no flatness hypothesis. It supplies the comparison, and the tensor-formula adjunction supplies the counit b tensor s -> b s|_U. I wrote the balanced pure-tensor calculation: the two products give bc(st)|_U, and the unit gives b r|_U times 1. The comparison on local tensors is the canonical scalar-extension tensor comparison, not an arbitrary chosen isomorphism. The cited sheaf tensor and sheafification definitions extend these equalities uniquely. Thus multiplication compatibility is justified beyond knowing a comparison only on Zariski opens.

For Step 7 the algebraic-space definition gives a local rank-one frame for a line module, and the quasi-coherent-module definition permits arbitrary local presentations. A frame for L gives a one-generator presentation for EVERY tensor power, including B_0=O, so no tensor-closure theorem is being assumed without citation. The tensor definition supplies the canonical products, and in frames their laws reduce to commutative ring multiplication. Frame changes multiply by u^d and respect products by u^(m+n)=u^m u^n. Ordinary commutativity is justified here by rank one; no signed commutativity is introduced.

I tested the empty space (all compatible section modules and units are the unique zero-ring/module maps), the zero homogeneous algebra, degree zero, a trivial line, and nontrivial line frames. Infinite families and non-quasi-compact opens cause no issue because all sums in the conclusion are sheaf coproducts. No finite-generation, Noetherian or global affine hypothesis was smuggled in. All cited nodes were checked for dependency paths back to the item: none was found. I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the files and sources, particularly that each fact used is actually in the cited statement. No proof step exceeds 2000 characters; the longest is 905. I have completed every clause of the split; no mathematical work remains unfinished.

## Validation

Verbatim citation validation passed locally (substring checking only, not the prohibited local DAG validators). The first required remote dry run passed at 3212b635d34. I subsequently added the existing definition def-trf-scheme-algebraic-space to the statement dependencies and Step 1 citations, to explicitly type T as a representable algebraic space, and run the final dry run before delivery. The delivery tool records its result.
