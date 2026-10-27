# Q23 stage-1 delivery: lem-sfb-finite-polynomial-simplicial-resolution

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-polynomial-simplicial-resolution.json: item, statement unchanged, split in five steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-truncated-algebra-matching-finite-type.json: new statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-split-polynomial-boundary-attachment.json: new statement, unsplit, no Mathlib match.
- citations.json: one exact statement quotation per citation per step.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint id and polynomial/simplicial resolution, 08PW/08PX, compatible polynomial faces, and polynomial cell terminology found no declaration proving this item. AffinePolynomialResolutionOfStalkwise and KoszulResolution concern ordinary module resolutions, not augmented simplicial algebras. No compiler was run and no Lean file was written.

## WANTED

None. All sources used are in the read repository.

## Source error

The statement is correct, and is unchanged. The printed proof of Stacks 08PX contains a genuine compatibility gap, not a false theorem. Its first coskeleton paragraph writes fibre products over A; in the category of A-algebras mapping to B they are over B. More substantially, lifting each s_i separately through a polynomial surjection Q to the next matching algebra does not enforce the degeneracy-degeneracy identities. At n=1 one needs s'_0 s_0 = s'_1 s_0. Take P_0=A[x], a split polynomial P_1 with s_0(x)=u, a finite polynomial cover of its next matching algebra, and adjoin a spare variable z mapping to zero. Modify the chosen lift s'_1(u) by z, leaving the other lifts fixed. All compositions with the cover, and hence all required face images, are unchanged, while s'_1 s_0(x)-s'_0 s_0(x) changes by z. Thus independent lifts do not prove the identity. The matching-finiteness proof also has an index typo at its end: it is P_{k_0+1}, not P_{k_0}, which maps to boundaries of (k_0+1)-simplices.

The split preserves the source's finite-matching and degree induction, replacing arbitrary degeneracy lifts with free generators indexed by surjections. The new boundary-attachment node states precisely the compatible construction, independently of Noetherianity and acyclicity. Its future proof can attach free polynomial simplex generators along the prescribed boundaries: in each degree the simplex indices not in the boundary are exactly surjections, so the pushout is polynomial in the surviving variables, and simplicial identities are inherited from precomposition. This is not a claim that arbitrary polynomial algebras are already split as algebras.

## Searches and reuse

The interrupted attempt had no item or report, only searches.jsonl and search result files. I read the saved results and reused them. Matching and attachment each have logged grep, LeanSearch, Loogle and two additional LeanFinder phrasings; the item has two semantic phrasings as well. All recorded queries are exact queries present in searches.jsonl. No unavailable response has been called a negative result.

The returned finite-presentation declarations were checked at Mathlib/RingTheory/FinitePresentation.lean:69 and RingTheory/Extension/Presentation/Basic.lean:123. They give single finite algebra presentations. SimplicialObject.Truncated.cosk at AlgebraicTopology/SimplicialObject/Basic.lean:297 and IsCoskeletal at Coskeletal.lean:60 are generic Kan extension constructions, not finite-type matching theorems. Splitting.IndexSet.instFintype at SimplicialObject/Split.lean:87 and Splitting at :212 supply coproduct indexing, not compatible face assignments for polynomial generators. None is a one-line specialization of either new lemma.

Before creating either id I searched the whole DAG by 08PW/08PX/08QI, matching-algebra and compatible polynomial-generator terminology, and the whole imported blueprint using blueprint_refs.py search for matching, polynomial, simplicial polynomial, 08PW, polynomial resolution and boundary cell. No equivalent statement was found. The ancestor command reports blueprint.from.node=None for this inherited historical chain; the new nodes faithfully retain that result and prepend the item to via. Read the current latest blueprint unit and direct-image proof (3); this is supporting cotangent algebra within the existing alteration chain, not a new proof of that unit.

## Not duplicates

lem-sfb-truncated-algebra-matching-finite-type vs lem-sfb-finite-polynomial-simplicial-resolution: the former is finite generation of one matching algebra for an arbitrary finite-type truncation, with no polynomial-resolution conclusion.
lem-sfb-split-polynomial-boundary-attachment vs lem-sfb-finite-polynomial-simplicial-resolution: the former extends one prescribed split polynomial truncation with any prescribed finite boundary data over any ring; it assumes neither Noetherianity nor boundary surjectivity and concludes no resolution or quasi-isomorphism.
lem-sfb-split-polynomial-boundary-attachment vs lem-sfb-split-simplicial-nondegenerate-homotopy: the latter is an additive homotopy-equivalence result for already given simplicial modules, not construction of face/degeneracy-compatible commutative algebras.
lem-sfb-split-polynomial-boundary-attachment vs lem-trf-polynomial-resolution-extension-trivial-kan: the latter adjoins constant variables to a whole existing resolution; the new node attaches generators with arbitrary specified boundary in a single new degree.
lem-sfb-truncated-algebra-matching-finite-type vs lem-weil-pbc-truncated-coskeleton-finite-limits: the latter gives existence and limit formulas but does not assert finite generation of algebraic matching terms.
lem-sfb-split-polynomial-boundary-attachment vs def-trf-cotangent-resolution-data: the definition supplies terminology and conditions, not the construction with prescribed boundary data.
lem-sfb-split-polynomial-boundary-attachment vs lem-sfb-cotangent-ext-smooth-support: finite support and localization of positive cotangent Ext are downstream consequences; they do not give a simplicial cell construction.
lem-sfb-truncated-algebra-matching-finite-type vs lem-trf-polynomial-augmentation-boundary: standard arbitrary-size resolutions and an augmentation criterion do not establish finite generation of matching algebras.
lem-sfb-split-polynomial-boundary-attachment vs lem-coef-sorted-simplicial-algebra-model: a transferred model structure allows arbitrary cell factorizations but does not assert the finite compatible polynomial presentation of this new node.

lem-sfb-split-polynomial-boundary-attachment vs lem-sfb-polynomial-bar-divided-monomial-normalization: the latter normalizes a prescribed cosimplicial polynomial bar complex over a rational algebra using divided monomials and an additive simplicial splitting; it constructs no arbitrary-ring truncated commutative algebra with prescribed boundary generators. I read its full statement, including the direct-sum splitting, derived-complex equivalence, and multidegree bounds.

## Review by Q23

I read Stacks cotangent.tex 08PW (lemma-polynomial), 08PX (proposition-polynomial), and 08QI (remark-resolution) in full, including the next-degree finiteness proof. I read more-algebra.tex lemma-fibre-product-finite-type and lemma-formal-consequence to check that the finiteness argument is not the false claim that arbitrary subalgebras of Noetherian finite-type algebras are finite type. Surjectivity of lower matching maps is indispensable. The new matching lemma uses precisely those hypotheses. Its statement encodes the relative boundary algebra explicitly; M_0 is B and M_1 is a fibre product over B, not over A. Applying 08PW to the coskeleton of such a truncation is legitimate: the given lower boundary surjections and the unique higher coskeletal fillers give a trivial Kan fibration. The matching-finiteness argument proceeds over the finite proper-face diagrams just as in 08PW. The second new statement uses the surjection indexing of simplicial.tex 017P (definition-split) to isolate the compatible polynomial attachment missing from the printed proof. It is statement-only; the future construction is explained in the Source error section above, not hidden in its statement.

Step 1 cites the full definition of finite-type algebra, which explicitly gives a finite polynomial surjection. The base truncation has E_0 finite and a surjective degree-zero matching map. The invariant, including specified generator-compatible degeneracies, is written out. The polynomial presentation and generator-compatible degeneracies are included explicitly in the invariant.

Step 2 cites the new matching-finiteness statement and the finite-type definition. I checked A Noetherian and B finite type from the item, finite type of every P_k from its finite polynomial presentation, and all lower boundary surjections from the induction. Its conclusion is exactly finite type of M_{n+1}, from which the definition supplies finitely many algebra generators. Each chosen generator has every face and a common augmentation, including the n=0 pair over B.

Step 3 cites the new attachment statement and the finite-type definition. The specified old bases satisfy its composition requirement, T is finite, and the prescribed tuples have the exact compatibility and augmentation equations assumed there. It returns a genuine truncation, not separate incompatible lifts. The new matching map is surjective because it contains an algebra generating set in its image. No additional surjective-map theorem is being hidden here: evaluate each generating polynomial on the y_t. The lower terms are literally retained. The index set is finite by counting functions between finite ordinals.

Step 4 uses the definitions of simplicial object and trivial Kan fibration, whose full statements I opened. This is an elementary assembly: every operator and every equation appears in a finite common truncation. All matching maps already exist and are surjective by induction. A boundary in degree k is precisely its compatible face tuple (its degenerate faces are determined by those faces); take a preimage in Q_k. The zero-dimensional lift is the separate surjectivity of Q_0 to B. A degeneracy composite carries any preimage in Q_0 to a preimage in Q_k. Thus no inverse-limit preservation theorem or unproved exactness assertion is used.

Step 5 uses the full statements of lem-weil-pbc-trivial-kan-homotopy-equivalence, lem-trf-simplicial-abelian-set-homotopy-quasi-iso and def-trf-cotangent-resolution-data. The first produces exactly the underlying set homotopy inverse needed by the second; the inverse is not presumed additive. The algebra augmentation itself is additive. I also read simplicial.tex 08NS and 08P2 at the cited source places. The constant additive complex has alternating differentials 0 and identity, so the explicit cohomology calculation supplies the remaining comparison to B[0]. The resolution definition asks for polynomial terms, surjectivity and this additive quasi-isomorphism, all established. The two off-unit comparison statements are declared as generic tool uses in split_report, not as an alteration-route replacement.

Small cases checked: A=B (one may take the constant A resolution with no variables), A=0 and B=0 (the zero polynomial algebra causes no exceptional case), B=0 over nonzero A (the matching construction can still choose generators, including in M_1), n=0 (no d_i a_j equations; equal augmentations are the condition), empty T (attachment adds only forced degenerate generators), and E_j empty in higher degrees. The simple non-smooth finite type algebra F_p over Z is included; no flatness or smoothness was introduced. A field over itself does not force a positive number of generators. The induction never claims a common bound on generator numbers or truncation of the resulting complex.

Against delivery-errors B--E: new nodes are self-contained statements with no proof/dependencies-of-proof; notions are defined inline or have actual definition citations; TeX is single-escaped after JSON parsing; sources have tags and labels; all searches are real and read; no false Mathlib leaf is asserted. Every actual use has a statement quote in citations.json. The two new facts are independent next-degree tools, not the item or its quasi-isomorphism clause. The proof sets up base and step without a cycle, every hypothesis was checked as above, and the source gap is repaired explicitly. All five steps have fewer than 1000 characters, so there is no long step hiding an extra lemma. No SGA source is used.

## Unfinished work

No part of the stage-1 item is left unfinished. The two new unsplit statements are the required next-level tasks. No Lean work is authorized or attempted. Delivery validation results will be recorded after the required dry run.
