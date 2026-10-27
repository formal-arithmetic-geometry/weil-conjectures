# Stage-1 report: lem-sfb-square-zero-relation-tor-obstruction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-square-zero-relation-tor-obstruction.json: split, statement unchanged, four proof steps.
- dag/nodes/sec-six-functors-basics/def-sfb-divided-power-dga.json: definition, unsplit; no complete Mathlib match for the graded differential structure.
- dag/nodes/sec-six-functors-basics/lem-sfb-tate-free-resolution.json: statement-only, unsplit; no Mathlib Tate-resolution match.
- dag/nodes/sec-six-functors-basics/lem-sfb-square-zero-dga-curvature.json: statement-only, unsplit; no Mathlib curvature-derivation match.
- dag/nodes/sec-six-functors-basics/lem-sfb-lifted-relation-curvature-class.json: statement-only, unsplit; no Mathlib relation-to-curvature-class match.

The sandbox also contains citations.json with the verbatim statement of every node used by each item step, searches.jsonl with the actual search records, and this report. The temporary writing script is not a delivery file.

## Attachments

None. Searched the live project source under lean/WeilConjectures for the item id, square-zero/Gulliksen/Tate terms, the Stacks lemma labels and divided-power differential terminology. The Tate arguments in KoszulIdealAlternatingProducts, KoszulConormalCycleRelations and SelfTorConormalComparison are docstring arguments for conormal/Koszul comparison results, not declarations of this obstruction or of the new general auxiliary statements. The unrelated Tate residue and purely inseparable field declarations do not apply.

## WANTED

None. All mathematical sources used are present in literature/stacks-project/dpa.tex. No SGA source is used.

## Corrections and route

The item's statement and its statement dependencies are unchanged. The new split follows precisely Stacks Tag 09PU, lemma-not-finite-pd. The original empty proof is replaced by Tate resolution, curvature and relation-class assembly, followed by the divided-power calculation and the explicit free-resolution computation of Tor.

The source represents g in (R/I)[x]; the item already uses a polynomial lift g' in R'[x]. These give the same scalar in S/IS because multiplication by f identifies R/I with (f), coefficient by coefficient. No extra hypothesis is added.

I read the chapter and stored unit records and the current blueprint under literature/blueprint/latest, in particular sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and the direct-images proof. The stored unit record has an older chapter/text; the current unit's branch (3) is the proper/open direct-image route. This is a supporting commutative-algebra split below the existing complete-intersection chain, not a replacement of that route. The ancestor tool returns blueprint.from.node = None for this pre-existing chain. The item retains its existing provenance; each child uses that returned null ancestor and extends the existing via list by the item. The precise supporting source clause is added to each child's from.place. Blueprint searches for square-zero, Tate, divided power, 09PN, 09PS, 09PT, 09PJ and curvature found no equivalent imported node. same_as is therefore empty. The item is not a unit's key node, so no unit realization record is changed.

## Source error

Tag 09PU's proof correctly writes theta^n(gamma_n(xi)) = g^n, but then says that xi^n is nonzero. The valid conclusion is that gamma_n(xi) is nonzero. In the divided-power polynomial algebra F_p<T>, with |T|=2, zero differential and theta(T^[a])=T^[a-1], theta(T)=1 and theta^p(gamma_p(T))=1, whereas T^p=p! T^[p]=0. Thus one cannot infer nonvanishing of ordinary powers in characteristic p. The split uses gamma_a(z) throughout and leaves the true item statement unchanged.

No divided powers on homology are assumed: the warning immediately after Tag 09PJ says this is not automatic for arbitrary divided-power DGAs. The proof uses divided powers on a cycle representative in B, then the commuting operator to detect whether that cycle is a boundary.

## Not duplicates

The whole-DAG searches for the source tags 09PG, 09PH, 09PI, 09PJ, 09PL, 09PN, 09PS and 09PT found no existing statement or definition with these sources. The parent review mentions some of these tags but states injectivity of minimal ideal generators, not the auxiliary facts. In particular:

- def-sfb-divided-power-dga vs lem-sfb-finite-tor-ideal-generators-injective: a definition of graded differential/divided-power data versus injectivity of a local ideal-generator map.
- lem-sfb-tate-free-resolution vs lem-sfb-finite-tor-ideal-generators-injective: existence of a general augmented free DGA resolution versus the local ideal-generator injectivity conclusion.
- lem-sfb-square-zero-dga-curvature vs lem-sfb-finite-tor-ideal-generators-injective: constructing a degree minus two operator on a quotient DGA versus injectivity of a local ideal-generator map.
- lem-sfb-lifted-relation-curvature-class vs lem-sfb-finite-tor-ideal-generators-injective: constructing a degree-two cycle and computing its curvature image versus injectivity of the local map.
- def-sfb-divided-power-dga vs lem-sfb-square-zero-relation-tor-obstruction: algebraic structure definition versus an infinite Tor-dimension obstruction.
- lem-sfb-tate-free-resolution vs lem-sfb-square-zero-relation-tor-obstruction: arbitrary finite type algebras have resolutions, without a square-zero relation or nonvanishing conclusion.
- lem-sfb-square-zero-dga-curvature vs lem-sfb-square-zero-relation-tor-obstruction: no relation, augmentation or nonnilpotence is required, and no Tor conclusion is asserted.
- lem-sfb-lifted-relation-curvature-class vs lem-sfb-square-zero-relation-tor-obstruction: its output is one cycle with prescribed curvature image; it assumes neither nonnilpotence nor a resolution in all degrees and asserts no Tor nonvanishing.
- lem-sfb-tate-free-resolution vs new-r4-self-tor-conormal-comparison-tate-construction: existence of the actual divided-power DGA resolution of an arbitrary finitely generated algebra, versus a map from conormal exterior powers to self-Tor of a quotient, calculated on chosen Koszul lifts. The latter gives no such resolution.

The other 09PQ self-Tor/conormal nodes likewise concern wedge maps or special regular/Koszul calculations. Their statements do not give the general Tate resolution, divided-power DGA definition, curvature operator, or lifted-relation class needed here. The existing def-weil-pbc-tor-modules is reused for the projective-resolution formula and no duplicate Tor-computation lemma is created.

## Review by O1

I read dpa.tex's definitions 09PG and 09PJ, the adjoining-variable examples 09PH and 09PI, the Tate-resolution statement and construction 09PN, the base-change statement 09PL, the entire curvature construction 09PS and the entire relation computation 09PT, and compared the item with the statement and proof of 09PU. These are the sources for the four new nodes, respectively. Each new statement introduces its rings, modules/graded data, differentials, scalar action and maps; new unsplit statements contain no proof or proof dependencies. No notion is defined by a tag alone. The new definition spells out the odd-square condition even in characteristic two, the integer divided-power coefficients, the differential identity, the homology convention, and the polynomial/exterior/divided-power generators.

Step 1 uses the full statement of lem-sfb-tate-free-resolution, which supplies the same prescribed P in degree zero, the augmentation to S, positive-degree acyclicity, degreewise R-freeness and finitely many variables in each degree. Its hypotheses hold because R is Noetherian and S is the given finite polynomial quotient. R-freeness does not mean finite R-rank: the degree-zero polynomial monomials can form an infinite basis.

Step 2 uses lem-sfb-square-zero-dga-curvature and lem-sfb-lifted-relation-curvature-class. I opened both new statements after writing them. The first supplies the lifted graded algebra and operator, quotient divided powers and precisely the Leibniz/divided-power/chain identities used later. The second assumes H_1(A)=0, which Step 1 supplies, and gives a cycle representative z with [theta(z)] equal to the image of the specified g'. The coefficient-annihilator condition, the coefficientwise lifting conditions and the lifted relation are exactly the item's hypotheses; neither a regular sequence nor flatness of S over R is used. The identification H_0(A/IA)=S/IS follows directly by taking the quotient of A_0 by d(A_1)+IA_0, so no base-change exactness is assumed.

Step 3 uses the differential compatibility in def-sfb-divided-power-dga and the three operator identities in lem-sfb-square-zero-dga-curvature. Its induction is written in full: theta^k(gamma_a(z))=u^k gamma_{a-k}(z), starting at k=0 and using theta(u)=0 because u has degree zero. It only applies the divided-power rule when a-k is positive; the induction ends at gamma_0=1. The differential identity gives cycles; commutation gives that a boundary would map to a boundary. It follows that [u]^a=bar(g)^a would vanish, contrary to the exact nonnilpotence hypothesis. This is elementary assembly from the two cited statements, not a hidden general nonvanishing lemma.

Step 4 uses the existing def-weil-pbc-tor-modules, whose statement explicitly computes Tor as homology of any chosen free/projective resolution tensored with N. The degreewise tensor/quotient isomorphism and its inverse are written in the item and commute with the differentials by R-linearity. Taking N=R/I and a=d+1 gives 2a>d. This establishes the negation of precisely the quantified finite-Tor bound in the item.

For C1/C4, every non-elementary input is one of those cited statements, not a source tag, a docstring, or material borrowed from another node's proof. citations.json copies the complete cited statements verbatim for all six step/node pairs, avoiding selective quotes that could conceal missing clauses. No step exceeds 2000 characters. The statement-only nodes are independently useful smaller results: none restates the infinite-Tor conclusion. Their dependency direction is definition to construction to computation; nothing depends on the item. All new nodes share the item's unit/chapter; the reused Tor definition is a Mathlib leaf, so no off-unit route theorem is used.

I checked degenerate cases. If f=0, then I=R and S/IS is zero, so the item's nonnilpotence hypothesis fails; the curvature statement reduces to the zero operator on B=0 and remains valid. If m=0, then g'f=0 forces q(g') to have coefficients in I, again excluding nonnilpotence. If S=0 or R=0, the same hypothesis fails. For a positive test, take R'=k[t]/(t^3), R=k[t]/(t^2), f=t^2, I=(t), n=0 and h_1=r_1=t. Their chosen lifts multiply to f with g'=1; S=k, and the result detects the familiar unbounded Tor of k over the dual numbers. The Tate statement also permits S=R with no positive variables and S=0 (a degree-one generator with differential 1); neither produces a false nonvanishing claim. The relation-class lemma with g'=0 only promises a class with zero curvature image and asserts no nonvanishing. The characteristic-p test in the source-error paragraph checks exactly why ordinary powers cannot replace divided powers.

For the Mathlib verdicts, I read the actual search hits, with separate natural-language formulations from LeanFinder and LeanSearch, Loogle patterns and logged source greps for each new node. I read Basic.lean's DividedPowers structure, DividedPowerAlgebra/Init.lean's basis passage, ToSquareZero.lean's degree-zero derivation construction and Extension/Presentation/Core.lean's relationOfHasCoeffs. Each supplies only part or a different construction, as recorded in the nodes. No unavailable search is represented as mathematical absence. Prior item searches are preserved, and four fresh logged item searches confirm no full match. No Lean code or compiler/build command was run; all writes are in the sandbox.

## Unfinished work

No part of this one-level split remains unfinished. The four new nodes are deliberately unsplit and join the stage-1 queue. The server dry run and push are the required final validation and delivery steps.

## Dry-run repair

The first server preflight rejected the new DGA definition because it cited no underlying definition node. I read def-weil-pbc-module-chain-complex-homology in full: it states precisely the homological indexing, zero extension, linear differential and kernel/image homology convention used here. I added it as the new definition's statement dependency and explicit citation. It is an existing Mathlib leaf, so it introduces neither a duplicate nor an off-unit proof route. The actual divided-power DGA data remain spelled out in the new node; no unsupported graded-commutative algebra assertion is imported from the chain-complex definition. I refreshed the verbatim citation for Step 3.
