# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-reductive-torus-fibre-openness.json`: split statement, unchanged statement and statement dependencies; ten proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-torus-centralizer-normalizer.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-geometric-torus-fppf-lift.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-torus-bundle-weights.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-corank-one-centralizer-reductivity-test.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-nonsolvable-central-torus-corank-three.json`: statement, unsplit; no Mathlib match.
- `citations.json`: one entry for every node used in every proof step, quoting its statement verbatim. Full statements are quoted so the exact hypothesis and conclusion are visible together.

The five new statements have empty proofs and proof dependencies. Search results are preserved in `search-results-first.json`, `search-results-second.json` and the msearch-owned `searches.jsonl`; node records contain the exact tool and query and actual output. Each new node received LeanFinder, LeanSearch, Loogle, grep, and a second semantic phrasing. Searches of the item were also run. No Mathlib leaf was identified.

## Attachments

None. Searched `lean/WeilConjectures/` by the blueprint tag, reductive, maximal torus, torus and the relevant concepts. Lie-algebra reductivity and a compact topological torus do not state this group-scheme result. No project declaration supplies the item.

## WANTED

WANTED: Brian Conrad, *Reductive group schemes* (2014), `literature/conrad-reductive-group-schemes.pdf`, Proposition 3.1.9 and Lemma 3.1.10, printed pp.85-88, for the item and the two field criteria; Proposition 2.1.2, pp.56-60, Lemma 2.2.4, pp.64-66, Corollary B.2.7, Proposition 3.1.6, pp.83-84, and the weight-bundle paragraph of 3.1.9 for the three relative inputs. The PDF is absent locally. I read the Stanford PDF online at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf without adding a local copy. The item's proof origin is therefore marked agent, as the brief requires. No prohibited source is used.

## Problems found and changes

The original item had no proof. Its statement matches Conrad 3.1.9(1),(2), restricted to split tori and omitting semisimplicity and the stronger relative centralizer-isomorphism conclusion. There is no statement dispute and no statement change. The original source, creation record, blueprint ancestry and statement dependencies are retained.

I avoided assuming relative affineness of the neutral component: only its individual geometric fibres are affine. The maximality argument precedes and does not use openness of reductivity. The normalizer argument takes the open image of a prescribed character-action stratum; it does not require a geometric normalizer point to lift as a rational point over the original residue field. All weights are integral characters, including in characteristic two and when a root is divisible in the character lattice. The torus kernel is formed from the saturated lattice, so it is a smooth subtorus rather than a possibly nonreduced kernel.

I explicitly added the existing smooth-implies-flat-and-lfp lemma to step 7 after reading the hypothesis of the open-map node. Step 1 also explicitly cites preservation of smoothness on an open. Those were the two citation omissions identified during my own read-through.

## What remains

No part of this stage-1 split remains unfinished. The five new nodes are intentionally statement-only and will be split by later stage-1 workers. No Lean file, compiler, Lake or build tool was used.

## Not duplicates

lem-sfb-relative-torus-centralizer-normalizer vs lem-sfb-torus-centralizer-smooth-connected: the existing node is over a field and assumes geometric connectedness; the new node works over an arbitrary base, allows disconnected fibres, includes the normalizer and its integral action strata, and gives arbitrary base change and relative Lie invariants.

lem-sfb-relative-torus-centralizer-normalizer vs lem-sfb-lie-normalizer-centralizer-invariants: the existing node only computes field tangent spaces when representing subgroups have already been supplied; the new node represents smooth relative centralizers and normalizers over arbitrary schemes.

lem-sfb-relative-torus-centralizer-normalizer vs lem-sfb-torus-normalizer-components: the existing node is a field statement about identity components, not relative representability or smoothness.

lem-sfb-relative-torus-centralizer-normalizer vs lem-sfb-cartan-containing-normalizer-smooth: the existing field theorem concerns a smooth subgroup containing a maximal-torus centralizer, not a relative torus in an arbitrary smooth affine group.

lem-sfb-geometric-torus-fppf-lift vs lem-sfb-split-torus-etale-subgroup-lift: the existing node requires the original residue field to be algebraically closed; the new node starts with any point and a chosen torus over its algebraic closure, and first allows a finite residue extension through a quasi-finite fppf neighborhood. The hypothesis needed to apply the existing node is unavailable here.

lem-sfb-relative-torus-bundle-weights vs lem-sfb-trivial-torus-coherent-weight-decomposition: the existing node requires a Noetherian scheme over a field, whereas the new statement applies to finite projective modules over an arbitrary ring, including mixed-characteristic non-Noetherian rings, with arbitrary ring base change.

lem-sfb-relative-torus-bundle-weights vs lem-sfb-split-torus-representation-weight-decomposition: the existing statement is for finite-dimensional vector spaces over a field; it does not give projective summands or rank neighborhoods over arbitrary rings.

lem-sfb-corank-one-centralizer-reductivity-test vs lem-sfb-reductive-torus-fixed-subgroup: the existing lemma assumes reductivity and only gives reductivity of a centralizer. The new criterion has the converse for an initially possibly nonreductive smooth connected group with self-centralizing maximal torus.

lem-sfb-nonsolvable-central-torus-corank-three vs lem-sfb-connected-group-dimension-two-solvable: the existing statement concerns dimension at most two; the new statement concerns nonsolvable groups of dimension three modulo a central torus and concludes reductivity.

lem-sfb-nonsolvable-central-torus-corank-three vs lem-sfb-semisimple-rank-one-tangent-dimension: the existing lemma assumes semisimplicity; the new lemma must establish reductivity without that assumption.

I searched all DAG titles and statements for these concepts, their Conrad source places, and the whole latest blueprint with `tools/blueprint_refs.py search` (centralizer, normalizer, torus, weight, solvable, reductive and corank concepts). No blueprint node states a new input or the item. The characteristic-zero algebraic-group geometry nodes returned for centralizer do not state these arbitrary-characteristic relative results. The ancestor command gives null; the inherited from.node=null and via chain are retained, with precise supporting proof places filled. The unit and chapter are unchanged; this is a supporting item, not the unit's key statement.

## Review by Q49

I read Conrad's actual statement and proof of Proposition 3.1.9, pp.85-88. It proves maximality before reductivity, uses relative centralizers, the finite adjoint-weight decomposition, Lemma 3.1.10, and the rank-one nonsolvability argument. The ten steps follow exactly that route. The only variation is to use the open image of the normalizer stratum rather than explicitly choosing an etale section of the Weyl quotient. This uses smoothness and the same integral character action and yields the same noncentral element on each nearby geometric fibre.

For the new relative-centralizer-normalizer node I read Proposition 2.1.2 and Lemma 2.2.4: their hypotheses permit a split torus in a smooth affine finitely presented group, with arbitrary base. The Lie invariant assertion uses the whole torus. The matrix strata are the fibres of the locally constant character automorphism of a split torus, as in the character-rigidity discussion; they need not be all nonempty or have a section. Rank zero gives the identity matrix and C=N=G, which tests the disconnected case as well.

For the new geometric-torus lift I read Proposition 3.1.6 and the first paragraph of the proof of 3.1.9(1). The selected geometric torus and its finitely many defining coefficients descend to a finite residue extension. Lifting successive monic equations realizes that extension through a finite locally free neighborhood; 3.1.6 gives the subsequent etale lift, and etale-local splitting gives the split torus. Taking affine neighborhoods keeps the composite flat, quasi-finite and finitely presented. The requested identification includes the parametrization, not only the torus image. No algebraic closedness of the original residue field is assumed. For rank zero the identity section already supplies the lift.

For the relative-weight node I read the weight-bundle paragraph on pp.86-87 and the grading discussion on p.66. Coassociativity identifies the Laurent coefficients with the weight summands; counitality sums the coefficients to the original element. Finite generation bounds the support, the summands are direct summands of a finite projective module, and the coefficient projectors commute with every base change. Their finite-projective ranks are locally constant. This is a genuine generalization needed for an arbitrary base; the existing coherent Noetherian-field statement cannot be substituted. Checked the zero ring, V=0, r=0, a projective module of nonconstant rank on a disconnected base, and weights p and -p in characteristic p: integral characters remain distinct.

For the centralizer criterion I read the full Lemma 3.1.10 on p.87. It applies to a possibly nonreductive group, provided the maximal torus is self-centralizing. The proof detects every nonzero weight of the unipotent radical inside a corank-one centralizer; torus fixed subgroups of a smooth connected group are smooth connected, so reductivity kills these intersections. What remains is torus-fixed and lies in the self-centralizer, forcing the unipotent radical to vanish. The empty-weight case is valid: the tangent dimension is that of T and the connected smooth group equals T. A Borel of SL2 fails its centralizer reductivity test, as it should; a reductive SL2 passes in characteristic two as well.

For the nonsolvable corank-three node I read the final dimension paragraph on p.88. Quotienting by the central torus gives a nonsolvable smooth connected group of dimension three. A positive-dimensional unipotent radical would leave a quotient of dimension at most two, hence solvable, making the dimension-three group solvable too. Thus that quotient is reductive. The unipotent radical of the original group has trivial image in the quotient and would lie in a torus, so is trivial. This field criterion neither says that every three-dimensional group is reductive nor assumes characteristic zero. Checked SL2 and PGL2 in characteristic two, their products with a central torus, and solvable three-dimensional triangular groups (excluded by the nonsolvability hypothesis).

I opened and read every cited node's statement before forming citations.json. Step 1 uses the component-open statement under smooth, quasi-compact, quasi-separated hypotheses, the field identity-subgroup statement, connectedness under field extension, and open restriction of smoothness; G is affine finitely presented, so the topological hypotheses hold. Step 2 uses the new relative centralizer for C, the field connectedness and self-centralizer statements only inside the connected reductive special fibre, then the smooth-group fibre-dimension lemma and the explicit strict-dimension clause of the products node. The latter clause is about arbitrary smooth connected closed inclusions, so no hidden solvability assumption is imposed there. A smooth affine scheme is also a group algebraic space, as allowed by the fibre-dimension lemma.

Step 3 uses only the existing Borel-pair existence clause and the new geometric lift; it does not apply the existing algebraically-closed-residue lift at an arbitrary point. Step 4 takes the precise finite-weight and root-line clauses of the relative-weight and rank-one-reflection nodes. Step 5 writes the elementary primitive-integer-vector calculation and then uses the invariant-summand clause of the relative-weight node. It excludes nonprimitive-kernel errors without assuming alpha primitive.

Step 6 uses the centralizer's relative Lie formula, field connectedness of torus centralizers, tangent equals dimension for smooth groups, and preservation of reductivity by torus centralizers only on the original special fibre. Step 7 uses the reflection node to find the special element inside its stated rank-one centralizer, the new normalizer's matrix strata and smoothness, the component open, smooth restriction, smooth implies flat and lfp, and the open-map statement. It does not use a Yoneda claim, smallness assumption or a representation criterion that is absent from a cited statement.

Step 8 uses the explicit field-extension clause of the products node, the perfect-field solvable unipotent/torus quotient statement, and the isomorphism-on-a-maximal-torus clause of solvable-torus-complements. The contradiction is the displayed quotient computation, so nonsolvability is not asserted without an argument. Step 9 checks all hypotheses of both new field criteria: smooth connected affine fibres, maximal self-centralizing T, the full nonzero weight set, central K_alpha, dimension difference three and nonsolvability. Step 10 is elementary except for the cited open-map statement: quasi-finiteness in the torus-lift node makes the lifted geometric point have finite residue extension, hence the same algebraically closed field. This proves descent with exactly the same geometric fibre, without assuming a separate unproved invariance of reductivity under transcendental extension.

Every proof step is below 2000 characters. I checked B1-B10: no proof in a new node, all objects introduced, definitions cited or given inline, single TeX escaping, honest searches, no false Mathlib leaf, blueprint references and project-source attachment search. C1-C8: all non-elementary inputs are nodes whose actual statements supply the use; exact quotes are supplied, off-unit foundational tools are declared in split_report.tool_uses, and no dependency reaches the item. D1-D5: no new node restates an item clause, and the item carries the neighborhood, rank, normalizer and assembly arguments. E1-E7: the hypotheses and small cases above were checked; no source error was found. No independent second-reader claim is made: this is the direct-delivery self-review authorized by the brief.
