1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-derived-basis-bbd-descent.json`: unchanged statement; complete eight-step split following Stacks 0D6C.
- `dag/nodes/sec-trace-formula/lem-trf-derived-basis-local-hom-glue.json`: statement-only lemma on negative cross Hom and descent of morphisms between objects already defined globally; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-derived-basis-increasing-union.json`: statement-only continuous-ordinal gluing lemma, Stacks 0D6B specialized to schemes; no Mathlib match.
- `citations.json`: verbatim statements for every dependency cited in every proof step.

2. Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the item tag and the concepts BBD, negative extensions, derived gluing, complexes and increasing opens found no declaration stating the item or either new lemma. Upstream master was treated as reference material only. No Lean was written or compiled.

3. WANTED

None. The Stacks sources and their tag map are available locally.

4. Problems found and corrected

The item was statement-only. I checked its statement against Situation 0D67 and Theorem 0D6C in `literature/stacks-project/cohomology.tex`; it is correct, and I did not change it or its statement dependencies. This family of opens need not be a basis for the original topology, and neither compactness nor containment of a limit-stage open in one earlier stage may be assumed.

During self-review I removed two never-delivered proposed child files for uniqueness and finite-cover gluing: these would have repackaged clauses of the item. Uniqueness now follows by explicitly gluing maps and their inverse maps using the general global-object Hom-descent lemma. Successors use the existing `lem-sc-derived-open-gluing` (08DG), rather than creating a duplicate. The old local-Hom proposal required a basis on a different ringed space; I replaced its statement by the precise consequence of 0D66 through Topology 0D5Q actually needed here, for arbitrary intersection-refining covering families.

I wrote out the compatibility bookkeeping omitted at the end of Stacks 0D6C, including the limit-stage case where U is contained in no W_beta. At such a limit, U is covered by V contained in some earlier stage, and the maps are shown independent of the index before they are glued. All proof steps are shorter than 2000 characters (the largest is 1046), and no hidden comparison lemma is left in a long step.

The first delivery attempts failed the search-log check because I mistakenly used new-node IDs as the search command's item argument. I then ran the relevant searches under the assigned `Q103 lem-trf-derived-basis-bbd-descent` item and recorded their actual results. No log was synthesized or copied. The current child records are generated from the twelve relevant entries in this item's `searches.jsonl`; full outputs are preserved under `work/search-*.txt`. Both statements have two semantic phrasings, LeanSearch, a valid Loogle substring query and source greps. Earlier item search records are retained. The earlier grep using `Mathlib/Algebra/Homology` as a subdirectory was superseded by correctly relative `Algebra/Homology`, `CategoryTheory/Sites` and `AlgebraicGeometry` queries; I confirmed these directories exist. Related hits concern ordinary sheaf/scheme gluing, general prestacks, t-structure vanishing or localized-complex representatives; their displayed signatures do not state either lemma.

The item's original blueprint ancestry is retained, and each new node prepends this item to its full inherited via chain. Neither the unit nor the chapter was edited. The off-unit binary derived-gluing citation is declared as a generic tool in `split_report.tool_uses`.

5. Unfinished work

No gap remains in the one-level split. The two new nodes are intentionally unsplit statement-only inputs. They have no proof, proof dependencies or hidden proof sketch in their statements.

## Not duplicates

Whole-DAG searches by 0D66, 0D68, 0D6A, 0D6B, 0D5Q and the exact source labels found no pre-existing node for the two new inputs. Whole-blueprint searches using `tools/blueprint_refs.py search` for these tags, negative extensions, increasing union, vanishing/gluing and finite-cover solution concepts found no blueprint duplicate. I opened the nearby candidate statements before choosing the final dependencies.

lem-trf-derived-basis-local-hom-glue vs lem-sc-derived-hom-mayer-vietoris: the existing statement is the binary-open long exact Hom sequence; the new statement is arbitrary-family Hom descent plus negative cross Hom propagation, with no fixed two-open cover.
lem-trf-derived-basis-local-hom-glue vs lem-sc-derived-open-hom-scalar-mayer-vietoris: the existing statement supplies a scalar-linear boundary and its image in a two-open sequence, not the arbitrary-cover negative-Hom criterion.
lem-trf-derived-basis-local-hom-glue vs lem-pur-degree-zero-derived-map-gluing: the existing result is for finite constant coefficients on the etale/pro-etale site and objects locally concentrated in degree zero. The new result is for structure-sheaf modules on the Zariski space and arbitrary unbounded objects with negative cross Hom vanishing.
lem-trf-derived-basis-local-hom-glue vs lem-sc-derived-open-restriction-iso-descent: the latter descends natural isomorphisms of functors through one open restriction; it is not descent of maps between two fixed global complexes over a covering family.
lem-trf-derived-basis-increasing-union vs lem-pc-complex-hocolim-colimit: the existing result compares a countable telescope with a termwise colimit of an already strict sequence on one ringed site; the new result constructs compatible global derived objects over a continuous ordinal chain of different open subschemes.
lem-trf-derived-basis-increasing-union vs lem-sc-derived-k-injective-restrict-open: restriction of one K-injective complex is K-injective in the existing statement; it supplies neither strictification nor a compatible global object on an ordinal union.
lem-trf-derived-basis-increasing-union vs lem-sc-derived-open-gluing: binary gluing has a single overlap isomorphism and a two-open cover; it does not handle a continuous ordinal chain with simultaneous compatibility of every restriction.

Neither new node is a clause of the item: the Hom input assumes both global objects already exist and constructs no descended object; the ordinal input is effectiveness only for an increasing continuous chain, which still leaves the item's successor gluing, all original-basis identifications, their equations and uniqueness to prove.

## Review by Q103

I read Stacks `cohomology.tex` Situation 0D67, Lemma 0D66(2), Lemma 0D68, Remark 0D69, Lemmas 0D6A and 0D6B, Theorem 0D6C, and the binary-gluing lemma 08DG. I also read `topology.tex` Lemma 0D5Q and checked the labels in `tags/tags`. I read the assigned chapter and unit, the inherited ancestry through the polynomial-chart duality item, the definition statements `def-pc-scheme` and `def-pc-derived-category`, and every final cited statement. The item is the scheme specialization of the ringed-space theorem, with the unbounded category and all restriction/cocycle assumptions retained. In particular, Hom(K_U,K_U[i]) means the Ext group appearing in the source.

For the new Hom lemma, 0D5Q produces f:X->Y whose basis inverse images are exactly the chosen opens, even when they are not a basis for X. With O_Y=f_*O_X, 0D66(2) gives negative cross Ext on all inverse-image opens and a sheaf of Hom groups. An O that is a union of chosen opens is such an inverse image. Inclusion-compatible maps agree on overlaps because those overlaps are covered by smaller chosen opens; the Hom sheaf then gives exactly the stated bijection. Thus the formulation retains every necessary hypothesis and is not an assertion that arbitrary derived maps always form a sheaf. For the new ordinal lemma, I compared the increasingness, continuity at every non-successor (including zero), set size, negative self Hom hypothesis, transition maps, cocycle and conclusion equation directly with 0D6B. No boundedness or quasi-compactness was added.

Step 1 uses only the stated Hom bijection and vanishing clause of the new Hom node. The source and target are locally isomorphic to K_U, so the required negative cross Hom vanishes. I checked the inverse compositions on every chosen open; injectivity, not an uncited locality assertion, makes them identities. This also yields the global negative self Hom needed at ordinal limits.

Step 2 uses that same statement on the overlap, with a covering family made from basis members lying in the overlap. Refining U_1 intersect U_2 proves this family covers and refines intersections. I checked the formula (s_2,V)^(-1)s_1,V and its restrictions; on triple overlaps the middle identification cancels, so the comparison maps satisfy the cocycle without an extra theorem.

Step 3 sets up a set-sized transfinite induction, its zero base, invariant and comparison maps. It again uses the Hom node to identify comparison composites because they have identical restrictions. At the empty base, the only sheaf of modules on the empty scheme is zero, so its derived category and all maps are zero as required.

Step 4 cites `lem-sc-derived-open-gluing`. Its statement explicitly supplies an object and both restriction isomorphisms with the specified overlap transition, for arbitrary derived objects and a two-open cover; no perfectness or quasi-coherence is assumed. I checked that the transition from Step 2 has precisely the needed direction. The two definitions of t_V agree where both apply, and the restriction equation follows from the original cocycle.

Step 5 uses the new Hom node on each original U and the refinement C_U by the two gluing opens. Its cross negative Hom hypothesis holds because both restrictions identify with K_V. I checked the inverse-map argument and, on C_U', the equality rho^U_U' s_U = s_U'. This fills all chosen-open identifications, not merely the two cover members.

Step 6 uses exactly the statement of the ordinal-union node: W_beta are increasing and continuous with W_0 empty, the induction supplies negative self Hom, and Step 3 supplies all pairwise maps with the cocycle. Its conclusion gives r_beta satisfying the displayed compatibility equation. It does not by itself identify F_lambda with every K_U; that is the next step's work.

Step 7 verifies that the refinement C_U covers even when U is contained in no W_beta. It checks index independence using both displayed comparison equations, takes the maximum of two earlier indices to verify inclusion compatibility, and invokes the Hom node with locally isomorphic source/target. Step 8 checks the two solution maps on C_U', uses Hom injectivity to prove their equality, and checks compatibility with every earlier-stage comparison. Only then is the transfinite induction concluded at W_kappa=X and uniqueness applied from Step 1.

I tested the new statements and uses on the empty scheme/empty family, the zero object, one open equal to X, repeated/constant stages, a successor ordinal, and a limit cover such as the countable disjoint union of points with finite initial unions (where X is contained in no earlier stage). I also checked a covering family that is not a topological basis: {X} on an arbitrary scheme. In that case negative Ext on X controls only the permitted unions, not all smaller opens; the new Hom statement correctly quantifies only those unions. In a one-open cover both uniqueness and existence reduce to the given object and identity. None of these cases needs compactness or boundedness. No new statement is false, no target statement is weakened, no source route is replaced, and no SGA source is cited.
