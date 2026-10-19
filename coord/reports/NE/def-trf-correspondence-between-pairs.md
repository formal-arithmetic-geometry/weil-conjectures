# Stage-1 worker report: def-trf-correspondence-between-pairs

## Files written

- `dag/nodes/sec-trace-formula/def-trf-correspondence-between-pairs.json`: definition, split; no whole-node Mathlib match. Its mathematical statement and hypotheses are preserved, with explicit constituent citations added.
- `citations.json`: `[]`; a definition has no proof steps, so no step/node citations are required.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. The existing `def-pc-fibre-product` is a Mathlib leaf, reused rather than recreated. No unit record was edited: this item is not the unit key node `sk-d-corr`.

## Attachments

None claimed. Read `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/SixFunctors/ProEtale/TraceFormula/Correspondence.lean` throughout the relevant declarations (lines 101–418): `AlgebraicGeometry.ProEtale.Correspondence`, `Correspondence.toProd`, `Correspondence.toProdSwap`, `Correspondence.intersection`, `Correspondence.ofEnd`, and `Correspondence.intersectionOfEndIso`. The last declaration bears the item's blueprint tag and covers its final geometric specialization, not every clause. The coefficient map in `Correspondence` uses the ambient `rightDerivedUpperShriek` with `HasBoundedBelowUpperShrieks`; the identity construction additionally takes `G : GeometricOperations A s` and its predicate `G.ctf`. The item instead uses the finite-coefficient constructible exceptional inverse image through `def-trf-admissibility`. No identification of these notions under exactly the item's hypotheses is given by the candidate declarations. The compressed sorry-map entries for the identity construction were also consulted; their conditional sorry-free status does not remove this mismatch. Accordingly neither the tag nor the partial constructions are asserted to close this node.

## WANTED

None. The current and original blueprint sources and all constituent definitions are available locally. No outside literature or SGA route is used.

## What was wrong or incomplete

The imported dependency list did not explicitly supply the fibre-product notion used for the ambient products, factor swap, intersection support and its projections. Reused the existing `def-pc-fibre-product`; no new definition is justified. Added bracket references for already-listed global conventions, scheme properties and derived pullback. No mathematical statement dispute or source error was found. The equalities with identity derived functors in the source use their canonical unit identifications; they are not a claim of strict equality between unrelated implementations.

## What could not be finished

Nothing in the stage-1 definition split remains. No Lean, compiler, Lake or build command was run, and no shared/live source, launcher, unit, or coordinator file was changed. Delivery is left to the second reader after the required dry run.

## Review by NE

I read the chapter record `sec-trace-formula`, unit record `sk-d-corr`, and the item's actual source in `literature/blueprint/master/blueprint/sec-trace-formula/sk-d-corr/def-trf-correspondence-between-pairs.md` (order 2276). I compared every clause with `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-corr/def-trf-correspondence-between-pairs.md` (order 2620); the mathematical text is unchanged. I also read the cohomological-correspondence definition and opposite-pair discussion in `literature/blueprint/slopmaster2/src/version/sketch/34_trace_formula.tex` (the section beginning at line 403 and the discussion around line 488). These confirm the ordering of the two legs. The unit's additional supported-class bijection is a different definition/lemma and is not silently included or reproved here.

For the opening setup I opened `def-weil-finite-field-fiber`, which supplies the global datum and finite coefficient rings; `def-trf-coefficient-conventions`, which supplies the small pro-etale coefficient categories and finite-Tor subcategory; and `def-weil-scheme-morphism-properties`, which explicitly directs finite type and separatedness to their definitions. This item introduces all four schemes and both complexes. It retains the finite level A = A_(E,n), with ell different from the residue characteristic, rather than changing to integral, rational, condensed or arbitrary coefficients.

For clause 1 I opened `def-weil-derived-pullback-tensor-hom` and checked its finite-level formula for Lf* on the ambient derived category. I opened `def-trf-admissibility` and checked that its exceptional inverse image is the constructible one, right adjoint on the bounded constructible finite-Tor category, not the strong ambient admissibility condition. The maps have the correct types: c2 goes to X, so it pulls K back, and c1 goes to Y, so exceptional inverse image applies to L. I also opened `def-trf-correspondence`: substituting Y = X and L = K gives exactly its coefficient morphism, leg labels and admissibility condition. That substitution is elementary and is not a new lemma or a restatement child node.

For clause 2 I checked the reversal explicitly: d1 maps D to X and d2 maps D to Y; therefore v has source Ld2* L and target Rd1! K. Calling the second correspondence opposite does not invert u, require it to be invertible, or manufacture v; it is separately specified data.

For clause 3 I opened the full statement of `def-pc-fibre-product`. It states existence with chosen projections, the universal property and uniqueness compatible with the projections. Thus it actually supplies the products and E(C,D), rather than merely naming a base-change operation. The factor exchange is the unique map with its two projections reversed. Its composite with the exchange in the other direction has the identity's two projections, so uniqueness gives its inverse. Similarly, the composites of tau d with p1 and p2 are d2 and d1, respectively. These are immediate calculations with the cited universal property and require no new non-elementary node. All support maps and projections remain specified.

For the final specialization I opened `def-trf-fixed-scheme`, whose displayed definition is exactly C times_(X times_s X,c,Delta_X) X with its two projections. Both projections of tau Delta_X are id_X, so tau Delta_X = Delta_X by uniqueness. Substitution in the definition of E gives that very fibre product with the same named legs; no set-theoretic replacement or unspecified support isomorphism is used. The identity coefficient is read through the canonical unit identifications for derived pullback and exceptional inverse image, as in the source. This is a defining specialization, not a hidden trace or pairing theorem. Because the item has kind definition, its `proof` and `proof_deps` stay empty, and there are no numbered proof steps to cite; `citations.json` is therefore empty.

I tested the construction on X = Y = C = D = Spec k with finite coefficient complexes: after the unit identifications the coefficient maps are simply K to L and L to K, and the intersection is Spec k. Empty C or D gives empty intersection, without any nonemptiness hypothesis. Taking a nonreduced support still uses the scheme fibre product, retaining its scheme structure. The endocorrespondence/diagonal specialization retains the same projections even when the fixed locus is nonreduced or empty. These tests reveal no missing properness, smoothness, invertibility of u, or support-reduction assumption.

I checked delivery-errors B–E against these files. B: no new node needs a self-contained statement, proof removal, Stacks tag, Mathlib match or blueprint ancestry; the item's existing metadata is retained, its searched same_as is empty, and its imported from remains null. C: every notion used in the definition has an actual definition dependency; none is cited as if it proved an extra theorem. There are no proof-step citations or off-unit theorem tools. D: no clause of the item was moved into a new node and no elementary swap/substitution fact was promoted to a node. E: all map directions, coefficient levels and adjoint domains were checked as above. No hypothesis was added and no conclusion weakened.

I searched the whole DAG and blueprint for correspondences, opposite pairs and fibre products using `rg` and `tools/blueprint_refs.py search`; this found the existing constituents and the broader sketch node, not another node stating the entire bundle. I ran the six recorded Mathlib searches using only the required msearch command and read their hits. In particular I inspected the ordinary module-sheaf setup in Mathlib/AlgebraicGeometry/Modules/Sheaf.lean, the point-triple construction in Mathlib/AlgebraicGeometry/PullbackCarrier.lean and the constructible-image theorem in Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean. They concern different objects and do not match this definition. The second LeanFinder phrasing and broader grep likewise yielded no match. All services returned results successfully; no unavailable query is being represented as a negative search.

## Second reading by NE

- Item statement: checked clause-by-clause against the current blueprint source (main-20261015, order 2620), the unchanged master source (order 2276), and the relevant `Correspondence` declarations in `Correspondence.lean` (lines 101–418); verdict: agrees, with no hypothesis or conclusion change.
- Definition setup and coefficient domains: checked the finite-field datum, $A=A_{E,n}$, separated finite-type schemes, and bounded constructible finite-Tor complexes against the cited convention nodes and source; verdict: correct.
- Correspondence and opposite-correspondence clauses: checked leg directions, domains and codomains of $u$ and $v$ against `Correspondence` and `toProd`/`toProdSwap`; verdict: correct.
- Fibre-product, exchange, intersection, specified-data, and diagonal clauses: checked against `def-pc-fibre-product`, `intersection`, `intersectionOfEndIso`, and the blueprint displays; verdict: correct, including empty and nonreduced supports.
- Proof steps and citations: this node is a definition, so it has no proof steps; `citations.json` is correctly empty and no elementary or non-elementary argument is hidden in a proof field.
- New nodes: none were created, so B1–B7 and per-node Mathlib/source checks are inapplicable; the reused `def-pc-fibre-product` is the existing reviewed Mathlib leaf and was not duplicated.
- Mathlib searches: inspected all six recorded queries and their logged results; verdict: no whole-definition match, and the fibre-product constituent is correctly reused.
- Edge cases: checked $X=Y=C=D=\operatorname{Spec}k$, empty supports, zero/identity coefficient maps, and nonreduced fixed loci; verdict: no missing nonemptiness, properness, smoothness, or invertibility hypothesis.

Changes made during this second reading: appended this review section only, documenting the checks and verdicts; no mathematical or node-file repair was needed.
