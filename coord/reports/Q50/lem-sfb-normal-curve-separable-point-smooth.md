## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normal-curve-separable-point-smooth.json: statement, now split in six steps; no exact Mathlib match.
- citations.json: all twelve step/node citations, quoted verbatim from their statements.
- searches.jsonl: five prescribed searches actually run for the item.
- report.md: this report.

No new nodes and no new Mathlib leaves.

## Attachments

None for the item. I searched lean/WeilConjectures for the exact blueprint tag and for normality, curves, separable residue fields and smoothness. Curve/NormalSmooth.lean proves a global perfect-field result, which does not apply to this item's arbitrary field. RingTheory/RegularLocalSeparableResidueSmooth.lean supplies the algebraic criterion already attached to lem-weil-pbc-regular-local-separable-residue-smooth, but does not itself give the curve's DVR conclusion or its affine-chart/local-dimension inputs. RingTheory/RegularLocalDimOneIffNormal.lean is likewise a tool for an existing node. None is an exact attachment for the item.

## WANTED

None for this split. All sources needed here are in literature/stacks-project. The inherited comment about de Jong's PDF concerns the parent's alteration argument; this local lemma is proved from the available Stacks sources.

## Audit of the item and route

The statement is unchanged and is exactly the normality-to-DVR and separable-residue smoothness implication in Varieties Tag 0B8Y, lemma-regular-point-on-curve. There is no statement dispute. The input had an empty proof. I supplied its affine-local argument and retained the recorded chapter/unit, created metadata and blueprint chain. The current blueprint's sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), is the ancestor direct-image route; the item's recorded chain explains its supporting role under the marked plurinodal/tame-normalization argument. No unit-level step is replaced. tools/blueprint_refs.py ancestor returned None, consistent with the inherited null from.node; I have not fabricated an ancestor. The existing detailed from.place is retained and split_report.blueprint explains the support role.

## Not duplicates

No new nodes. Whole-DAG tag and concept searches and blueprint_refs searches for regular point, discrete valuation, separable residue, normal curve, normal local, and smooth at led to reuse of the existing general algebraic and dimension statements. In particular, lem-sc-dimension-locally-algebraic states dimension at a point on an irreducible locally algebraic scheme, not local-ring dimension. I did not use it for the latter: the separate existing lem-weil-pbc-closed-point-dimension-local-ring supplies that bridge.

## Review by Q50

I read Varieties 0B8Y in varieties.tex, including its proof and the separable-field qualification. I read its cited Algebra 00PD (lemma-characterize-dvr), Algebra 00TV (lemma-separable-smooth) and Varieties 0A21 (lemma-dimension-locally-algebraic). I also read Algebra 00FN (lemma-Noetherian-permanence), 00OU (lemma-dimension-closed-point-finite-type-field), Morphisms 01T2 (lemma-locally-finite-type-characterize), 01V6 (lemma-smooth-characterize), and Schemes 01HV (lemma-spec-sheaves) and the open-subspace stalk description. There are no new-node sources to review. This follows 0B8Y's local argument and does not invoke an SGA source.

For step 1, I opened the statements of lem-weil-pbc-affine-open-spec-points, lem-weil-pbc-lft-affine-pairs and lem-weil-pbc-affine-open-stalk-localization. They give, respectively, the actual affine chart and point, finite type of its section algebra from the structure morphism, and the germ-preserving localization isomorphism. The chart prime is maximal because the singleton x remains closed in the open chart. The proof spells out preservation of the k-algebra structure: both scalar maps are the structural germ map. This is needed to identify the residue extensions over k, rather than just the abstract residue fields.

For step 2, I opened lem-weil-pbc-finite-type-algebra-noetherian and lem-weil-pbc-localization-noetherian. The base field is Noetherian (its ideals are zero and the unit ideal); the first cited statement then applies to S and the second to the multiplicative set S minus q. Thus the local ring really is Noetherian before 00PD is used. Locality is part of a scheme's locally ringed structure, and integral closedness/domain are explicit hypotheses, so no global normality of X is assumed.

For step 3, I checked the statements of lem-sc-dimension-locally-algebraic and lem-weil-pbc-closed-point-dimension-local-ring separately. Integrality provides irreducibility; finite type provides locally finite type; the item fixes dimension exactly one. The first cited statement gives dim_x X = 1. Cofinality of open neighbourhoods within U identifies this with the dimension at q of Spec S. Only the second cited statement, with its finite-type and maximal-ideal hypotheses verified in step 1, identifies that dimension with dim S_q. This repairs the tempting but invalid shortcut of treating topological dimension at an arbitrary point as local-ring dimension.

For step 4, lem-sc-normal-dim1-dvr says precisely that a one-dimensional Noetherian normal local domain is a DVR, and lem-weil-pbc-regular-local-dim-one-iff-normal gives regularity under the same Noetherian/local/dimension-one hypotheses. Those are all established before use. These are general algebraic tools, not new nodes restating this item's clauses, and neither assumes a perfect field or global smoothness.

For step 5, I opened lem-weil-pbc-regular-local-separable-residue-smooth: it assumes a finite type algebra over a field, a prime, and a separable residue field extension, and concludes smoothness at that prime iff the local ring is regular. The chart, its structural residue-field identification and regularity establish exactly those hypotheses. A finite separable algebraic extension is separable in the criterion's more general field-extension sense. The proof never replaces separability by perfection.

For step 6, def-weil-pbc-singular-ideal explicitly defines smoothness at a prime by an element g outside the prime with S_g smooth. It supplies a neighbourhood, not merely formal smoothness of a stalk. lem-weil-pbc-smooth-ring-map-iff-smooth-affine states the comparison with the formally-smooth, locally finitely presented scheme notion actually used by the item. Applied to k -> S_g it proves smoothness of the principal open. The open contains x exactly because g is outside q.

I recorded these general off-unit inputs in split_report.tool_uses with their roles; I did not set the maintainer-owned tool_uses field. Every cited statement was opened, and citations.json copies its words rather than words from its proof. The proof_deps list is exactly the union of step uses. No proof step exceeds 2000 characters or hides an additional local claim.

I tested the hypotheses against the following small cases. The origin of A^1 over any field has local ring k[t]_(t), a DVR, and the constructed principal open may be all A^1. A non-rational point of A^1 defined by a separable irreducible polynomial also fits; nowhere is kappa(x)=k assumed. For necessity of separability in the general inference, over k=F_p(a) the curve Spec(k(a^(1/p))[t]) is normal with a DVR at t=0 but is not smooth over k, and its residue field is inseparable, so it is excluded exactly where 00TV is applied. The generic point of a curve has a field as its local ring and dimension zero, but it is not a closed point: the proof never applies its closed-point dimension input there. The empty scheme and dimension-zero schemes are excluded by the curve hypothesis; singular nonnormal closed points are excluded by integral closedness.

All B--E checks have been applied: there are no unsplit new nodes or duplicate definitions, the statement is self-contained, exact source tags and labels are retained, mathematical hypotheses and scalar structures are checked, and every non-elementary assertion is taken from a cited statement. The item retains the five existing Mathlib search records, all of whose queries I actually reran with msearch.py. The two semantic phrasings give smooth-locus definitions, unramified residue results and elliptic good reduction, not this theorem; the recorded Loogle and AlgebraicGeometry grep have no hits. No fabricated or unavailable search is recorded as a negative result.

## Unfinished work

None in the one-level split. The independent maintainer review and eventual Lean implementation are outside this delivery's stage-1 scope.
