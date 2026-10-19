# Worker report

Item: lem-trf-relative-duality-polynomial-chart. Group: Q89. Stage 1 only, direct delivery. The item statement is unchanged. Four new statement-only nodes, no Mathlib leaves.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-relative-duality-polynomial-chart.json: nine-step split, inherited source and searches retained, blueprint ancestry retained and searched.
- dag/nodes/sec-trace-formula/lem-trf-algebraic-shriek-calculus.json: statement; no Mathlib match. Polynomial construction of algebraic upper shriek, derived coinduction, composition, flat base change and localization. This is a tool on arbitrary bounded-below input complexes, not an existence theorem for a relative dualizing pair.
- dag/nodes/sec-trace-formula/lem-trf-algebraic-shriek-relative-perfect.json: statement; no Mathlib match. Relative perfection and scalar self-Hom for the algebraic complex; no diagonal class or comparison of presentations is asserted.
- dag/nodes/sec-trace-formula/lem-trf-relative-dualizing-pair-rigidity.json: statement; no Mathlib match. Uniqueness and scalar self-Hom assuming the pairs are already supplied; no existence claim.
- dag/nodes/sec-trace-formula/lem-trf-derived-basis-bbd-descent.json: statement; no Mathlib match. General derived-object descent over a set of basis opens with negative self-Ext vanishing.
- citations.json: verbatim statement certificates for every step/node citation.

## Attachments

None. The exact blueprint tag and coherent-relative-duality terms were searched under /home/ubuntu/weil-src-slopmaster2/WeilConjectures. The only relative-dualizing phrase hit is an unrelated finite-coefficient smooth-duality docstring in SixFunctors/Etale/Derived/SmoothDuality.lean:17, not the coherent polynomial-chart theorem. No compiler was run.

## WANTED

None. All sources used are in the supplied Stacks checkout. No SGA source is used.

## Audit findings and changes

The imported source list alone did not supply a split. In particular Tag 0E2X is a scheme-level existence result, whereas the affine proof needed here is dualizing.tex Tag 0E2E. Tag 0BZI's footnote proposes the canonical top-differential normalization but does not print its sign/lift calculation. The proof is accordingly marked agent-written: it expands the one-variable computation of 0BZJ and uses existing Koszul and resolution-homotopy nodes for the normalization, rather than pretending that the footnote proves every compatibility.

An unsubmitted draft had moved local existence and a refinement clause into new nodes and included base-change/smooth-locus conclusions that the item does not ask for. I discarded those draft nodes and rewrote the split: the item now carries the affine diagonal argument and the refinement calculation itself. Its four prerequisites are general duality/rigidity/descent tools. The inherited statement was neither strengthened nor weakened. All previous search logs are retained; no claim is made that the unused earlier base-change searches prove a theorem is in Mathlib.

## Unfinished work

None for this one-level stage-1 split. The four new nodes deliberately have statements and searches only, and remain unsplit for later workers.

## Searches and blueprint

I searched the full DAG for the Stacks tags 0BZI, 0BZJ, 0BZN, 0BZT, 0BZW, 0E2V, 0E2W, 0D6C, 0A70, 0A71 and 0C0F, and searched titles/statements for relative dualizing, algebraic shriek, BBD, gluing of derived objects, affine derived equivalence, derived Hom models and resolution homotopies. The blueprint_refs.py searches included BBD, relative dualizing, upper shriek algebraically, algebraic shriek, dualizing rigidity, 0D6C and affine derived. The BBD text hit is about an abelian heart, and the relative-dualizing blueprint hits are finite-coefficient pro-etale statements, so neither substitutes for coherent O-module duality.

Existing nodes are reused for affine derived equivalence, affine derived pullback, affine-morphism derived equivalence, finite-projective ordinary Hom models, finite-free sheaf derived-Hom models, K-projectivity, derived Hom bijections, open restriction of internal Hom, Koszul regular-sequence duals and homotopy uniqueness of augmented-resolution maps. In particular no new affine dictionary or new graph-Koszul lemma is created. Binary descent lem-sp-ringed-topos-binary-descent does not give descent over the possibly infinite affine basis, so it does not replace the BBD node.

For each new node I ran LeanFinder and LeanSearch with two formulations, a Loogle query and a Mathlib grep via the prescribed msearch.py, and read the returned types. Ordinary module dual/base-change, flatness/projectivity, generic categorical adjunction and ordinary sheaf-gluing hits do not imply derived coherent duality or BBD descent. Two Loogle patterns had unknown identifiers; their errors are recorded explicitly and the semantic searches still supplied both formulations. Exact queries, result summaries and digests appear in the nodes and searches.jsonl. No service-down result was turned into an absence claim.

Every new node inherits the exact ancestor lem-trf-local-term-locality and the full chain beginning with this item, lem-trf-flat-lci-canonical-adjunction and lem-trf-marked-nodal-dualizing-degrees. Its from.place names the semistable/marked-dualizing auxiliary construction in that ancestor. The inherited item place was already specific. same_as is empty after the searches. Off-unit existing statements are declared as generic tool uses; the curve-local-term geometric route is unchanged.

## Not duplicates

lem-trf-algebraic-shriek-calculus vs lem-trf-relative-duality-polynomial-chart: the new node constructs algebraic functors for arbitrary finite-type Noetherian maps and arbitrary input complexes, with unnormalized polynomial models and their calculus; it supplies no relative-dualizing pair, global gluing, or canonical differential normalization. The item constructs those using the calculus.

lem-trf-algebraic-shriek-calculus vs lem-trf-flat-lci-canonical-adjunction: the latter identifies a flat lci dualizing object with a determinant line in one degree and describes its regular-immersion adjunction; it is also an ancestor depending on this item. The new node is algebraic upper-shriek calculus for all finite-type Noetherian maps, without any lci or determinant-line conclusion. It does not cite that ancestor.

lem-trf-relative-dualizing-pair-rigidity vs lem-trf-relative-duality-polynomial-chart: both mention the pair definition at 0E2T, but the new theorem assumes two pairs have already been supplied and proves scalar self-Hom and a unique class-preserving isomorphism (0E2V/0E2W); the item asserts existence, a polynomial-chart construction and its refinement normalization, and does not assert uniqueness of all supplied pairs.

The relative-perfection and BBD nodes have no existing same-tag node in the shared DAG at the time of the search. As an additional conceptual comparison, lem-trf-derived-basis-bbd-descent vs lem-sp-ringed-topos-binary-descent: the existing result glues two opens and asserts no unique arbitrary-morphism gluing; the new result handles a whole basis, possibly on a non-quasi-compact scheme, under negative self-Ext vanishing and includes uniqueness of the descent solution.

## Review by Q89

I read the actual statements and proofs of duality.tex Tags 0E2T, 0E2U, 0E2V, 0E2W and 0E2X, dualizing.tex Tags 0BZI, 0BZJ, 0BZW and 0E2E, and the coinduction, flat-base-change, composition and localization lemmas at 0A70, 0A71, 0C0F, 0BZN, 0BZT and 0C0H. For the descent input I read cohomology.tex's BBD theorem 0D6C with its locally-given situation 0D67. The new finiteness node uses exactly the flat finite-type Noetherian case of 0BZW: bounded coherent, finite relative Tor amplitude and scalar self-Hom. Its hypotheses are not just finite presentation over an arbitrary base. The calculus node explicitly limits the composition/base-change isomorphisms to D+ and requires both rings in a base-change map to be Noetherian. The rigidity node assumes supplied pairs and uses 0E2V/0E2W; it is not an existence lemma under a new name. The BBD node spells out the basis refinement, identity/cocycle, set-indexing and negative-self-Ext hypotheses.

Step 1 uses algebraic-shriek-calculus for its actual polynomial formula and algebraic-shriek-relative-perfect for the three finiteness conclusions. The coefficient change from P to its free top-differential line is an explicit isomorphism with the ordered coordinate generator. Flatness, finite presentation and Noetherianness are available on the affine charts; no complete-intersection property of the quotient is assumed.

Step 2 uses only the calculus node's actual flat-base-change, surjective-coinduction and composition assertions. I checked the two coprojections: the first pulls back K and the resulting upper-shriek functor is for the second. The base change is R to A, which is flat, both are Noetherian, and the input is R[0] in D+. The multiplication map composed with either coprojection is the identity. The isomorphism is A-linear, so its value on 1 really produces the diagonal class and recovers the isomorphism by multiplication. This supplies the argument formerly hidden in an affine-existence node.

Step 3 uses the statements of new-affine-qcoh-derived-equivalence-core, lem-pc-affine-derived-pullback-tensor-tilde and lem-sc-finite-affine-derived-equivalence for the equivalence, pullback and quotient-algebra pushforward comparisons respectively. None is cited as an internal-Hom theorem. Instead the latter comparison is computed using lem-sc-affine-finite-projective-hom-model and lem-sc-derived-hom-finite-free-model, plus the two actual K-projective declarations. The first says only that ordinary total Hom models agree, and the second is what identifies the sheaf model as derived Hom. Noetherianness gives the bounded-above finite-free resolution of the finite B-module A, and flatness of the other A factor preserves boundedness of the target. Bounded-above/bounded-below makes the total Hom degree sums finite. Thus the argument does not commute sheafification with uncontrolled infinite products.

Step 4 cites the actual open-restriction statement for internal Hom and the open-restriction clause of affine derived pullback. It checks the defining pair condition after restriction and then uses the rigidity node, which really says unique class-preserving isomorphism. Consequently it gets a cocycle, not just some pairwise isomorphisms.

Step 5 uses rigidity's scalar self-Hom and the BBD node's exact descent assertion. Negative Ext is negative cohomology of O on each basis open and therefore vanishes. The chosen affine opens cover every intersection by smaller such opens. No quasi-compactness of X or finite subcover is assumed or needed. Pseudo-coherence and relative Tor bounds descend locally with the supplied identifications.

Step 6 uses the two restriction statements again, then ordinary degree-zero sheaf gluing: once all other cohomology of E vanishes, Hom into E is global sections of its zeroth sheaf. The products U times_S U need not cover the full product, so I explicitly add the complement of the closed diagonal, where the first internal-Hom argument is zero. This is exactly where separatedness is used. Matching on product overlaps is checked by smaller basis opens at diagonal points and by zero elsewhere; no unjustified derived-object gluing is used for the diagonal map.

Step 7 reads the actual regular-sequence Koszul dual theorem: it gives the dual conormal in degree one and the quotient-module action, not merely a rank assertion. Monicity proves t-g is regular even when the base has zero divisors. The source's coinduction transitivity is applied before contraction. The written coefficient-line calculation puts d(t-g) last and evaluates its conormal dual, so the extra positive and negative shifts cancel and the requested dual(t-a) tensor d(t-a) maps to 1.

Step 8 uses new-t4-augmented-resolution-lift-homotopy for the precise missing lift-independence assertion: the two scalar maps have the same augmentation to A, and its projective-source and exact-target hypotheses hold for the chosen resolution. It writes the induced triangular map of graph cones and the top evaluation. Derived coinduction transitivity, including its counits, identifies the resulting comparisons with class-preserving maps; the rigidity node is then applicable. The multi-variable comparison is the ordered tensor of those displayed two-term evaluations; the tensor and wedge permutations supply the usual signs. The common polynomial presentation exists by taking both sets of generators, so uniqueness gives comparison coherence.

Step 9 uses calculus's open-localization clause, the actual restriction lemmas, and rigidity to descend the model to P open in affine space. The formula denotes coinduction with its O_U-module action, not a claim that an arbitrary complex merely supported on U automatically is a complex on U. The resulting object is identified with the already constructed global pair. This verifies the full chart clause rather than only the globally affine case.

Small-case checks: identity maps give R in degree zero; the zero ring and empty chart give zero; zero variables give Omega^0=O and no shift. The graph element t-a is regular over any ring, so no reducedness or characteristic assumption slips into the normalization. Tensoring two graph resolutions has the sign from swapping their cohomological degree-one dual factors and the matching alternating top-form sign. Over a singular flat non-lci finite-type algebra, the construction remains a coherent complex and never asserts it is an invertible sheaf or a single shift. None of the four new statements claims pair existence, lci purity or base change over a non-Noetherian target.

I checked delivery-errors B--E against the final files: new nodes are self-contained statement-only inputs; existing Koszul and affine tools are reused; every non-elementary input has a cited statement and a verbatim certificate; the argument does not cite a finite-coefficient duality theorem as an O-module theorem; and each proof step is shorter than 2000 characters. The corrections from the first draft were removing its clause-restatement nodes, removing its extraneous conclusions, supplying the affine diagonal construction, citing BBD instead of treating derived gluing as elementary, and proving the one-variable normalization in the item itself.
