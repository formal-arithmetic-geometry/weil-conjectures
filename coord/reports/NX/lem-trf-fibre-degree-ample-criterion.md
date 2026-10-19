1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-fibre-degree-ample-criterion.json`: split item; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-surjective-ample-reflection.json`: new statement-only node, Stacks 0B5V; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-proper-integral-curve-ample-degree.json`: new statement-only node, Stacks 0B5X; no Mathlib match.
- `citations.json`: one verbatim statement quotation for each node in each step's `uses`.

2. Attachments

None. Searches of `WeilConjectures/` in the read-only slopmaster2 source found no declaration tagged with this item, no componentwise ampleness criterion, and no finite-surjective ampleness-descent theorem. `AlgebraicGeometry.Scheme.isAmple_iff_degree_pos` in `WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean:1519` is a related result: it assumes smoothness of relative dimension one and `GlobalSectionsBijective k X`. Those hypotheses are absent here, so it neither attaches the item nor covers the new general integral-curve node. The upstream master checkout is reference material only.

3. WANTED

None: the sources needed are in `literature/stacks-project/`.

4. Corrections and source comparison

The item had an empty proof. Its mathematical statement is unchanged; I made explicit its citations for properness, reduction, irreducible components and module pullback, and removed the unused statement dependency on `def-sc-ample`, since the item already specifies absolute ampleness. There is no STATEMENT-DISPUTED finding.

The proof follows the finite-surjective-cover argument of Varieties Tag 0B5Y, but uses normalized components in that cover directly. This gives exactly the normalized-degree formulation requested in the item, without a separate degree-pullback identification. The original source field mentioning 0AYZ is retained as inherited provenance; the proof does not need that tag. Step 2 verifies the normalized components using the existing `lem-sc-normalization-exists`. Coherent Tag 0B5V applies over the original field, which is Noetherian. Varieties Tag 0B5X applies to integral proper curves over arbitrary fields; smoothness and geometric integrality are not assumed.

I corrected the first draft's missing comparison between component ampleness and normalized-component ampleness by replacing its cover with the normalized-component cover. I also expanded its finite-cover/properness justifications, wrote out both directions for finite disjoint unions, restored the item's original blueprint ancestry (no self-entry), and replaced related-but-unequal `same_as` metadata with `[]`. The dry run identified missing chapter/unit metadata, the exact required report heading, a same-tag duplicate comparison, and non-verbatim citation snippets. These have been repaired; quotes now preserve the node statement text exactly, including TeX and newlines.

The two new nodes carry statements only, with no proof sketches or proof dependencies. Their searches were actually run via `msearch.py`; `searches.jsonl` records the queries and returned names. Each has LeanFinder and LeanSearch searches with a second mathematical phrasing, Loogle queries including the valid quoted substring `"IsAmple"`, and Mathlib source grep. Earlier weak identifier/name-only queries are retained as the real searches they were, alongside the subsequent full mathematical queries. Returned morphism/normalization, quasi-affine and polynomial-degree hits do not state these results. The item also has its own two componentwise semantic phrasings. Blueprint tag/keyword searches and whole-DAG searches found the related existing nodes discussed below, but no statement of either new input with these hypotheses.

5. Unfinished work

None in the stage-1 split. The two statement-only children intentionally remain unsplit for later stage-1 work. Required delivery preflight and push are performed after this report.

## Not duplicates

- lem-trf-proper-integral-curve-ample-degree vs lem-pc-ample-positive-degree: the new node is the arbitrary-field proper integral curve criterion, including singular or nonsmooth curves; the existing node assumes a smooth projective curve. It cannot be applied to a normalization over an imperfect field without extra hypotheses.
- lem-trf-proper-integral-curve-ample-degree vs lem-sc-ample-positive-degree: the existing node gives only the forward implication for the Hilbert degree over an algebraically closed field, whereas the new node gives both implications for Euler-characteristic degree over any field on an integral proper curve.
- lem-trf-proper-integral-curve-ample-degree vs lem-sc-positive-degree-ample: the existing node assumes a smooth connected curve over an algebraically closed field and gives one implication; the new node removes those field/smoothness hypotheses and gives the equivalence for proper integral curves.
- lem-trf-finite-surjective-ample-reflection vs lem-weil-pbc-pullback-ample-invertible: the existing node proves only ascent under affine pullback; 0B5V also descends ampleness along finite surjective maps of proper schemes over a Noetherian ring.

The integral-curve criterion is the supporting lemma explicitly invoked by the source 0B5Y. It does not restate the item's component gluing/reduction/normalization argument: Steps 1–5 carry that argument, including the nilpotent and zero-dimensional cases. The other new node is a dimension-independent descent theorem, also explicitly invoked by 0B5Y.

## Review by NX

I read `coord/delivery-errors.md` B–E in full, the unit/chapter records, the three-level rule in SETUP, the current blueprint's related degree lemmas, and the local Stacks passages. For the item I read Varieties Tag 0B5Y (`lemma-ampleness-in-terms-of-degrees-components`), whose proof constructs a finite surjective component cover. For the new descent node I read Coherent Tag 0B5V (`lemma-surjective-finite-morphism-ample`), including the Noetherian-base and properness hypotheses. For the new integral curve node I read Varieties Tag 0B5X (`lemma-ample-curve`), including both directions of its section/cohomology proof. I read Varieties Tag 0BXR (`lemma-normalization-locally-algebraic`) to check the normalized cover. The tag/label pairs were checked in `literature/stacks-project/tags/tags`.

Step 1 cites finite-type Noetherianity for Noetherian X, finite-component finiteness for enumeration, the reduced-induced-closed-subscheme theorem for the component structures, and the integral definition for their integrality. The dimension definition justifies the inherited bound on closed subspaces. The scheme-sobriety statement explicitly gives the generic point used to see that a zero-dimensional component is a point. The finite closed decomposition then shows those point components are isolated. A field is Noetherian by the definition, since its only ideals are zero and the unit ideal.

Step 2 cites the closed-immersion-finite, finite-proper and proper-composition statements: together they give proper finite-type integral components over k. The normalization-existence node explicitly states finiteness, surjectivity, properness and dimension equality under exactly those hypotheses. Integrality of each normalization follows on the affine charts in its definition: the integral closure is a subring of a field, and the charts share the original generic point. No assertion that a normal curve over an imperfect field is smooth is used.

Step 3 cites finite composition and the binary finite-coproduct statement, applied inductively to the finite family. Surjectivity follows from the covering components and the surjectivity clause of Step 2. Finite-proper and proper-composition give properness of the whole source Z. Thus every hypothesis of the new 0B5V node is established, including properness of both X and Z over the Noetherian ring k. The empty case is handled directly before applying the nonempty cover argument.

Step 4 checks the ampleness definition in both directions on a finite disjoint union. Restriction of an affine witnessing locus is affine because the summand inclusion is a closed immersion and the cited closed-immersion-finite statement says it is affine. Conversely the sheaf axiom extends a section by zero on the other summands. These are few-line deductions from the two cited statements, so this step is elementary. Step 5 shows that a reduced zero-dimensional component is Spec of a field, trivializes its one-dimensional module, and takes its nonzero section with exponent one; this directly satisfies the ampleness definition and is also elementary.

Step 6 cites the invertible-pullback theorem, whose clauses (1) and (2) give precisely invertibility and the composition isomorphism used for the restrictions. The new 0B5X node is applied only to the integral proper dimension-one normalization already checked in Step 2. Its degree is the chi-difference in the existing degree definition, and its ampleness is the same absolute notion as in the item and 0B5V. Combining the preceding equivalences proves both directions. I read the statements of every cited node; citations.json now contains their verbatim text rather than paraphrased sentences.

For small cases I checked X empty; a finite nonreduced scheme such as Spec(k[epsilon]/epsilon^2), whose reduction is one point and whose line bundles are ample; a curve with a disjoint point component; a nodal integral curve; and a reducible curve with degree zero or negative on one component. The latter fails ampleness because the corresponding normalized component fails the integral-curve criterion, even if total degree is positive. On P^1, O(d) has the predicted answer for d positive, zero or negative. For imperfect fields the proof uses only integral normalized curves, so it avoids a nonexistent smoothness implication. For a finite field extension K/k, P^1_K viewed over k has deg_k O(1)=[K:k]>0, consistent with the arbitrary-field node. For finite-surjective descent I checked a reduction map as well as a finite field extension; neither injectivity of structure sheaves nor flatness is being assumed. No new node is elementary, a duplicate with matching hypotheses, or the whole item moved to a child. All six steps are below 2000 characters, and no comparison lemma is hidden in a long step.
