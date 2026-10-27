## Worker report

Files written: dag/nodes/sec-trace-formula/lem-trf-tensor-double-hom-exact-comparisons.json (statement; split; no exact Mathlib match), citations.json, and this report. The sandbox also retains searches.jsonl and the item-local drafting script. No new nodes and no Mathlib leaves were created. No Lean was written or compiled and the shared repository was read only.

Attachments: none. Searches for the blueprint id and for double Hom, derived Hom and tensor triangulation in lean/WeilConjectures found generic derived tensor and Hom infrastructure, not a declaration giving every clause with these explicit two-target comparisons.

WANTED: none.

The item statement is unchanged. Its originally empty proof is replaced by six steps. Existing nodes give the signed tensor cone and integer shifts, unbounded K-flat and K-injective models, the cone criterion, and the arbitrary-single-target double-Hom cone comparison. The latter already suffices for unequal targets: apply it to the auxiliary complex J plus I and select one of its four invariant blocks. I did not create a lemma restating this elementary direct-summand specialization. The full integer-shift calculation is included; the raw first-Hom source shift alone should not be treated as a coherent contravariant triangulated structure, and the composite leading factor (-1)^m is essential.

Nothing is left unfinished in the split. The branches below it remain the existing DAG's responsibility.

## Not duplicates

No new nodes. lem-sf-double-hom-cone-comparison is reused rather than duplicated: its arbitrary target J plus I gives the mixed block required here. lem-weil-pbc-total-tensor-homotopy-cone-signs and lem-weil-pbc-total-tensor-integer-shifts already contain the tensor formulas, so no tensor-cone or shift node was introduced. The imported blueprint searches for Hom triangulated, tensor cone, 08JC, 064J, double, and derived tensor found no blueprint statement equivalent to this item's complete normalized two-target assertion; same_as remains empty.

## Review by Q74

I read the chapter and unit records, the current main-20261015 local-term-locality proof and its ancestor record, the item's created-from chain, and the source statements and proofs in more-algebra.tex Tag 064J (lemma-derived-tor-exact) and sites-cohomology.tex Tags 08JC (lemma-RHom-triangulated) and 0A8X (section-hom-complexes). These are the allowed Stacks route. The source's 08JC proof leaves the cone calculation implicit; the six steps spell out the needed two-target argument using existing signed cone data. This is agent-written expansion, recorded as such. No SGA source or alternate unit route is used.

Step 1 uses prop-pur-kinjective-resolutions-exist for arbitrary, functorially resolvable complexes on a small site; the identity-covering one-object site meets that hypothesis. def-pur-derived-internal-hom explicitly permits arbitrary source representatives with a K-injective target, twice, so it really computes both A and the outer Hom. lem-pc-kflat-resolution gives the extra flat-term condition required by lem-weil-pbc-kflat-fixed-tensor-triangulated. I checked that condition rather than assuming A itself is flat or K-flat. The last cited tensor-homotopy-cone-signs statement explicitly preserves arbitrary-endpoint quasi-isomorphisms when the other argument is K-flat, which justifies B tensor P to A tensor P without any hypothesis on A's cohomology.

Step 2 quotes precisely the second-variable sign of total-tensor-integer-shifts and the left cone map and projection equation of total-tensor-homotopy-cone-signs. Their statements say these things for arbitrary fixed A. Negating the projection equation proves the connecting equation, including the negative sign used by def-weil-abstract-derived-category. I added lem-pur-quasi-iso-cone-acyclic to justify the small cone-closure argument explicitly; acyclic endpoints give a quasi-isomorphism on their zero cohomology. This avoids citing merely the definition of K-flatness for a preservation theorem.

Step 3 uses only the actual Hom differential and the shift convention in the two definition statements. I expanded both sides of the chain-map equation. The exponent of the composite is mn+m(c+m)+m, reducing to m(n+c), and the two successive shifts produce a discrepancy 2ml, which is even. The inverse comparison has the correct domain because Hom is contravariant. These are elementary computations, not an unstated exactness result.

Step 4 uses the statement, not the proof, of lem-sf-double-hom-cone-comparison. That statement allows every target V, explicitly gives its s and theta maps, and imposes no K-injectivity. Taking V=J plus I is therefore legal even if these representatives were chosen independently. The four-block decomposition uses only binary biproducts: project the output and restrict each input, and invert by adding four maps. The Hom differential, source shifts, cone component sign, and their inverses preserve each block. Restricting a block-preserving isomorphism is thus an isomorphism on the mixed block. This is a short specialization of an existing node, not a new non-elementary lemma.

Step 5 uses the inclusion and negative-projection equations actually present in that same node's statement. They restrict blockwise as the maps themselves do. The normalized mixed comparison at m=1 is exactly the leading-minus composite from that node, and equals step 3's comparison. I also wrote the first reversal's cone differential to identify the two reversal signs instead of asserting vaguely that the connecting maps agree.

Step 6 applies lem-pur-rhom-well-defined twice, each time using a fixed K-injective target and its identity as the target quasi-isomorphism. The second application accepts the arbitrary source complexes from the first Hom; their being K-injective is unnecessary. The derived-category definition explicitly states that every distinguished triangle is isomorphic to a localized cone triangle, including the convention -p. Thus the earlier three-arrow cone isomorphism proves exactness by def-weil-triangulated-category. Naturality equations remain true after inversion by multiplying by inverses. All cited statements were opened and their full verbatim text is in citations.json for the respective uses; no inference is taken from an inaccessible proof of a dependency.

For small cases I checked zero complexes and the zero ring, the split zero-map cone, identity maps, m=0, m=1, m=-1 and the addition m+l=0. The sign law uses parity for every integer and works also in characteristic 2. The mixed-block method works for J=0 or I=0 and does not impose J=I. No products were asserted exact and no infinite sum/product interchange occurs. All six steps are shorter than 2000 characters. The definitions, theorem hypotheses, all clauses, source tags, blueprint fields, and unchanged statement were checked against delivery-errors B through E. Generic off-unit tools are declared with individual reasons in split_report.tool_uses; none replaces the contracting-correspondence route.

## Validation

The server review_split check passed with zero new nodes before the final cone-criterion citation was added. The final required deliver.py dry run follows and validates the final files.
