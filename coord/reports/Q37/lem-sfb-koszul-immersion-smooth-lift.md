# Stage-1 delivery: lem-sfb-koszul-immersion-smooth-lift

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-koszul-immersion-smooth-lift.json: item, split into the graph factorization, smooth-section regularity, regular-to-Koszul conversion, flat ascent, and composition. Mathlib searches found no matching immersion theorem.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-section-regular-immersion.json: one new statement-only theorem, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle, and source grep.
- citations.json: one full verbatim statement quotation for every citation in the item's five steps.

## Attachments

None. Searched the project source under lean/WeilConjectures for the exact blueprint tag and the immersion, smooth-section, and Koszul-regular notions. The regular-diagonal declarations require closed diagonals and fixed relative dimension, and do not state this item or the general section theorem. No Lean files were written or compiled.

## WANTED

None. All mathematical inputs are in the local Stacks source or existing DAG statements.

## Problems and corrections

The imported mathematical statement agrees with Stacks 067S. Its proof was empty. I supplied the source's graph proof and normalized doubled TeX backslashes in the item statement; no hypotheses or conclusion changed. The source of the new lemma is Tag 067R. The existing composition and flat-ascent nodes already state exactly the geometric results needed, so no new versions of those lemmas were created.

The inherited blueprint ancestor is null: tools/blueprint_refs.py ancestor reports None. I preserved that ancestry and its precise existing from.place, extended it for the new supporting fact, and searched the current whole blueprint via blueprint_refs.py (regular immersion, section smooth, smooth section, regular section, section-smooth, 067R, 067S, Koszul). No blueprint node states the new arbitrary-base smooth-section theorem. The current latest unit and its direct-images proof were read; this is the same inherited local-algebra prerequisite, with no replacement of a unit step.

## Unfinished work

The new smooth-section theorem is intentionally unsplit. Its future split follows Stacks 067R: a section is an immersion; after restricting to its closed-image neighbourhood, apply the flat finite-presentation fibre criterion and regularity of smooth local rings over fields, then spread the finite regular generators. That argument is not claimed elementary or moved into the item's proof. The present item uses its independently stated theorem as one ingredient alongside flat ascent and composition.

## Not duplicates

lem-sfb-smooth-section-regular-immersion vs lem-trf-smooth-curve-section-cartier: the existing result assumes separatedness and relative dimension one and concludes the Cartier property; the new result allows all smooth morphisms and varying local sequence lengths.
lem-sfb-smooth-section-regular-immersion vs lem-sc-standard-smooth-affine-diagonal-generators: the existing result treats standard-smooth affine diagonals in positive fixed dimension, not arbitrary sections or dimension zero.
lem-sfb-smooth-section-regular-immersion vs lem-sc-flat-polynomial-diagonal-differences-weakly-regular: the existing result proves injectivity for explicit tensor-product differences for a flat polynomial map; it gives neither general section immersions nor their local defining ideals.
lem-sfb-smooth-section-regular-immersion vs lem-sc-affine-regular-immersion-kernel-criterion: the existing result requires a supplied surjection, positive-length weakly regular equations, and a kernel-clearing element; the new theorem establishes local regularity for arbitrary smooth sections without those supplied data.
lem-sfb-smooth-section-regular-immersion vs lem-sc-etale-polynomial-diagonal-kernel-clearance: the existing result supplies a kernel-clearing element in an explicit tensor-product diagonal; it does not state the geometric smooth-section theorem.
lem-sfb-smooth-section-regular-immersion vs lem-sfb-smooth-marking-normalization-twist: the existing result concerns marked nodal curves over locally Noetherian bases, their Cartier divisors and line bundles; its smooth-section case is dimension one with extra assumptions.
lem-sfb-smooth-section-regular-immersion vs lem-per-regular-lci-geometric-calculus: the existing smooth-section clause assumes Noetherian schemes, separatedness, and a fixed relative dimension; none is available for the graph here.
lem-sfb-smooth-section-regular-immersion vs lem-sc-smooth-section-affine-coordinates: the existing result assumes a closed section and fixed pure relative dimension, and supplies coordinates. The new theorem also proves that an arbitrary smooth section is an immersion and covers locally varying dimensions without assuming global closedness.
lem-sfb-smooth-section-regular-immersion vs lem-pur-smooth-pair-regular-immersion: the existing result assumes a closed immersion between two smooth schemes over a common base. An arbitrary section is only an immersion a priori; closed-neighbourhood reduction and stability under restriction would still have to be supplied. The new theorem is the distinct general section input explicitly cited by 067S.

## Review by Q37

I read Stacks divisors.tex Tag 067S, its entire proof and the full statement/proof of Tag 067R, the statements/proofs of Tags 067P and 067Q, the definition in 063J, and more-algebra.tex Tag 062F. I also read the smooth-base-change and smooth-flat statements in morphisms.tex (01VB and 01VF). The new node is exactly the arbitrary-base regular-section theorem of 067R, with regular immersion expanded into local equations at source points. Nonzero final quotients are only required on a chart containing a source point. Nothing is asserted about a nonexistent source point on an empty scheme.

For Step 1 I opened def-pc-fibre-product: it provides both existence and the universal property, so the compatible pair (id_Z,i) gives the section and the factorization with both projection identities. This step uses no geometric graph theorem beyond that universal property. For Step 2 I opened lem-pc-proper-base-change: clause (2), not its properness clause, gives smoothness of the projection to Z along arbitrary j. The new section lemma has exactly a smooth morphism and a right inverse, both supplied here; it assumes neither a closed section nor separatedness. For Step 3 I opened lem-weil-pbc-regular-sequence-koszul-regular: its statement explicitly covers all finite tuples with successive injectivity, hence applies with M=A to the equations obtained in Step 2, including r=0. For Step 4 I opened lem-pc-smooth-flat and lem-sfb-koszul-immersion-flat-ascent-etale-descent: the former explicitly supplies flatness of p, and clause (1) of the latter applies to the given immersion j with flat target change p. Etale descent is not being used. For Step 5 I opened lem-sfb-koszul-immersion-composition: its full arbitrary-base, variable-length, no-flatness statement applies to s and b, which the previous steps established to be immersions with the required Koszul regularity. Its conclusion is the composite b s, exactly i by Step 1. Every cited statement is quoted verbatim in citations.json; no proof of another node is substituted for its statement.

I checked B through E of delivery-errors.md against these files. The new node introduces all of its objects and defines regularity through cited sequence and immersion definitions; it contains no proof. It is one genuine independent geometric input, not a restatement of the item: the item has an arbitrary Koszul-regular j, while the new lemma concerns sections and ordinary regularity. The remaining argument still needs flat base change, the algebraic regular-to-Koszul implication, and composition. No node for an elementary graph identity was made. The same-tag statements were read and distinguished above. All recorded new-node searches ran through msearch.py and their hits were read: they concern ordinary smooth maps/immersions and local smooth presentations, not regularity of sections. Loogle's sole smooth/immersion hit concerns manifolds, not schemes. No service outage was represented as a negative result.

I tested the new statement on the identity section (empty regular sequence), the zero section of affine space over a non-Noetherian ring (coordinate sequence), an etale section (locally an open immersion, length zero), and a disjoint union of smooth pieces with different relative dimensions. Empty S gives only vacuous pointwise assertions. I also checked the item when p is the identity, when j is the identity and i is a section, and when Z is empty. A nonseparated smooth target only requires local closedness of its section, exactly what the new statement says. All five steps are below 2000 characters (the largest is 433), and no long inline comparison lemma is hidden.

The off-unit smooth-base-change and regular-to-Koszul statements are declared as generic tool uses in split_report. They implement the very inputs of 067S rather than changing the surrounding cohomological route. No SGA source is used.
