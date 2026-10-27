## Worker report

Files written under dag/nodes/sec-six-functors-basics/:

- lem-sfb-stable-moduli-regular-universal-atlas.json: the item, split into seven steps; statement unchanged.
- lem-sfb-arithmetic-nodal-curve-stack-smooth.json: statement-only unsplit lemma, no Mathlib match.
- lem-sfb-arithmetic-stable-open-bounded.json: statement-only unsplit lemma, no Mathlib match.
- lem-sfb-arithmetic-stable-isom-finite.json: statement-only unsplit lemma, no Mathlib match.

Auxiliary sandbox files: citations.json, retained searches.jsonl and this report. No Lean, compiler, library build, repository edit, launcher edit or delegation was used.

Attachments: none. Searches of lean/WeilConjectures/ for the exact blueprint tag and stable-curve/moduli terminology found no declaration giving this arithmetic theorem. Neither a partial statement nor a sorried declaration was treated as finished.

WANTED: none for this split. Its sources are in the local Stacks checkout. The existing framed-smoothing node also lists Morrison, but its smoothing conclusion is supported by its cited local deformation example; this split does not require downloading Morrison.

The empty proof needed an arithmetic argument. Existing nodal-stack, stable-locus and finite-Isom nodes fix a field base. They cannot be applied over Spec Z or to mixed-characteristic test schemes. The three arithmetic inputs correct that gap without assuming the atlas, regularity, nerve or dense-open conclusions being proved. The proof constructs a finite affine atlas, describes arbitrary-base pullbacks as finite Isom schemes, and inducts on the nerve.

The inherited blueprint ancestor is null because the creation chain is broken, as blueprint_refs.py ancestor confirms. The documented supporting route in from.place runs through the stable Picard theta and stable level parameter prerequisites to det-thm-sf-ctf-stability-direct-images. I retain null for from.node, as the tool explicitly documents for a broken chain, and retain the inherited place and via chain. I read its current source at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.md: clause (3) is direct-image stability, and the imported dependency chain supplies this supporting moduli input. The current blueprint text is a statement, not an additional proof of the moduli construction. The chapter and unit records were read and left unchanged. Whole-blueprint searches for nodal, stable and 0E9C found no arithmetic atlas or any of these three inputs. I searched the whole DAG by keywords and each source tag and read the related statements distinguished below.

No statement dispute was found. Nothing remains unfinished at this one-level split: the three new nodes are intentionally statements for later workers, with empty proof and proof_deps.

## Searches retained and read

I read searches.jsonl before reusing it. The new nodes record the exact msearch.py query texts with their actual tools, results and verdicts. Each has LeanFinder and LeanSearch in alternate phrasings, Loogle and grep. No unavailable service was recorded as evidence of absence. Hits concern scheme smoothness/etaleness, formal unramifiedness, generic compactness, elliptic-curve isomorphisms and interpolation. They do not assert algebraicity of nodal-curve moduli, boundedness of the arithmetic stable genus locus, or Isom representability for varying stable families over arbitrary schemes. Generic scheme calculus is cited through existing nodes, not recreated. The item's own generic atlas and Isom searches also do not give this moduli theorem. There are zero new Mathlib leaves.

## Review by Q51

I reviewed delivery-errors B--E with the sources and node statements open. For the item I read moduli-curves.tex theorem-stable-smooth-proper (0E9C) and lemma-stable-curves-smooth (0E79), lemma-stable-curves-deligne-mumford (0E7A), lemma-stable-separated (0E9A), lemma-stable-quasi-compact (0E9B), and lemma-smooth-dense-in-stable (0E87). They give the smooth separated arithmetic DM moduli problem and the dense open, while the split constructs its required regular universal scheme presentation.

For lem-sfb-arithmetic-nodal-curve-stack-smooth I read quot.tex theorem-curves-algebraic (0D5A), moduli-curves.tex lemma-nodal-curves (0DSY), lemma-nodal-curves-smooth (0E00), lemma-smooth-dense (0E86), and the chart smoothness definitions/composition (075U, 075V). The ambient family can be an algebraic space with geometric fibres of dimension at most one. The nodal predicate uses nonempty pure one-dimensional fibres, with no connectedness or genus assumption. Nonemptiness is an additional open condition, not a claim that every ambient family has nonempty fibres. Arbitrary smooth charts, even nonsurjective ones, have smooth composite to the base. Smooth-family openness commutes with base change. The exact ambient-family, nodal and algebraic-stack definitions are cited; no proof sketch is hidden in the statement.

For lem-sfb-arithmetic-stable-open-bounded I read lemma-stable, lemma-stable-curves (0E76), lemma-stable-one-piece-per-genus (0E78), and lemma-stable-quasi-compact (0E9B). Stability is an open condition, fixed genus is an open-and-closed decomposition on that locus, and tricanonical boundedness is arithmetic. The projective-bundle convention is significant: the relatively ample dualizing line and fixed-genus tricanonical embedding yield a scheme embedded in a finite-rank projective bundle. Thus the locus is the same groupoid as the item's, rather than an algebraic-space variant. I made algebraicity and quasi-compactness of the topological point space explicit. No global projective frame or globally free module is asserted on a disconnected base.

For lem-sfb-arithmetic-stable-isom-finite I read lemma-curves-diagonal-separated-fp (0DSQ), lemma-stable-curves-deligne-mumford (0E7A), lemma-stable-separated (0E9A), spaces-morphisms.tex lemma-locally-quasi-finite-separated-representable (0418), and spaces-more-morphisms.tex lemma-characterize-finite (0A4X). A proper unramified diagonal is finite; its tests over schemes are schemes. There is no field or Noetherian hypothesis on those tests. The statement includes natural representing bijections and the universal isomorphism; it neither chooses isomorphism-class representatives nor asserts the atlas theorem.

Step 1: the new nodal and stable-open statements give algebraicity, openness and arithmetic smoothness. The finite-Isom statement gives the unramified diagonal on scheme tests. lem-sfb-unramified-diagonal-etale-atlas explicitly supplies the etale surjective scheme atlas under that hypothesis. lem-weil-pbc-open-immersion-etale and lem-sfb-stack-chartwise-smooth-etale-calculus give the smooth composite of the atlas with the open nodal inclusion; the new nodal statement permits exactly this nonsurjective smooth chart. No inference from regular geometric fibres to regularity of the arithmetic base is used.

Step 2: lem-pc-fppf-affine-open-cover gives affine opens of the atlas. Open-immersion etaleness and the chart calculus make their maps etale, hence flat locally finitely presented. lem-sfb-stack-point-topology-flat-lfp-open makes their images open, and the new stable boundedness statement selects finitely many images covering the point space. lem-weil-pbc-scheme-coproduct-family supplies the scheme coproduct and its disjoint open cover; lem-weil-pbc-finite-affine-coproduct-spectrum makes this finite coproduct affine, and lem-weil-pbc-affine-scheme-qcqs gives quasi-compactness. The chart calculus includes the disjoint-source etale clause and source locality. Local finite type over affine Spec Z gives an affine cover by finitely generated Z-algebras, from which quasi-compactness selects a finite subcover, exactly the criterion of def-weil-finite-type-morphism. I replaced a terse claim about affine morphisms with this explicit cover argument. The moduli-groupoid definition identifies the map from U with the stable family C_U.

Step 3: on S times_Z U the two pullbacks are stable families of the same genus. The arithmetic Isom statement supplies a finite scheme and its universal isomorphism with natural representing bijections. The triples definition in def-sfb-stable-pointed-moduli-groupoids identifies it with S times_M U. The chart calculus supplies arbitrary-base etaleness and surjectivity. S need not be reduced, Noetherian or finite type. A field-only Isom statement would be insufficient precisely here.

Step 4: the induction starts from affine finite-type smooth U_0=U. The arithmetic Isom statement presents U_n over U_(n-1) times_Z U. lem-weil-pbc-fibre-product-affine-spectra makes the base affine and clause (b) of lem-weil-pbc-finite-morphism-permanence makes U_n affine. def-weil-finite-integral-morphism and the written module-generator argument imply finite type of its finite map, and lem-sfb-finite-type-composition-base-change gives finite type over Z. The chart calculus proves the forgetting projection etale and therefore all earlier projections by induction. I explicitly added permutations of factors, with inverse/composite Isom coordinates, to cover the last projection as well. Etale maps are smooth and smooth composites are smooth by that same cited calculus. The triples convention identifies the objects in the induction, not just their point sets.

Step 5: lem-weil-pbc-finite-type-over-noetherian includes Spec Z and gives Noetherianity. lem-weil-pbc-smooth-ring-map-iff-smooth-affine is exactly the scheme/ring smoothness comparison needed for affine U_n. lem-weil-pbc-regular-ring-smooth-ascent assumes a regular base ring, which I checked for Z by its localization at (0), namely Q, and at (p), the one-dimensional local principal ideal ring with maximal ideal generated by p. def-weil-regular-scheme gives the local-ring conclusion. I read algebra.tex lemma-regular-goes-up (07NF). The two ring results are declared generic tools in split_report.tool_uses; they do not replace another unit's geometric route.

Step 6: the new nodal statement supplies the base-change-compatible smooth-family open. I opened lem-sfb-stable-curve-framed-trait-smoothing and lem-sfb-trait-specialization-etale-chart-density: the former gives the stable power-series trait with smooth generic fibre, and the latter permits nonsurjective etale charts and prescribed geometric lifts. Choose a projective frame over the algebraically closed field and forget it after smoothing. The chart calculus makes U_n -> U -> M etale and gives the same after geometric field base change. Density is proved separately in each algebraically closed field fibre by the trait statement; continuity sends its specializations back to U_n. I do not assume that an arbitrary base change preserves density. This includes vertical characteristic-p points.

Step 7 is elementary: in the 2-fibre-product definition the third Isom on triple overlaps is phi_12 composed with phi_01. Associativity gives the cocycle and identity arrows give degeneracies. No existence/descent assertion is smuggled into the groupoid definition.

I tested g=2 and positive characteristics, including 2. Nodal fibres may be disconnected in the first input; stable fibres are geometrically connected in the second. Smooth stable curves are included, while curves with nodes are not called smooth. Empty test schemes, disconnected and nonreduced bases are permitted. The Isom scheme of nonisomorphic families may be empty, hence finite unramified; it is not claimed surjective. When C=D, automorphisms need not be trivial, so a coarse moduli scheme cannot replace the groupoid. At n=0 the construction is U; at n=1 and n=2 it is respectively a universal Isom and composable-Isom scheme. Only finite coproducts of affines were called affine; no intersection-of-affines claim occurs.

Every new node introduces its objects and cites its definitions or defines a notion inline, has empty proof/proof_deps and no proof sketch, correct created.item and inherited chapter/unit, and explicit blueprint place/via and same_as (from.node remains null for the inherited broken chain). Tags and labels were checked against tags/tags. The new inputs are substantial algebraicity/deformation, arithmetic boundedness and finite diagonal results, not elementary facts or clauses renamed from the item. The proof retains the atlas construction, arbitrary-base comparison, nerve induction, regularity, density and cocycle argument. Every non-elementary step is shorter than 2000 characters. citations.json was refreshed after the edits and has a literal statement excerpt for every step/node pair.

Server srvcheck completed review_split PASS and check_dag OK before this report. The final deliver.py dry run checks the complete delivery and report before pushing.

## Not duplicates

lem-sfb-arithmetic-stable-isom-finite vs lem-sfb-proper-curve-automorphism-scheme: the existing theorem treats automorphisms of one fixed proper algebraic space over a field; the new theorem treats Isom between two varying stable families over any scheme and gives finite unramified representatives.

lem-sfb-arithmetic-stable-isom-finite vs lem-sfb-labelled-stable-isom-unramified: the existing theorem assumes a locally Noetherian base and concludes separated finite type unramified, without finiteness; the new unpointed theorem drops the base restriction and gives finite Isom.

lem-sfb-arithmetic-stable-isom-finite vs lem-sfb-projective-curve-isom-graphs: the existing theorem concerns projective curves over locally Noetherian bases and graph representability, without finite unramified Isom; the new theorem treats stable families over any scheme.

lem-sfb-arithmetic-stable-isom-finite vs lem-sfb-curve-graph-fixed-polynomial-cover: the existing theorem constructs numerical polynomial covers for graphs over a locally Noetherian base, not finite unramified Isom for stable families on arbitrary bases.

lem-sfb-arithmetic-stable-isom-finite vs lem-sfb-bounded-double-graph-hilbert-locus: the existing theorem assumes a Noetherian affine base and fixed Hilbert polynomial to construct a graph locus; the new theorem has neither restriction and gives finite unramified stable Isom.

lem-sfb-arithmetic-stable-isom-finite vs lem-sfb-isom-graph-representatives-zariski-gluing: the existing theorem glues supplied local graph representatives; it does not establish existence, finiteness or unramifiedness for stable Isom on arbitrary bases.

lem-sfb-arithmetic-stable-isom-finite vs def-sfb-stable-fiber-curve: the existing node defines base transport of a curve in a fibre groupoid, rather than proving representability or any diagonal property.

lem-sfb-arithmetic-stable-isom-finite vs lem-sfb-stable-isom-finite-unramified: the existing theorem permits only k-schemes for a field k; the new Isom theorem applies to any base scheme, including mixed-characteristic and non-Noetherian bases.

lem-sfb-arithmetic-stable-open-bounded vs lem-sfb-stable-curve-framed-trait-smoothing: the existing theorem constructs a smoothing trait for one curve over an algebraically closed field, rather than the arithmetic open bounded stable locus.

lem-sfb-arithmetic-stable-open-bounded vs lem-sfb-stable-and-smooth-family-open-loci: the existing theorem fixes a field k and has no arithmetic quasi-compactness conclusion; the new inputs give arithmetic smooth-locus openness and the stable algebraic locus over Z with its bounded point space.

lem-sfb-arithmetic-nodal-curve-stack-smooth vs lem-sfb-trait-specialization-etale-chart-density: the existing theorem detects density assuming smoothing traits and a field base; it gives neither arithmetic algebraicity nor nodal-stack smoothness.

lem-sfb-arithmetic-nodal-curve-stack-smooth vs lem-sfb-dm-open-finite-etale-permanence: the existing theorem assumes a smooth finite-type DM stack over a field and proves permanence for open/finite-etale decorations; it neither constructs the arithmetic nodal stack nor treats Spec Z.

lem-sfb-arithmetic-nodal-curve-stack-smooth vs lem-sfb-nodal-curve-stack-smooth: the existing theorem fixes a field k; the new theorem applies over arbitrary schemes and gives arithmetic nodal-stack smoothness and arbitrary smooth chart tests.

lem-sfb-arithmetic-nodal-curve-stack-smooth vs def-sfb-curve-moduli-groupoids: the existing node defines the nodal-geometric-fibre predicate and asserts no algebraicity, openness or smoothness theorem.

lem-sfb-arithmetic-nodal-curve-stack-smooth vs lem-sfb-finite-type-stack-affine-smooth-atlas: the existing theorem assumes a finite-type algebraic stack over a field and extracts a smooth atlas; the new theorem establishes nodal-moduli algebraicity and smoothness over arbitrary bases.

lem-sfb-arithmetic-nodal-curve-stack-smooth vs lem-sfb-gerbe-smooth-universal-homeomorphism: the existing theorem assumes an algebraic gerbe over an algebraic space and proves smoothness and a topological comparison; it has no assertion about algebraicity or smoothness of nodal-curve moduli.

lem-sfb-arithmetic-nodal-curve-stack-smooth vs lem-sfb-stable-and-smooth-family-open-loci: the existing theorem fixes a field k and has no arithmetic quasi-compactness conclusion; the new inputs give arithmetic smooth-locus openness and the stable algebraic locus over Z with its bounded point space.

lem-sfb-arithmetic-nodal-curve-stack-smooth vs def-sfb-algebraic-moduli-stack: the existing node defines algebraicity and smooth atlases but proves none of the curve-stack assertions.

## Dry-run repair

The first complete dry run rejected the three new blueprint.from.node values: I had filled the documentary ancestor even though the ancestry tool reports None for the broken creation chain. I read blueprint_refs.py, whose format specifies null if the chain is broken, and preflight_delivery.py, which requires agreement with that tool. I restored null on the item and new nodes, preserved the detailed place/via route, and corrected this report and split_report. No mathematical statement or proof changed.
