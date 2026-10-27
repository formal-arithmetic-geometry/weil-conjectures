# Worker report: lem-sfb-space-derived-chow-neighbourhood

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-derived-chow-neighbourhood.json: split statement, eight proof steps following the local proof of Stacks 0CTR; unchanged statement.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-partial-section-schematic-image.json: statement-only auxiliary theorem, unsplit; Mathlib searches found no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-flat-closed-kernel-base-change.json: statement-only auxiliary theorem, unsplit; Mathlib searches found no match.
- citations.json: a verbatim statement quotation for each citation in each proof step. Search outputs are preserved in search-results-*.json; searches.jsonl is the unmodified msearch log.

## Attachments

None. Searches of lean/WeilConjectures for the item id, derived Chow, Chow neighbourhoods, partial sections, relative flat closed kernels and pseudo-coherent kernels found no project declaration stating the item or either new lemma. The existing ChowLemma files concern scheme modifications and contain no derived algebraic-space kernel. Existing ring pseudo-coherence results concern module complexes, not this statement.

## WANTED

None: all mathematical sources used are in literature/stacks-project/.

## Corrections and source error

The item statement is faithful to 0CTR, together with the finitely presented closed immersion noted in 0CTS, and was retained. The source proof says that after base change there is a unique point over x. Uniqueness is false: take A'=F_3, A=F_9, X'=Spec(F_3), W'=Spec(F_9). Then W' times_{F_3} F_9 is Spec(F_9 times F_9), with two points over the single point of X=Spec(F_9). Step 6 uses the existing fibre-product-point theorem to choose one point, which is all the statement requires.

The first paragraph of 0CTR also calls the remaining kernel-identification clause '(5)', although it is clause (4) of the printed statement, and writes U' times V' and U times V where the required conclusion is on X' times V' and X times V. Step 8 specifies the actual projection between the entire product opens and proves exactly that restriction isomorphism. No extra flatness of A over A_0 is introduced.

The unit record's source is historical; the newest blueprint was read through literature/blueprint/latest (main-20261023-1620), specifically the direct-images proof (3). The item is a supporting input on the inherited 0CTT route. It is not the unit's key node, so no unit record was changed. blueprint_refs ancestor returns None for the inherited chain; its null ancestor and exact via list are retained, and both new nodes extend that same chain. Whole-DAG and blueprint searches for Chow, partial section, relative flat, kernel, 0CP3 and 0CTQ found no equivalent blueprint theorem for either new node.

## Unfinished work

Stage 1 is complete in this sandbox. Both new auxiliary statements are intentionally unsplit, without proof sketches or proof dependencies. They are subsequent work items; no Lean or compiler work was attempted.

## Not duplicates

lem-sfb-space-partial-section-schematic-image vs lemma-nagata-scheme-image-partial-section: the existing theorem concerns schemes and a graph into a product; the new theorem permits algebraic-space source and target and proves the partial-section restriction isomorphism for them.

lem-sfb-space-partial-section-schematic-image vs lem-sfb-space-qc-open-schematic-closure: the existing theorem starts with an open immersion into the ambient space; the partial section is generally closed, rather than open, over its domain, so the new theorem treats a different map and proves the isomorphism after closure.

lem-sfb-space-partial-section-schematic-image vs lem-sfb-space-proper-schematic-image: the existing result assumes a proper source over a base and concludes properness of its image; no properness is available here, and it does not state the partial-section isomorphism.

lem-sfb-space-partial-section-schematic-image vs lem-sfb-stack-schematic-image-qc: the existing theorem supplies schematic images, their ideals and flat base change, but does not assert that the image of a partial section of a separated morphism is isomorphic over its open domain. The new node states precisely this nontrivial specialization with its inverse map; it does not duplicate image existence alone.

lem-sfb-space-relative-flat-closed-kernel-base-change vs lem-sfb-relative-flat-closed-kernel-base-change: the existing theorem is exclusively about schemes and their scheme module derived categories. The new theorem permits algebraic-space factors and is an isomorphism in their small-etale derived categories.

lem-sfb-space-relative-flat-closed-kernel-base-change vs lem-sfb-tor-independent-closed-pushforward-comparison: the existing theorem has schemes and assumes stalkwise Tor independence. The new theorem permits algebraic spaces and obtains the needed independence from two relative flatness hypotheses, without assuming the closed immersion itself flat.

lem-sfb-space-relative-flat-closed-kernel-base-change vs lem-sfb-flat-space-derived-pushforward-base-change: the existing theorem requires its pushforward morphism flat; the closed immersion here need not be flat. Its flatness is over the first product factor instead.

lem-sfb-space-relative-flat-closed-kernel-base-change vs lem-sfb-flat-space-derived-external-cup: the existing theorem identifies derived global sections under external cup products of two flat spaces. It does not identify derived pullback of the structure module of an arbitrary relatively flat closed subspace of a product.

lem-sfb-space-relative-flat-closed-kernel-base-change vs lem-sfb-projective-cohomology-coefficient-kunneth: the existing theorem concerns coefficient maps and cohomology Kunneth formulas with finite projective cohomology. The new result requires no such cohomology hypothesis and concerns a derived closed-kernel base-change isomorphism.

## Review by Q45

I read the statements and full proof of 0CTR and the statement and first paragraph of 0CTS in spaces-more-morphisms.tex. For the partial-section node I read 0CP3 in spaces-morphisms.tex, together with image existence and etale restriction in 082X and 082Z. For the closed-kernel node I read 0CTQ in spaces-more-morphisms.tex, including its chart-reduction footnote, and the full 08IR statement and proof in spaces-perfect.tex. The latter only applies to quasi-coherent complexes and a quasi-compact quasi-separated morphism: here the structure module is quasi-coherent and a closed immersion is affine, hence meets the required compactness and separation conditions. The two relative flatness hypotheses of 0CTQ are exactly those written in the new node. The kernel need not itself be flat over its product ambient space. These are supporting tools, not restatements of the item's geometry or kernel-existence conclusion.

I opened every cited DAG statement. Step 1 uses the affine inverse-limit presentation, essential surjectivity of the finitely presented-space limit category, descent of separatedness, and finite-type Noetherianity exactly as those statements say; all stages have affine bases. Step 2 uses the fp-source qcqs theorem before the affine etale atlas theorem, chooses a point using atlas surjectivity, and applies the affine-immersion theorem to a genuinely affine finite-type scheme. The scheme-image existence and immersion-open-in-image nodes apply to schemes, namely U_0 and P_0, rather than to X_0. Properness of finite projective space provides its separatedness and quasi-separatedness before the compactness-permanence argument. Step 3 uses the new partial-section statement for the separated projection X_0 times Y_0 to Y_0 and the quasi-compact open U_0 in Y_0, so it obtains exactly the restriction isomorphism needed. The closed composition and inverse-image ideals are written out; the smallest-image comparison explains that this is the source's graph closure.

Step 4 uses the qcqs product theorem, polynomial projective charts, and the scheme Noetherian theorem on finite-type affine charts to verify the Noetherian hypotheses of every subsequent citation. Step 5 applies the closed-pushforward coherence/support theorem, then the Noetherian pseudo-coherence criterion to a degree-zero coherent module. The closed-structure finite-presentation equivalence applies to h_0 and j_0 because their ordinary structure pushforwards are coherent, hence finitely presented. In particular, finite presentation of j is proved before arbitrary base change, without claiming that every open in a non-Noetherian projective space is quasi-compact.

Step 6 checks the base-change geometry on scheme tests by the same finite ideal generators, and uses scheme etale base change only after taking such a test. For the chosen point the fibre-product-point theorem has scheme sources Spec(kappa(x)) and W_0 with the same image in X_0; its conclusion gives existence and does not imply uniqueness. Step 7 is the explicit local finite-free argument from the definition of pseudo-coherence, the bounded-above-flat K-flat theorem on a ringed site (not just on a topological space), and the derived composition definition. Thus it proves preservation by pullback and support without an unquoted lemma. Step 8 verifies relative flatness via etaleness and flat projective charts, then applies the new closed-kernel theorem on the entire open product. Restriction of ordinary direct image is checked from the chart-limit definition, and the pullback comparison is in the derived category, not only on cohomology groups.

I checked edge cases: an empty X supplies no x and the item has no obligation; zero-variable affine embedding gives n=0 without needing a nonempty variable list; an empty partial-section domain gives the empty schematic image and an empty restriction isomorphism; identity base change gives the original closed kernel. The F_3/F_9 example above checks the important nonunique-point case. I also tested the necessity of the relative-flatness condition: for k[t] mapping to k, a closed kernel supported at t=0 and base change t=0 has nonzero Tor_1, so the two-flatness condition is not silently removed. No new node assumes that the whole algebraic space X_0 is flat over A_0.

The comparison with delivery-errors B--E found no proof in an unsplit node, no clause of the item moved into a node, no unsupported invocation of a tag, no circular dependency, and no source using the prohibited SGA route. All eight steps are below 2000 characters. Queries were actually run through msearch.py, including second phrasings, and their full returned signatures were read; no Mathlib hit states either new theorem. Off-unit inputs are recorded as generic tool uses, preserving the unit route. Every citation has its verbatim statement in citations.json.
