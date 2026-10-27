## Worker report

Files written:
- dag/nodes/sec-six-functors/lem-sf-site-hom-comparison-thick.json: item, split; statement unchanged.
- dag/nodes/sec-six-functors/lem-sf-ringed-hom-complex-pullback-shift.json: new statement-only lemma, unsplit, no Mathlib match.

Attachments: none. Read-only rg searches of WeilConjectures for the blueprint tag found no declaration for this item. Concept searches found ClosedTriangulated.lean, whose first-variable theorem only supplies existence of a boundary, and scheme-etale pullback comparisons, none proving this specified site comparison, its shift structure and restriction clauses together. No compiler was invoked.

WANTED: none.

The imported item had no proof. Its whole statement is retained, with no new hypothesis and no discarded clause. The current ancestor proof is literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md, paragraphs 1-2. Its assertion that exactness alone makes the comparison a triangle morphism requires checking the actual map and its shift; our steps 2-4 supply that check. The historical source field is preserved. The unit and chapter were read; the comparison is a formal input to the finite-coefficient duality route. No SGA source is used.

Nothing in the assigned split is unfinished. The new chain-level lemma is intentionally unsplit and carries no proof or proof dependencies. Its argument for the future worker is the following: form product projections by transposing pulled-back component evaluation; naturality of evaluation gives compatibility with pre/postcomposition. Expanding d(f)=d_I f-(-1)^n f d_E shows that these projections commute with the differential. Reindex p to p-m and multiply by (-1)^(mn) for the source shift; the same sign appears on both routes. Products are used only in the target universal property. An exact inverse image is never claimed to preserve infinite products.

## Mathlib and duplicate searches

Searches ran only through msearch.py and are retained verbatim in searches.jsonl and the node fields. Both the item and the new node received natural-language searches, Loogle and grep, including a second conceptual phrasing. Read the actual candidate sources: Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean lines 904-949 maps cochains of categorical morphisms, rather than sheaf-valued Hom complexes between different sites. Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean lines 292-310 gives internal Hom and its two-variable adjunction in one category. PullbackContinuous.lean and PullbackFree.lean give module pullback adjunctions and free objects. These do not specialize in one line to the new node. No search result was invented, and no failed service is treated as evidence of absence.

Before creation, searched all dag/nodes for 0GMX, Hom-complex/pullback and evaluation/shift concepts, searched project WeilConjectures and Sheaf, and used blueprint_refs.py search for Hom complex, Hom complexes, pullback Hom, 0GMX, source shift, internal Hom comparison, evaluation and thick. The existing lem-sf-etale-hom-complex-pullback requires a morphism of schemes and its small-etale inverse image. The new node instead takes a morphism between arbitrary small ringed sites, needed for the etale-to-proetale comparison which is not such a scheme morphism. We cite existing exactness and slice-normalization tools rather than duplicate them.

## Review by Q55

I read the ancestor comparison proof against the item and read Stacks sites-modules.tex remark-pullback-internal-hom (Tag 0GMX), sites-cohomology.tex section-hom-complexes (0A8X), lemma-internal-hom (08J9), lemma-restriction-RHom-to-U (08JB) and lemma-RHom-triangulated (08JC). The last proof explicitly omits details; the new node isolates the ordinary signed model calculation rather than assuming that an arbitrary natural transformation of exact functors preserves boundaries. The new node introduces both ringed sites, rings, exact module inverse image, complexes, shifts and product projections. It says nothing about derived invertibility. Its source agrees with the ordinary pullback-map construction and the Hom differential.

Step 1 uses the exactness statement of lem-sf-comparison-pullback-exact and the termwise-derived theorem lem-sf-exact-functor-derived-triangulated, then the actual two-variable exactness and shift clause of lem-weil-pbc-ringed-internal-hom-exact-restriction. The signed-exact node supplies a coherent opposite-category shift structure, not a beta comparison. Its arbitrary-small-ringed-site scope covers both sites, and its arbitrary M covers the unbounded second input. I did not use the etale-only lem-sf-hom-triangulated on the proetale site.

Step 2 uses functorial K-injective existence separately on each site, the new node's ordinary chain map, postcomposition from def-pur-hom-complex, the explicit representative definition of RHom, and lem-pur-rhom-well-defined to invert source quasi-isomorphisms. Exact F computes the source termwise. FI need not be K-injective, so an additional resolution q:FI to J is present. This corrects the common unsupported inference that inverse image preserves injectives or products.

Step 3 uses flat-term K-flat existence, the pullback theorem's actual K-flat-preservation clause, total-tensor descent, and the closed adjunction whose statement explicitly specifies its evaluation counit. I read each of those statements: a plain tensor isomorphism would not justify K-flat preservation, but the cited derived-tensor-pullback node states both. The component calculation is evaluation of each actual Hom projection followed by q, hence its uncurry is precisely the map defining beta. K-flat replacement of E and Hom well-definedness justify arbitrary inputs. This is a direct model identification, not an assertion of agreement only on generators.

Step 4 uses the new lemma's signed source-shift equation and ordinary postcomposition; the displayed component after reindexing is the same on both paths. The coherent reversed structure has the same normalization on the two rows; thus that scalar cancels in the square. Naturality at w[-1], together with the shift square, gives the connecting square, not only the first two squares. The exactness citation gives the common reversed-triangle signs. There is no uncited existence theorem hidden in this step.

Step 5 cites lem-sf-triangle-morphism-iso, whose statement applies to an actual morphism of distinguished triangles with two invertible components; step 4 provides all its hypotheses. Zero, isomorphisms and finite sums follow from additivity and naturality with their inclusions and projections, which are written in the step. Step 6 is elementary: I checked the types and both products for the explicit inverse B(i) a^-1 C(p); contravariance has the right direction. No idempotent-completeness hypothesis is needed for an already specified retract.

Step 7 uses the ringed localization square, its normalized derived pullback comparison on K-flat models, and the slice-evaluation-transpose node's explicit preservation of evaluation and transposition. I read these statements; the mere objectwise RHom restriction isomorphism was insufficient. Uncurrying both sides gives the displayed F_U of restricted evaluation after the same tensor comparison. The closed Hom bijection then proves equality of maps. The site localization works for every etale object, not just open immersions. Canonical tensor components are identified on K-flat total tensors, so no arbitrary identifications enter.

Small cases checked: zero ring, zero complex, empty finite sum, m=0 and m=1 source shifts, a complex concentrated in degree zero, negative shifts, a split triangle, and the identity retract. All constructions still make sense for unbounded E,I; target products are not commuted with F. The new node's signed map is well typed: H(E[m],I)^n reindexes to H(E,I)^(n-m), and f^(p-m) maps E^p to I^(p+n-m). For m=1, the minus sign in the Hom differential yields the same (-1)^n on both sides of its chain-map identity. No new statement dispute was found.

I checked delivery-errors B-E with the files open: complete statement-only new node, definition dependencies present, single-escaped TeX, Stacks tags and labels rather than section numbers, real recorded searches, and no theorem made into a leaf from a merely related hit. The only new node is strictly chain-level and general, not an item clause; the derived assembly and restriction argument remain in the item. Every cited statement is quoted verbatim in citations.json. No proof step exceeds 2000 characters. Off-unit results are declared as generic tool uses in split_report, preserving the Hom-complex route.

## Not duplicates

lem-sf-ringed-hom-complex-pullback-shift vs def-coef-hom-representative-evaluation: the existing node concerns Canonical evaluation on fixed Hom representatives; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs def-pc-ring-hom-extension-shared-definitions: the existing node concerns Shared ring-site Hom extension definitions; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs def-pc-scheme-ordinary-evaluation-component: the existing node concerns Actual scheme ordinary evaluation component; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs def-pur-derived-internal-hom: the existing node concerns Derived internal Hom on a ringed site; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs def-pur-external-rhom-pairing-interface: the existing node concerns External global Hom evaluation interface; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs def-pur-hom-complex: the existing node concerns Hom complex of complexes of sheaves of modules; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs def-pur-signed-line-pullback-normalization-data: the existing node concerns Normalized signed pullback families and scalar squares; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs def-pur-signed-line-scalar-normalization-data: the existing node concerns Signed line powers and normalized scalar comparisons; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs def-real-common-stage-lisse: the existing node concerns Pro-etale local finite freeness at common rational coefficient stages; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs def-real-common-stage-weil-linear-dual: the existing node concerns Evaluation universal property of the linear dual of a common-stage Weil complex; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs def-sc-hom-complex-unit-evaluation: the existing node concerns Degreewise unit Hom-complex evaluation; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs def-sc-signed-sheaf-dual-complex: the existing node concerns Signed internal sheaf dual complex; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs def-sp-canonical-scalar-extension-maps: the existing node concerns Canonical unit, tensor, dual and tower maps for scalar extension; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-coef-bidual-evaluation-shift-one: the existing node concerns Degree-one signed shift compatibility of coefficient evaluation; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-coef-etale-hom-transpose-exact: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-coef-rational-bidual-triangle-compatibility: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-coef-signed-derived-internal-hom-exact: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-coef-slice-hom-source-shift: the existing node concerns Slice restriction preserves the normalized source shift of derived Hom; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-hom-complex-over-equiv-projections: the existing node concerns Hom complex comparison with its specified product projections; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-normalized-hom-complex-global-cochains: the existing node concerns Explicit normalized global-cochain comparison; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-normalized-ring-hom-extension: the existing node concerns Normalized scalar-extension map of ring-site Hom complexes; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-ordinary-dual-projection-differential: the existing node concerns Dual Hom differential after projection; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-ordinary-evaluation-component-over-transport: the existing node concerns Evaluation components with a fixed normalized total tensor comparison; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-ordinary-evaluation-over-component-identity: the existing node concerns Dual and output transport of a local evaluation component; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-ordinary-evaluation-over-dual-projection: the existing node concerns Inverse dual comparison recovers the unit-valued projection; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-ordinary-evaluation-over-tensor-formula: the existing node concerns Tensor summand formula for ordinary evaluation under open reindexing; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-ordinary-evaluation-tensor-summands: the existing node concerns Unit-normalized symmetric tensor comparison and total summand equations; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-ordinary-evaluation-transport-summand-projection: the existing node concerns Transport a tensor summand followed by a Hom projection; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-ring-hom-extension-degrees: the existing node concerns Normalized scalar-extension Hom degree maps; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-ring-hom-extension-differential: the existing node concerns Differential compatibility of normalized Hom degree maps; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-ring-hom-extension-differential-adjacent: the existing node concerns Adjacent-degree differential compatibility for normalized Hom maps; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-scheme-ordinary-evaluation-of-components: the existing node concerns Scheme evaluation from its isolated components; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-single-degree-exact-term-hom-quasi-iso: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pc-stupid-tail-hom-short-exact: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-per-localization-dual-boundary-pairing: the existing node concerns The dual localization boundary transposes to evaluation followed by the support boundary; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-per-relative-bidual-triangles: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pod-derived-automorphism-hom-evaluation: the existing node concerns Derived internal Hom and evaluation under an isomorphism of coefficient sites; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pod-module-hom-signed-evaluation: the existing node concerns Signed evaluation for ordinary module Hom complexes; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pod-point-hom-complex-adjunction: the existing node concerns Normalized chain-level Hom adjunction at the point; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pod-point-sheaf-hom-maps: the existing node concerns Sheaf evaluation and sections-tensor maps for the point model; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pod-point-tensor-hom-evaluation: the existing node concerns The normalized Hom comparison intertwines signed evaluation; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-derived-internal-hom-shift-comparison: the existing node concerns Shift comparison for internal derived Hom; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-derived-internal-hom-shift-left: the existing node concerns Left-argument shift comparison for internal derived Hom; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-derived-internal-hom-shift-right: the existing node concerns Right-argument shift comparison for internal derived Hom; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-external-rhom-cone-pairing: the existing node concerns External global derived Hom evaluation respects coefficient cones; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-external-rhom-derived-braiding: the existing node concerns Localization tensor comparison preserves Koszul braiding; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-external-rhom-signed-cones: the existing node concerns Transport normalized external evaluations to both native coefficient cones; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-global-hom-chain-evaluation: the existing node concerns Unsigned chain evaluation from global cochains; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-global-hom-evaluation-model: the existing node concerns A-linear evaluation-normalized global derived Hom model; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-hom-complex-global-cochains: the existing node concerns Global sections of the sheaf Hom complex identify ordinary cochains; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-hom-complex-resolution-shift-comparison: the existing node concerns Localized Hom comparison for shifted functorial resolutions; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-hom-complex-sections-cochains: the existing node concerns Degreewise section products identify localized external cochains; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-hom-complex-sections-cochains-comm: the existing node concerns Section cochain identifications respect the Hom differential; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-hom-complex-sections-cochains-comm-universes: the existing node concerns Section cochain identifications respect the Hom differential with independent coefficient universe; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-hom-complex-sections-cochains-universes: the existing node concerns Degreewise section products identify localized external cochains with independent coefficient universe; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-hom-complex-shift-left: the existing node concerns Signed source-shift natural isomorphism for the sheaf Hom complex; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-hom-complex-shift-right: the existing node concerns Chain-level right-shift comparison of sheaf Hom complexes; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-inverse-image-hom-comparison: the existing node concerns The unit-normalized internal-Hom comparison for an isomorphic base change; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-isomorphism-inverse-image-tensor-hom: the existing node concerns Inverse image along an isomorphism of schemes commutes with tensor products and sheaf Hom; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-localized-hom-complex-boundaries: the existing node concerns Localized degree-minus-one boundaries are null-homotopies; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-localized-hom-complex-cycle-lift: the existing node concerns Lifting localized chain maps to Hom-complex cycles; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-localized-hom-complex-cycles-aux: the existing node concerns Degree-zero cocycles identify localized chain maps; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-localized-hom-complex-cycles-bijective: the existing node concerns Bijectivity of the localized cycle component function; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-localized-hom-complex-cycles-forward: the existing node concerns Projection components of localized cycles are chain maps; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-localized-hom-complex-homology-aux: the existing node concerns Homology identifies homotopy morphisms; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-ringed-site-finite-free-dual-pullback: the existing node concerns Pullback of the dual of a finite locally free module on a ringed site; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-ringed-site-pullback-dual-free-chart: the existing node concerns Invertibility of a pulled evaluation comparison on a finite-free chart; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-ringed-site-pullback-pairing-transfer: the existing node concerns Extension of module pairings along a ringed site morphism; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-signed-line-derived-base-change: the existing node concerns Signed line comparisons and their unbounded derived tensor action; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-signed-line-scalar-pullback-square: the existing node concerns Pullback of a compatible line scalar square through all signed powers; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-pur-signed-line-scalar-tensor-tower: the existing node concerns Dual scalar comparisons of lines and signed tensor and tower coherence; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-dual-total-comparison: the existing node concerns Signed Hom short-complex comparison with an opposite total; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-mapping-cone: the existing node concerns Internal Hom complexes commute with mapping cones; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-mapping-cone-differential: the existing node concerns Differential compatibility of the internal Hom cone comparison; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-projections: the existing node concerns Specified projections for the chosen Hom-complex; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-restrict-open: the existing node concerns Ordinary sheaf Hom complexes commute with open restriction; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-restrict-open-differential: the existing node concerns Differential compatibility of the factorwise open-restriction comparison; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-restrict-scheme: the existing node concerns Ordinary Hom complexes commute with scheme open restriction; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-restrict-scheme-transport: the existing node concerns Transport Hom complexes through the open-subscheme equivalence; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-single: the existing node concerns Internal Hom complex from a sheaf in degree zero; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-single-natural: the existing node concerns Natural single-source internal Hom chain comparison; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-single-naturality: the existing node concerns Naturality of single-source internal Hom complexes; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-to-single: the existing node concerns Collapse internal Hom into a single target; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-unit-evaluation-comm: the existing node concerns Unit evaluation commutes with the differential; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-unit-evaluation-is-iso: the existing node concerns Unit evaluation is an isomorphism in each degree; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-unit-evaluation-naturality: the existing node concerns Degreewise unit evaluation commutes with chain maps; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-hom-complex-unit-iso: the existing node concerns Hom complex from the structure sheaf is the identity; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-homology-evaluation-formal-complex: the existing node concerns Homology evaluation is perfect on locally split finite free models; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sc-single-supported-finite-free-homology-iso: the existing node concerns Cohomology of Hom from a single supported finite free complex; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sf-bifunctor-homotopy-exact: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sf-double-hom-cone-comparison: the existing statement concerns double Hom and a cone isomorphism; the new one concerns a single ordinary Hom-complex pullback map.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sf-etale-generic-hom-triangle: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sf-etale-hom-complex-pullback: the existing statement is only scheme-induced small-etale pullback; the new statement covers a general exact ringed-site pullback, including etale-to-proetale.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sf-even-line-hom-shift: the existing node concerns Signed first-variable shift compatibility of the internal-Hom line comparison; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sf-localized-bounded-hom-comparison: the existing node concerns Localized bounded internal-Hom comparison by finite tails; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sfb-independent-bounded-exact-term-hom: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sfb-rhom-colimit-cohomology-ladder: the existing node concerns Exact cohomology ladder for the internal-Hom filtered-colimit comparison; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sfb-rhom-colimit-source-transport: the existing node concerns Source-isomorphism and signed-shift transport of the internal-Hom colimit comparison; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sfb-rhom-continuity-triangle-closure: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sfb-scalar-dual-signed-assembly: the existing node concerns Signed cochain assembly of a natural additive dual comparison; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sfb-scalar-hom-chain-coefficient-coherence: the existing node concerns Coefficient-square coherence of normalized sheaf Hom chain maps; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sfb-scalar-hom-chain-evaluation: the existing node concerns Sheaf scalar-Hom evaluation chain map and input naturality; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-sfb-slice-scalar-hom-chain-adjunction: the existing node concerns Normalized slice scalar adjunction and product Hom chain isomorphism; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-trf-derived-evaluation-canonical-map: the existing node concerns Canonical derived evaluation morphism and its triangle naturality; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-trf-tensor-double-hom-exact-comparisons: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-weil-native-internal-hom-contravariant-exact: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-weil-pbc-bilinear-hom-complex: the existing node concerns Product Hom complexes for an additive coefficient bifunctor; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-weil-pbc-ringed-complete-element-addition: the existing node concerns Sum of complete local sections is complete; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-weil-pbc-ringed-complete-element-multiplication: the existing node concerns Multiples of complete local sections are complete; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-weil-pbc-ringed-internal-hom-exact-restriction: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs lem-weil-pbc-ringed-internal-hom-exact-universes: the existing statement is a derived exactness, triangle, or thick-locus assertion; the new one only constructs an ordinary Hom-complex pullback map with its explicit source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-b2-homology-evaluation-cycle-existence: the existing node concerns Cycle evaluation descends to homology; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-b2-homology-evaluation-definitions: the existing node concerns Cycle evaluation and finite-free zero models: shared interfaces; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-b2-homology-evaluation-local-cycle-lift: the existing node concerns Local cycle lift for homology evaluation; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-b2-homology-evaluation-local-iso: the existing node concerns Local perfection of cycle evaluation; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-b2-homology-evaluation-uniqueness: the existing node concerns Cycle evaluation determines a unique morphism; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-e3-homology-evaluation-restriction-comparison: the existing node concerns Open restriction transports cycle-compatible homology evaluation; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-e3-homology-evaluation-roof-naturality: the existing node concerns Common-source naturality of cycle-compatible homology evaluation; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-g3-hom-to-single-coefficient-square: the existing node concerns Hom to single coefficient square; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-g3-signed-sheaf-dual-coefficient-map: the existing node concerns Signed sheaf dual coefficient map; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-h3-finite-free-zero-homology-product: the existing node concerns Coordinate homology product for finite-free zero-differential internal Hom; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-t4-open-over-hom-complex-cycle-projection-comparison: the existing node concerns Cycle projection and quotient comparisons for restricted Hom complexes; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-t4-open-over-hom-complex-cycle-projection-comparison-cycle-square: the existing node concerns Chain isomorphism for restricted Hom with a fixed projection; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-t4-open-over-hom-complex-cycle-projection-comparison-homology-square: the existing node concerns Cycle and homology comparisons induced by the same restricted chain isomorphism; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-t4-open-over-internal-hom-comparison: the existing node concerns Natural internal Hom comparison for composite open restriction; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-t4-open-over-internal-hom-cycle-homology-squares: the existing node concerns Internal Hom transport squares for cycles and homology; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-v2-homology-evaluation-restriction-diagrams: the existing node concerns Projection and homology compatible restriction comparisons for cycle evaluation; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-v4-finite-free-zero-homology-evaluation: the existing node concerns Cycle-compatible evaluation for a finite-free zero-differential complex; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-v4-finite-free-zero-homology-evaluation-cycles: the existing node concerns Canonical cycle evaluation and homology descent for a zero-differential source; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-v4-finite-free-zero-homology-evaluation-iso: the existing node concerns Invertibility of a supplied compatible finite-free evaluation map; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

lem-sf-ringed-hom-complex-pullback-shift vs new-v4-homology-evaluation-roof-comparison: the existing node concerns Restriction and roof compatibility of cycle evaluation; it does not state the map F Hom-complex(E,I) to Hom-complex(FE,FI) for every exact ringed-site pullback with arbitrary unbounded E,I and its signed source-shift equation.

