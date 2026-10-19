# Stage-1 report: lem-trf-nodal-open-locus

1. Files written:
   - `dag/nodes/sec-trace-formula/lem-trf-nodal-open-locus.json`: item, statement, split; existing Mathlib searches retained; no exact match.
   - `dag/nodes/sec-trace-formula/lem-trf-syntomic-locus-base-change.json`: new statement-only unsplit node; no Mathlib match. Stacks 02V3 supplies the fibrewise complete-intersection locus, its openness under flatness/local finite presentation, and inverse-image equality under arbitrary base change.
   - `dag/nodes/sec-trace-formula/lem-trf-unramified-locus-base-change.json`: new statement-only unsplit node; no Mathlib match. Stacks 0475 supplies the locally-finite-type unramified locus and arbitrary-base-change equality; 02GF supplies the fibre-local-ring/residue-field characterization.
   - `citations.json`: every step/node pair with a verbatim cited statement, retaining the hypotheses as well as each used clause.
2. Attachments: none. Searches of `WeilConjectures/` by the item tag and nodal/syntomic/unramified-locus notions found no declaration proving this item; the incidental nodal-curve comments do not state it.
3. WANTED: none. All mathematical sources used are in the local Stacks checkout.
4. The imported statement is unchanged. Its proof was empty. An initial draft incorrectly omitted the intersection with the complete-intersection locus, and tried a duplicate Fitting auxiliary. Both are removed: the final construction is $U=M\cup(V\cap W)$, and the existing differential and Fitting base-change statements prove formation of the singular subscheme in Step 2. The existing nodal-family Fitting theorem is **not** used: it assumes all fibres nodal, the fact at issue here. The correct tag for `lemma-set-points-where-fibres-unramified` is 0475, not 02V4 (which is the smooth locus). All node files, quotations and reports have been rewritten around the corrected argument.
5. Nothing remains unfinished in this one-level split. The two new nodes deliberately have statements only, as required.

## Review by Q40

I read Stacks `curves.tex`, Tag 0DSC, the full construction using the syntomic locus and the unramified part of the singular subscheme; `morphisms.tex`, 02V3, 0475 and 02GF; `curves.tex`, 0C4D and 0C4E; and the relevant Divisors Fitting statements 0C3I/0C3K. I opened the statement of every cited DAG node. The two new statements have independent, smaller content than the maximal nodal-open conclusion: neither mentions nodes or the maximal nodal open. The Mathlib search log was read, including two semantic phrasings for each locus, LeanSearch, Loogle and source grep. The algebraic unramified-locus API supplies related ingredients but not the scheme-level equality after arbitrary base change; the only complete-intersection grep hit is a presentation-dimension comment. All recorded searches correspond to actual `msearch.py` log entries.

Step 1 uses the algebraic-closure embedding lemma to handle an arbitrary algebraically closed geometric field, local-finite-presentation permanence to ensure the chosen fibre is locally finite type, and relative-dimension base change for its field-valued structure morphism. This checks an easily missed hypothesis: the imported geometric-fibre definition chooses an algebraic closure, while subsequent base changes may use a larger algebraically closed field.

Step 2 uses the first-Fitting definition, the affine tensor-product description, differential base change, and Fitting base change for finite modules. The differential module is finite because the morphism is locally finite type. The ideal equality gives the closed subscheme equality, with no nodal assumption; taking reductions would be incorrect. This is a short explicit combination of existing nodes, so no new Fitting theorem is created.

Step 3 uses the dth-Fitting smooth-locus statement with d=1, whose flatness, local finite presentation and dimension hypotheses are verified. For a geometric fibre, flat and locally finitely presented base-change permanence supply the first two and Step 1 supplies dimension even after further geometric extension. It identifies the actual relative smooth locus with the complement of the Fitting support. Step 4 uses the new 02V3 lemma and the new 0475 lemma exactly as stated. The singular morphism is only asserted locally finite type: the quotient of each finite-type affine algebra is finite type. No unwarranted finite-presentation hypothesis is put on its closed singular subscheme. The closed-complement formula proves the constructed union is open.

Step 5 applies the existing pointwise LCI criterion on the open V in a geometric fibre and the new unramified local criterion on W. The latter supplies both the local ring equal to the residue field and its finite separability. The finite-residue closedness lemma ensures the point is closed in the ambient curve before applying the nodal-point equivalence. Thus all three conditions on that equivalence's right side are actually verified. Step 6 applies the reverse direction to every node, then the LCI and unramified locus characterizations put it in V and W. Smooth points are included directly through M. These steps prove pointwise equality, not just the sufficient nodality of the constructed open.

Step 7 uses flat and local-finite-presentation permanence, dimension from Step 1, Fitting formation from Step 2 and the two new locus equalities. Inverse images preserve the union/intersection defining U, so the equality of open subschemes is obtained for every base change. Step 8 checks maximality on each chosen geometric fibre. A closed node of a competing open has finite residue field by Zariski's lemma and is closed in the ambient curve by the finite-residue closedness lemma; its completion is unchanged on the open. Faithfully flat field-extension base change and surjectivity of spectra, on the affine tensor-product fibre charts, justify descending inclusion and the final whole-fibre criterion. No inference merely assumes geometric projections are surjective without a cited theorem.

Small cases checked: the empty source and empty fibres (all loci and criteria vacuous); a smooth curve (Z empty and U=Y); the node uv=0 and its smoothing uv=t; the cusp y^2=x^3 (the unramified singular-locus test excludes the cusp); a doubled line (failure of the singular unramifiedness test); and non-Noetherian bases. The smoothing base change t=s^2 has a nonreduced singular subscheme, retained by the Fitting construction. Over characteristic 2 the criteria use finite separability and Fitting ideals rather than dividing by 2, so the proof does not discard that case. Each proof step is under 2000 characters. I checked B--E: complete statements and defined notions, correct sources, no clause-relabelling, no circular nodal-family use, no hypothetical hypotheses, no SGA route, and no new proof inside an unsplit child. The unit and chapter are unchanged; this supports the historically retained stability-locus branch beneath the ancestor, not a replacement of the current contracting-correspondence route.

## Not duplicates

lem-trf-syntomic-locus-base-change vs lem-weil-pbc-fibre-of-base-change: the existing node identifies fibres as residue-field base changes; the new node proves which fibre local rings are complete intersections, openness under flatness/lfp, and equality of those loci under base change.

lem-trf-unramified-locus-base-change vs lem-weil-pbc-fibre-of-base-change: the existing node is only a cartesian fibre identification; the new node is the open unramified locus and its exact inverse-image equality, with the local field criterion.

lem-trf-unramified-locus-base-change vs lem-sbc-formally-unramified-stalk-neighbourhood: the existing node gives an unramified neighbourhood from a formally unramified stalk map, but does not give the locus's arbitrary-base-change equality or its fibre-local-ring characterization.

lem-trf-unramified-locus-base-change vs lem-trf-unramified-over-field-local-criterion: the existing node tests global unramifiedness over a field by the local rings at all points; the new node applies to arbitrary bases and states the pointwise locus and its exact arbitrary-base-change equality.

lem-trf-unramified-locus-base-change vs lem-weil-pbc-unramified-fibre-point-isolated: the existing node only concludes that an already unramified point is isolated in its fibre; it does not characterize the open unramified locus or give its inverse-image equality.

lem-trf-unramified-locus-base-change vs lem-weil-pbc-etale-smooth-zero-dimensional-fibres: the existing node proves smooth relative dimension zero from etaleness, without any unramified-locus theorem.

lem-trf-unramified-locus-base-change vs lem-weil-pbc-unramified-etale-local-decomposition: the existing node constructs étale-local decompositions around finitely many unramified points of a separated morphism; the new locus theorem assumes neither separation nor a finite selected list and constructs no such decomposition.

lem-trf-unramified-locus-base-change vs lem-sc-finite-flat-unramified-tangent-criterion: the existing node tests étaleness by tangent injectivity for finite locally free morphisms at rational points; the new node allows arbitrary locally finite type morphisms and characterizes their unramified locus and base-change equality.

lem-trf-unramified-locus-base-change vs lem-sbc-root-normalization-generic-source-etale-point: the existing node obtains an étale source neighbourhood under particular root-normalization hypotheses; no general locus/base-change characterization is stated there.

lem-trf-unramified-locus-base-change vs lem-sbc-stalk-normalization-trait-section-unramified: the existing node supplies formally unramified neighbourhoods in a particular trait-section normalization setting; the new node does not concern normalization and provides a general fibre criterion and locus/base-change equality.

lem-trf-unramified-locus-base-change vs lem-sbc-root-normalization-generic-stalk-unramified: the existing node only states formally unramified stalk maps for particular normalization points; the new general theorem states an open locus and its exact inverse-image equality.
