## Worker report

Files written, all under dag/nodes/sec-six-functors-basics/:

- lem-sfb-quasidm-flat-locally-quasifinite-atlas.json: item, statement unchanged, six proof steps following Stacks 06MF.
- lem-sfb-stack-finite-type-smooth-closed-chart.json: statement, unsplit; Mathlib no match. An affine smooth chart with a closed point representing a finite-type stack point, including local finite type of its field self-groupoid.
- lem-sfb-smooth-fibre-image-parameters.json: statement, unsplit; Mathlib no match. Functions on a scheme cutting a smooth field-space at a rational point with zero-dimensional fibre to a regular zero-dimensional slice.
- lem-sfb-stack-quasifinite-fibre-neighbourhood.json: statement, unsplit; Mathlib no match. The open-source consequence of a zero-dimensional point in a representable field fibre (06ME).
- lem-sfb-representable-lqf-calculus-descent.json: statement, unsplit; Mathlib no match. Base change, composition, open-source locality and fppf target testing for representable local quasi-finiteness, with algebraic-space left cancellation.

Also written: citations.json, with 19 entries giving verbatim statement excerpts for every citation of every step; searches.jsonl, the actual msearch log; sandbox-only preparation scripts. No Lean or shared-repository file was written and no compiler was invoked.

Attachments: none. I searched lean/WeilConjectures for the blueprint tag and for algebraic-stack, quasi-DM, atlas and quasi-finite-locus terminology; the relevant hits concern scheme morphisms and do not state this algebraic-stack equivalence. The new statements have likewise no matching project declaration.

WANTED: none. All mathematical sources used are present in literature/stacks-project/.

Problems in the imported item: no statement error found. Its proof was empty. The existing support lemmas for unramified diagonals or Deligne--Mumford stacks cannot be applied here: locally quasi-finite diagonals need not be unramified (for example the classifying stack of a non-etale finite group scheme in characteristic p). The proof therefore uses the general algebraic-stack version of the regular-slice construction, rather than the DM-only finite-type calculus. The inherited blueprint.from.node is null, exactly as tools/blueprint_refs.py ancestor reports; I preserved it and its full via chain. The current latest blueprint is the main-20261023-1620 snapshot, whose direct-images proof (3) no longer prints the old alteration chain retained in this created node's provenance. This delivery proves the existing generic supporting statement along its Stacks route; it changes no chapter, unit or target.

Nothing mathematical remains unfinished in the item's one-level split. The four new inputs are intentionally statement-only for later splitting. There are zero new Mathlib leaves. The logged search results were read: scheme quasi-finite loci, scheme cancellation and scheme flat descent are useful background, but none is a one-line specialization giving these algebraic-space or stack statements. For the parameter lemma the hits on regular sequences and regular local rings do not select elements from the image of a different local ring and do not give the geometric conclusion. Every new node has two semantic phrasings, LeanSearch, Loogle and grep recorded exactly from msearch.py. The original item's inherited searches were retained and our own recorded searches appended.

## Proof handoff for the new inputs

For the closed-chart statement I read 06FX, implication (1) to (2), and the first paragraph of 06G3. Shrink the chart to an affine neighbourhood of its closed point. The map from the residue field is a closed immersion followed by a smooth map; each self-groupoid projection factors through the base change of that closed immersion followed by the base change of the smooth map. This proves the local finite type clause independently of the quasi-DM hypothesis.

For the parameter statement I read the local-ring paragraph of 06MF together with 06LC, 06M1, 06LQ, 00NQ and 04NQ in their local .tex files. Choose an etale scheme chart V of E and v over z. Since z is k-rational, kappa(v)/k is finite separable. Put A=O_(U,u), B=O_(V,v). The smoothness over k makes B Noetherian regular local, hence Cohen--Macaulay. The zero-dimensional p-fibre says B/m_A B has dimension zero, so the radical of m_A B is m_B. Lemma 06LC selects d=dim B elements of m_A with regular images in B. Represent them by functions after shrinking U; their denominators are units at v, so this does not change regularity or the generated local ideal. Their quotient in B has dimension zero. Formula 04NQ, and algebraicity of kappa(v)/k, then give dimension zero at z of the cut field-space. All functions vanish at u, so the point is retained. This is an independent geometric local-algebra lemma: it asserts neither flatness over a stack nor the existence of any atlas.

For the fibre-neighbourhood statement I read 06ME and its cited 06M5 item (2), 04NV and 04NW. The largest open locally quasi-finite locus on the space source commutes with representable base change. Pulling back along the given field object, the point z lies in this locus by relative dimension zero. Consequently p(z) lies in the original locus. This works for any locally finite type representable map, without assuming quasi-DM or flatness.

For the calculus statement I read 04XD with P equal to locally quasi-finite, the local-quasi-finite assertion of spaces-descent.tex 0427, and spaces-morphisms.tex 03XK, 03XL and 03XN. These give the independent generic properties asserted. Open-source locality follows from etale scheme charts; no quasi-compactness hypothesis is added, and the cancellation assertion imposes no condition on the second map. This statement is not 06MB or either implication of the item.

## Review by Q94

I checked sections B through E of delivery-errors.md against the item, the four new statements, their sources and every cited node's statement. New nodes contain no proof steps, no proof dependencies and no proof sketch in their statement. Each introduces all its objects and defines the space and stack conventions it uses, with definition-node citations and matching stmt_deps. The source records name actual Stacks tags and .tex labels. I searched the whole DAG by tags and concepts, used blueprint_refs.py searches for quasi-DM, locally quasi-finite, regular sequence, finite type point, 06FX, 06LC, 06ME and 03XN, and inspected the candidate node statements. No blueprint node states a new input. Shared-tag comparisons are below. These are smaller inputs to an argument, rather than aliases for an item clause.

Step 1 uses the new calculus statement for base change, left cancellation and target descent; its statement explicitly supplies all three. The existing chartwise smooth/etale calculus explicitly supplies stability of surjectivity, flatness and local finite presentation under base change and composition. The diagonal is representable by the algebraic-stack hypothesis. Its covering W times_S W is an algebraic space (a scheme), and both factors of that cover are base changes of q, so the descent lemma's hypotheses hold. The identification of its diagonal pullback with W times_X W is the definition of the 2-fibre product of isomorphisms; it does not assume a scheme diagonal.

Step 2 uses the closed-chart statement for the closed point, smooth affine chart and locally finite type field self-groupoid. It uses the existing chartwise calculus to make F smooth over k by base change, and the existing representable-diagonal lemma to ensure all the space-to-stack maps are representable. That lemma assumes only representable diagonal, not a DM atlas. No Noetherian assumption on U or X was introduced.

Step 3 uses the calculus for the stabilizer base change, the existing scheme relative-dimension-zero criterion on etale scheme charts, and the existing field-groupoid dimension statement for dim R=dim G. I checked that its hypotheses are exactly local finite type of both projections, not unramifiedness or finiteness. The stabilizer identification is checked on objects: its points are automorphisms of the field object. A chosen identity makes G and R nonempty. The chart criterion gives dimension at every point, rather than merely dimension of a local ring. I corrected an earlier draft that invoked the zero-dimensional decomposition statement to prove zero-dimensionality: that implication would have run in the wrong direction. The final proof cites the scheme dimension-zero criterion instead and declares it as an off-unit generic tool.

Step 4 uses the new parameter statement with E=F. The field point z is the identity of the self-groupoid, hence is k-rational; its image u is closed and k=kappa(u). Its p-fibre is R of dimension zero by step 3. The new statement supplies precisely the regular sequence on an etale chart required in the existing stack-fibre-regular-slice-flat statement. The latter requires a flat locally finitely presented scheme map to a stack, which the chosen smooth chart supplies. The cut is by finitely many functions, and shrinking around u retains z and the dimension-zero field-fibre point. I checked the existing slice statement, rather than using anything from its proof.

Step 5 uses the new fibre-neighbourhood statement on Z to X, which is locally finite type because it is locally finitely presented, exactly as the existing chartwise calculus states. The dimension is dimension at z in Z times_X Spec k, which is the same object produced in step 4. Its open restriction is a scheme, contains u, and preserves flatness and local finite presentation by that calculus.

Step 6 uses the existing scheme coproduct statement for an open disjoint family covering W, the size convention for the index bound, and the algebraic-stack definition for descent on this disjoint open cover. It uses the representable-diagonal lemma for representability of the assembled map and the two calculus statements for its properties on open summands. The finite-type-surjectivity statement applies to a flat locally finitely presented map from an algebraic space, and its image contains every finite-type point by construction, so it gives genuine scheme-base-change surjectivity and hence the field-lifting convention of the item. No density assertion alone is used in place of surjectivity.

I checked small cases: the empty stack uses the empty coproduct; an already zero-dimensional smooth field-space uses the empty regular sequence; E=A^d_k mapping to U=A^d_k at its origin gives the usual coordinate sequence; E=A^d_k mapping constantly to Spec k with d>0 fails the zero-dimensional-fibre hypothesis, so the parameter statement does not assert nonexistent parameters. A non-etale finite stabilizer is permitted throughout; replacing the flat atlas by an etale one would be false and was not done. The quasi-finite neighbourhood statement assumes local finite type, and the descent statement assumes a surjective flat locally finitely presented cover. None of these hypotheses was dropped in use. No step exceeds 2000 characters; their lengths are 530, 462, 722, 652, 434 and 629 characters. Every non-elementary fact is supplied by a cited statement, and every recorded citation quote was checked literally in that statement.

## Not duplicates

lem-sfb-representable-lqf-calculus-descent vs lem-a1-space-separated-lqf-permanence: the existing statement assumes separatedness and a scheme target and gives base change and open restriction; the new one includes nonseparated maps, stack targets, fppf tests and cancellation.

lem-sfb-representable-lqf-calculus-descent vs lem-sfb-representable-proper-fppf-target-test: the existing statement tests properness, rather than local quasi-finiteness.

lem-sfb-representable-lqf-calculus-descent vs lem-sfb-representable-fppf-etale-open-descent: the existing list is flatness, local finite presentation, etaleness and open immersion; it contains no local-quasi-finiteness test.

lem-sfb-representable-lqf-calculus-descent vs lem-sfb-representable-stack-fppf-locality: the existing quasi-finiteness notion includes finite type and finite geometric fibres; it has a quasi-compactness requirement and does not state the locally quasi-finite case.

lem-sfb-representable-lqf-calculus-descent vs lem-sfb-flat-groupoid-quotient-open-presentation: the existing statement constructs quotient presentations and invariant open restrictions for flat scheme groupoids; it gives no generic local-quasi-finite descent or cancellation theorem.

lem-sfb-representable-lqf-calculus-descent vs lem-sfb-space-four-property-fppf-descent: the existing list includes quasi-finiteness with a finite-type hypothesis, not local quasi-finiteness; it also does not give the stack-target and cancellation conclusions.

lem-sfb-representable-lqf-calculus-descent vs lem-sfb-stack-representable-unramified-descent: the existing statement tests unramifiedness, which does not include arbitrary locally quasi-finite maps.

lem-sfb-representable-lqf-calculus-descent vs def-sfb-space-affine-quasifinite-properties: the existing node defines affine and finite-type finite-geometric-fibre quasi-finiteness; it gives no theorem on local-quasi-finite descent or cancellation.

lem-sfb-smooth-fibre-image-parameters vs lem-zl-bertini-finite-cover-irreducible-system: the existing statement concerns general divisors irreducible simultaneously on a finite etale cover; it does not select functions on U whose pullbacks cut an independently specified smooth field-space at a rational point with zero-dimensional U-fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-trf-etale-coordinate-intersection-geometry: the existing statement starts with chosen coordinate parameters and transports regular intersections; the new statement selects parameters from functions on a different scheme using a zero-dimensional fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-trf-power-series-cohen-hypersurface-normality: the existing statement concerns normal ambient power-series rings and cohen hypersurfaces; it does not select functions on U whose pullbacks cut an independently specified smooth field-space at a rational point with zero-dimensional U-fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-trf-parameter-product-strict-local-branches: the existing statement concerns minimal primes of a parameter product in a strict henselization; it does not select functions on U whose pullbacks cut an independently specified smooth field-space at a rational point with zero-dimensional U-fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-trf-regular-local-regular-sequence-depth: the existing statement computes depth of quotients by an already given regular sequence; it does not produce a sequence from the image of a local map.

lem-sfb-smooth-fibre-image-parameters vs lem-trf-regular-ring-universally-catenary: the existing statement concerns noetherian regular rings are universally catenary; it does not select functions on U whose pullbacks cut an independently specified smooth field-space at a rational point with zero-dimensional U-fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-sfb-point-blowup-local-chart-package: the existing statement concerns local chart package for a regular point blowup in dimension at most two; it does not select functions on U whose pullbacks cut an independently specified smooth field-space at a rational point with zero-dimensional U-fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-sfb-parameter-root-boundary-dvrs: the existing statement concerns boundary primes and dvr localizations of a simultaneous parameter-root algebra; it does not select functions on U whose pullbacks cut an independently specified smooth field-space at a rational point with zero-dimensional U-fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-sfb-finite-inertia-flat-quasifinite-presentation: the existing statement assumes finite inertia and constructs a scheme self-relation near a stack point; the new lemma has no stack or inertia and only cuts a smooth field-space at a rational point.

lem-sfb-smooth-fibre-image-parameters vs lem-sfb-transverse-prime-ideal-parameters: the existing statement adapts parameters to specified transverse divisorial primes in one regular local ring; it does not select image parameters for a morphism with zero-dimensional fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-weil-pbc-hypersurface-derivation-regular: the existing statement concerns quotient of a regular ring by an element with a unit derivative is regular; it does not select functions on U whose pullbacks cut an independently specified smooth field-space at a rational point with zero-dimensional U-fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-weil-pbc-popescu-find-sequence: the existing statement assumes a Noetherian source and controls powers of prime generators and annihilators; the new lemma permits an arbitrary scheme U and selects functions by a map to a smooth field-space.

lem-sfb-smooth-fibre-image-parameters vs lem-weil-pbc-regular-local-generators-regular-sequence: the existing statement starts with generators of the maximal ideal in one regular local ring; it does not select a sequence from the image of another local ring.

lem-sfb-smooth-fibre-image-parameters vs lem-weil-pbc-global-complete-intersection-local-regular-sequence: the existing statement concerns the equations of a global complete intersection form a regular sequence at every prime; it does not select functions on U whose pullbacks cut an independently specified smooth field-space at a rational point with zero-dimensional U-fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-weil-pbc-geometrically-regular-over-field-flat: the existing statement concerns flatness over a localized polynomial ring whose variables give a basis of the differentials of a residue subfield; it does not select functions on U whose pullbacks cut an independently specified smooth field-space at a rational point with zero-dimensional U-fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-weil-pbc-regular-local-hypersurface-criterion: the existing statement concerns a non-square element cuts a regular local hypersurface; it does not select functions on U whose pullbacks cut an independently specified smooth field-space at a rational point with zero-dimensional U-fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-weil-pbc-flat-polynomial-append-tensor-fibre: the existing statement concerns flatness of the polynomial-append tensor fibre; it does not select functions on U whose pullbacks cut an independently specified smooth field-space at a rational point with zero-dimensional U-fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-weil-pbc-flat-polynomial-append-fibre-regular-sequence: the existing statement concerns appending closed-fibre regular coordinates preserves flatness; it does not select functions on U whose pullbacks cut an independently specified smooth field-space at a rational point with zero-dimensional U-fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-weil-pbc-regular-ring-normal: the existing statement concerns a regular ring is normal; it does not select functions on U whose pullbacks cut an independently specified smooth field-space at a rational point with zero-dimensional U-fibre.

lem-sfb-smooth-fibre-image-parameters vs lem-weil-pbc-flat-regular-fibre-parameter-selection: the existing statement appends polynomial flat coordinates in a Noetherian algebra with a regular closed fibre; the new statement requires neither that algebraic presentation nor an initially flat local-ring map.

lem-sfb-stack-finite-type-smooth-closed-chart vs lem-sfb-finite-type-point-residual-substack: the existing statement constructs a reduced singleton residual substack; it does not supply a smooth affine chart with a closed lift or the field self-groupoid projections.

lem-sfb-stack-finite-type-smooth-closed-chart vs lem-sfb-stack-locally-closed-finite-type-point: the existing statement asserts finite-type points meet locally closed subsets; it does not characterize a specified finite-type point by a closed lift to a smooth affine chart.

lem-sfb-stack-finite-type-smooth-closed-chart vs lem-sfb-finite-type-point-etale-self-relation: the existing statement assumes an unramified diagonal and constructs an etale field self-relation; the new input has no diagonal finiteness or unramifiedness hypothesis and only claims local finite type.

lem-sfb-stack-quasifinite-fibre-neighbourhood vs lem-sfb-space-quasifinite-locus-open: the existing statement concerns an algebraic-space map to a scheme; the new statement concerns a space-to-stack map and deduces a source neighbourhood from a point of a field 2-fibre.

lem-sfb-stack-quasifinite-fibre-neighbourhood vs lem-sfb-stack-unramified-locus-base-change: the existing statement is about the unramified locus; local quasi-finiteness allows non-etale finite field fibres.

lem-sfb-smooth-fibre-image-parameters vs lem-sfb-quasidm-flat-locally-quasifinite-atlas: the item is an equivalence about a stack diagonal and a global flat locally quasi-finite atlas. The new statement is a geometric local-algebra assertion about an arbitrary scheme U, a smooth algebraic space E over a field, a morphism E to U, and a rational point with zero-dimensional U-fibre. It asserts selection of functions from U and regularity and dimension of their cut, and asserts no stack atlas, flatness over a stack, diagonal condition or surjectivity. It is the independent local-algebra argument of the same source proof, rather than either clause of the item.
