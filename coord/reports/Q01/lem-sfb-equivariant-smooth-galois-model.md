# Worker report: Q01 repair

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-smooth-galois-model.json: statement, split; statement unchanged, five assembly steps (2030 characters).
- dag/nodes/sec-six-functors-basics/lem-sfb-quasi-split-tower-smooth-resolution.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-snc-projective-semilinear-induction.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-generic-orbit-dense-quotient.json: statement, unsplit; no Mathlib match.
- citations.json: one verbatim statement quote for each node cited in each parent step.

## Attachments

None. The project theorem AlgebraicGeometry.exists_equivariant_smooth_galois_model, lean/Sheaf/AlgebraicGeometry/EquivariantSmoothGaloisModel.lean:183, ends in sorry. Searches by the blueprint id and by the notions in lean/WeilConjectures and lean/Sheaf found no completed declaration of the parent or of any extracted node. The field-only smooth alteration in PlurinodalAlteration.lean also has sorry, requires an algebraically closed positive-characteristic field, and supplies no equivariant marked-tower theorem.

## Wanted sources

WANTED: Vidal 2004b, Propositions 4.4.3 and 4.4.4 and the remark following 4.4.4, for the quasi-split marked tower resolution. The existing node already records this source as wanted. I read the available primary ILO exposition, Expose X Lemma 2.2 proof, printed pp.149--150; the new node is sourced to that text, not to an unread primary article.

## Returned point and repair

The return requires at least two comparable statement-only nodes and a parent proof of at most 3000 characters, without deleting any of the 8713-character argument. This delivery adds three independent conditional geometric lemmas. Their pending arguments are approximately 2010, 2006 and 2610 characters of the old proof respectively. All three have status unsplit, empty proof and proof_deps, null proof_origin, complete hypotheses, source places, inherited chapter and unit, and blueprint provenance. No proof sketch is hidden in their statements. Their arguments are preserved in full below for their future workers. The existing statement and all imported/source/Lean metadata are retained. The sandbox initially contained only dispatcher marker files: there were no prior nodes, report, citations or search log to retain. I copied the current returned node without using git, and checked that its nine step lengths match the return.

Allocation: old Steps 1 and 2 remain parent assembly Steps 1 and 2; old Steps 3--4 belong to the tower-resolution node; old Step 5 remains parent Step 3; old Steps 6--7 belong to the induction-permanence node (the common-field existence input remains a separate citation); old Steps 8--9 belong to the quotient node. These are conditional tools on supplied towers, supplied induction data, and supplied invariant maps, respectively; none constructs the whole model, and none merely restates an unconditional clause of the parent.

## Citation mismatch repaired

The old Step 3 takes a quasi-split tower from lem-sfb-equivariant-plurinodal-field-alteration and applies lem-sfb-equivariant-nodal-smooth-pair-resolution, whose current statement requires split marked curves and trivial stabilizer action on marked legs. This is not a valid specialization. The plurinodal input expressly permits permutations. For example, P1 over an algebraically closed field with the involution exchanging two marked smooth points has rational branches but nontrivial action on the marked legs. No parent hypothesis rules that out. The maintainer's notes on both cited nodes flag this mismatch.

The parent now invokes the new tower-resolution statement with precisely the quasi-split hypotheses it has. Its source is the smooth-pair-over-a-field paragraph of ILO X Lemma 2.2, pp.149--150, which treats this entire equivariant tower without the extra stabilizer condition. The parent statement is unchanged. The future worker must prove that theorem for the actual quasi-split action; it must not silently reuse the stronger split-action lemma. The old induction argument is archived below, explicitly subject to this correction. The tower's resolution can instead use equivariant toroidal modification and strictification as in the cited ILO paragraph; no tameness or graph-triviality assumption may be added. This is an exposed pending argument, not an assertion that the existing stronger node covers it.

## Review by Q01

I read the worker brief, stage 1 rules, all of delivery-errors B--E, the three blueprint levels in SETUP, GOAL, the chapter and sk-thm-sf-ctf-stability unit records. I read ILO X 2.2 and 2.3 Step 2 directly in the local PDF (text extraction in this sandbox), including the full passage from the plurinodal alteration through the subdivisor observation, contracted products and diagram (2.b), and the full-quotient universal-homeomorphism assertion on p.151. The parent follows that route before any Sylow selection. No SGA source is used.

For the first new node I checked the hypotheses of the plurinodal output individually: integral finite-type levels, one-dimensional reduced nodal geometric fibres, smooth geometrically integral generic fibres, projectivity/flatness/finite presentation, rational singular points and branches, stable marking unions, and the recursive closed boundary. The node's statement covers the simultaneous successive resolutions and the reduced Cartier sub-boundary, including regular local parameter equations needed by the old factorization argument. Dominance makes a Cartier equation nonzero on the integral top scheme; its zero set is contained in the resolved boundary. The old UFD calculation and the induction data are retained below. This is stronger in its permitted actions than the existing one-curve lemma, and I do not cite that lemma as though its hypotheses held. Zero-length towers force the identity and the empty boundary. Empty markings or C impose no spurious nonempty-divisor condition.

For the second new node I read ILO diagram (2.b) and the statement of lem-sfb-common-field-semilinear-induction: it supplies the finite normal common field, compatible-pair groups, induced scalar-twisted coset copies, purely inseparable fixed field, and orbit/generic-field transfer. It does not state smoothness, SNC permanence, or projectivity. The new node takes these induction data as hypotheses and supplies precisely those geometric consequences. A finite field extension can be inseparable: smooth schemes and smooth component intersections remain smooth on scalar extension. A smooth integral component may split, but its new components are disjoint, so choosing the reduced integral components creates no extra intersection. Intersections from different coset or family summands are empty. The r=0 condition is smoothness of the whole Y. Unequal dimensions of summands cause no codimension ambiguity. The absolute projective-space embedding over e uses finite K/e and composition; graph embedding over the separated (indeed proper) B supplies relative projectivity. It does not assume B itself projective. I read the finite-projective-bundle, ample conversion and H-projective-composition node statements, as well as the base-change statements used in the old argument. Smoothness also supplies reducedness, explicitly included in this new statement for the quotient application.

For the third new node I read ILO p.151 and the exact statement of lem-sfb-admissible-finite-type-field-quotient. That existing statement gives finite subgroup quotients, categorical factorization, geometric orbits, invariant rings, reducedness, and finiteness over a base open where h is finite. It does not give shrinking to a universal homeomorphism from a generic orbit. I checked the exact Noetherian-domain and zero-dimensional-generic-fibre hypotheses in lem-fin-projective-generically-finite. Each B component is integral finite type over e, hence Noetherian. Generic domination with finite residue extensions forces the generic fibre to have dimension zero. The quotient's generic algebra is reduced, finite and has one geometric point, so is a finite purely inseparable field. I read Stacks morphisms.tex Tag 01S4, lemma-universally-injective, and Tag 04DF, lemma-universal-homeomorphism: field-valued injectivity is equivalent to radiciality, and integral + universally injective + surjective is equivalent to universal homeomorphism. The old common q-th-power, denominator AND annihilator clearing calculation is retained in full below. In characteristic zero use q=1; in characteristic p choose one p-power for finitely many generators. This requires neither a faithful action nor tameness. Reducedness is essential to the asserted generic field and is included. The disjoint integral components allow the finitely many shrinking opens to be united and still meet every generic point.

Parent Step 1 cites only the component presentation: its statement supplies normal geometrically integral X_j, finite etale invariant u_j, finite Galois constants, faithful H_j action and the Cartier pullback. The nowhere-dense verification is written explicitly. Parent Step 2 cites the plurinodal alteration and the new tower resolution; the first statement supplies the entire marked quasi-split tower and generic kernel orbits, and the second supplies the smooth top modification with actual Cartier sub-boundary. Parent Step 3 cites those two inputs and the component presentation: the H_j orbit followed by the kernel orbit proves the full J_j orbit, while birationality preserves generic fields. No orbit assertion is borrowed from a proof rather than a statement. Parent Step 4 cites common-field induction for the field/group and orbit data, and the new permanence node for the geometric properties: the S_j are smooth projective and their actual reduced Cartier inverse images are SNC by Step 2, as that node requires. Parent Step 5 cites the new generic-orbit quotient theorem with reduced Y, projective surjective h, correct generic residue fields and orbit assertions already supplied. This is exactly its hypothesis list. Each use has a verbatim statement in citations.json.

I checked B1--B10: each new node is statement-only and self-contained, with definition citations, single-escaped TeX, actual logged searches and source/provenance. I corrected an auxiliary source citation to the exact morphisms.tex labels and Tags 01S4 and 04DF. I checked C1--C8 by opening every cited parent statement and separating the pure induction construction from its geometric permanence; the old split/quasi-split mismatch was repaired instead of assumed away. All new nodes have only statement dependencies, so they introduce no return edge to the parent. I checked D1--D5: the three tasks take intermediate input data and have different independent conclusions, not the whole existence model or mere renamed clauses. I checked E1--E7: hypotheses, generic base fields, relative intersections, empty and inseparable cases, and explicit power localization are as above. No parent step is longer than 2000 characters; the entire parent proof is below 3000. The three new nodes have no steps to hide work.

## Mathlib and blueprint searches

For each new id I ran two distinct LeanFinder phrasings, a Loogle name pattern, a Mathlib source grep and LeanSearch through the required msearch.py command; query text and actual hit summaries are recorded in its mathlib_searches and searches.jsonl. The quotient node has a second, more precise source grep because the initial quotient pattern returned mostly ring-quotient noise. The returned facts about smoothness/base change, Proj, field radiciality and set/topological orbit quotients do not supply any of the new geometric arguments. I inspected Smooth.lean:113--121, StructureSheaf.lean:1094--1126 and UniversallyInjective.lean:40--65 to separate partial facts from exact matches. Thus there are zero new Mathlib leaves. No invented search or unavailable-service-as-no-match record was added.

DAG searches covered the full dag/nodes tree by statements and sources, plurinodal/tower/resolution, stabilizers/graphs, semilinear induction/projectivity and generic quotient/radicial/dense-open keywords. I ran blueprint_refs.py searches for plurinodal, nodal, semilinear, induced, radicial, quotient, relative strict normal crossings, geometric generic fibre, contracted product, marked tower, semilinear induction, and quotient universal homeomorphism. No blueprint node states one of these three conditional tools; basic Frobenius, curve-duality and torsor hits have different hypotheses and conclusions. All three same_as lists are empty. blueprint_refs.py ancestor returns None for this parent; the new nodes retain that null imported ancestor and prepend the parent to its existing via chain, with precise ILO/old-step places. No unit realization is changed: the parent is not the unit's key statement.

## Not duplicates

lem-sfb-quasi-split-tower-smooth-resolution vs lem-sfb-equivariant-nodal-smooth-pair-resolution: The existing statement is one curve and requires split fibres with stabilizers fixing the graph and marked legs; the new node treats a whole quasi-split tower without those assumptions, its compatible successive smooth models and the Cartier sub-boundary.

lem-sfb-quasi-split-tower-smooth-resolution vs lem-per-split-nodal-relative-resolution-charts: The existing statement assumes a split marked curve over a G-strict regular pair with trivial stabilizer graph action; the new node has a field-based quasi-split tower with arbitrary stabilizer permutations.

lem-sfb-quasi-split-tower-smooth-resolution vs lem-sfb-equivariant-plurinodal-field-alteration: The existing statement constructs a nodal tower which need not be smooth; the new node resolves a supplied tower and extracts a supplied Cartier sub-boundary.

lem-sfb-snc-projective-semilinear-induction vs lem-sfb-common-field-semilinear-induction: The existing statement constructs common constants and induced group actions and transfers generic orbits; it states none of the smooth/SNC and absolute/relative projectivity permanence proved by the new node on supplied data.

lem-sfb-generic-orbit-dense-quotient vs lem-sfb-admissible-finite-type-field-quotient: The existing statement gives admissible quotient existence and finiteness when the source map is finite. The new node uses a projective generic orbit to find a dense open with purely inseparable generic quotient field and a universal homeomorphism.

lem-sfb-generic-orbit-dense-quotient vs lem-sfb-finite-quotient-generic-fields: The existing statement identifies generic fields of already supplied normal quotients, without any shrinking-to-homeomorphism assertion; the new node needs only reducedness and supplies that shrinking from geometric generic orbits.

lem-sfb-generic-orbit-dense-quotient vs lem-fin-projective-generically-finite: The existing lemma only shrinks a projective map to a finite one. The new node also constructs subgroup quotients and proves the full quotient radicial on a dense open from its geometric generic orbit.

lem-sfb-generic-orbit-dense-quotient vs lem-sbc-affine-torsor-stabilizer-section-mono: The existing node concerns Monomorphy of a descended section with exact stabilizer; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs sbc-lem-thickening-etale-site: The existing node concerns The etale site of a thickening; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-sbc-radicial-preparation-fibre-comparison: The existing node concerns Radicial preparation fibre comparison; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-sbc-reduced-generic-fibre-field-embedding-core-map: The existing node concerns Dominant map from the reduced generic fibre; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs def-weil-radicial-morphism: The existing node concerns Radicial and universally injective morphisms of schemes; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs def-weil-pbc-scheme-conventions: The existing node concerns Scheme and morphism conventions; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-trf-relative-frobenius-universal-homeomorphism: The existing node concerns Relative Frobenius is an integral universal homeomorphism; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-trf-scheme-frobenius-finite-radicial: The existing node concerns Finiteness and radiciality of the scalar-extended scheme Frobenius; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-pur-absolute-frobenius-universal-homeomorphism: The existing node concerns Absolute finite-field Frobenius is a universal homeomorphism without a finite-type hypothesis; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-trf-weakly-etale-homeomorphism: The existing node concerns A weakly etale universal homeomorphism is an isomorphism; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-trf-proetale-topological-invariance: The existing node concerns Universal homeomorphisms induce equivalences of small pro-etale topoi; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs i-relative-frob: The existing node concerns Relative Frobenius; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-trf-universally-homeomorph-integral: The existing node concerns Universal homeomorphisms are integral; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs i-topology: The existing node concerns Topological invariance; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-pc-integral-radicial-surjective-universal-homeomorphism: The existing node concerns An integral, universally injective, surjective morphism is a universal homeomorphism; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-pc-spec-pure-insep-integral-radicial-surjective: The existing node concerns Spec of a purely inseparable extension is integral, universally injective and surjective; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-pc-homeo-pure-insep: The existing node concerns Base change along a purely inseparable extension is a homeomorphism; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-sfb-proper-pair-radicial-preparation: The existing node concerns Proper normal pair preparation over a radicial constant extension; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-sfb-universal-closed-immersion-open: The existing node concerns The universal closed-immersion locus in the base is open; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-sfb-universal-unramified-radicial-open: The existing node concerns The universal unramified and universally injective locus in the base is open; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-sfb-semilinear-sylow-good-components: The existing node concerns Good components of a semilinear Sylow quotient; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-sfb-equivariant-plurinodal-field-alteration: The existing node concerns Equivariant marked plurinodal alteration over a field; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-sfb-normal-alteration-constant-regularization: The existing node concerns Equivariant regularization of the constants of a normal alteration; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-per-regular-gysin-calculus: The existing node concerns Gysin purity calculus on regular affine schemes; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-weil-pbc-finite-splitting-closed-immersion-descent: The existing node concerns Finite etale-local splitting descends through a surjective closed immersion; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-weil-pbc-descend-universally-injective-qcqs: The existing node concerns Universal injectivity descends for finitely presented qcqs models; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-weil-pbc-descend-open-immersion-qcqs: The existing node concerns Open immersions descend along qcqs affine-transition limits; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-weil-pbc-finite-open-partition-thickening-transport: The existing node concerns Transport finite disjoint open partitions across a thickening; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism: The existing node concerns A surjective closed immersion is a universal homeomorphism; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-weil-pbc-finite-radicial-model-descent: The existing node concerns A finite radicial surjection over a limit has a finite-stage model; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-weil-pbc-reduction-universal-homeomorphism: The existing node concerns The reduction of a scheme is reduced and a universal homeomorphism; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-pur-power-generated-spectrum-homeomorphism: The existing node concerns Power-generated ring maps induce universal homeomorphisms; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-pur-quasifinite-finite-parts-presentation: The existing node concerns Finite-parts presentation of a pulled-back sheaf with proper support; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-weil-pbc-spread-purely-inseparable-factors: The existing node concerns Spreading purely inseparable factors; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

lem-sfb-generic-orbit-dense-quotient vs lem-kun-universal-homeomorphism-exchange: The existing node concerns Underived exchange is invertible for universal-homeomorphism base changes; it does not construct and shrink the full finite-group quotient of a supplied projective generic-orbit map. The shared tag is only the radicial/universal-homeomorphism criterion used inside the new argument.

## Preserved arguments and worker handoff

The following is the returned proof verbatim, including all original citations and source places. Its allocation is indicated for each step. The warning about the unavailable split-action hypothesis in old Step 3 applies; the new quasi-split tower node is the replacement obligation. These paragraphs are handoff material in the report, not proof fields on the new unsplit nodes.

### Returned Step 1 — Parent assembly Step 1

Write $B=\coprod_{j=1}^n B_j$ using the given finite disjoint integral components. Apply the Galois component presentation to each $B_j$. It gives $e_{0j}/e$, a normal geometrically integral proper $e_{0j}$-scheme $X_j$, its finite group $H_j$, and $u_j:X_j\to B_j$. In particular $u_j$ is finite etale surjective and its geometric fibres are single $H_j$-orbits. The pullback of $C_B$ is an $H_j$-stable Cartier support $Z_j$. This also verifies the nowhere dense hypothesis: in an integral local domain a nonzero Cartier equation does not vanish at the generic point. The faithful semilinear action and geometric integrality are exactly the hypotheses of the nodal-tower input, not properties inferred merely from the notation $B_{e_{0j}}$.

Cited nodes: lem-sfb-galois-component-presentation.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.3 Step 2, p.150, geometric component and decomposition subgroup.

### Returned Step 2 — Parent assembly Step 2

For each $(X_j/e_{0j},H_j,Z_j)$ apply the equivariant marked plurinodal alteration. Denote its constants by $F_j$, its group by $J_j$, the surjection by $\rho_j:J_j\to H_j$, and its tower and marked closed sets by $T_{ji},Z_{ji}$. We obtain an equivariant projective generically finite surjection $a_j:T_{jd_j}\to X_j$, with $a_j^{-1}Z_j\subseteq Z_{jd_j}$. Over a dense open of $X_j$, every geometric fibre is one orbit under $N_j=\ker\rho_j$. Retain this orbit assertion when making the following birational modifications; it will control the full quotient, rather than only the degree of the alteration.

Cited nodes: lem-sfb-equivariant-plurinodal-field-alteration.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.2 proof, p.149, application of Vidal 4.4.3.

### Returned Step 3 — lem-sfb-quasi-split-tower-smooth-resolution

Resolve the tower by induction on $i$. The induction data are a smooth integral projective $F_j$-scheme $S_{j,i-1}$ with an equivariant projective birational map to $T_{j,i-1}$ and relative SNC boundary equal to the reduced preimage of $Z_{j,i-1}$. Start with $S_{j0}=\operatorname{Spec}F_j$ and empty boundary. Apply the one-curve resolution lemma to $f_{ji}:T_{ji}\to T_{j,i-1}$, $D=Z_{j,i-1}$, its marked sections and the already constructed base modification $S_{j,i-1}\to T_{j,i-1}$. Its conclusion resolves the fibre product and makes the composite back to $T_{ji}$ projective birational and surjective, giving $S_{ji}$ and precisely that induction datum with $i$ in place of $i-1$. The projectivity clause of the lemma applies because the preceding base is projective over $F_j$. At the top obtain $S_j=S_{jd_j}$, smooth integral projective over $F_j$, with equivariant birational $r_j:S_j\to T_{jd_j}$ and relative SNC boundary $E_j=(r_j^{-1}Z_{jd_j})_{\mathrm{red}}$. The lemma gives regular local rings and parameter equations for $E_j$. Length zero requires no resolution. Each modification induces equality of function fields; thus $a_jr_j$ remains dominant and generically finite.

Cited nodes: lem-sfb-equivariant-nodal-smooth-pair-resolution, lem-sfb-equivariant-plurinodal-field-alteration.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.2 proof, p.149 last paragraph--p.150, successive applications of Vidal 4.4.4.

### Returned Step 4 — lem-sfb-quasi-split-tower-smooth-resolution

The reduced inverse image $D_j$ of $C_B$ in $S_j$ is a sub-divisor of $E_j$, not necessarily the whole marked boundary. Indeed, the composite $S_j\to B_j$ is dominant, so a local Cartier equation $c$ on $B_j$ pulls back to a nonzero element in the integral local ring of $S_j$. Off $E_j$ it is a unit, since its zero set is contained in $E_j$. At a point, write the boundary equations as distinct regular parameters $t_1,\ldots,t_r$. The cited regular-local UFD factorization gives $c=u\prod t_i^{a_i}$. Its reduced zero divisor is therefore cut out by $\prod_{a_i>0}t_i$. Globally these are a subset of the finitely many components of $E_j$. Their intersections are among the same smooth intersections, with the same codimensions, so $D_j$ is relative strict normal crossings. If $c$ is a unit, this subset is empty.

Cited nodes: lem-trf-regular-local-ufd-boundary-factorization, lem-sfb-equivariant-nodal-smooth-pair-resolution, def-trf-smooth-strict-normal-crossings-divisor.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.2 proof, p.149, the reduced inverse image is a subdivisor of the resolved marked boundary.

### Returned Step 5 — Parent assembly Step 3

Put $v_j=u_ja_jr_j:S_j\to B_j$. It is $J_j$-invariant since $u_j$ is $H_j$-invariant. At a geometric generic point of $B_j$, its lifts to $X_j$ form one $H_j$-orbit by the component presentation. Above each such lift, the geometric generic fibre of $a_jr_j$ is one $N_j$-orbit: the birational map $r_j$ induces equality of generic residue fields, and hence changes none of these geometric generic fibres. Given two points, first lift an element of $H_j$ carrying their images to one another along the surjection $\rho_j$, then use an element of $N_j$ in that fibre. Thus the whole geometric generic fibre of $v_j$ is one $J_j$-orbit. All generic residue extensions remain finite, and every generic point maps to the generic point of $B_j$.

Cited nodes: lem-sfb-galois-component-presentation, lem-sfb-equivariant-plurinodal-field-alteration, lem-sfb-equivariant-nodal-smooth-pair-resolution.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.2(iii) and X 2.3 Step 2, before (2.b): two-stage orbit argument.

### Returned Step 6 — lem-sfb-snc-projective-semilinear-induction

Apply common-field semilinear induction to the finite family $(F_j,J_j,S_j,v_j)$. Obtain one finite normal $K/e$, one finite group $G$ acting on $K$, and the induced schemes $Y_j$ with invariant maps to $B_j$. Set $Y=\coprod_jY_j$ and $h=\coprod_j(Y_j\to B_j)$. The induction lemma gives $K^G/e$ purely inseparable, single $G$-orbit geometric generic fibres, and finite residue extensions at every generic point. Every summand of $Y$ is a scalar twist of $S_j\times_{F_j}K$. Consequently $Y$ is smooth projective over $K$ and the reduced inverse image of $C_B$ is relative SNC: field extension preserves smoothness and all the intersection codimensions; any components that split are disjoint smooth components, so taking the reduced irreducible components gives the same condition. Twisting changes only the scalar structure. Finite disjoint unions preserve these properties (embed the finitely many projective summands in disjoint linear subspaces of one sufficiently large projective space). The map $h$ is surjective since each $v_j$ is surjective, the field base changes are surjective, and every coset family is nonempty.

Cited nodes: lem-sfb-common-field-semilinear-induction, def-trf-smooth-strict-normal-crossings-divisor, lem-sbc-smooth-relative-dimension-permanence, lem-sc-fibre-dimension-after-base-change, lem-weil-pbc-closed-immersion-base-change, def-kun-projective.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.3 Step 2, diagram (2.b); finite-family common normal constants and induced conjugate copies.

### Returned Step 7 — lem-sfb-snc-projective-semilinear-induction

The projective $K$-scheme $Y$ is also H-projective over $e$. The finite map $\operatorname{Spec}K\to\operatorname{Spec}e$ is projective-bundle by the finite-morphism lemma; $\mathcal O$ is ample on the affine point (the section $1$ has affine nonvanishing locus), so the ample-base conversion makes it H-projective, and H-projective composition applies. Choose $i:Y\hookrightarrow\mathbf P^m_e$. Since $B$ is proper over $e$, its diagonal is closed. The graph $Y\to Y\times_eB$ of $h$ is its base change, and $i\times\mathrm{id}_B$ is also a closed immersion by base change. Their composite embeds $Y$ into $\mathbf P^m_e\times_eB=\mathbf P^m_B$ over $B$. Thus $h$ is H-projective and therefore projective in the projective-bundle convention as well (use the free module $\mathcal O_B^{m+1}$). This establishes projectivity even though $B$ need not itself be projective over $e$.

Cited nodes: lem-trf-finite-projective-bundle, def-weil-pbc-ample-invertible-module, lem-trf-projective-bundle-to-h-projective, lem-trf-h-projective-composition, def-weil-proper-morphism, lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-closed-immersion-comp, def-nagata-projective-space-base-change, def-kun-projective, def-trf-projective-bundle-morphism.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.3 Step 2, projectivity of the induced alteration (graph verification).

### Returned Step 8 — lem-sfb-generic-orbit-dense-quotient

Apply finite quotient existence over $e$ to $Y$ and to every subgroup of $G$; the preceding projective embedding supplies its quasi-projective admission hypothesis. This gives all the finite categorical geometric quotients and their orbit and invariant-sheaf properties. In particular $h$ factors through $Q=Y/G$. For each $B_j$, choose a nonempty affine open $\operatorname{Spec}A_j$. It is Noetherian by the component preparation. The morphism $h$ is projective and its generic fibre is zero-dimensional, since its finitely many generic residue extensions are finite. The projective-generically-finite lemma gives a nonempty open on which $h$ is finite; shrink this to a principal affine open in $\operatorname{Spec}A_j$. The quotient lemma then gives finiteness of $Q\to B$ there. These finitely many opens together meet every component. The generic fibre of $Q\to B_j$ is reduced, since invariant subrings of reduced rings are reduced, and has one geometric point by the orbit calculation. The radicial criterion applies also over the generic field: two distinct field-valued lifts would remain distinct over an algebraic closure, contradicting the one-point geometric fibre. Thus this generic morphism is radicial. Its reduced finite coordinate algebra has a single prime ideal, which is zero; being a finite-dimensional domain, it is a field, purely inseparable over $\kappa(B_j)$ by the same criterion.

Cited nodes: lem-sfb-admissible-finite-type-field-quotient, lem-sfb-galois-component-presentation, lem-fin-projective-generically-finite, def-weil-radicial-morphism.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.3 Step 2, p.151, full quotient is generically radicial; retain actual finite quotients.

### Returned Step 9 — lem-sfb-generic-orbit-dense-quotient

Here is the dense-open radicial verification. On one of the preceding affine opens write $A\subseteq L=\operatorname{Frac}A$ and $Q=\operatorname{Spec}R$ with $R$ finite over $A$. Its generic algebra $R\otimes_A L$ is the purely inseparable field just found. Choose finitely many algebra generators $b_i$ of $R$. In characteristic $p>0$, choose a common $q=p^r$ with $b_i^q\in L$ in the generic algebra. Clear the finitely many denominators and annihilators of $b_i^q-a_i$ to obtain one nonzero $s\in A$ and $a_i\in A[1/s]$ such that $b_i^q=a_i$ in $R[1/s]$. In characteristic zero the generic field equals $L$ and the same argument uses $q=1$. For any field $M$ over $A[1/s]$, an $M$-valued point of $Q$ must send each $b_i$ to the unique possible root of $T^q-a_i$ in $M$. Hence there is at most one such point. The cited radicial criterion proves universal injectivity. Surjectivity holds because both $h$ and the quotient map are surjective. The integral-radicial-surjective lemma now makes this finite morphism a universal homeomorphism. Taking the union of these principal opens gives the required dense $U$ meeting every component. This last shrinking changes none of $Y,K,G,h$ or the boundary.

Cited nodes: def-weil-radicial-morphism, lem-pc-integral-radicial-surjective-universal-homeomorphism.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.3 Step 2, p.151, verification of the universal-homeomorphism assertion on a dense open.

## Remaining work

The three new nodes are intentionally unsplit work items, as the human's re-split decision requires. No Lean, compiler or Lake tool was written or run. First server dry run: OK (not pushed) at f425883bd8f; preflight passed. Final terminology audit made the normal-field condition explicit and cited geometrically reduced and reduced scheme definitions in the induction node; all parent statement text remains unchanged. Final dry run and push follow these edits.
