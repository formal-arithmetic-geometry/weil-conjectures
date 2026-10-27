## Worker report

Files written, all under the item sandbox:

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-picard-h1-natural.json`: the item, statement unchanged, nine proof steps, status split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-site-abelian-torsor-h1.json`: new statement-only prerequisite, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-topos-cohomology-pullback-delta.json`: new statement-only prerequisite, unsplit; no Mathlib match.
- `citations.json`: an exact statement quotation for every node used in every proof step.

Attachments: none. The project declarations in `WeilConjectures/AlgebraicGeometry/Sites/GmPicard.lean` concern schemes. The general-site declarations in `WeilConjectures/CategoryTheory/Sites/Torsor.lean`, including `CategoryTheory.Sheaf.nonempty_equiv_H_one_torsor`, require a terminal object in the presenting category. Neither states this arbitrary-ringed-topos item or the no-terminal-object prerequisite. `PicardH1RestrictionCompatibility.lean` is also scheme-specific. No Lean was written or compiled.

WANTED: none. Sources used are present locally.

What needed repair: the imported item has no proof, and the nearest existing torsor and Picard DAG nodes are restricted to scheme sites. I retained the exact statement, including its precise injective-resolution pullback map, its no-flatness clause, its universe restriction and its final-sheaf definition of global sections. I did not use a scheme-only result as a general-site theorem. The ancestry tool returns `None` for the imported item's nearest blueprint ancestor; the item already records a long explicit ancestry place and via list. I retained that null ancestor, extended its place for the two children and prepended the item to their via lists, rather than inventing a blueprint id. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-image proof. This is a prerequisite within the inherited Picard-obstruction branch; no unit or chapter route is replaced and this item is not the unit's key statement.

Unfinished: the two new prerequisites are deliberately unsplit as the stage-1 brief requires. Their complete, self-contained statements specify the torsor extension and the resolution map respectively. There is no unreported gap in the assembly proof conditional on those cited statements.

## Source error

In Stacks Tag 040E, `sites-cohomology.tex`, `lemma-h1-invertible`, the surjectivity paragraph says that the sectionwise orbit quotient is a presheaf of modules. On an object where the torsor has no section that quotient is empty, so it has no zero. For example take a nontrivial line bundle L on the Zariski site of the projective line over a field and T its frame torsor. T has no global section, so `(T(P1) × O(P1))/O(P1)^×` is empty. This is a construction-level error, not an error in the theorem. Step 2 first sheafifies the SET quotient, and defines all module operations on the resulting locally trivial sheaf. It supplies the missing zero by gluing the local zero sections. It proves independence of frame by the linear coordinate change `a ↦ ua`. The item statement does not change and is not statement-disputed.

040E itself assumes a locally ringed site to deduce rank-one local freeness from its invertibility convention. Here local freeness of rank one is the definition of a line, so that hypothesis is not used or silently imported.

## Proof plans retained for the new nodes

For `lem-sfb-site-abelian-torsor-h1`, I read 03AJ (`lemma-torsors-h1`), 03AH (`definition-torsor`) and 01FT (`section-cohomology-sheaves`) in `sites-cohomology.tex`. The quotient `(G ⊕ Z[T])/(g,[t]-[g+t])` is locally the extension `G ⊕ Z`: after choosing t0, `[g+t0]` goes to `(g,1)`. This proves its kernel, cokernel and fibre statements, and also corrects the ambiguous shorthand that identifies a generator difference directly with an element of G before adjoining G. The map t ↦ [t] is locally the bijection to degree one. To verify the inverse omitted in 03AJ, embed G into an injective I, set Q=I/G and extend G→I across the monomorphism G→E_T by injectivity. The resulting T→I is G-equivariant, its image in Q is invariant and therefore glues to a global section q, and the map to the lifts of q is locally a bijection. The boundary class is δ(q). Every H1 class is such a boundary because I has vanishing positive cohomology. Two lifts torsors for q,q' are isomorphic exactly when q'-q lifts to a global section of I: subtract their equivariant maps to I to obtain the invariant global difference, and conversely translate by that global lift. This identifies both sides with Γ(Q)/im Γ(I). For any other extension E, an extension map to I identifies its fibre class with its boundary by naturality of the long exact sequence. The trivial fibre is a global translate and has zero class. If T,T' map equivariantly into I with quotient sections q,q', addition in I descends to their contracted product and gives its isomorphism with the lifting torsor of q+q'. This verifies the group-law clause without a terminal object of the site. These are plans in the report only; the new node carries no proof or proof dependencies.

For `lem-sfb-topos-cohomology-pullback-delta`, I read 01FT and 08J6 (`remark-before-Leray`) in `sites-cohomology.tex`, 01F8 (`lemma-functoriality`) in `cohomology.tex`, and the 015B higher-derived universal-delta-functor statement. The source 01F8 is for ringed spaces; the node explicitly records the extension to geometric morphisms, rather than pretending its stated scope already covers them. Exact inverse image carries a source resolution to a resolution. The comparison theorem into an injective resolution gives β, unique up to augmented chain homotopy. Apply the sections unit degreewise; homotopies survive the additive sections functor and therefore have equal cohomology maps. Source and target comparison maps give independence of both resolutions and naturality. For the boundary identity, use injective horseshoes for the source short exact sequence and its exact inverse image; choose comparison maps compatibly on the horseshoes. Degreewise split short exact rows stay split under inverse image and stay exact under global sections. The resulting morphism of short exact section complexes commutes with their homology boundaries. Resolution independence identifies these with the prescribed P_f and derived cohomology boundaries. The coefficient-morphism boundary clause is the ordinary naturality of the same long exact sequence. Γ(f_*M)=Γ(M) follows from adjunction and preservation of the final sheaf, so the construction uses no presented site functor. The new node again carries only this theorem's statement, not these plans.

## Review by Q15

I reviewed the actual JSON statements and the source paragraphs, not just the dependency lists. For the item, 040E supplies the frame construction and its inverse, and 03AJ supplies the abelian torsor route. I verified that neither a final site object nor a local-ring condition is used in the rewritten rank-one argument. The two new statements were checked against the sources just identified, with their explicit additional boundary and group-law clauses justified by the retained plans above. Each is a general abelian-sheaf prerequisite, not a new restatement of the Picard isomorphism or its naturality clause.

Step 1 uses only the stated definition of module sheaves and local freeness. The values at one and their inverse maps are glued explicitly; the unit relating two frames is `(t^{-1}t')(1)`. The sheaf condition gives the elementary locality arguments.

Step 2 uses `lem-weil-pbc-site-sheafification-sections-local` for local representatives AND local equality. I checked its statement gives both and uses a universe containing the site data, which is available here by the item's size convention. The section coefficient construction is written out, not an unsupported reference to effective module descent. The module definition node states exactly what the glued operations must satisfy.

Step 3 is elementary from those charts: evaluation and the frame map have local inverse formulas, and uniqueness makes them glue. It is not a citation of the proof of the scheme-specific line-bundle torsor node.

Step 4 uses `def-pur-sheaf-tensor-product`, whose statement defines sheaf tensor by sectionwise tensor and sheafification, and the full statement of the new torsor H1 node, which explicitly gives the contracted-product law and zero. The tensor maps `a⊗b ↦ ab`, `c ↦ c⊗1` are inverse by balancing. Dual frames give the inverse line. The Picard group isomorphism is assembled here; it has not been moved into a child node.

Step 5 uses `lem-trf-geometric-inverse-image-exact`, whose statement covers arbitrary geometric morphisms rather than only morphisms of presented sites, and the new resolution-pullback node. I matched its unit/adjunction/β composite literally with the one in the item. I do not claim f^{-1} preserves injectives. Its exactness is what makes β a comparison from a resolution.

Step 6 uses `lem-weil-pbc-inverse-image-local-families` for local sections of f^{-1}T; the node's statement covers any left adjoint on set sheaves and does not assume a presenting site functor. Finite limits are supplied by the cited ringed-topos definition, not by a definition of site pullback. `lem-weil-pbc-geometric-module-construction` explicitly transports scalar actions through the finite-product comparison; this is precisely the linearity of the pulled evaluation trivialization. The tensor definition and balancing relation give the displayed scalar-extension inverse. The equivariance formula is included, and no exactness of B⊗- is asserted.

Step 7 uses the full extension-and-fibre clause in the torsor node and exact abelian inverse image in the geometric exactness node. The ringed-topos definition gives finite-limit preservation, which identifies the fibre over one with f^{-1}T. I added the existing left-adjoint-colimit theorem and the sheafification universal property for preservation of the integer sheaf: the coproduct characterization is proved in the step and its operations are preserved by finite products. Thus no unrecorded theorem about constants is used.

Step 8 is the elementary extension-map calculation using the two exact extensions: on a local frame send h+n j(v) to ρ(h)+n j'(s(v)), and changing v to u+v changes the two terms by -nρ(u) and +nρ(u). This proves overlap compatibility, additivity and the end maps. It does not assert that an unidentified transport commutes with boundaries.

Step 9 uses both clauses of the resolution-pullback node: first its pullback boundary formula, then its coefficient-morphism boundary naturality. The torsor node identifies the three boundary-of-one classes. This proves precisely `c_B([f*L])=H1(ρ)(f*c_A([L]))`.

Small cases: with the zero ring the unit sheaf is trivial, the sole line is zero and its frame torsor is the final sheaf; all maps reduce to the zero group identity. With the identity geometric morphism β may be the identity and the formula is the coefficient-change formula. With the identity ring map it is pure inverse image. Nonflat scalar change Z→Z/nZ still has the explicit inverse on a rank-one chart, so no flatness is needed. A site with no terminal object is handled everywhere using Hom(*,-); the torsor classification source itself is stated for an arbitrary site. The degenerate sheaf topos also has singleton torsor and cohomology classes. For the new torsor node, local trivial torsors give the split extension G⊕Z and boundary zero; the transition relation has the correct positive sign. For the new cohomology node, q=0 sends one to one and the displayed boundary equation is well typed. These tests detected no false statement.

I searched the full DAG by tags 040E, 03AJ and 03AH and by torsor/Picard/pullback concepts, and used `tools/blueprint_refs.py search` for torsor, invertible, torsors and, cohomology pullback, cohomology of units, and functoriality of cohomology. The scheme-only candidates were opened, including `lem-sc-torsor-h1`, `lem-sc-line-bundle-torsor`, `lem-sc-h1-gm-pic`, `lem-sc-h1-gm-pic-pullback`, and the Zariski/etale functoriality nodes. No candidate gives the arbitrary-site statements. The Mathlib queries are exactly those in searches.jsonl. I read the hits and the source of SheafCohomology/Basic.lean, NonabelianCohomology/H1.lean and Abelian/RightDerived.lean: fixed-family Cech H1, the definition of Ext cohomology, and same-source right-derived transformations do not give either new theorem. Every new node has a second semantic phrasing plus Loogle, LeanSearch and grep. No unavailable service was recorded as absence.

I checked delivery-errors B1–B10: self-contained TeX statements, actual Stacks labels, unchanged import metadata, statement-only children, real logged searches, and no false attachment. For C1–C8 I read every cited statement, checked all exact quotations locally, rejected scheme-only citations, tested dependency closures for cycles, and declared generic off-unit tools in split_report. For D1–D5 the nine steps carry the line-module and extension-map arguments; both children are smaller general prerequisites, and 040E's omitted chart checks are supplied. For E1–E7 I checked ranks, universes, site versus topos hypotheses, exactness versus flatness, and the sign and change-of-frame equations. No step exceeds 2000 characters. The source construction error and its repair are recorded above. The server check_dag call passed with no finding introduced by the sandbox. The final deliver.py dry run and push are the remaining validation and handoff.

## Not duplicates

lem-sfb-site-abelian-torsor-h1 vs lem-sfb-finite-cover-derived-presheaf-continuity: the existing theorem is filtered-colimit continuity under finite-cover hypotheses, not a torsor classification.

lem-sfb-site-abelian-torsor-h1 vs lem-weil-pbc-zariski-etale-resolution-cocycle-compatibility: the existing theorem is chain-map naturality of individual cycle classes, not a torsor classification.

lem-sfb-site-abelian-torsor-h1 vs new-module-cohomology-ext-resolution-naturality: the existing theorem compares module and Ext cohomology of schemes, not torsors on arbitrary sites.

lem-sfb-site-abelian-torsor-h1 vs lem-weil-pbc-abelian-derived-global-ext-pullback: the existing theorem compares scheme etale derived and Ext pullbacks, not arbitrary-site torsors.

lem-sfb-site-abelian-torsor-h1 vs lem-weil-pbc-zariski-etale-resolution-pullback-cocycle: the existing theorem assumes scheme Zariski/etale sites and proves a counit cocycle formula; it does not classify torsors.

lem-sfb-site-abelian-torsor-h1 vs def-weil-pbc-sites-and-cohomology: the existing definition specifies sites and object cohomology; it supplies no torsor classification.

lem-sfb-site-abelian-torsor-h1 vs lem-weil-pbc-free-representable-homotopy-homology: the existing theorem compares homotopy classes and evaluated homology presheaves; it says nothing about torsors.

lem-sfb-site-abelian-torsor-h1 vs new-sheaf-cohomology-derived-evaluation: the existing theorem identifies Ext with derived evaluation at a terminal site object; the new theorem classifies torsors without such an object.

lem-sfb-site-abelian-torsor-h1 vs lem-weil-pbc-pullback-cohomology-long-exact-ladder: the existing theorem is an etale scheme pullback ladder; it is not a torsor classification on arbitrary sites.

lem-sfb-site-abelian-torsor-h1 vs lem-weil-pbc-zariski-etale-pullback-map-ext: the existing theorem identifies prescribed Zariski/etale object-cohomology maps with an Ext formula, not torsor classes.

lem-sfb-site-abelian-torsor-h1 vs lem-weil-pbc-object-resolution-cocycle-equivalence: the existing theorem compares representable-source Ext classes and resolution cycles over one site object; no torsors occur.

lem-sfb-site-abelian-torsor-h1 vs lem-weil-pbc-zariski-etale-resolution-cocycle-homology: the existing theorem concerns two scheme-site cocycle/homology comparisons, not torsor classification.

lem-sfb-topos-cohomology-pullback-delta vs lem-sc-p1-horseshoe-derived-triangle-comparison: the existing theorem identifies endpoint homology of a specified horseshoe triangle comparison; it does not construct global cohomology pullback across a geometric morphism.

lem-sfb-topos-cohomology-pullback-delta vs lem-sc-affine-basis-acyclic-sections-preserves-homology: the existing theorem is an acyclicity criterion on affine opens of schemes, not geometric-topos cohomology pullback.

lem-sfb-topos-cohomology-pullback-delta vs lem-sc-p1-injective-resolution-derived-comparison-naturality: the existing theorem is naturality in an object morphism for one functor; the new theorem crosses an exact inverse image and normalizes the sections unit.

lem-sfb-topos-cohomology-pullback-delta vs lem-sc-p1-right-derived-triangle-connecting: the existing theorem identifies horseshoe and triangle boundaries for one functor; it gives no geometric inverse-image pullback.

lem-sfb-topos-cohomology-pullback-delta vs lem-sc-p1-right-derived-injective-boundary: the existing theorem compares a derived functor with a boundary on a specified injective short exact complex; it has no sections unit or geometric morphism.

lem-sfb-topos-cohomology-pullback-delta vs lem-sc-integer-section-acyclic-incoming-kernel-image: the existing theorem is a vanishing consequence for kernel and image cohomology on a scheme, not a pullback theorem.

lem-sfb-topos-cohomology-pullback-delta vs lem-sc-p1-horseshoe-comparison-boundary: the existing theorem compares boundaries on one fixed horseshoe and functor; it does not compare global sections across topoi.

lem-sfb-topos-cohomology-pullback-delta vs lem-sc-p1-injective-resolution-derived-comparison: the existing theorem constructs the resolution comparison for one functor; it does not construct the morphism of cohomology functors across an exact inverse image.

lem-sfb-topos-cohomology-pullback-delta vs lem-weil-pbc-site-cohomology-pullback-data: the existing node defines a family for a continuous site functor; the new theorem proves choice independence and boundary compatibility for arbitrary geometric morphisms with no site functor.

lem-sfb-topos-cohomology-pullback-delta vs lem-weil-pbc-site-cohomology-pullback: the existing theorem assumes a specified continuous site functor and evaluates at site objects; the new theorem uses final-sheaf global sections and any geometric morphism.

lem-sfb-topos-cohomology-pullback-delta vs lem-weil-pbc-module-cech-vanishing-criterion: the existing theorem is Cech-to-derived vanishing on schemes; it neither constructs pullback nor compares boundaries across topoi.

lem-sfb-topos-cohomology-pullback-delta vs lem-weil-pbc-site-cohomology-pullback-exists: the existing theorem asserts existence for a specified continuous functor and object cohomology; the new theorem treats arbitrary geometric morphisms and the explicitly prescribed resolution composite.

lem-sfb-site-abelian-torsor-h1 vs lem-sc-torsor-h1: the existing statement is restricted to schemes and their etale/Zariski sites; the new statement is for every small site, with no terminal object, and explicitly gives arbitrary-extension fibres.

lem-sfb-topos-cohomology-pullback-delta vs lem-weil-pbc-right-derived-universal-delta-functor: the existing theorem is universality for one left exact functor; the new theorem identifies the specific two-resolution unit composite across exact inverse image and its boundary compatibility.

lem-sfb-site-abelian-torsor-h1 vs cohomology-site-equivalence-fixed-degree: the existing theorem compares object-cohomology presheaves under an equivalence of presenting sites; it does not classify torsors.

lem-sfb-site-abelian-torsor-h1 vs lem-sc-cohomology-resolution-evaluation-natural: the existing theorem compares Ext cohomology and evaluated injective resolutions at a terminal site object; it gives neither torsors nor the no-terminal-object classification.

lem-sfb-site-abelian-torsor-h1 vs lem-sc-site-cohomology-right-derived-sections: the existing theorem identifies object cohomology with derived evaluation; the new theorem is a classification by global derived H1 of arbitrary abelian torsors.

lem-sfb-site-abelian-torsor-h1 vs lem-sc-topological-terminal-resolution-ext-comparison: the existing theorem normalizes an Ext/resolution comparison for a continuous map of spaces; it makes no assertion about torsor classes.

lem-sfb-site-abelian-torsor-h1 vs new-etale-cohomology-natural-derived-evaluation: the existing theorem compares scheme etale Ext cohomology with derived evaluation at a terminal object; it does not classify torsors on arbitrary sites.

lem-sfb-site-abelian-torsor-h1 vs def-weil-pbc-etale-cohomology-presentation: the existing definition fixes the evaluation comparison for scheme etale cohomology; the new theorem constructs and classifies arbitrary-site torsor extensions.

lem-sfb-site-abelian-torsor-h1 vs lem-weil-pbc-etale-object-cohomology-stalk-complex: the existing theorem identifies a colimit of scheme-object cohomology with a stalk section complex; it says nothing about torsors.

lem-sfb-site-abelian-torsor-h1 vs lem-weil-pbc-object-cohomology-presheaf-resolution: the existing theorem compares a supplied resolution's homology presheaf with object cohomology, with no torsor statement.

lem-sfb-topos-cohomology-pullback-delta vs lem-sc-boundary-horseshoe-representative: the existing theorem represents a degree-zero boundary by a cycle for a scheme module-sheaf horseshoe; the new theorem constructs resolution pullback across arbitrary geometric morphisms and proves its boundary compatibility in all degrees.

lem-sfb-topos-cohomology-pullback-delta vs lem-sc-resolved-boundary-naturality: the existing theorem is coefficient naturality of a chosen resolution representative for one left exact functor, not cohomology pullback across two sheaf topoi.

lem-sfb-topos-cohomology-pullback-delta vs stage3-boundary-global-lift: the existing theorem only produces lifts and cycles for a specified scheme horseshoe; it has no inverse image or global-cohomology pullback map.

lem-sfb-topos-cohomology-pullback-delta vs stage3-boundary-identification: the existing theorem identifies a prescribed scheme module-boundary representative with its cycle class; it does not give resolution independence or geometric pullback compatibility.
