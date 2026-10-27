# Stage-1 report: lem-sfb-space-relative-proj-quotient-closed-immersion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-proj-quotient-closed-immersion.json — statement, split into seven steps, not a Mathlib leaf.
- citations.json — 28 step/node pairs with verbatim quotations from the live cited statements.

No new nodes and no new Mathlib leaves. No Lean written, compiler or Lake invoked, repository files edited, or repository git commands run. The existing sandbox initially contained only dispatcher markers; its item copy was initialized from the live repository. Searches are recorded in searches.jsonl by the prescribed msearch.py command. The local write_split.py only constructs this sandbox's JSON and citation records.

## Attachments

None. Searched the live lean/WeilConjectures tree for the exact blueprint id and relative-Proj/quotient/closed-immersion vocabulary. The scheme declaration AlgebraicGeometry.Scheme.GradedAlgebraData.isClosedImmersion_relProjMap, WeilConjectures/AlgebraicGeometry/RelativeProj/Functoriality.lean:150, covers the existing scheme functoriality node, not this item over algebraic spaces. Its presence does not establish this item's construction on all scheme tests, uniqueness or composition clauses.

## WANTED

None. All source material used is present under literature/.

## Corrections and route

The imported source reference is appropriate: spaces-divisors.tex Tags 085F (lemma-morphism-relative-proj), 085H (lemma-surjective-graded-rings-map-relative-proj), and 085G (lemma-morphism-relative-proj-transitive). Their omitted descent/transitivity details have been expanded using existing generic nodes. The statement's closed-immersion sentence is clarified to say explicitly that the space morphism is representable by schemes and is a closed immersion on every scheme base change. The old reference def-weil-closed-immersion defines only the scheme notion; adding the existing atlas-locality node and this inline explanation supplies the intended space meaning. This changes no hypothesis or mathematical conclusion.

The quotient functor lemma is used as a genuine general tool, not as a replacement statement of the item: it describes maps from arbitrary schemes to the Proj of a single algebra. Precomposition by the given surjection, its well-definedness, naturality, the resulting space morphism, and its closed-immersion property are proved in the item's steps.

Read SETUP's three levels and the chapter/unit records. The latest blueprint is main-20261024; read its sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and direct-images proof paragraph (3), where compactification enters. Also read the latest scheme relative-Proj functoriality statement/proof under sec-nagata-compactification/sk-def-nagata-admissible. The inherited from.place locates the supporting quotient closed immersion in the finite-degree-ideal descent argument (0860 via 085M/085H). blueprint_refs.py ancestor returns None on this inherited chain, so the existing from.node=null and via list are retained, not replaced with an invented ancestor. The latest scheme blueprint has a stronger affine-base version of clause (4) than the live DAG's flat clause; this split only takes clauses (1) and (3) of that node, and proves the needed naturality separately. No unit route or realization is changed.

## Source error

In the local Stacks text, Tag 085H clause (2) reads r_psi:Q -> R, but R is not defined in its preceding setup; the target is P, as in Tag 085F and the scheme counterpart 07ZI. The item already has the correct target P_X(A). This is a source notation typo, not a false item and not a reason to change its mathematical content.

## Mathlib and duplicate searches

Ran the exact six queries in searches.jsonl: LeanFinder twice with different formulations, Loogle once, LeanSearch once, and grep twice (ProjectiveSpectrum subtree, then all Mathlib). All services answered successfully. LeanFinder and LeanSearch return ordinary Proj, standard opens, properness/separatedness, and closed immersions of affine spectra. Loogle has zero hits. Read ProjectiveSpectrum/Functor.lean, including Proj.map and its fraction behavior; the ProjectiveSpectrum/Proper.lean closed-immersion occurrences are used for the diagonal/separatedness proof. There is no algebraic-space relative-Proj result. The full-tree grep for AlgebraicSpace|RelativeProj|relativeProj has zero hits. Preserved the pre-existing search history and appended only the searches actually run in this session.

Whole-DAG searches by Tags 085F/085G/085H/07ZI, graded-map/surjection vocabulary, and the source declarations found the existing scheme functoriality node, scheme quotient-functor node, space scheme-test node, affine-chart calculus and atlas-locality node. blueprint_refs searches for relative Proj, surjective graded, graded surjection, and quotient Proj found no other blueprint statement of this algebraic-space item. No new node is required.

## Not duplicates

No new nodes; there are no new/existing same-tag pairs to distinguish. The existing prop-nagata-relative-proj-functoriality concerns schemes, not arbitrary algebraic spaces, and is cited rather than copied.

## Review by Q02

I read the item against the actual Stacks statements and proofs at 085F, 085H and 085G, then the scheme construction and its quotient interpretation in constructions.tex at 01NY and 01NZ, the ordinary fraction map in lemma-morphism-proj, and the scheme surjection assertion at 07ZI. I read spaces-morphisms.tex Tag 03M4, especially the direction from an etale target atlas to representability and closed immersion. I opened the statement of every cited node; citations.json was generated only after asserting each quote is an actual substring of that statement.

Step 1 uses the specified tensor pullback adjunction, the actual left-adjoint-preserves-colimits theorem, the module-category definition's abelian and cokernel clauses, and preservation of quasi-coherence. The finite cokernel diagram fits the smallness convention, and the Zariski/etale equivalence supplies an inverse, so it preserves the zero cokernel. No exactness on the left and no flatness are asserted. The tensor compositor's explicit formula proves naturality in the map being pulled back; the scheme-test statement already supplies the graded-algebra pullbacks and comparison data.

Step 2 takes the whole statement of lem-sfb-scheme-proj-veronese-quotient-functor: its equivalence relation, transition maps, arbitrary-test limit prescription and normalized representing bijection, not just the existence of a Proj scheme. I checked that precomposition preserves the degree-one surjectivity required of a quotient datum, and wrote the common-multiple witness equation that makes it descend to equivalence classes. Yoneda is cited for its full natural-transformation/evaluation bijection. The non-quasi-compact extension uses the cited compatible-family prescription and restrictions to quasi-compact open refinements; it does not assume a test scheme or inverse image of a quasi-compact open is quasi-compact.

Step 3 uses actual exactness on affine chart sections from the chart-calculus statement, so degreewise sheaf surjectivity really gives homogeneous lifts of b. The standard-open theorem supplies both the covering and degree-zero chart. The quotient theorem specifies its twisting normalization, and the twist definition specifies the fractions. On D_+(b), multiplication by b identifies degree zero with degree d; dividing by b is its explicit inverse. Thus the precomposed quotient has comorphism x/a^m -> alpha(x)/b^m, the ordinary map in the cited scheme functoriality theorem. That theorem's closed-immersion clause applies to a degreewise surjection with all components quasi-coherent; no degree-one generation, A_0=O, Noetherian or finite-generation hypothesis is inserted.

Step 4 uses the scheme-test theorem's comparisons for arbitrary scheme base change and the quotient theorem's test pullbacks. It proves equality on data by pulling back a composite, using the normalized compositor; it does not extract a naturality claim about algebra homomorphisms from the statement of a comparison that only concerned objects. I checked the same formula respects the canonical isomorphism between iterated pullbacks. This supplies the compatibility needed by step 5.

Step 5 constructs the natural transformation on every section, using the diagonal section (id_T,q) and the representing scheme on that test. The naturality equation is proved by the preceding step and the stated compatibility of the scheme-test comparisons. Morphisms of algebraic spaces are natural transformations by their definition. Uniqueness is checked on every q, not assumed from an unquoted descent theorem. This is an elementary assembly step once the preceding maps and comparisons have been established.

Step 6 pulls an atlas of X back to the target P, as the fibre-products/etale-covers statement allows. P times_X U is a scheme by the scheme-test lemma, regardless of whether P itself is a scheme. The atlas-locality statement explicitly requires no representability in advance; its conclusion is exactly representability plus closed immersion after every target scheme test. All its hypotheses therefore hold. The affine clause uses chart sections to lift each homogeneous element and the affine restriction clause of scheme functoriality. I explicitly avoided identifying sections of an infinite coproduct with a direct sum without a theorem.

Step 7 proves the contravariant composition order by associativity of precomposition on quotient classes, and identity by the identity operation. Empty Proj is handled without a chosen point: the scheme morphism constructed on a test forces an empty source whenever its target is empty. The sectionwise construction then gives the corresponding assertion for the algebraic space.

Small cases checked: the identity quotient; a composite of two quotients; A -> A/(t) for a positive-degree generator t, where the source Proj may be empty; a zero graded target algebra; both Proj spaces empty; grading concentrated in degree zero; algebras not generated in degree one (the quotient-functor Veronese degree is retained); arbitrary nonflat scheme tests; and degree-zero structure maps not isomorphisms. Nothing requires quasi-compactness or separation of X. Each proof step is under 2000 characters and no unproved sublemma is moved into an inline long step. Checked delivery-errors B through E: no new statement-only node issues, no duplicate/clause nodes, no source tag substituted for a node citation, no use of a cited node's proof in place of its statement, and no SGA source.

The two off-unit tool uses are declared in split_report: the scheme Zariski/etale equivalence and base change of etale covers of spaces. They are foundational comparisons/locality tools, not trace-formula results. No existing result of the item's unit replaces their specific statements.

## Unfinished

No mathematical part left open in this stage-1 split. Independent maintainer review remains part of the delivery process.
