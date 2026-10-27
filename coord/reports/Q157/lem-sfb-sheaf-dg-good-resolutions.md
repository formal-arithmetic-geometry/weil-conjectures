## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-dg-good-resolutions.json: split into eight steps following the first proof of Stacks 0FSH.
- dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-dg-free-graded-generators.json: one new statement-only lemma, Stacks 0FSG; no Mathlib match.
- citations.json: verbatim statements for every node used in every numbered proof step.

Attachments: none. Searched lean/WeilConjectures for the blueprint tag, good differential graded modules, universal K-flatness, and free graded sheaf generators. The ordinary K-flat resolution in WeilConjectures/Algebra/Homology/KFlatResolution.lean concerns complexes over a commutative ring sheaf; it does not furnish resolutions over arbitrary associative dg algebra sheaves, nor the universal conditions here.

WANTED: none.

The imported statement is retained, with all existence, closure, annihilation, open-restriction, and left-module clauses. The source's localization label was corrected from the nonexistent section-localization-dg to section-localize-dg. There is no statement dispute. The source has harmless typographical slips in 0FSG ("differential graded A-algebra" where the surrounding context is O-algebra); the new statement uses the actual ringed-site hypotheses and right-module signs.

Nothing remains unfinished in this one-level split. The new free-generator lemma remains unsplit deliberately; its argument belongs to its future worker. No Lean was written, no compiler was run, and all writes were confined to this sandbox.

## Sources and searches

Read literature/stacks-project/sdga.tex, section-P-resolutions: definition of good, 0FSC, 0FSD, remark-sheaf-graded-sets (0FSF), 0FSG with proof, the first proof of 0FSH and the proof of 0FSI. Read section-localize-dg. Read sites-modules.tex, 03CO and 03DB, and homology.tex, lemma-long-exact-sequence-cochain (0117). Checked the right-module shift and cone conventions against sdga.tex and the existing dg-homotopy-system statement.

Mathlib searches were made solely with the supplied msearch.py. searches.jsonl contains their exact results and digests; both node records preserve the queries actually run. LeanFinder and LeanSearch returned ordinary flat modules, K-projective resolutions, free sheaves, and condensed constructions. Loogle returned ordinary free presheaf constructions and no sheaf DifferentialGraded hits. The regex searches found no dg-module/KFlat implementation. Read Mathlib/Algebra/Category/ModuleCat/Sheaf/Free.lean:39,61,131, Presheaf/Free.lean:43,52,67 and Sheaf/PullbackFree.lean:40-100; the constant-index ordinary free-sheaf pullback is not this graded sheaf-of-sets construction. Read Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean:35-48: maps from K-projective complexes are a different assertion. Two different semantic phrasings were tried for both the item and the new lemma; no exact or one-line match was found.

Searched the whole DAG for 0FSG, 0FSD, the source labels, free graded modules and graded sheaves of sets; no existing node states the new input. blueprint_refs.py searches for "0FSG", "graded sets", "free graded", and "good differential graded" returned no matching blueprint nodes. The generic exact-filtered-colimit and restriction nodes were reused instead of creating specialization nodes. Read their full statements, as listed below.

The ancestor command returns None because the inherited created.item chain is broken. Preserved the existing blueprint.from.node = null and its via list, prefixing the item for the new node. Read the current latest blueprint sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This is a generic sheaf dg prerequisite below the inherited scalar-adjunction branch; it does not replace any chapter or unit route. No unit realization is changed: this item is not its key statement.

## Not duplicates

The new node has source tags 0FSG and 0FSF. No pre-existing DAG node with either tag was found. The item asserts existence of resolutions for every dg module, whereas the new node concerns only the explicitly constructed free module on a specified graded sheaf of sets and its base change; none of the item's conclusion clauses is merely transferred to the new node. Ordinary algebraic semi-free nodes assume rings or small dg categories with objectwise acyclicity, rather than arbitrary ringed sites and sheaf cohomology.

## Review by Q157

I read the sources named above with the actual statements open and checked B--E of delivery-errors.md in full. The single new lemma is self-contained: its algebra, actions, differential, sheafified homogeneous-generator construction, tensor, cohomology and arbitrary base changes are specified, and its five statement dependencies define exactly the referenced foundational notions. It has no proof, proof dependencies or concealed proof sketch. The primitive source is 0FSG, not a restatement of the resolution theorem.

Step 1 uses lem-weil-pbc-complex-ses-homology-long-exact, whose statement gives the long exact sequence for degreewise short exact cochain complexes in every abelian category. The graded splitting makes its hypotheses hold after tensor and after any base change. Graded flatness of the middle is checked using its actual direct-sum decomposition; no false two-out-of-three claim for arbitrary flat modules is used. Shift and cone goodness are proved with this sequence, rather than cited from an unrelated K-flat notion.

Step 2 uses lem-pur-ringed-site-grothendieck-abelian, whose statement explicitly provides all small colimits and exactness of filtered colimits for module sheaves on a small ringed site. The given universe convention ensures sequential diagrams are small, including after base change to another presented small site. Balanced-map universal properties establish tensor/colimit compatibility; the proof describes why kernels, images, and cohomology commute. Thus no enough-points, countable-cover, or boundedness hypothesis has entered.

Step 3 uses the new free-generator statement for goodness of the actual constructed P_0 and def-weil-presheaf-modules-sheafification for the extension of its coefficient-linear map. Its generator set is the sheaf of cycles in each degree. Surjectivity is on cohomology SHEAVES, by local representatives, not an incorrect assertion about global section cohomology.

Step 4 uses those same two nodes for the explicitly described graded direct sum and its quotient. I checked d(ea), the cancellation in d², u d = d u, and that the quotient has zero differential on the new generators. The quotient is exactly the object of 0FSG. The proof keeps the differential on P_i, so induction really applies to dg submodules.

Step 5 uses exact filtered colimits from the same ringed-site node. I checked the kernel condition in degree n: one adjoins a degree n-1 generator for a pair (p,m), with p a degree-n cycle and dm=u(p). Localizing once to represent a cohomology class and again to choose m is legitimate for sheaf kernels. Every kernel is therefore killed in the next stage. The induced map on the colimit is both epi and mono, for every integer n.

Step 6 cites no external lemma: it supplies both algebra/module opposite formulas and the Koszul interchange map. Associativity, the two Leibniz identities and tensor differential compatibility follow by substitution on homogeneous elements. This proves left resolutions before they are used; it does not argue circularly from the tensor-annihilation clause.

Step 7 uses exactly the same long-exact-sequence node as step 1. The cone is degreewise split, and its connecting map is ±H(Q→N), so its acyclicity follows from the proved quasi-isomorphism. Left goodness of Q applies to the acyclic right module P; right goodness of P applies to the acyclic left cone. Tensor preserves the graded splitting without assuming N flat. The long exact sequence then proves the required tensor annihilation.

Step 8 uses lem-weil-pbc-site-restriction-exact, which is explicitly a GENERAL-site statement, unlike the many scheme-only restriction lemmas. The open site localized at V is the open site of V. Exactness on abelian sheaves gives the cohomology and quasi-isomorphism claim. The balanced tensor restriction identity is proved by equality of its local presheaves and covering families, not imported from a theorem about schemes. Universal goodness restricts by composing ringed-topos morphisms and writing the associativity map.

Small cases checked: zero and empty graded sheaves give the zero free module; the terminal site gives the familiar free graded dg module; characteristic two removes the signs without invalidating any cancellation; the empty space and empty open have only zero module sheaves; zero inputs and cones of identities satisfy all arguments. Noncommutative dg algebras are allowed throughout: no unsigned swap or commutative-A tensor symmetry is used. Unboundedness is handled by sheafified direct-sum tensors and exact sequential colimits, never by a convergence assertion. The base-change ring map is arbitrary, with no flatness assumption. All steps are shorter than 2000 characters.

The reused ringed-site exact-colimit and site-restriction lemmas are generic tools from other units; split_report.tool_uses records why they are foundational inputs and do not replace a unit route. The long-exact-sequence node is a Mathlib leaf. The report's citation table copies whole statements verbatim so each claimed sentence is available to the delivery checker and independent reviewer.

Final self-review: made the small base-change site, its commutative ring sheaf, and its dg algebra explicit in the new lemma, so the base-change quantifier introduces every object independently. Updated the verbatim citation entries. The preceding server dry run passed; rerunning after this wording correction.
