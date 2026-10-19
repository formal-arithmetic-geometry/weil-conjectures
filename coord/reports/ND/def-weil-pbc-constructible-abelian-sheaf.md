## Worker report

### Files written

- dag/nodes/sec-proper-base-change/def-weil-pbc-constructible-abelian-sheaf.json: definition, split; no Mathlib match. All six component definition nodes already exist.
- citations.json: empty list, since this definition has no proof steps.
- report.md: this report.

No new nodes and no Mathlib leaves were created. Only the sandbox was edited manually. The prescribed delivery tool is used only with --no-push.

### Attachments

None. Searched the entire WeilConjectures source for the item tag and constructibility terminology, then read WeilConjectures/ConstructibleSheaf/Defs.lean, especially IsFiniteSheaf (lines 193–196), IsFiniteLocallyConstantSheaf (212–213), and IsConstructibleSheaf (321–323). This source class uses ConcreteCategory.IsFinitelyGenerated, whose definition was read in CategoryTheory/ConcreteCategory/FinitelyGenerated.lean. Finite generation in the category of abelian groups is not finite cardinality: the constant abelian sheaf Z on an algebraically closed point satisfies the former condition and fails the item's finite-group condition. Consequently Scheme.IsConstructibleSheaf cannot be attached to this item. No declaration bearing the item's blueprint tag was found. Upstream master is reference material only, not evidence of completion.

### WANTED

None. The Stacks sources and the ancestor blueprint file are present locally.

### Audit and changes

Read the chapter sec-proper-base-change and unit sk-thm-p1, and the ancestor lemma-weil-pbc-constructible-finite-pushforward's statement and blueprint proof. This is a component definition used by that ancestor, not the unit's key theorem. Its finite-partition convention is already explicit in the imported node; it is retained without changing the constructibility predicate or adding qcqs hypotheses to T.

Stacks 03RW(2), label definition-constructible, defines constructibility separately on each affine open. Stacks 095E, label lemma-constructible-quasi-compact-quasi-separated, gives the global-partition formulation when the base is qcqs, and explicitly includes the abelian variant. This node deliberately defines the global condition on arbitrary T, as does the existing module-sheaf counterpart. The source field now states that distinction precisely. No equivalence for arbitrary T is claimed.

The definition contained explanatory theorem claims about the qcqs equivalence, finite geometric stalks, a bounded exponent on a quasi-compact base, and choosing reduced strata. These were removed from its statement, leaving its defining clauses unchanged. They are not new definition data or reasons to create nodes. The bounded-exponent statement already has the node lem-weil-pbc-constructible-abelian-bounded-exponent, and the ancestor's proof addresses it. The paragraph before 03RW treats the reduced-stratum replacement by topological invariance, rather than as part of the definition. The module analogue's qcqs comparison is separately carried by lem-weil-pbc-constructible-qcqs-affine-local; no abelian comparison proof is claimed here.

The inverse-image dependency's statement purports to sheafify along a functor U_Et to V_Et for a general morphism U to V. Composition need not send an etale U-scheme to an etale V-scheme. This is an inherited description problem in that dependency, not a problem with the abelian inverse-image operation itself; this item uses its stated left adjoint u^{-1}, not that alleged functor. No dependency file was edited.

### Searches and duplicates

Searched the whole DAG for 03RU, 03RW, 095E and constructibility terminology. Ran blueprint_refs.py search for constructible, constructible abelian and constructible torsion, and ancestor for this item. The blueprint definition def-weil-pbc-constructible-torsion is scoped to a curve coefficient pair; it is not the definition for an arbitrary scheme T here. def-weil-pbc-etale-constructible-sheaf has a finite coefficient ring and module sheaves, so it is not the abelian definition. The remaining hits assert properties rather than define this predicate. No blueprint node defines precisely this arbitrary-scheme finite-valued abelian predicate; same_as is [].

Fresh searches were made only with msearch.py and their exact queries and results are recorded in the item's mathlib_searches and searches.jsonl. LeanFinder was run with two distinct phrasings: it returned condensed locally constant functors and finite-type sheaf-of-modules definitions. Loogle returned Topology.IsConstructible and related subset predicates. Grep returned no constructibility or finite-local-constancy declarations in AlgebraicGeometry/Sites and CategoryTheory/Sites. LeanSearch returned Internal Server Error and is recorded as unavailable. Read Mathlib/Topology/Constructible.lean and the IsFiniteType declaration in Mathlib/Algebra/Category/ModuleCat/Sheaf/Generators.lean: neither is the requested sheaf predicate. The other semantic hits explicitly concern compact Hausdorff/condensed sites and cannot specialize to this definition in one line.

### Unfinished work

None for this stage-1 definition. No theorem proof is asserted and no new node is left to split. A fresh second reader still needs to review and deliver; this worker does not push.

## Review by ND

I read the abelian part of Stacks Definition 03RU in etale-cohomology.tex: its values must be finite abelian groups, and trivializations are isomorphisms of abelian sheaves on an etale covering. Clause (b) now spells out exactly those requirements. I read Definition 03RW(2), the preceding paragraph about constructible locally closed subschemes, and all of Lemma 095E including its qcqs hypotheses and its abelian variant. The node uses the global clause as its definition, not an unsupported equivalence with the affine-local condition on an arbitrary scheme. The ancestor works on qcqs U, so this retained convention matches its route.

I opened every statement dependency. def-weil-pbc-etale-site supplies etale objects and jointly surjective coverings; def-weil-pbc-abelian-etale-sheaves supplies the category of abelian sheaves; def-constructible-stratification supplies a finite locally closed partition and immersed schemes realizing the strata. Its partition notion imposes no extra frontier condition. def-weil-constructible-subset supplies constructibility, which is separately required in clause (a), not inferred from local closedness. def-weil-pbc-inverse-image supplies the abelian left adjoint for each immersion and each etale cover map; its inherited construction wording is flagged above. def-weil-pbc-constant-sheaf supplies sheafification of the constant abelian presheaf, so the local values are groups, not merely underlying sets or finitely generated modules. Each of the six statement dependencies is genuinely used, and none is being cited for a theorem about the notion.

There are no proof steps to audit under C1/C4 and no new statements to test under B/E. This is a definition split by exposing its constituent notions, not a theorem split by relabelling its clauses. Thus proof, proof_deps and proof_origin remain empty/empty/null and citations.json is empty. Finite locally constant is fully defined inline and needs no artificial new node restating clause (b). The removed explanatory claims are not used to define the predicate and were not silently treated as elementary proofs. I checked that the existing bounded-exponent node depends on this definition: citing it back as a dependency would make a cycle, so I did not do so.

I tested the definition on the empty scheme (r=0 is allowed), a point with a finite abelian constant value, and a point with value Z (excluded despite finite generation). On a non-noetherian base clause (a) still requires constructible subsets, so a locally closed but nonconstructible open cannot automatically be accepted as a stratum. Local trivialization groups may vary with i and no uniform integer annihilator is smuggled into the definition. The schemes Z_k remain part of the existential data; no reduction or topological-invariance theorem is needed to make the definition meaningful. No quasi-compactness, quasi-separatedness, invertibility, coefficient ring or nonemptiness hypothesis has been added. The changes I made were removal of theorem commentary, explicit abelian restrictions/isomorphisms, precise source qualification, fresh searches and blueprint ancestry metadata. I checked B–E against these files and sources and found no new-node duplicate or proof-citation issue.

## Second reading by ND

- Item statement: checked each clause against Stacks 03RU, label definition-finite-locally-constant, abelian clauses (1)–(4), and 095E, label lemma-constructible-quasi-compact-quasi-separated, clause (3); accepted as the explicitly qualified global-partition definition already imported. Read 03RW, label definition-constructible, clause (2): its affine-local quantifier is different on arbitrary schemes; no unrestricted equivalence is claimed, and the ancestor assumes qcqs.
- Clause (a): checked def-constructible-stratification and def-weil-constructible-subset; accepted, finite locally closed partition with constructibility separately imposed and no frontier condition.
- Clause (b): checked def-weil-pbc-etale-site, def-weil-pbc-abelian-etale-sheaves and def-weil-pbc-constant-sheaf against 03RU; accepted, finite abelian groups and abelian isomorphisms, with no fixed coefficient ring or uniform annihilator required.
- Restriction clause: checked def-weil-pbc-inverse-image; its left-adjoint interface gives the required operation. The inherited incorrect description of a functor from U_Et to V_Et was already explicitly reported by the first reader; it is not used as a construction or theorem here and lies outside this item's edit scope.
- Proof steps: none; checked proof=[], proof_deps=[] and proof_origin=null. This definition exposes its component notions and does not hide a theorem proof. citations.json=[] is accurate.
- New nodes: none; verified the sandbox has only the existing item. No elementary lemma, duplicate, special case or relabelled clause was created. Read the 03RU/03RW/095E DAG hits and the module and curve-scoped definition alternatives; neither replaces this abelian arbitrary-scheme definition.
- Source attachments: independently read slopmaster2 IsFiniteSheaf (193–196), IsFiniteLocallyConstantSheaf (212–213), IsConstructibleSheaf (321–323), and ConcreteCategory.IsFinitelyGenerated; accepted the decision not to attach. Constant Z on an algebraically closed point has finitely generated stalks but infinite values. Read master IsConstructibleSheaf as reference only, not proof evidence.
- Small cases: zero sheaf is trivialized with the one-element group; empty scheme permits the empty partition; an algebraically closed point with a finite constant group is accepted, and constant Z is excluded. The trivial group (order 1) needs no nonemptiness or invertibility assumption. Constructibility of the strata is not silently inferred from local closedness on a non-noetherian scheme.
- Blueprint route: read the ancestor's full statement/proof, chapter and unit; the ancestor is qcqs and explicitly uses finite stratification and finite stalk groups. No change to the fixed route or unit is needed.
- Mathlib: independently ran LeanFinder with a different phrasing and a whole-Mathlib grep using class names and sheaf vocabulary. The semantic hits concern condensed/compact Hausdorff sites, not etale constructibility; grep returned zero hits. Exact outputs were appended by msearch.py to searches.jsonl and recorded in the item.

Changes: removed the redundant parenthetical source tag from the defining clause (the complete meaning is already inline and the source field retains the tag and label); added the independently executed search records and this second-reading audit. No defining hypothesis, conclusion, dependency, proof step, or citation changed. The first reader's sections, including Review by ND, are retained.
