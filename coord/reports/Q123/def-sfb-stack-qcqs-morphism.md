# Stage-1 report: def-sfb-stack-qcqs-morphism

## Files written
- dag/nodes/sec-six-functors-basics/def-sfb-stack-qcqs-morphism.json: definition; split using the six existing statement dependencies; not in Mathlib for algebraic stacks.
- citations.json: empty list, because a definition has no proof steps.

No new nodes; no Mathlib leaves. The sandbox contained no prior node, report or search log when work began. The original six recorded searches are preserved and the current recorded searches are appended.

## Attachments
None. Searched lean/WeilConjectures by the blueprint tag, algebraic-stack terminology and qcqs notions. The nearby Sheaf/AlgebraicGeometry/DmStackMorphismProperties.lean defines a DM scheme-test predicate, not all clauses for arbitrary algebraic stacks. No exact project attachment was found.

## WANTED
None. All defining sources are available in literature/stacks-project.

## Corrections and scope
The statement, all six stmt_deps, and empty proof/proof_deps are retained. Added the missing explicit Tag 03E3 (spaces-properties-definition-quasi-compact) source for the algebraic-space atlas predicate. Marked split and added the split report. No STATEMENT-DISPUTED issue was found. No Lean was written or compiled.

The computed blueprint ancestor is null, as inherited: the creation chain ultimately originates in a Lean-module split. Its explicit from.place and via identify the alteration/moduli prerequisites under direct-images proof (3); these are preserved. The latest blueprint unit and direct-images proof in sec-six-functors-basics/sk-thm-sf-ctf-stability were read. No chapter/unit route is changed and this definition is not a unit key node. Blueprint searches 050U, 04YW, 03E3 and algebraic stack found no equivalent blueprint node; broad quasi-compact/quasi-separated searches were also inspected.

## Not duplicates
No new nodes are created. Same-tag existing nodes were opened or inspected: lem-sfb-dm-quasicompact-atlas-criterion proves an atlas equivalence for DM stacks, lem-sfb-finite-type-stack-affine-smooth-atlas proves existence of affine smooth finite-type charts, and lem-sfb-stack-finite-type-calculus proves finite-type permanence. def-sfb-proper-curve-moduli contains space conventions inside a curve-family definition. None replaces this generic combined definition for arbitrary algebraic stacks. Other same-tag hits are downstream applications (adequate moduli, finite covers, formal charts, open-stack permanence), not duplicate definitions newly introduced here.

## Review by Q123
I read stacks-morphisms.tex definition-quasi-compact (050U) and definition-separated clause (4) (04YW), stacks-properties.tex lemma-quasi-compact-stack (04YC), spaces-properties.tex definition-quasi-compact (03E3), and spaces-morphisms.tex definition-quasi-compact (03HE) and definition-separated clause (3) (03HL). The stack morphism tests quantify over all quasi-compact algebraic stacks, not merely schemes; the stack separation condition retains both compactness and separation of its representable diagonal. The algebraic-space morphism tests quantify over all quasi-compact algebraic spaces. Using the smooth quasi-compact atlas criterion as the definition does not assert the topology/atlas equivalence as a theorem in this node. The algebraic-space atlas criterion likewise is the defining convention. No existence, independence, permanence or comparison theorem is hidden in the statement.

I read the statement of each dependency: def-pc-scheme supplies schemes; def-weil-size-convention supplies universes; def-sfb-algebraic-moduli-stack supplies smooth surjective atlases and algebraic stacks; def-sfb-stable-pointed-moduli-groupoids supplies general fibred groupoids, morphisms and 2-fibre products; def-weil-pbc-quasi-compact-scheme supplies quasi-compactness without a Hausdorff condition; def-trf-algebraic-space supplies fppf sheaves, sheaf products, algebraic spaces and representable etale maps. Only those general clauses are used from the moduli-groupoid node, without its genus, level or curve hypotheses. The relative diagonal is given explicitly on objects. The statement itself defines the additional space and stack compactness/separation predicates, so no further prerequisite node is needed. There are no proof steps, hence no step citations or non-elementary proof facts to check under C1/C4, and citations.json is correctly empty.

I checked B through E of delivery-errors.md against the node. This is a complete definition, not a proof moved to a new node. It makes existential atlas predicates and does not select unspecified data. Empty schemes/stacks are permitted: the empty atlas witnesses compactness. An identity has identity diagonal and tests the unchanged base; a quasi-compact scheme with its identity atlas is allowed without finite-type assumptions. Non-DM stacks are permitted: no etale stack atlas was substituted for a smooth atlas. For example the affine smooth group classifying stack B(G_m) is not excluded by an added DM condition. The two algebraic-space and stack compactness conventions are defined separately without claiming their comparison for arbitrary fibred groupoids. No missing finite-type, Noetherian, separated-base or field hypothesis is invoked.

The logged LeanFinder and LeanSearch hits and Loogle pattern were read; a second semantic phrasing looked for the smooth atlas criterion. The grep found only Mathlib scheme compactness/separation and scheme-cover predicates. I read QuasiCompact.lean at 35-46, QuasiSeparated.lean at 46-52, and Cover/QuasiCompact.lean at 30-40: their Scheme endpoints prevent an exact match or one-line specialization to arbitrary algebraic stacks. All appended query texts and results come directly from this sandbox searches.jsonl; original search records are preserved.

## Unfinished work
None for this one-level definition split. Existing prerequisite nodes remain their owners' work.
