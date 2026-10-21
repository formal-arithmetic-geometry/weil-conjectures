# Q128 — lem-trf-point-system-transport-descent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-point-system-transport-descent.json`: item, statement, seven proof steps, complete proof dependencies, blueprint provenance, statement-change record, and actual Mathlib searches. Status split; no matching Mathlib theorem for the specified geometric whole-system transformation.
- `citations.json`: one verbatim statement extract for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log; `prepare.py` is the sandbox-only authoring script.

New nodes: 0. New Mathlib leaves: 0. No unit, chapter, Lean source, repository file, or launcher file was changed.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, point-system/point-transport names, Frobenius point names, and transport terminology. No declaration supplies the item, including arbitrary quotient-linear transitions and naturality for whole derived-system morphisms. A completed finite-level or generic localization declaration would not attach the whole item.

## WANTED

None. All material needed for the split was present locally.

## Statement corrected

STATEMENT-DISPUTED: the imported component formula has a codomain mismatch if read literally. By the item itself, `G_r` is levelwise `F_r=(h^r)^{-1}`, so its section target at level n is Gamma(s,F_r M_n). However j has type F_r M_n -> (h^r)^* M_n, so Gamma(j) sigma has target Gamma(s,(h^r)^* M_n). Those are canonically isomorphic objects, not the same declared object. This is an explicit type check using comparison (a), rather than a counterexample to the intended transport.

The statement now specifies sigma as the component in the inverse-image model and Gamma(j) sigma as its expression after the already stipulated j identification with the tensor-pullback model. It also explicitly identifies the target derived category as D(Tow(Mod R)) and identifies the positive level indices with the natural-number indices of the tower-operations definition. No hypotheses, existence assertion, uniqueness assertion, coefficient action, transition square, finite-level normalization, or derived naturality assertion was weakened. The inverse-image and tensor expressions give the very same prescribed transport under j.

The statement-change record retains the original text and identifies all three current users. I read the statements of `lem-trf-point-system-roos-transport`, `lem-trf-point-system-power-roos-coherence`, and `lem-trf-integral-point-transport-tower-powers`. All three explicitly work through the same j identifications; their uses survive unchanged. In particular the Roos user actually wants the inverse-image expression on both product coordinates, and the integral-powers user explicitly describes every map as read through j.

## Source and route

Read the chapter record `sec-trace-formula`, the unit record `sk-thm-trace-transport`, the current blueprint proof of `thm-trf-l-function-euler-product`, Step 1 / Global powers, and `prop-trf-rational-frobenius-integral-model.proof.md`, clause (3). The latter says the integral transport is obtained from actual compatible level maps and their derived limit, while the former requires naturality of the global transports. This item constructs their point-factor maps on the whole ordinary derived system category. It does not prove a trace formula by a different route. The inherited blueprint ancestor is retained with its precise place and via list.

The blueprint does not contain this fully explicit strict-system theorem verbatim. The proof is marked agent-written and spells out the indicated prerequisite. For the generic exact localization step I read `literature/stacks-project/derived.tex`, Tag 015F, label `lemma-right-derived-exact-functor`, including its assertion about all unbounded complexes. For localization I read `literature/stacks-project/categories.tex`, Tag 04VG, label `lemma-properties-left-localization`, and used the natural-transformation form stated explicitly in the existing `lem-weil-pbc-localization-universal-property`; I do not claim the Stacks lemma's printed statement already includes that enhancement. The source uses no SGA 4 or SGA 4½.

## Searches and reuse

Read the item's inherited Q89 search records and retained them. For this delivery ran the required msearch command for the item with LeanFinder twice, Loogle, grep, and LeanSearch; the exact queries and returned declaration names are appended in the node and logged by the command in searches.jsonl. All services answered successfully. The two LeanFinder phrasings concern first general strict varying-coefficient sheaf towers and then the specific geometric-Frobenius point transport; neither returned the theorem. The LeanSearch localization hits are relevant tools, not a theorem about this geometric recipe. Read `Mathlib/CategoryTheory/Sites/GlobalSections.lean`, lines 156-181, especially natTransΓRes:178, and `Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean`, including mapDerivedCategory:36. These give ordinary restriction and exact derived functors, not the specified whole semilinear-system assertion.

Searched the whole DAG for localization/natural-transformation statements and the exact point-transport notions. Read the statements of `lem-sfb-exact-derived-natural-iso`, `lem-sp-exact-derived-transformation-pasting`, `lem-trf-point-exact-derived-model`, `lem-weil-pbc-exact-functor-derived-functor`, `lem-weil-isomorphism-comparison-natural`, and the existing restriction lemma. Chose the already general `lem-weil-point-automorphism-restriction-natural` and `lem-weil-pbc-localization-universal-property` instead of creating new specialized lemmas. The existing natural-iso lemma alone would be the wrong citation for a general transformation; the finite-point exact-model lemma alone would not establish whole-system naturality. Blueprint searches for point transport, automorphism restriction, and localization did not identify a duplicate whole-system item. No new node was created, so no new-node search record or Mathlib-leaf declaration is needed.

## Not duplicates

No new nodes. The point restriction, coefficient isomorphism, strict abelian system, exact sections, exact derived factorization, and localization facts are all cited from existing nodes. Tensor-unit inversion and the semilinear transition calculation are elementary steps in the item, not separate nodes or restated clauses.

## Review by Q128

I checked the item against delivery-errors B through E with the actual node statements and local sources open. Its objects and coefficient actions are all introduced: h^r is a scheme automorphism, k is algebraically closed, each finite coefficient sheaf is constant, completed coefficients use the inverse limit with actual projections, and S_s is the abelian category of arbitrary strict quotient-linear systems. The proof uses the strict transition morphisms, not invertibility of their derived scalar-extension adjoints. The indexing shift to the tower-operations definition is explicitly recorded. No new definitions or nodes obscure those hypotheses.

In step 1 the statement of `lem-weil-point-automorphism-restriction-natural` expressly allows any scheme automorphism and any unbounded complex. It gives the exact restriction/insertion map, the identity description of insertion after reindexing, constant-scalar linearity, and chain naturality. Thus applying it to h^r does not incorrectly assume a theorem stated only for one Frobenius power. The reindexing equivalence and the canonical ring maps are also explicitly given in `lem-weil-proetale-isomorphism-inverse-image`. I verified that its part (3) has naturality for every coefficient ring homomorphism, so it applies to the nonflat quotient maps here.

Step 2 uses comparison (a) of `def-weil-inverse-image-pullback-comparison` for the specific tensor map and `def-pur-sheaf-tensor-product` for its sheafified construction. The proof writes the inverse and checks balancedness and both composites on local generators, so invertibility is not smuggled in by citing a definition. Restriction compatibility makes these actual sheaf maps; the tensor relation gives both identities before sheafification. The calculation for a module map and for the differential is written explicitly. No derived tensor preservation assertion is needed.

In step 3 the coefficient types change, so I did not apply an A_{n+1}-module naturality statement while pretending M_n had the same original coefficient sheaf. Instead the underlying sheaf-map restriction square is written directly. The coefficient-reduction square from the isomorphism lemma makes that square compatible with the transported module actions. The tensor-unit calculation records rho_n(1)=1, including the actual tensor transition. The completed scalar equation is literally in `def-weil-inverse-image-pullback-comparison`, with index m relabeled n, and is exactly what proves completed-scalar compatibility. This verifies C4 rather than citing an unrelated scalar-extension theorem.

In step 4 the tower-operations definition says precisely that sections retain transitions; its scalar-restriction comparison is identity on the sections. The preceding strict squares therefore assemble the map, and componentwise uniqueness is uniqueness of strict tower maps, where it is valid by definition. Naturality for chain maps is supplied by the restriction lemma at each level. The tensor expression is interpreted through j, as required by the corrected type. This is a direct construction, not an application of a new node restating the desired map.

In step 5 the semilinear-derived-sections node explicitly states componentwise abelian exactness for varying-ring systems. The inverse-image node supplies exactness for the isomorphism h^r, while point-proetale-sections-exact supplies exact sections for modules on this algebraically closed point. Restricting scalars changes only the action and leaves kernels and cokernels unchanged; tower kernels and cokernels are componentwise. These checks establish exactness of both functors actually used. The exact-functor-derived-factorization node explicitly states preservation of quasi-isomorphisms and the unbounded termwise representative formula, with no acyclicity or bounded-below assumption to verify. This covers the only homological claim used at this step.

In step 6 the localization-universal-property node explicitly includes descent and uniqueness of natural transformations for two functors inverting W. Here W is the class of quasi-isomorphisms of whole strict-system complexes. Step 5 checks exactly that hypothesis, and step 4 supplies the chain transformation before localization. I also wrote the inverse-quasi-isomorphism naturality equation to exhibit why arbitrary derived morphisms are covered. Nowhere is equality of derived system maps inferred from equality of their evaluations; the transformation is localized before evaluation. The cited generic tools are declared in split_report.tool_uses with their purposes; they do not replace a unit-level proof route.

In step 7 the finite-level point-transport definition has exactly the restriction/insertion/sheafification recipe followed by comparison (a), and comparison (a) represents finite module derived pullback termwise. With h replaced by h^r, this is the notation iota^(r) already stipulated by the item. Thus its bounded-constructible normalization is an identity of the prescribed representative maps followed by localization, not merely an unspecified isomorphism of their targets. Bounded constructibility is required only to name this existing finite-level point-fiber normalization; it was not used in constructing the system map.

I tested the formulas on zero systems, degree-zero systems, unbounded complexes, zero transition maps, and the system B_n with its quotient maps. Zero transitions commute on both sides, demonstrating that no normalization was tacitly assumed. For B_n the inverse to j is multiplication by the inverse coefficient isomorphism and the tensor transition sends 1 tensor 1 to 1 tensor 1; rho_n need not be flat. For arbitrary unbounded complexes the proof is degreewise and the exactness argument is kernel/image/quotient exactness, with no totalization or infinite-diagonal sum. At r=1 the map is the original definition; higher r uses the same arbitrary-automorphism statement and introduces no power-composition assertion. These checks revealed only the codomain ambiguity, which was repaired and logged above.

Every non-elementary ingredient is an existing cited statement, and every such citation has a verbatim statement extract in citations.json. Every proof step is under 2000 characters; the elementary tensor and transition calculations remain steps with explicit arguments. There are no statement-only new nodes with hidden proofs, no duplicated helper nodes, no clause moved into a new node, no newly introduced source tag requiring a duplicate distinction, and no newly introduced circular dependency.

## Unfinished work

None at stage 1. The seven-step split is complete; generic prerequisite nodes retain their own independently tracked stage states. Server dry-run and delivery results are recorded by the delivery tool.
