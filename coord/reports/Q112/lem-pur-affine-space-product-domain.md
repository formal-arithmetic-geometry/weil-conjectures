## Worker report

Files written, all in the sandbox:

- `dag/nodes/sec-smooth-purity/lem-pur-affine-space-product-domain.json`: repaired split, identical statement, 2155-character assembly.
- `dag/nodes/sec-smooth-purity/lem-pur-relative-external-power-regrouping.json`: new statement-only lemma, status unsplit; Mathlib searches find no match.
- `dag/nodes/sec-smooth-purity/lem-pur-relative-product-geometric-factors.json`: new statement-only lemma, status unsplit; Mathlib searches find no match.
- `citations.json`: one literal quotation for each assembly step/node citation.

Attachments: none. I searched WeilConjectures for the item id and affine-space/product-domain notions, then read `SixFunctors/Etale/Derived/Kunneth/Relative.lean`. The full relative-product theorem there ends in `sorry`; its sorry-free `_of_iso` assembly assumes the geometric isomorphisms and projection formulas. Neither supplies this item's iterated finite-Tor assertions or a completed attachment. The affine-space files concern purity and trace, not this finite-Tor product-domain statement.

WANTED: none for this extraction. The primary sources, the current blueprint and cited DAG statements are available locally.

What was wrong: the returned proof contained 4914 characters of work in one node. The human expressly requires distributing it into at least two statement-only tasks of comparable size. The sandbox initially contained only dispatcher brief markers, no node/report/search log, so I copied the current returned node from the read-only repository and retained its full proof below. There was no retained split/report on which to run an initial dry run. The current main-20261015 source moves the parent to `sec-smooth-purity/sk-prop-sp-composition/`; its four-step proof is unchanged in content. The old node's historical source pointer and all blueprint/review metadata are retained; the new nodes use actual existing source locations. The earlier correction of an unbound nu to u is already in the returned head. No statement correction is made by this repair.

Unfinished: the two new nodes deliberately have no proof, no proof dependencies, and null proof origin. Their proof work is assigned to subsequent workers, exactly as the return requests. No Lean was written and no compiler, Lake, or build tool was run.

## Repair of the return

The return has one substantive demand, repeated in its attribution. I repair all its clauses: (1) the item keeps its exact statement; (2) two new unsplit statement-only nodes are added, with self-contained hypotheses and sources, blueprint provenance, and logged Mathlib searches; (3) their statements are 1275 and 1571 characters, independent tasks of comparable size; (4) the item's assembly is 2155 characters, below 3000; (5) all former arguments remain either in an extracted task or in the assembly, with the full returned proof retained below. Neither new node restates the whole item, and no new node simply restates the existing full relative-product theorem.

Extraction map:

- Old Step 1 remains assembly Step 1: the base case, given isomorphism u, tensor unit and its Tor interval.
- Old Step 2 becomes the external-power regrouping task: separated/finite-type base changes and composites, each pulled-back finite-Tor complex, tensor closure, the actual derived tensor-pullback/pullback-composition identification, and transport of constructibility and the Tor interval. Its statement allows varying factors, not only identical M. Assembly Step 2 specializes it to m+1 copies of (f,M).
- Old Step 3(a),(c), including the étale-origin witnesses and the agreement of the concrete exchange with transported compactification exchange, become the geometric-factors task. It asserts the two precise invertible factors and their domains, not the entire Künneth isomorphism. The future proof must use constructible-origin (ii), compact-support composition, fix-lem-exchanges, and finite-level compact-support base change, with qcqs B. These are the same arguments in the old proof.
- Old Step 3(b),(d) remain assembly Step 3. The two projection transformations have base coefficients M on X and V_m on B. The latter is admitted only after the induction hypothesis has established V_m≅A_B and Tor interval [0,0]. Compact-support ctf stability supplies bounded constructibility. Their inverses and the two symmetries finish the same explicitly ordered composite. The datum-level relative-product theorem specifies its shape only.
- Old Step 4 remains assembly Step 4, including the exact interval addition [0+0,0+0]. Old Step 5 remains assembly Step 5, including the recursive κ_m and tensor power of u. The purely functorial assembly is elementary; no coherence theorem about permuting or base-changing these comparisons is asserted.

## Review by Q112

I read the parent statement and proof in the current `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/prop-pur-affine-space-composition-law` files and the unit `sk-prop-an` and chapter records. This item is the finite-coefficient domain check used in the parent's product construction, not a replacement for the unit's affine-line iteration. The chapter, unit, item statement, field, finite coefficient ring A_{E,n}, and prohibition on assuming duality are retained. The item is not the unit's key statement, so no realization fields are edited.

For the new regrouping node I read Stacks sites-cohomology Tag 07A4, label lemma-pullback-tensor-product; 0G7E, lemma-pullback-K-flat; and 0D6D, lemma-derived-pullback-composition. They provide the canonical derived isomorphisms, not constructible preservation. I separately read thm-sf-ctf-stability (i),(ii), which assert the needed ctf pullback/tensor stability. For scheme hypotheses I read schemes-lemma-separated-permanence (01KU) and morphisms-lemma-composition-finite-type (01T3), and the existing base-change node lem-pod-separated-finite-type-base-change (01T4 for finite type). Every P_j and projection is obtained by those base changes and compositions, so the stability theorem applies. The statement does not pretend that a tensor-complex identity is already an identity in the derived category: rho_j is explicitly a derived isomorphism with its comparisons specified. The next worker has all the content of old Step 2, not a shortened unproved assertion hidden in the parent.

For the geometric-factors node I read the current relative-product proof, factors (1),(3), the current thm-sf-comp-composition and thm-cbc-finite-level-proetale source files, and the complete DAG statements of lem-sf-proetale-constructible-origin, fix-lem-exchanges, def-exchange-projection, and def-cbc-exchange-map. Constructible-origin (ii) supplies witnesses for K and H; the definition of a witness was opened as well and requires retaining the pair (etale complex, comparison isomorphism). Boundedness gives D^+, and finite-type separated B is qcqs, so finite-level base change is applicable. The coefficient ring is finite and has invertible residue characteristic as required by the conventions. Composition is checked on H with its witness; exchange is checked on K with its witness. The statement includes precisely the agreement needed to use these arrows as the concrete arrows, not a different arbitrarily chosen isomorphism. No dualizing object, exceptional adjunction, or coefficient change is used.

I checked each assembly citation against its actual statement:

1. The base case uses only definitions, u and the tensor unit, and checks Tor vanishing directly for every coefficient sheaf. It is elementary.
2. The regrouping statement supplies all P_j/projection hypotheses, both pulled-back ctf inputs, T_{j+1} ctf and rho_j. Substituting K_i=M gives exactly M_{m+1}. No use of the future proof is made.
3. The geometric-factors statement supplies alpha inverse and Rf_!(Ex inverse tensor identity) on the stated inputs. thm-sf-ctf-stability(iv) says Rf_! preserves ctf and thus supplies bounded constructibility for V_m. thm-sf-pf-proetale explicitly permits intrinsic finite-stage bounded constructible finite-Tor inputs and says the specified PF transformation is invertible. The first pair is (Lπ_X^*M_m,M), the second (M,V_m). I checked their schemes, finiteness, sites and coefficient rings match. thm-sf-kunneth-relative is cited only for its stated definition of the ordered composite; no conclusion or axiom (A6) is borrowed from it.
4. thm-sf-ctf-stability(ii) states exactly the interval sum used. The two intervals are [0,0] by induction and the original u. The rest is composition and tensor of isomorphisms and transport of vanishing, not a new theorem.
5. A functor preserves an inverse because it preserves the two inverse equations. Apply that to tensoring κ_m with an identity, then compose with κ_{m,1}. This justifies the elementary step and the tensor power of u with unitors. It needs no separate geometric node.

For section B I verified the two nodes are statement-only, every scheme, morphism, index and complex is introduced, every specialized notion has its definition dependency, TeX is singly escaped as mathematical strings, and each source identifies the particular proof factors or Stacks tags/labels. Neither is a Mathlib leaf. Source and whole-blueprint searches preceded creation: `blueprint_refs.py ancestor` identifies the same parent, and searches for external tensor, relative product, Künneth, regroup, étale-origin, compact-support composition, and external product were read, as were whole-DAG keyword/tag searches. I found the existing sketch sk-thm-sf-kunneth-relative and kept its complete relative-product assertion out of the new node. The detailed theorem thm-sf-kunneth-relative additionally assumes a datum including duality; it is not substituted for the concrete checks. Same-tag comparisons are listed below.

For sections C and D I opened every cited node, generated citations.json from literal statement substrings, and checked the uses/proof_deps union. The new nodes depend on definitions and already-existing named structure, not the item, so neither creates a cycle. This extraction is explicitly requested by the human; it distributes a derived regrouping argument and an étale-origin geometric comparison argument, while leaving the unit induction in the parent. It does not transfer the whole result to a single child or invent a second version of the whole relative-product theorem.

For section E I tested r=1 (no regrouping comparison is demanded), r=2 (ordinary binary tensor-pullback), varying K_i including zero complexes, empty B and empty product schemes, f=g=id, and the original affine-line case M=A(1)[2]. Every conclusion is valid in the zero category for an empty scheme. In the geometric task no condition Rf_!K≅A_B is assumed or deduced: only the geometric factors are treated. In the parent it is crucial to use the induction hypothesis before the PF factor with base coefficient V_m; this order is explicit. No residue characteristic, finite-Tor, boundedness, separatedness, or finite-type hypothesis has been dropped. The repair makes no claim about cohomology with supports or exceptional-product formulas.

No assembly step is longer than 2000 characters. There are no new source errors or statement disputes. The old proof's nu/u typing correction remains recorded in its metadata and is unchanged. The return's substantive correction is the new independent tasks, not textual compression alone. The required dry run and delivery are run after this report is written.

## Search record

All new search records are copied from searches.jsonl with the exact query/tool strings. The first node has LeanFinder, LeanSearch, Loogle and Mathlib grep; the second has two phrasings with all these tools. LeanSearch's first comparison query was rate-limited and is recorded as unavailable, not absence; its second query succeeded. I read the hits: Tor functors and monoidal tensor functors do not prove geometric constructibility; scheme base-change permanence does not prove a derived compact-support exchange; light condensed objects are different coefficient categories. Mathlib's Proetale.lean defines sites but not the required compact-support comparisons. The project Relative.lean full relative-product theorem is sorry and its `_of_iso` is only conditional assembly. There are zero new Mathlib leaves.

## Not duplicates

lem-pur-relative-external-power-regrouping vs def-a1-proper-sections-germ-and-moving-point: the existing node concerns Canonical proper compact rational germs and semilinear moving points; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-per-derived-hom-pullback: the existing node concerns Canonical pullback on shifted etale derived Hom; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-a1-finite-pullback-strict-tower-comparison: the existing node concerns Natural finite pullback comparison of strict reduction towers; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-per-proetale-scalar-slice-comparison: the existing node concerns Normalized scalar extension comparison on a pro-etale slice; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pd-section-derived-realization: the existing node concerns Canonical derived section-module realization; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pd-section-derived-tensor-data: the existing node concerns Canonical derived section-module tensor data; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pd-module-ringed-topos-derived-comparison: the existing node concerns Module-object and ringed-topos derived tensor comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pd-section-derived-tensor-normalization: the existing node concerns Derived tensor and actual pullback tensor arrows under section equivalence; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pod-constant-comparison-module-localization: the existing node concerns Canonical finite-coefficient derived composition is ordinary module composition localized; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pod-finite-system-pullback-coherence: the existing node concerns Coherent composition of finite-coefficient pullback on strict systems; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pod-integral-pullback-composition: the existing node concerns Composition isomorphism for integral derived pullbacks; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pe-constructible-comparison-tensor-test-reflection: the existing node concerns Reflection of a single comparison tensor test; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pe-kflat-scalar-tower-realization: the existing node concerns K-flat realization of the augmented derived scalar-extension tower; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pbc-successive-derived-scalar-normalization-data: the existing node concerns Normalized presentation data for successive derived scalar extensions; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-weil-pbc-actual-finite-coefficient-transport: the existing node concerns Actual-ring finite coefficient transport and normalized local restriction; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-weil-pbc-derived-direct-image-composition: the existing node concerns Composition isomorphisms of derived direct images (conjugates of those of inverse images); the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-weil-pbc-derived-square-iso: the existing node concerns Square isomorphism on bounded below derived categories; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-weil-pbc-normalized-origin-scalar-comparisons: the existing node concerns Canonical quotient scalar-extension unit and associator; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-weil-pbc-normalized-scalar-restriction: the existing node concerns Normalized completed-coefficient scalar and restriction comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-weil-pbc-ring-restriction-pullback-comparison: the existing node concerns Canonical restriction-of-scalars and identified-coefficient pullback comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-weil-pbc-ringed-projection-restriction-data: the existing node concerns Normalized ringed projection and slice comparison data; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-weil-pbc-ringed-tensor-square-presentation: the existing node concerns Representative presentation of a commutative ringed tensor square; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-weil-pbc-strict-tower-operations: the existing node concerns Specified derived operations and mate on strict pro-etale module towers; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-weil-pbc-successive-derived-quotient-data: the existing node concerns Normalized presentations of derived coefficient extension; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pe-constant-exchange-encoding: the existing node concerns Constant scalar restriction identifies the ambient ringed exchange; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-augmented-cech-tensor-pullback: the existing node concerns Augmented Cech tensor actions commute with derived inverse image; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-augmented-diagram-projection-mate: the existing node concerns Projection mate for an augmented coefficient diagram before taking inverse limit; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-cochain-pullback-tensor-shift: the existing node concerns The prescribed cochain pullback tensor comparison commutes with both signed shifts; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-completed-adic-koszul-kflat: the existing node concerns K-flatness of the actual completed exterior Koszul complexes; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-completed-reduction-pullback-square: the existing node concerns Completed reduction respects the strict inverse-image square; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-constant-derived-normalization-universal: the existing node concerns Constant derived realization preserves universal coefficient arrows; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-derived-adjunction-shift: the existing node concerns Canonical derived ringed-topos adjunction is shift-compatible; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-derived-inverse-image-composition: the existing node concerns Composition isomorphisms of derived inverse images and their coherence; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-derived-scalar-extension-local-systems: the existing node concerns Coherent localized derived scalar extension and comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-derived-square-iso-pasting: the existing node concerns Identity and pasting laws of the derived square isomorphism; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-diagram-kflat-replacements: the existing node concerns Objectwise K-flat replacements in strict diagram categories; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-finite-reduction-pullback-coherence: the existing node concerns Finite reduction and the canonical pullback square; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-finite-reduction-pullback-square: the existing node concerns Finite reduction respects the inverse-image square; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-flat-coefficient-reduction-adjunct: the existing node concerns Finite scalar comparison preserves derived reduction adjuncts; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-frobenius-exchange-restriction: the existing node concerns Finite-level exchange is the restricted ambient exchange; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: the existing node concerns Derived pullback computes K-flat tensor representatives; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-normalized-derived-isomorphism-section-reduction: the existing node concerns Normalization-compatible evaluation of actual local Isom sheaves; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-normalized-derived-isomorphism-transport: the existing node concerns Universal normalization and evaluation of source-site local Isom sheaves; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-normalized-origin-comparison-coherence: the existing node concerns Comparison reduction respects canonical scalar units and composition; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-proetale-derived-pullback-composition: the existing node concerns Composition of derived pro-etale module pullbacks; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-pullback-resolving-computation: the existing node concerns Derived pullback computes on resolving complexes with independent universes; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-pullback-tensor-canonical-shift-unit: the existing node concerns Canonical shifts and action units of the derived pullback tensor comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-pulled-reduction-normalization-comparison: the existing node concerns Successive quotient normalizations under the pulled reduction comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-reduction-pullback-derived-tower: the existing node concerns Normalized derived pullback of a strict coefficient reduction tower; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-resolving-representative-whiskering: the existing node concerns Restriction to resolving representatives is fully faithful; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ring-sheaf-change-adjunction: the existing node concerns Derived adjunctions under compatible changes of ring sheaves; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-common-quotient-pullback-comparison: the existing node concerns Common quotient reduction of the geometric scalar comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-equivalence-module-hom: the existing node concerns Module and closed Hom transport under a ringed equivalence; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-exchange-tensor-coherence: the existing node concerns Projection-formula coherence for a square of ringed topoi; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-projection-global-model: the existing node concerns Existence of the canonically normalized global projection package; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-projection-local-model: the existing node concerns Localization of a normalized global projection package; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-projection-mate-exact: the existing node concerns Exactness data for the ringed-topos projection mate; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-projection-restriction: the existing node concerns Localization comparisons for the ringed projection mate; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-projection-tensor-comparison: the existing node concerns Descent and signed shifts of the normalized pro-etale tensor comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-projection-tensor-shifts: the existing node concerns Signed shifts of an already normalized tensor comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-pullback-preserves-kflat: the existing node concerns Ringed pullback kflat; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-slice-comparisons-shift: the existing node concerns Shift normalization of canonical ringed-slice comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-square-localization: the existing node concerns Ambient ringed square is exact localization of its ordinary square; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-square-tensor-compatibility: the existing node concerns Tensor compatibility of a ringed square on flat K-flat representatives; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence: the existing node concerns Canonical tensor comparison unit existence; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness: the existing node concerns Canonical tensor comparison unit uniqueness; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: the existing node concerns Derived tensor comparison for arbitrary ringed topoi; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-topos-acyclic-kflat-pullback: the existing node concerns Ringed-topos pullback in the acyclic K-flat case; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-topos-kflat-pullback: the existing node concerns Ringed-topos pullback preserves flat-term K-flat complexes; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-topos-pullback-adapted-flat-resolution: the existing node concerns A flat resolution whose ringed-topos pullback is K-flat; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-supplied-ringed-topos-kflat-pullback: the existing node concerns Tensor pullback adjoint to a supplied ringed-topos module direct image; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-tensor-comparison-descent-representatives: the existing node concerns Unique descent of tensor comparison from representatives; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-coef-ringed-tensor-hom-model: the existing node concerns Canonical closed tensor-Hom representative model on a ringed site; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-coef-semilinear-derived-calculus: the existing node concerns Ordinary derived semilinear calculus interfaces; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-coef-semilinear-geometry-base: the existing node concerns Geometry base fields for coefficient linear operations; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-coef-semilinear-geometry-derived: the existing node concerns Derived geometric system operations and normalization; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-coef-semilinear-geometry-ops: the existing node concerns Canonical geometric mate and projection words; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-coef-semilinear-system-models: the existing node concerns Generic strict semilinear system constructions and representative normalization; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-finite-coefficient-site-chain-tensor: the existing node concerns Canonical finite coefficient site comparison on total tensor complexes; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-finite-coefficient-site-hom-arrow: the existing node concerns Canonical finite coefficient site internal-Hom arrow; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-finite-coefficient-site-scalar-arrow: the existing node concerns Canonical finite coefficient site scalar comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-finite-open-tensor-operations: the existing node concerns Canonical finite open tensor and pullback operations; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-open-normalization-data: the existing node concerns Geometric and operation data for open tensor normalization; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-point-evaluation-derived-compatibility: the existing node concerns Representative-normalized derived point comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-point-evaluation-scalar-coherence: the existing node concerns Tensor square for balanced point scalar data; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-point-evaluation-scalar-data: the existing node concerns Balanced scalar comparison for point sections; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-point-evaluation-tensor-coherence: the existing node concerns Signed tensor coherence for point sections; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-point-evaluation-tensor-data: the existing node concerns Normalized tensor presentation for point sections; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-point-fibre-tensor-common-stage: the existing node concerns Canonical common-stage point tensor and coefficient unit; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-point-fibre-tensor-finite-models: the existing node concerns Canonical finite point tensor normalization on K-flat representatives; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-point-fibre-tensor-models: the existing node concerns Canonical integral representative normalization; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-point-fibre-tensor-rational-compatibility: the existing node concerns Canonical rational point tensor, unit, and scalar compatibility; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-point-fibre-tensor-reduction: the existing node concerns Canonical module scalar tensor data and finite reduction squares; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-point-fibre-tensor-system: the existing node concerns Strong symmetric tensor comparison data for the point fibres; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-point-finite-source-constraints: the existing node concerns The finite point source uses the recorded tensor constraints; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-point-integral-scalar-square: the existing node concerns The integral point completion commutes with scalar extension; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sf-semilinear-proper-open-comparisons: the existing node concerns Canonical semilinear proper/open compositors and intrinsic clopen comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-coef-etale-tensor-model-comparison: the existing node concerns Unique flat-model normalization of the étale scalar tensor comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-coef-ringed-pullback-hom-evaluation-comparison: the existing node concerns Evaluation-defined Hom comparison for ringed pullback; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-coef-semilinear-operations-existence: the existing node concerns Geometric and coefficient operations on a fixed semilinear system calculus; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-coef-semilinear-system-existence: the existing node concerns Ordinary semilinear system calculus and cartesian internal Hom; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-derived-right-exact-tensor-comparison: the existing node concerns Normalized tensor comparison for a right exact strong monoidal functor; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pod-point-extension-kflat: the existing node concerns K-flatness of the point extension of a flat-term module complex; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-factorized-pullback-square-pasting: the existing node concerns Pasting canonical pro-etale derived pullback comparisons for factored endomorphisms; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-boundary-bounded-tensor-comparison: the existing node concerns Bounded tensor preparation for the boundary direct-image comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-canonical-open-restriction-model: the existing node concerns Canonical open restriction on augmented quotient models; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-comparison-open-tensor-coherence: the existing node concerns Etale/pro-etale comparison respects the canonical open tensor map; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-completed-tensor-rational-naturality: the existing node concerns Naturality and rationalization of a completed tensor comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-generator-reduction-coherence: the existing node concerns Basic generator coefficient squares in semilinear systems; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-integral-line-tensor-comparison-representative: the existing node concerns K-flat line tensor models and finite balancing; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-open-exchange-roos-restriction: the existing node concerns Restriction of the strict-limit completed open exchange and its units; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-open-operation-models: the existing node concerns Open operation comparisons with fixed tensor models and right square; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-open-pullback-support: the existing node concerns Derived pullback preserves open support; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-open-restriction-completeness: the existing node concerns Completeness and the actual completion unit after ordinary open restriction; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-point-fibre-derived-tensor: the existing node concerns The point fibre functor preserves derived tensor at all coefficient stages; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-point-field-tensor-descent: the existing node concerns Rational and common-field point tensor descent; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-point-finite-tensor-comparisons: the existing node concerns Finite point tensor comparisons and all quotient squares; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-point-integral-completed-tensor-comparisons: the existing node concerns Completed integral point tensor and scalar squares; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-point-ringed-evaluation-model: the existing node concerns Ringed geometric-point evaluation with signed tensor and coefficient models; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-ringed-finite-free-tensor-complex: the existing node concerns Actual scalar tensor comparison on complexes and K-flat preservation; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-scalar-pullback-composition: the existing node concerns Composition coherence of normalized scalar/pullback comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sf-semilinear-compositor-coherence: the existing node concerns Associative normalized compositors for arbitrary semilinear systems; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-etale-native-tensor-pullback: the existing node concerns Native unbounded derived tensor commutes with etale inverse image; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-slice-evaluation-transpose: the existing node concerns Slice restriction preserves evaluation for an arbitrary dualizing object; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-slice-koszul-coherence: the existing node concerns Normalized slice restriction preserves Koszul exchange; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-pbc-ringed-slice-normalized-comparisons: the existing node concerns Existence of normalized slice tensor, Hom and Koszul comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sfb-integral-quotient-coefficients: the existing node concerns Canonical integral uniformizer quotient coefficient maps; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sfb-integral-quotient-projection-map: the existing node concerns Integral quotient internal projection arrow; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sfb-internal-derived-scalar-comparisons: the existing node concerns Normalized internal derived scalar comparison interface; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sfb-internal-scalar-tensor-comparison: the existing node concerns Scalar-unit normalized tensor comparison for internal modules; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sfb-proetale-composite-coefficients: the existing node concerns Composite pro-etale coefficient identification; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sfb-proetale-ordinary-pullback-comparison: the existing node concerns Section-normalized ordinary pro-etale pullback composition; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sfb-proetale-projection-exchange-maps: the existing node concerns Canonical projection and exchange maps on internal pro-etale modules; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sfb-proetale-trace-coefficient-interfaces: the existing node concerns Canonical internal-module trace coefficient interfaces; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sfb-ringed-derived-comparison-data: the existing node concerns Data of normalized derived monoidal comparisons of ringed topoi; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sfb-ringed-projection-coherence-data: the existing node concerns Recorded data for tensor projection coherence; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sfb-ringed-slice-comparison-model: the existing node concerns Normalized ringed slice comparison data; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sfb-scalar-hom-comparison-data: the existing node concerns Actual scalar-adjunction and normalized tensor-Hom comparison data; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-closed-scalar-hom-composition: the existing node concerns Composition of the five closed-Hom bijections; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-closed-scalar-hom-transport: the existing node concerns Transport of closed-Hom comparison along adjoint isomorphisms; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-constant-module-kflat: the existing node concerns Constant realization preserves flat-term K-flat complexes; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-constant-realization-derived-scalar-extension: the existing node concerns Derived constant realization commutes with derived scalar extension; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-etale-proetale-cube-flat-model: the existing node concerns One flat model computes all six etale/pro-etale scalar cube faces; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-etale-proetale-scalar-pullback-cube: the existing node concerns Etale/pro-etale inverse-image square commutes with derived scalar comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-etale-stalk-total-tensor-comparison: the existing node concerns Canonical signed total tensor stalk comparison and chain naturality; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-exact-completed-koszul-pullback: the existing node concerns Exact product-preserving inverse image transports the actual Koszul unit; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-flat-term-kflat-functor: the existing node concerns Flat-preserving colimit functors preserve flat-term K-flat complexes; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-geometric-stalk-tensor-constant-single: the existing node concerns Geometric stalks commute with derived tensor against a constant module; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-hom-flat-scalar-evaluation-model: the existing node concerns Flat scalar evaluation on an arbitrary first complex and its derived coherence; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-internal-extension-monoidal: the existing node concerns Scalar-unit normalized strong monoidal extension of internal scalars; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-internal-extension-preserves-flat: the existing node concerns Extension of scalars preserves flat internal modules; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-kflat-scalar-comparison-normalization: the existing node concerns Representative and adjunction normalization of scalar pullback comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-projection-comparison-etale-proetale: the existing node concerns Etale-to-proetale comparison of the canonical direct-image projection morphism; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-comparison-tensor-adjunction: the existing node concerns Tensor and adjunction compatibility of canonical ringed-topos path comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-derived-composition-comparison: the existing node concerns Composition comparison with normalized representative formulas; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-derived-identity-comparison: the existing node concerns Identity comparison with normalized representative formulas; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-derived-monoidal-comparisons: the existing node concerns Monoidal and adjunction normalization of derived ringed-topos comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-derived-tensor-diagrams: the existing node concerns Coherence equations for explicit canonical derived comparison maps; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-derived-tensor-lift: the existing node concerns Symmetric monoidal coherence of a canonical derived tensor lift; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-derived-two-iso-comparison: the existing node concerns Specified geometric 2-isomorphism comparison on derived modules; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-projection-first-shift: the existing node concerns The ringed projection mate commutes with shifts in its direct-image input; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-projection-pullback-comparisons: the existing node concerns Normalized identity, composition and section pullback comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-projection-tensor-compatibility: the existing node concerns Tensor constraints and compatibility of normalized comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-projection-tensor-structure: the existing node concerns Canonical tensor structure in arbitrary recorded presentations; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-site-point-acyclic: the existing node concerns A conservative point family detects acyclicity; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-site-point-kflat-resolution: the existing node concerns K-flat resolution with K-flat stalk; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-ringed-site-point-tensor: the existing node concerns Signed total tensor comparison for normalized stalks; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-scalar-extension-kflat: the existing node concerns Scalar extension preserves all K-flat sheaf complexes; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-scalar-hom-tensor-coherence: the existing node concerns Tensor coherence of the normalized scalar extension maps; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-scalar-internal-hom-tower-coherence: the existing node concerns Coefficient-tower and identity coherence for normalized internal Hom; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-scalar-tensor-comparison: the existing node concerns Derived scalar tensor comparison on all K-flat representatives; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-scalar-tensor-tower-comparison: the existing node concerns Simultaneous normalized scalar tensor comparisons with coefficient coherence; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sfb-successive-derived-quotient-normalization: the existing node concerns Successive derived scalar extensions agree with direct quotient extension; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sbc-pullback-comparison-comp: the existing node concerns Composition of coefficient pullback and single-complex comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-fix-proper-etale-origin-scalar-data: the existing node concerns Canonical scalar, tensor and direct-image comparisons at etale origins; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-kun-constant-projection-morphism: the existing node concerns Canonical constant-coefficient derived projection morphism; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-adic-site-strict-quotient-interface: the existing node concerns Small-site adic strict quotient interface and canonical normalizations; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-change-of-rings-complex: the existing node concerns Termwise change of rings of a cochain complex; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-cochain-coefficient-arrows: the existing node concerns Canonical scalar-association and transition arrows on cochain sheaves; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-cochain-coefficient-universe-transport: the existing node concerns Canonical common-universe transport of ring and module sheaves; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-cochain-tensor-coherence-data: the existing node concerns Canonical cochain ringed-pullback and coherence data; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-completed-pullback-tensor-comparison: the existing node concerns Canonical completed, rational and common-stage tensor pullback comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-derived-constant-pullback-comparison: the existing node concerns Canonical derived constant-sheaf pullback comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-etale-scalar-pullback-iso: the existing node concerns Canonical derived scalar and pullback isomorphism; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-finite-pullback-tensor-comparison: the existing node concerns Canonical finite derived pullback tensor comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-integral-line-reduction-data: the existing node concerns Signed integral line reduction and restriction data; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-open-coefficient-normalizations: the existing node concerns Exact-pullback and open-unit coefficient normalizations; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-ringed-coefficient-projection-data: the existing node concerns Normalized coefficient projection interfaces; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-scalar-pullback-representative-data: the existing node concerns Canonical scalar/pullback representative data; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-strict-quotient-expressions: the existing node concerns Strict quotient expressions with actual horizontal transitions; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-pur-system-tensor-mate-arrows: the existing node concerns Canonical tensor and proper/open arrows for varying coefficient systems; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sp-constant-scalar-pullback-comparison: the existing node concerns Canonical constant-coefficient scalar extension, direct image and pullback comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sp-open-coefficient-adjunction-data: the existing node concerns Intrinsic open coefficient adjunction data; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sp-open-scalar-operations: the existing node concerns Constant-ring pro-etale scalar and open operations and their canonical comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sp-open-scalar-tensor-data: the existing node concerns Open scalar tensor normalization data; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sp-proetale-scalar-mate-identifications: the existing node concerns Normalized pro-etale scalar-to-tensor and coefficient-pullback identifications; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-sp-semilinear-constant-ring-operations: the existing node concerns Constant-ring semilinear system operations and normalized evaluation mates; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-cbc-completed-open-kflat: the existing node concerns Completed-coefficient open extension preserves flat-term K-flat models; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-cbc-strict-tower-direct-image-coherence: the existing node concerns Coherence of canonical strict-tower direct image and its square mates; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-exc-proetale-constant-support-projection: the existing node concerns Constant-coefficient projection for compact support; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-fix-ringed-scalar-tensor-monoidal: the existing node concerns Normalized strong monoidality of derived scalar extension in independent universes; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-fix-tensor-pullback-square: the existing node concerns Tensor inverse-image comparisons commute around an open square; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-kun-derived-pullback-composition-monoidal: the existing node concerns Canonical derived etale inverse-image composition is monoidal; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-kun-geometric-point-projection-comparison: the existing node concerns Geometric-point projection morphism agrees with the constant-section projection morphism; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-kun-geometric-point-pullback-tensor-normalization: the existing node concerns Tensor normalization of the pullback/stalk evaluation comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-kun-inverse-image-monoidal: the existing node concerns Monoidality of the derived inverse image; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-canonical-coefficient-system-geometry: the existing node concerns Geometric realization on the literal constant finite coefficient tower; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-cochain-comparison-monoidal-equations: the existing node concerns Monoidal equations for the canonical cochain pullback comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-cochain-pullback-tensor-coherence: the existing node concerns Signed tensor comparison and composition on cochain sheaf pullbacks; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-coefficient-associator-shifts: the existing node concerns Shift compatibility of balanced derived scalar associators; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-coefficient-pullback-coherence: the existing node concerns Balanced coherence of canonical coefficient pullback comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-coefficient-pullback-comparison: the existing node concerns Canonical inverse-image coefficient comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-coefficient-pullback-shifts: the existing node concerns Shift compatibility of normalized inverse-image coefficient comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-coefficient-scalar-units: the existing node concerns Multiplication units for derived scalar extension; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-common-stage-tensor-line-coherence: the existing node concerns Natural associativity and regular right unit for common-stage tensor; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-constant-native-pullback-monoidal: the existing node concerns Canonical native derived tensor comparison for constant coefficients; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-derived-pullback-tensor-iso: the existing node concerns Derived pullback commutes with derived tensor product on the constructible categories; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-etale-scalar-flat-kflat-comparison: the existing node concerns Native flat-term K-flat étale complexes in scalar coordinates; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-etale-scalar-pullback-existence: the existing node concerns Existence of normalized derived scalar/pullback comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-etale-scalar-pullback-uniqueness: the existing node concerns Uniqueness of normalized derived scalar/pullback comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-exact-pullback-signed-comparison: the existing node concerns Exact ringed pullback identifies the canonical signed derived tensor comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-external-rhom-evaluation-naturality: the existing node concerns Four-variance naturality of the external evaluation transpose; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-flat-term-kflat-tensor-native: the existing node concerns Total tensor of native flat-term K-flat complexes; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-geometric-scalar-association-cocycle: the existing node concerns Scalar-association cocycle from normalized inverse-image restriction squares; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-independent-composite-algebraic-image: the existing node concerns Algebraic inverse image and coefficient map for a composite; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-independent-normalized-scalar-composition: the existing node concerns Normalized composition of module scalar extensions; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-integral-ambient-operation-models: the existing node concerns Ambient completion presentations for integral pullback and tensor; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-integral-coherence-tower: the existing node concerns Coherence identities on normalized integral comparison towers; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-integral-line-derived-comparisons: the existing node concerns Normalized derived signed-line reductions and support; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-integral-line-power-comparisons: the existing node concerns Signed power scalar comparisons and evaluations; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-integral-line-reduction-restriction: the existing node concerns Signed line reductions and restriction to the derived-complete integral category; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-integral-line-restrictions: the existing node concerns Completeness and normalized restricted line equivalences; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-integral-operations-well-defined: the existing node concerns The towers defining integral pullback and completed tensor product are invariant under change of K-flat resolution; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-integral-tensor-reduction-tower-comparison: the existing node concerns Strict tensor comparison for finite coefficient-reduction towers; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-integral-tensor-transition-compatibility: the existing node concerns Quotient compatibility of the normalized total tensor comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-integral-tower-limit-comparison: the existing node concerns Derived limit of the strict integral comparison tower; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-kflat-change-of-rings-all-independent: the existing node concerns Change of rings preserves all K-flat complexes with independent coefficient universe; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-kflat-change-of-rings-independent: the existing node concerns Change of rings preserves K-flat complexes with flat terms in independent universes; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-kflat-change-of-rings: the existing node concerns Change of rings preserves K-flat complexes with flat terms; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-kflat-total-tensor-model: the existing node concerns K-flat total tensor model for flat-term resolutions; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-module-tensor-coefficient-equations: the existing node concerns Ordinary module tensor equations for coefficient change; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-module-tensor-composition-equation: the existing node concerns Ordinary tensor square for composite module pullback; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-normalized-operation-system-models: the existing node concerns Normalization and simultaneous models for finite coefficient-system operations; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-normalized-pullback-composition-transport: the existing node concerns Transport of normalized pullback composition through coherent realization; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-normalized-scalar-comparison-realization: the existing node concerns Normalized realization of scalar comparisons on quotient systems; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-normalized-tensor-constraint-transport: the existing node concerns Transport of normalized tensor constraints through coherent realization; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-proetale-restricted-tensor-finite-local-constancy: the existing node concerns Finite local constancy of a restricted tensor with bounded-above inputs; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-quotient-expression-kflat-normalization: the existing node concerns Simultaneous K-flat normalization of strict quotient expressions; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-quotient-system-flat-models: the existing node concerns Strict flat quotient systems compute simultaneous tensor and geometric inverse image; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-scalar-extension-tower-coherence: the existing node concerns Coherent quotient towers for integral scalar extension; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-scalar-hom-comparison-tower: the existing node concerns Evaluation-defined scalar Hom maps respect coefficient towers; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-scalar-tensor-pullback-normalization: the existing node concerns Scalar/tensor pullback normalization on a K-flat representative; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-scalar-tensor-unit: the existing node concerns Scalar action unitor for a normalized signed tensor comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-signed-line-derived-base-change: the existing node concerns Signed line comparisons and their unbounded derived tensor action; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-strict-coefficient-comparison-calculus: the existing node concerns Simultaneous strict coefficient comparisons on ring-sheaf towers; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-support-site-comparison: the existing node concerns Etale-proetale comparison for supported sections and their exterior products; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-system-normalized-tensor-closure: the existing node concerns Normalized semilinear systems are closed under tensor and inverse image; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-system-tensor-reduction-formula: the existing node concerns Tensor formula for actual semilinear reduction adjoints; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-pur-varying-ring-tensor-comparison: the existing node concerns Normalized tensor comparison for one varying-ring inverse image; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sp-canonical-derived-pullback-normalization: the existing node concerns Canonical derived composition is localized normalized ordinary composition; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sp-canonical-open-scalar-tensor-models: the existing node concerns Canonical scalar tensor models compatible with open inverse image; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sp-constant-scalar-pullback-cube: the existing node concerns The canonical constant-ring scalar and geometric pullback cube; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sp-finite-free-balancing-coherence: the existing node concerns Scalar units and associators commute with the canonical balanced pullback comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sp-finite-free-direct-image-shift: the existing node concerns Shift compatibility of the actual coefficient/direct-image mate; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sp-intrinsic-open-projection-invertible: the existing node concerns Intrinsic open projection inverse is invertible; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sp-open-projection-scalar-comparison: the existing node concerns Scalar restriction of the normalized open projection; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sp-open-scalar-coefficient-coherence: the existing node concerns Coefficient coherence of scalar pullback; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sp-proetale-scalar-tensor-normalization: the existing node concerns Underlying tensor normalization of pro-etale scalar and inverse-image comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sp-scalar-associator-conjugate: the existing node concerns Right conjugate of the normalized scalar associator; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sp-scalar-tensor-pullback-square: the existing node concerns Scalar tensor comparisons respect arbitrary pullback squares; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-sp-supported-constructible-origin-comparison: the existing node concerns Supported constructible etale origin and its unbounded coefficient tensor comparison; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-weil-point-derived-tensor-tower-coherence: the existing node concerns Ordinary derived scalar associators and point sections-tensor tower coherence; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-trf-integral-comparison-realization-models: the existing node concerns Normalized realization interfaces for integral quotient systems; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-trf-integral-comparison-sequence-systems: the existing node concerns Canonical pullback and scalar change of whole quotient systems; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-trf-derived-pullback-coherence: the existing node concerns Associativity of finite pro-etale derived pullback comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-trf-integral-pullback-comparison-realization: the existing node concerns Strict-system realization and composition coherence of integral pullback comparisons; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-trf-point-exact-derived-model: the existing node concerns Exact point models and normalization of derived pullback composition; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-trf-pullback-coefficient-iterate-coherence: the existing node concerns Canonical pullback comparisons intertwine coefficient-map iterates; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs lem-trf-quotient-system-mixed-coherence: the existing node concerns Mixed geometric and scalar coherence on strict quotient systems; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-zl-finite-regular-coefficient-comparisons: the existing node concerns Finite regular coefficient comparisons and prescribed pullback compositor; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs def-zl-pbc-finite-raw-scalar-comparison: the existing node concerns Canonical comparison of normalized and embedding finite-field scalar extension; the new task is the finite-family relative external-product domain with all scheme projections and the derived regrouping rho_j, not a new construction of that existing comparison.

lem-pur-relative-external-power-regrouping vs thm-sf-ctf-stability: the latter provides individual operation-preservation clauses; the new task also identifies the actual external coefficients on the iterated fibre products and supplies the scheme/projection typing, without compact-support or unit claims.

lem-pur-relative-product-geometric-factors vs thm-sf-comp-composition: the existing node supplies composition on already-witnessed inputs, whereas the new task establishes admissibility for H and identifies and inverts the relative square's separate concrete exchange.

lem-pur-relative-product-geometric-factors vs thm-cbc-finite-level-proetale: the existing node handles a witnessed input for a compact-support square; the new task supplies the witnesses for K and H and the separately required composition factor for the relative product.

lem-pur-relative-product-geometric-factors vs fix-lem-exchanges: the existing node identifies exchange maps and coherences, while the new task includes their invertibility on the particular etale-origin relative-product domains together with the composition factor.

lem-pur-relative-product-geometric-factors vs sk-thm-sf-kunneth-relative: that node states the full relative Kunneth comparison and its coherence; the new task stops at the geometric factors and proves none of the projection-formula or product-comparison conclusions.

lem-pur-relative-product-geometric-factors vs thm-sf-kunneth-relative: that theorem is inside the six-functor datum including duality and proves the whole comparison with further compatibilities; the new task concerns only the concrete witnessed composition and exchange factors without that axiom.

## Retained returned proof and proof-task briefs

The returned argument below is retained verbatim to preserve all citations and details. It is a handoff record, not proof steps in the new unsplit node files. External regrouping is assigned old Step 2 in full; geometric factors are assigned old Step 3(a),(c), including its witness and map-identification arguments. The parent keeps Step 3(b),(d) and the assembly as described above.

### Former Step 1

For m=1, the definitions give X_1=X, f_1=f, M_1=M, and V_1=Rf_!M. Thus V_1 is identified with A_B by the given isomorphism u, while M_1 is in D^b_{ctf}(X,A) by hypothesis. The coefficient unit A_B has Tor amplitude [0,0] because tensoring it with any A-module is the identity; transporting this interval across u gives the same assertion for V_1.

Cited nodes: (elementary)

### Former Step 2

Assume M_m is in D^b_{ctf}(X_m,A). Write \pi_X:X_{m+1}=X_m\times_BX\to X_m and \pi_Y:X_{m+1}\to X for the two projections of [def-pc-fibre-product]. They are base changes of the separated finite-type morphisms f and f_m, hence separated of finite type by lem-pod-separated-finite-type-base-change; X_m and X_{m+1} are separated of finite type over B, hence over k, since a composite of separated morphisms is separated (Stacks 01KU(1), schemes-lemma-separated-permanence) and a composite of finite-type morphisms is of finite type (Stacks 01T3, morphisms-lemma-composition-finite-type); these two composition facts are elementary. So clause (i) of thm-sf-ctf-stability puts L\pi_X^*M_m in D^b_{ctf}(X_{m+1},A) and L\pi_Y^*M in D^b_{ctf}(X_{m+1},A), and clause (ii) puts their derived tensor product M_m\boxtimes M in D^b_{ctf}(X_{m+1},A). For the left-iterated product the i-th projection of X_{m+1} is \mathrm{pr}_i\circ\pi_X for i\le m and \pi_Y for i=m+1. The tensor-pullback comparison lem-weil-pbc-ringed-topoi-derived-tensor-pullback (applied m-1 times to L\pi_X^*) and the pullback-composition isomorphisms lem-weil-pbc-proetale-derived-pullback-composition give a canonical isomorphism M_m\boxtimes M\cong M_{m+1}. Constructibility of cohomology sheaves and the Tor-amplitude vanishing of def-weil-finite-tor-amplitude are invariant under isomorphism, so M_{m+1}\in D^b_{ctf}(X_{m+1},A).

Cited nodes: thm-sf-ctf-stability, def-pc-fibre-product, lem-pod-separated-finite-type-base-change, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-proetale-derived-pullback-composition, def-weil-finite-tor-amplitude

### Former Step 3

Form \kappa_{m,1} as the composite displayed in thm-sf-kunneth-relative for (f_m,M_m) and (f,M) over B, with the concrete finite-coefficient arrows; that theorem is used only for the shape of the composite, not for its invertibility, since its isomorphism assertion is made inside an axiomatized six-functor datum, and the item allows no duality axiom. Its four non-symmetry factors are, read from the source V_{m+1}=Rf_{m+1!}M_{m+1} (identified with Rf_{m+1!}(M_m\boxtimes M) by Step 2): (a) the inverse of the compact-support composition isomorphism \alpha_{f,\pi_Y}:Rf_!R\pi_{Y!}\xrightarrow{\sim}Rf_{m+1!}, which is an isomorphism by thm-sf-comp-composition on etale-origin inputs; M_m\boxtimes M is bounded constructible, so it has an etale-origin witness by lem-sf-proetale-constructible-origin(ii). (b) Rf_! of the inverse of \mathrm{PF}_{\pi_Y,L\pi_X^*M_m,M}, whose first input L\pi_X^*M_m lies in D^b_{ctf}(X_{m+1},A) by Step 2 and whose base coefficient M lies in D^b_{ctf}(X,A) by hypothesis. (c) Rf_! of the inverse of the compact-support exchange \mathrm{Ex}_!:Lf^*Rf_{m!}M_m\to R\pi_{Y!}L\pi_X^*M_m for the cartesian square with sides f_m and f, tensored with 1_M. By fix-lem-exchanges, at witnessed finite pro-etale level this Ex_! is the compactification formula of def-cbc-exchange-map, the map of def-exchange-projection, transported to the pro-etale site. thm-cbc-finite-level-proetale says it is an isomorphism for every K\in D^+ with an etale-origin witness, which M_m has by lem-sf-proetale-constructible-origin(ii). (d) the inverse of \mathrm{PF}_{f,M,V_m}, whose first input is M\in D^b_{ctf}(X,A) and whose base coefficient is V_m=Rf_{m!}M_m on B, of Tor amplitude [0,0] by the induction hypothesis (and in D^b_{ctf}(B,A) also by clause (iv) of thm-sf-ctf-stability). In (b) and (d) the projection transformations are the concrete ones of def-exchange-projection. thm-sf-pf-proetale (finite stage, intrinsic presentation) says that \mathrm{PF}_{u,K,L} is an isomorphism for every separated finite-type morphism u between finite-type k-schemes and all bounded constructible finite-Tor K,L, so both inverses are defined and invertible on these domains. The two symmetries of \otimes_A^L are isomorphisms. Hence \kappa_{m,1}:V_{m+1}\to V_m\otimes_A^LRf_!M is a composite of isomorphisms.

Cited nodes: thm-sf-kunneth-relative, def-exchange-projection, thm-sf-comp-composition, lem-sf-proetale-constructible-origin, thm-sf-pf-proetale, fix-lem-exchanges, thm-cbc-finite-level-proetale, def-cbc-exchange-map, thm-sf-ctf-stability

### Former Step 4

The induction hypothesis gives V_m\cong A_B and the original hypothesis gives Rf_!M\cong A_B, with both objects of Tor amplitude [0,0]. Since κ_{m,1} is an isomorphism, V_{m+1}\cong V_m\otimes_A^L Rf_!M\cong A_B\otimes_A^L A_B\cong A_B. Clause (ii) of thm-sf-ctf-stability gives Tor amplitude [0+0,0+0]=[0,0] for the tensor product, and hence for V_{m+1}. This closes the induction together with the preceding step.

Cited nodes: thm-sf-ctf-stability

### Former Step 5

Define κ_1 to be the identity of V_1=Rf_!M and define κ_{m+1}=(κ_m\otimes1)\circκ_{m,1}. Each κ_{m+1} is a composite of isomorphisms, so κ_m identifies V_m with (Rf_!M)^{\otimes_A^Lm}. Composing with the m-fold tensor power u^{\otimes m} gives the displayed isomorphism V_m\cong A_B, using the canonical associators and unitors of the derived tensor product. The induction already proves that each V_m and M_m has the required finite-Tor properties.

Cited nodes: thm-sf-kunneth-relative

