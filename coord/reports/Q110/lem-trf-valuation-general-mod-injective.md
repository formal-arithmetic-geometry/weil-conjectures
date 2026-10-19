1. Files written:
- `dag/nodes/sec-trace-formula/lem-trf-valuation-general-mod-injective.json`: repaired split, unchanged statement, nine proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-local-module-arrow-noetherian-descent.json`: new statement-only lemma, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-localization-system-kernel-stabilization.json`: new statement-only lemma, no Mathlib match.
- `citations.json`: one verbatim statement quotation for every node used in each item step.

2. Attachments: none. Read-only searches of `WeilConjectures/` for the item tag, module-arrow approximation, module injectivity and directed-limit kernels found no declaration proving this item or either new lemma exactly. The source's Noetherian flat-module criterion is a weaker tool, already represented by `lem-weil-pbc-flat-mod-injective`, not an attachment for 046Y.

3. WANTED: none.

4. Problems repaired: the original one-module descent citation supplied neither a common descent of M,N,u nor the Noetherian stages required by 00R6. Its fibre argument concerned the wrong module (N instead of M), omitted finite generation of the kernel and the field-extension injection, and used localization as if it were injective. Its final step falsely identified M_i with M and asserted quotient flatness without a theorem. The repair retains the exact 046Y route and makes two genuinely smaller auxiliary facts into statement-only nodes; neither asserts injectivity or flatness of the original map. The imported statement is correct and is unchanged. The reviewer explicitly requested correcting `created.item/group`: these now name this item and Q110, while its historical `blueprint.from` ancestor and via chain are retained. No unit, target, live source, launcher or Lean file was changed.

5. Unfinished work: none for this stage-1 item. The two new auxiliary nodes intentionally have no proof steps, proof dependencies or proof sketch in their statements; they are queued for their own one-level splits. No Lean was written, compiled, or built.

## Repair of the returned delivery

I read the full independent review at `/home/ubuntu/weil-launcher-nt/reviews/Q110__lem-trf-valuation-general-mod-injective__56efc7aa2b75/review.md`, not only the short return entry. I compared the retained sandbox item with the current read-only repository copy: the statement, chapter/unit, original created metadata and blueprint ancestry agree, while the base still has no accepted split. The required first dry run of the retained split exited OK at dc5252157d; that mechanical success did not resolve the mathematical return. I then repaired every point:

- C3/E1, old Steps 1–2: a new simultaneous-arrow approximation statement supplies the compatible u_i and both Noetherian stage rings. The eventual-flatness invocation now enumerates all its hypotheses, including the elementwise base colimit. Since its statement yields one flat stage, I explicitly propagate flatness to every later stage by the existing localized-base-change theorem at I=0.
- C3/E5, old Step 3: the finite module is P_i=M_i tensor_(R_i) k, over D_i=S_i tensor_(R_i) k. Its finite generating family is written down; D_i is Noetherian by finite type over a field followed by localization. The Noetherian submodule theorem gives finite kernel generation. Tensor/colimit commutation and the actual localization transition formulas supply a fixed-k system. Its finite-kernel stabilization is the second new lemma. Faithful field extension is then cited explicitly and applied to the source residue module, and the fibre square is chased elementwise; no target-fibre comparison is assumed injective.
- E5/long-step rule, old Step 5: new Step 8 proves injectivity by representing a kernel element and killing its image at a later stage; new Step 9 identifies the cokernel using tensor right exactness and proves flatness via the LIMIT localization and the I=0 instance of localized-base-change flatness. No stage is identified with its colimit. Every non-elementary step has fewer than 1100 characters, and the two independent auxiliary arguments have their own nodes.
- A4: corrected the metadata as the return explicitly requested, and recorded the reason here.

## Review by Q110

I read Algebra Tag 046Y (`lemma-mod-injective-general`) in full, including all three proof paragraphs, the construction in 00QV/00QX and the preceding 00R6 statement and proof. The item has precisely the local-map, essentially finite presentation, finite presentation of both modules, R-flatness of N and injective closed-fibre hypotheses in the source, and precisely its two conclusions. The general essentially-finite-presentation hypothesis is not silently replaced by finite type or a Noetherian original base.

For the first new node I checked 046Y's opening sentence (“and its proof”) against 00QX's matrix construction, and 00QV's contracted-prime construction. Here is the argument that the new statement records for later splitting. Write R as the union of localizations of its finite integer-generated subrings at their contractions of m_R. Descend the finitely many algebra presentation coefficients to get S_i, then descend finite presentation matrices A and B for M and N on that SAME ring tail. Lift u on the chosen free generators to a finite matrix U. Each column of UA lies in the image of B, so choose a finite matrix V with UA=BV. Descend A,B,U,V together, and pass farther until the finitely many entries of UA-BV vanish. Thus U_i induces a well-defined map of the two cokernels at every later stage, with compatible transitions and limit map u. Right exactness gives the module base-change formulas. The polynomial quotient/contracted-prime construction gives the ring localizations. Algebraic elementwise colimits give the group colimits. Both stage rings are Noetherian because they are localizations of finite type algebras over the Noetherian integers (00FN). This supplies real simultaneous data absent from the old one-module citation, and requires no flatness or fibre-injectivity assumption. Zero source/target, a zero map, identity map and a non-Noetherian R all fit. A local localization of a finitely presented algebra can be expressed at the contracted maximal prime, as required for 00QV.

For the second new node I read the middle paragraph of 046Y and the elementwise zero criterion 00D7. It abstracts only the finite-kernel/denominator argument AFTER scalar extension to one fixed residue field, so it needs neither Noetherianity nor any map u. Given generators z_1,...,z_t of ker(psi_i0), 00D7 kills them all at a common later j. Semilinearity kills their entire D_i0-span at j and at every l>=j. If x in P_l has psi_l(x)=0, express x as p_i0,l(y)/w by the assumed localization, for y in P_i0 and w in W_li0. Multiplying the equation by w gives psi_i0(y)=0 in P. Therefore y is in the finitely generated kernel already killed at j, so x=0. This is the source's missing finite-generation argument in a smaller reusable form. It allows noninjective localization maps: for D=k×k followed by localization at (1,0), the kernel generated by (0,1) dies at the second stage and the conclusion holds. It also handles a zero module, a zero kernel (take j=i0), a single stage, and a later zero ring. It does not claim that every localization map is injective.

I checked each item step against the actual statements it cites:

1. The new arrow-approximation statement explicitly supplies BOTH modules, commuting u_i, both Noetherian stage rings, algebraic colimits and the limit/transition comparisons. The old one-module node is not used for any unstated map-descent clause.
2. `lem-weil-pbc-colimit-eventually-flat` asks for Noetherian local base and top rings, finite target modules, local commuting transitions, localization/tensor comparisons and an algebraic base colimit; Step 1 supplies each. It concludes only existence of one flat stage. `lem-weil-pbc-localized-base-change-quotient-flat` with I=0 supplies the asserted flatness at all later stages, with N_i tensor S_j=N_j from Step 1.
3. `lem-weil-pbc-tensor-over-quotient-ring` clauses (1),(2) give the exact residue tensor identifications. `lem-weil-pbc-localization-tensor-over-base` gives the localization after tensoring the presenting algebra to k. `lem-weil-pbc-finite-type-algebra-noetherian` and `lem-weil-pbc-localization-noetherian` apply with Noetherian base k; their polynomial quotient/localization hypotheses follow from essential finite type of S_i. `lem-weil-pbc-noetherian-submodule-finite` applies to the explicitly finitely generated D_i-module P_i and its kernel. I removed the earlier fibre-ring citation, which assumed a Noetherian algebra and did not justify arbitrary scalar extension to k.
4. The localization-tensor theorem is applied over R_j to the actual localization of S_i tensor_(R_i) R_j, and to its module localization. Its formula identifies the transitions, not merely the abstract objects. The varying-ring tensor-colimit theorem is applied with second module the constant diagram k; it supplies exactly colim(M_i tensor_(R_i) k)=M tensor_R k, with the actual comparison maps. Compatibility of actions and semilinearity are in Step 1. A common containing universe keeps the index genuinely small.
5. The new stabilization statement applies to this fixed-k system: finite kernel from Step 3, localization transitions and additive colimit from Step 4, compatible D_i-actions on P via S_i→S and k. It gives injectivity for every sufficiently late source comparison.
6. The field-extension faithful-flat statement with D=k_j gives k_j→k faithfully flat. The universally-injective statement gives F_j→F_j tensor k injective; neither theorem is being used only from its proof. The ensuing two-line fibre-square argument uses the assumed injectivity of bar(u) and the proved injectivity of a_j; it needs nothing from b_j.
7. `lem-weil-pbc-flat-mod-injective` has Noetherian S_j, finite SOURCE M_j, flat TARGET N_j and an R_j-linear map; these match after swapping the source lemma's letters. In particular the original base R need not be Noetherian. It gives both stage injectivity and flat stage cokernel.
8. The elementwise-colimit node is used for the underlying abelian groups as Z-modules, so its fixed-ring hypothesis is met. Eventual zero of u_j(x_j) at a later l, plus compatibility, gives zero of x_l by stage injectivity. This is not an unjustified injection M_j→M.
9. Tensor right exactness needs no flatness of S over S_j and proves precisely the displayed cokernel isomorphism, because Step 1 includes compatibility with u. The localized-base-change theorem needs only C_j flat over R_j and the canonical limit localization S_j tensor_(R_j) R→S, both already supplied. I applied it at I=0, rather than presuming that flatness over a changing base survives by “transport”.

All cited statements were opened and their exact useful text is in citations.json. Generic algebra tools from other units are declared in split_report.tool_uses; they replace no geometric step of sk-i-curve-zero. There is no SGA citation. The item does not change definitions or any target statement. Field base, zero target and identity-map cases give the expected injectivity and flat quotient; zero target forces M=0 by the proved criterion, without any new hypothesis. I separately checked the noninjective-localization example to avoid the precise error in the returned Step 3.

## Searches retained and new searches

I read and reused searches.jsonl from the retained attempt. Its item searches found only ordinary flatness/faithful-flatness and residue-field splitting criteria, not 046Y; the extra searches for closed-fibre stabilization also did not state that lemma. I did not repeat those queries. I corrected the item's old grep query field to the exact logged query (removed the explanatory directory suffix) and its dates to the logged 2026-10-17 dates.

For arrow descent I ran LeanFinder, Loogle, grep and LeanSearch. Two different natural-language phrasings covered simultaneous Noetherian approximation and finite-stage factorization. The algebra finite-presentation hits concern ring maps or a fixed-category finitely presentable object, not simultaneous module and map descent with local ring diagrams. The finite-module source hits concern localizing a given map, not constructing a common Noetherian model. The source read for these candidates was Mathlib/Algebra/Category/Ring/FinitePresentation.lean and Algebra/Module/FinitePresentation.lean; no exact or one-line match.

For kernel stabilization I first searched the field-extension formulation, read its hits, and then simplified the auxiliary statement to a fixed localization system and ran fresh LeanFinder, Loogle, grep and LeanSearch queries for that exact question. `Module.DirectLimit.lift_injective` assumes all comparison maps already injective; `of.zero_exact` treats one element, not an entire finitely generated kernel followed by new denominators. `IsLocalizedModule.injective_of_map_zero` is a useful ingredient once the whole kernel is killed, but contains no eventual-stage or finite-generation assertion. I read the localization definitions and these interfaces in Algebra/Module/LocalizedModule/Basic.lean and Algebra/Colimit/Module.lean. Thus the new node remains unsplit, not a Mathlib leaf. Every search record is copied from a real command's tool/query with its actual hits; no outage is recorded as a negative result.

Before creating nodes I searched the entire DAG and blueprint for the tags 046Y, 00QX and 00QV and the concepts simultaneous module/map descent, finite kernel stabilization, localization colimit and closed fibre. I read the statements of the one-module descent family, the ring-only localization descent node, the tower variants, and the existing localization/tensor and elementwise-colimit tools. None asserts either new lemma. The ancestor command returns lem-trf-local-term-locality; each new node records that ancestor, the exact 046Y subargument and the retained via chain with this item prepended. same_as is empty after the whole-blueprint searches.

## Not duplicates

- lem-trf-local-module-arrow-noetherian-descent vs lem-pc-localized-approximation-base-change: the existing statement concerns Tensor base-change hypotheses after localization at contracted primes; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-sc-p1-polynomial-noetherian: the existing statement concerns A one-variable polynomial ring over a field is Noetherian; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-limit-module-colimit-part: the existing statement concerns Colimit part of module descent data; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-limit-module-localization-ring-data: the existing statement concerns Local polynomial-quotient descent with ring localization base change; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-base-change-diagram-elementwise: the existing statement concerns Representatives and eventual zero for a tensor base-change diagram; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-colimit-eventually-flat: the existing statement concerns A flat colimit of finite modules over Noetherian local stages is flat at some stage; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-fibre-ring-noetherian: the existing statement concerns Fibre rings of a Noetherian algebra are Noetherian; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-finite-algebra-noetherian: the existing statement concerns A module-finite algebra over a Noetherian ring is Noetherian; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-finite-presentation-base-change-diagram: the existing statement concerns Diagram and tensor comparisons from a lifted finite presentation matrix; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-finite-presentation-module-diagram: the existing statement concerns Descent of a finite module presentation along a given finite-type ring diagram; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-finite-type-algebra-noetherian: the existing statement concerns Finitely generated algebras over Noetherian rings are Noetherian; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-finite-type-ring-system: the existing statement concerns A finite type algebra as a compatible system over the base stages; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-flat-local-ring-maps: the existing statement concerns A flat ring map induces flat local maps of local rings; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-geometrically-regular-smooth-ascent: the existing statement concerns Geometric regularity ascends along smooth ring maps; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-graded-finiteness-cohomology: the existing statement concerns Cohomology of a finite type graded module over f^*B~ is a finite B-module; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-integer-approximation-flat-point-stage: the existing statement concerns A flat point occurs in a supplied finite-type integer approximation; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-limit-finite-presentation-colimits: the existing statement concerns Model colimit from a base colimit and final pushout squares; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-limit-finite-presentation-core: the existing statement concerns Finite-type approximation models and the base colimit; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-limit-finite-presentation: the existing statement concerns Noetherian approximation of a finitely presented ring map; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module-core: the existing statement concerns Auxiliary module descent data theorem; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module-data: the existing statement concerns Presentation-cokernel module descent data; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module: the existing statement concerns Module descent data from a descended ring system; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-ring: the existing statement concerns Ring descent data for a localized finitely presented algebra; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-limit-module-essentially-finite-presentation-over-system: the existing statement concerns Descending a local algebra essentially of finite presentation and a finitely presented module to the stages of a directed system of local rings; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-limit-module-ring-data-core: the existing statement concerns Core ring descent data without explicit cocone representatives; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-limit-module-small-over-system: the existing statement concerns Single local-algebra descent with the module diagram in an independent small universe; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-limit-tower-essentially-finite-presentation: the existing statement concerns Limit presentation of a tower of local rings essentially of finite presentation with a finitely presented module; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-limit-tower-over-local-system: the existing statement concerns Descent of the upper local tower over a prescribed directed base system; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-local-ring-colimit-essentially-finite-type-over-z: the existing statement concerns A local ring is a directed colimit of local rings essentially of finite type over Z; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-localization-noetherian: the existing statement concerns Localizations of Noetherian rings are Noetherian; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-localization-of-regular-ring: the existing statement concerns A localization of a regular ring is regular; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-localize-filtered-ring-system: the existing statement concerns Localize a filtered ring diagram at a local target; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-localized-approximation-transitions: the existing statement concerns Prime-localized transition base changes; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-localized-pushout-tensor: the existing statement concerns Tensor localization of a localized pushout square; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-noetherian-approximation-localized-diagrams: the existing statement concerns Local diagrams and module comparisons for a supplied Noetherian approximation; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-rees-algebra-noetherian: the existing statement concerns The Rees algebra of an ideal of a Noetherian ring is Noetherian; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-weil-pbc-surjective-image-noetherian: the existing statement concerns A ring receiving a surjection from a Noetherian ring is Noetherian; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-trf-fg-commutative-monoid-finite-presentation: the existing statement concerns Finite presentations of finitely generated commutative monoids; it does not simultaneously construct two modules and a compatible map u_i over common Noetherian local stage rings.

- lem-trf-local-module-arrow-noetherian-descent vs lem-trf-valuation-general-mod-injective: the existing statement is an injectivity/flat-cokernel criterion; this new lemma asserts only simultaneous approximation data, with neither conclusion or their flatness/fibre hypotheses.

- lem-trf-localization-system-kernel-stabilization vs lem-pc-tensor-tail-colimit-elementwise: the existing statement concerns Tensor representatives and eventual zero for an arbitrary colimit on a cofinal tail; it does not conclude eventual injectivity of every later structure map from a finite initial kernel and localization transitions.

- lem-trf-localization-system-kernel-stabilization vs lem-weil-pbc-base-change-diagram-elementwise: the existing statement concerns Representatives and eventual zero for a tensor base-change diagram; it does not conclude eventual injectivity of every later structure map from a finite initial kernel and localization transitions.

- lem-trf-localization-system-kernel-stabilization vs lem-weil-pbc-colimit-flat-relation-descent-elementwise: the existing statement concerns Finite flat relation descent for an elementwise ring colimit; it does not conclude eventual injectivity of every later structure map from a finite initial kernel and localization transitions.

- lem-trf-localization-system-kernel-stabilization vs lem-weil-pbc-directed-colimit-base-change-elementwise: the existing statement concerns Base change along a directed colimit of rings: elements and zero elements come from a stage; it does not conclude eventual injectivity of every later structure map from a finite initial kernel and localization transitions.

- lem-trf-localization-system-kernel-stabilization vs lem-weil-pbc-directed-tensor-cocones-colimit-n3: the existing statement concerns Colimits of coherent directed iterated tensor cocones; it does not conclude eventual injectivity of every later structure map from a finite initial kernel and localization transitions.

- lem-trf-localization-system-kernel-stabilization vs lem-weil-pbc-filtered-colimit-localization-at-prime-data: the existing statement concerns Localization at a prime filtered colimit data; it does not conclude eventual injectivity of every later structure map from a finite initial kernel and localization transitions.

- lem-trf-localization-system-kernel-stabilization vs lem-weil-pbc-filtered-colimit-localization-at-prime: the existing statement concerns Localization at a prime commutes with filtered colimits of rings; it does not conclude eventual injectivity of every later structure map from a finite initial kernel and localization transitions.

- lem-trf-localization-system-kernel-stabilization vs lem-weil-pbc-filtered-colimit-modules-criterion: the existing statement concerns Elementwise criterion for a cocone of a filtered diagram of modules to be a colimit; it does not conclude eventual injectivity of every later structure map from a finite initial kernel and localization transitions.

- lem-trf-localization-system-kernel-stabilization vs lem-weil-pbc-filtered-colimit-modules-elementwise: the existing statement concerns Elements, equality and vanishing in a filtered colimit of modules; it does not conclude eventual injectivity of every later structure map from a finite initial kernel and localization transitions.

- lem-trf-localization-system-kernel-stabilization vs lem-weil-pbc-filtered-colimit-rings-zero: the existing statement concerns Equality and vanishing in a filtered colimit of rings; it does not conclude eventual injectivity of every later structure map from a finite initial kernel and localization transitions.

- lem-trf-localization-system-kernel-stabilization vs lem-trf-valuation-general-mod-injective: the existing statement is an injectivity/flat-cokernel criterion for u; this new lemma only stabilizes a finite kernel in a localization system and mentions no such map or flatness.

The two new nodes differ from each other: the first constructs approximation diagrams and makes no assertion about their kernels; the second assumes a localization diagram and finite kernel and makes no approximation or Noetherian assertion. Neither is elementary packaging: the first must descend finitely many map-relation witnesses on one common local model; the second controls all fractions at all later stages after finite kernel generation.
