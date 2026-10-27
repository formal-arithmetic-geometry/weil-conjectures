# Stage-1 report: def-sfb-space-proper-quot-functor

## Files written

- dag/nodes/sec-six-functors-basics/def-sfb-space-proper-quot-functor.json — definition, split, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-module-base-change-flat-proper-support.json — new statement-only lemma, unsplit, no Mathlib match.
- citations.json — empty list: the item is a definition and has no numbered proof steps.

## Attachments

None. Searched WeilConjectures for the blueprint tag and proper-support/Quot names and concepts; no project declaration states this functor. Also searched the local Sheaf sources to avoid duplicating a definition.

## WANTED

None. All mathematical sources used are present in literature/stacks-project.

## Corrections and scope

This item is a definition, not a representability theorem. Its data remain the isomorphism classes of surjections, with the original hypotheses on a and F. The imported statement already used the correct A times_B T. Stacks 09TR has a typographical X times_S T in its pullback sentence; its preceding definition, its subsequent formula and situation-q all require times_B. No changed mathematical target statement is proposed.

Replaced the repeated morphism-property definitions by the existing general algebraic-space definition def-sfb-space-morphism-properties, including its scheme-test quasi-compactness convention. Kept finite presentation, quasi-separatedness, module finite presentation and proper-carrier support explicit. Added direct module-category and chartwise scheme-module flatness dependencies. The imported definition asserted that its transitions land in the prescribed set without naming the preservation theorem. Extracted that prerequisite into one statement-only module theorem, which has no fixed source sheaf, no surjection or quotient classes and no presheaf. It applies to every locally finite type space over a scheme, with arbitrary scheme base change, so it does not repackage the Quot definition or representability. The remaining transition operations are the actual tensor pullbacks, with unit and associativity identifications specified.

The ancestor tool prints None for this existing chain, so blueprint.from.node remains null, with the existing full via chain and precise ancestor proof place retained. The latest blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/ (unit and direct-images proof). It does not itself define Quot or assert the new module theorem; these are supporting prerequisites of the imported Hilbert-space/moduli route. No unit or chapter is changed.

## Review by N9

I read quot.tex situation-quot (Tag 09TR) and the preceding situation-q. The quotient objects agree clause for clause: arbitrary quasi-coherent F, finite presentation of a, and finitely presented, relatively flat quotient modules with proper support. In situation-q quotients are identified by their kernels; the item's target-isomorphism convention is identical because a surjection identifies its target with the quotient by its kernel. Pulling back isomorphic surjections gives isomorphic surjections. Tensor pullback is left adjoint to the specified direct image, so it preserves cokernel presentations and surjectivity. The transition formula is the pullback of q composed with the canonical identification of the pulled-back F with F at the new base; it does not select an arbitrary map. Unit and associativity of tensors send local tensors to the same product of scalar coefficients, so the maps on isomorphism classes satisfy the presheaf laws.

I opened and read the statements of every dependency. def-trf-algebraic-space supplies the spaces and etale charts; lem-trf-space-fibre-products-etale-covers supplies A_T as an actual algebraic space and its universal property. def-weil-size-convention supplies the universe bound. def-sfb-space-morphism-properties supplies space morphism properties rather than pretending a scheme-only definition applies directly to a space. def-weil-closed-immersion supplies the scheme tests for the explicitly representable closed carrier. def-weil-sheaf-of-modules-category and def-trf-space-quasi-coherent-module supply module categories and quasi-coherence. def-trf-space-etale-module-functors supplies the actual adjunction and tensor pullback, not a preservation theorem. def-pc-scheme-module-flat-over supplies the stalkwise condition after restriction to a scheme chart. These nodes are statement dependencies; there are no numbered proof steps and thus no step citations to quote. In particular I did not use the statement of a definition as though it proved base-change invariance.

For the new node I read spaces-morphisms.tex lemma-base-change-module-flat (Tag 05VW), especially (1) and its final sentence; sites-modules.tex lemma-local-pullback (Tag 03DO), clauses (5)-(7); and spaces-perfect.tex lemma-module-support-proper-over-base (0CZI) and lemma-base-change-module-support-proper-over-base (0CZJ). 05VW is about modules on algebraic spaces and allows arbitrary base change. 03DO preserves quasi-coherence and finite presentation without a flatness hypothesis on the morphism. 0CZI identifies proper support with the explicit finite-type module on a proper closed carrier used here; it requires local finite type of X over its base and a finite-type module. The new node includes the former, and finite presentation gives the latter. 0CZJ then gives precisely proper-support preservation. No noetherianity, flatness of g, or finite presentation of f is used. This source combination is a theorem still to be split, so its proof and proof dependencies are empty as required. For the item, base change of a finitely presented a is locally finite type, which is the prerequisite needed when the new theorem is used at T. I checked the scheme-only existing lem-pc-tensor-pullback-flat-proper-support rather than silently treating it as the space statement.

I tested the zero module (empty proper carrier), empty base, identity base change, and nonflat closed base changes. The zero quotient is allowed; F=0 has exactly its zero quotient class. A nonflat base change still preserves surjections by right exactness, and the new statement concerns relative flatness, not flatness of the projection p. The item imposes no finite presentation on F itself. The ambient A need not be proper or separated: properness belongs to the support carrier, not A. These cases preserve every clause.

Against delivery-errors B, the sole new node has a self-contained statement, named notions or explicit definitions, exact Stacks tags and labels, recorded actual searches and no proof sketch. Against C, the definition's only non-elementary well-definedness input is explicitly named, without a cycle back to Quot; the new theorem is independent of this definition. Against D, no new node repeats the functor's data or representability assertion. Against E, all source hypotheses above are checked, and the tensor identifications defining composition are specified. There are no non-elementary proof steps exceeding 2000 characters: the item has none. Searches of the whole DAG and blueprint for Quot, proper support and base-change-module-flat were read. Mathlib's local module presentations, ring-module base change and scheme morphism permanence are useful ingredients but no one-line specialization gives the algebraic-space theorem, so no Mathlib leaf is claimed. The search log is retained and all newly recorded query texts are actual msearch invocations.

## Not duplicates

lem-sfb-space-module-base-change-flat-proper-support vs lem-pc-tensor-pullback-flat-proper-support: the latter has schemes as total spaces; the new node permits a nonrepresentable algebraic-space total space with its etale ringed-site modules.

lem-sfb-space-module-base-change-flat-proper-support vs lem-pc-relatively-flat-module-pullback: the latter is scheme-only and does not assert proper support or finite presentation.

lem-sfb-space-module-base-change-flat-proper-support vs lem-sfb-space-module-pullback-quasicoherent: the latter asserts quasi-coherence only, with no relative flatness, finite presentation or proper support conclusion.

lem-sfb-space-module-base-change-flat-proper-support vs def-sfb-space-proper-quot-functor: the definition fixes F and constructs quotient classes and transition maps; the new lemma is a theorem about base change of any module on a locally finite type space and contains none of the quotient or functor data.

lem-sfb-space-module-base-change-flat-proper-support vs lem-sfb-space-hilbert-representability: the latter concerns representability of the Hilbert functor, not invariance of module properties under arbitrary base change.

lem-sfb-space-module-base-change-flat-proper-support vs lem-sfb-space-fp-module-limit-category: shared source tag, but this existing node states Finite-presentation module continuity for affine limits of spaces; it does not assert the conjunction of finite presentation, relative flatness and proper-carrier support under arbitrary scheme base change for modules on algebraic spaces.

lem-sfb-space-module-base-change-flat-proper-support vs lem-sfb-finite-locally-free-ringed-pullback: shared source tag, but this existing node states Ringed-site pullback preserves finite local bases; it does not assert the conjunction of finite presentation, relative flatness and proper-carrier support under arbitrary scheme base change for modules on algebraic spaces.

lem-sfb-space-module-base-change-flat-proper-support vs lem-weil-pbc-continuous-module-encoding-slice-freeness: shared source tag, but this existing node states Finite freeness on a pro-etale slice agrees with internal inverse-image freeness; it does not assert the conjunction of finite presentation, relative flatness and proper-carrier support under arbitrary scheme base change for modules on algebraic spaces.

lem-sfb-space-module-base-change-flat-proper-support vs lem-weil-pbc-continuous-module-encoding-restriction: shared source tag, but this existing node states Continuous module encoding commutes with restriction along an etale morphism; it does not assert the conjunction of finite presentation, relative flatness and proper-carrier support under arbitrary scheme base change for modules on algebraic spaces.

lem-sfb-space-module-base-change-flat-proper-support vs lem-weil-pbc-continuous-module-encoding-local-freeness: shared source tag, but this existing node states The continuous module encoding preserves and reflects finite local freeness; it does not assert the conjunction of finite presentation, relative flatness and proper-carrier support under arbitrary scheme base change for modules on algebraic spaces.

lem-sfb-space-module-base-change-flat-proper-support vs lem-weil-pbc-continuous-locally-free-pullback: shared source tag, but this existing node states Pullback preserves locally finite free internal modules; it does not assert the conjunction of finite presentation, relative flatness and proper-carrier support under arbitrary scheme base change for modules on algebraic spaces.

lem-sfb-space-module-base-change-flat-proper-support vs lem-weil-pbc-continuous-module-encoding-lattices: shared source tag, but this existing node states Local freeness and lattice compatibility of the explicit continuous encodings; it does not assert the conjunction of finite presentation, relative flatness and proper-carrier support under arbitrary scheme base change for modules on algebraic spaces.

## Unfinished work

The new preservation theorem intentionally remains statement-only for its subsequent stage-1 worker. The definition split is complete; no Lean file was written and no compiler or build tool was run.
