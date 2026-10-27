# Stage-1 delivery: def-sfb-space-coherent-adic-system

## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-space-coherent-adic-system.json`: definition, split using existing notions; searched Mathlib, no exact match.
- `citations.json`: empty list, since this definition has no proof steps.
- No new DAG nodes; no Mathlib leaves.

## Attachments

None. Searched the upstream `lean/WeilConjectures/` by the exact blueprint id and by coherent-adic, adic-system, formal-module and completion vocabulary. `AlgebraicGeometry.CoherentFormalModule` in `CoherentFormalModule.lean:81` is defined for schemes and Zariski module sheaves. `AlgebraicGeometry.Etale.AdicSystem` is instead a derived constructible coefficient tower. Neither states the present definition for algebraic spaces on their small etale sites, including the proper-carrier and bounded component-kernel conventions.

## WANTED

None. All sources used are in the read clone.

## Findings and changes

The item is a definition, so its one-level split consists of naming its constituent notions, not inventing proof lemmas. Retained all the original data and conditions. Added the existing definition references for quasi-coherent ideals and ordinary module-sheaf kernels/cokernels. Made the coherent input M of completion explicit; wrote the arrow compatibility equation, componentwise identities/composition and the meaning of the quotient. Specified that pullback is applied to a diagram on the target of g. No abelianness, exactness, descent, affine-completion equivalence or pullback-preservation theorem is asserted or used by this definition. Completion here names its explicit quotient diagram as in the original text.

Read Stacks `spaces-more-morphisms.tex`, section-existence-proper (Tag 089N), the opening definition and functoriality paragraph; equation-completion-functor (08B4); equation-completion-functor-proper-over-A (08B8) and its preceding proper-support paragraph; and remark-inverse-systems-kernel-cokernel-annihilated-by (08BA). Verified labels against `tags/tags`. The source's comparison with finite completed modules is a theorem; only its condition (1) is used to define the bounded-kernel terminology here.

Searched the DAG for 08B4/08BA, coherent adic and formal-module notions, and the whole imported blueprint with `blueprint_refs.py search` for adic, coherent adic, coherent formal and 08B4. The scheme-only node `def-weil-pbc-coherent-formal-module` is not equivalent to this algebraic-space definition; no new duplicate is created. The ancestor command returns None, as for the live item: retained its inherited null ancestor and explicit place/via chain. Read the chapter and unit records and the current latest unit and direct-image proof; this supplies language for the inherited proper-support existence prerequisite, not a replacement of the unit route. No unit record is changed.

Preserved the four inherited Mathlib search results and reran exactly those four queries through the required Q13 msearch command so they are now supported by this sandbox's log. Added a second semantic phrasing and read its eight hits. Module completion `AdicCompletion` (Basic.lean:171,268), scheme ideal sheaves and generic quasi-coherent presentations are not this coherent-adic category on algebraic spaces. All services returned successfully. The two semantic phrasings, LeanSearch, Loogle and grep were all actually run; no unavailable service is reported as absent mathematics.

## Unfinished work

None for this one-level definition split. Its existing unsplit dependencies remain separate work items.

## Review by Q13

I read the four Stacks passages above with the item open. The two object conditions are exactly the opening conditions: positive levels n, annihilation by J^n, and the quotient induced by the transition. For arrows, the commuting square is explicit; composition respects it because (b_n a_n)t_n=b_n(s_n a_{n+1})=(r_n b_{n+1})a_{n+1}, and identities respect it immediately. Thus no extra theorem node is needed for the category operations. Multiplication products, annihilation and the quotient are definitions of module-sheaf data, not hidden claims about kernels in the adic category.

I opened and read the statement of every statement dependency. `def-trf-algebraic-space` supplies the small etale structure sheaf, and `def-weil-sheaf-of-modules-category` supplies module maps, ordinary kernels and sheafified cokernels. `def-trf-space-quasi-coherent-module` supplies quasi-coherence; `def-sfb-space-quasi-coherent-ideal` really defines the required ideal submodule. `pqf-def-locnoeth` and `pqf-def-coherent` are scheme notions used on charts, so the text explicitly states their chartwise extension. Quasi-compactness and quasi-separatedness are spelled out. `def-trf-space-etale-module-functors` supplies the tensor pullback and direct image, while `def-sfb-space-morphism-properties` supplies properness and the separated finite-type condition; `def-sfb-space-proper-quot-functor` states exactly the finite-type quasi-coherent proper closed-carrier convention used for M_1. `def-pc-scheme`, `def-weil-affine-spectrum` and `def-weil-size-convention` supply the remaining base objects and universe convention. I did not take a theorem from the proof of any cited node. There are no numbered proof steps, and hence no per-step quotes or long non-elementary steps to audit.

I checked the small cases: for J=0 the transitions are isomorphisms and the quotient diagram of M is constant; for J=O_X annihilation forces every term zero; the zero module and empty space give the zero system. Over k[e]/(e^2) with J=(e), the quotient diagram starts with M/eM and is M from level two onward, with the stated quotient transitions. For K=0 the bounded-kernel predicate is automatic; for K=O_X it says all component kernels/cokernels vanish. The exponent must be one common t for all n, as in 08BA; the text has not replaced it by separate stagewise bounds. Proper support is required of M_1, not of an unspecified limit. These checks found no false statement or source error. No new node is elementary, duplicated, a renamed clause, or an unsearched Mathlib result because no new node is introduced. All edits and artifacts are confined to the assigned sandbox; no Lean or compiler/build action was used.
