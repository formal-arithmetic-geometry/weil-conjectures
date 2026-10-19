# Stage-1 worker report: lem-sfb-modobj-cokernels

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-modobj-cokernels.json`: statement, split into seven elementary steps; no exact Mathlib match. Statement unchanged.
- No new nodes; no Mathlib leaves.
- `citations.json`: five citations, covering every use in steps 3–7, with verbatim definition clauses from `sk-def-sfb-module-objects`.
- `searches.jsonl`: actual msearch.py log. `prepare.py` is a sandbox-only preparation script, not a delivered node.

## Attachments

None. The whole-project searches for `(blueprint: lem-sfb-modobj-cokernels)`, `isColimitCokernelCofork`, and module-object/cokernel terminology did not find the named exact project theorem. I read `WeilConjectures/CategoryTheory/Monoidal/Mod/Limits.lean` and `Abelian.lean` in the read-only slopmaster2 checkout. The former has `CategoryTheory.Mod.colimitSMul` (line 148), `colimitModObj` (167), `isColimitLiftedColimitCocone` (202), and `createsColimit` (215). These are useful general colimit constructions, but none states the item's full existence-and-uniqueness assertion about all action maps satisfying the specified cokernel equation. I therefore did not claim an exact attachment from only the generic construction. The abelian instance also has the stronger hypothesis that the ambient category is abelian. No master sorry declaration is treated as a finished proof.

## WANTED

None. The main-20261015 blueprint contains the statement and its complete proposed proof. This is an elementary universal-property argument written by an agent, and `proof_origin.by` remains `agent`. There is no external theorem quoted without a node or Stacks tag, and no SGA source is used.

## What needed repair

The imported proof had no declared dependencies and all `elementary` fields were null. I added the module definition exactly where its equations are used, and wrote out the cokernel cancellation argument, both action axioms, linearity of the projection, and linearity and uniqueness of the induced factorization.

The sentence that tensoring with the monoid preserves epimorphisms was not justified under a merely preadditive ambient category. The proof now needs only the particular regular epimorphisms at hand: the assumption preserves the cokernel of f, and then preserves the resulting cokernel of Tf. Thus T²π is a cokernel, and its required cancellation follows directly from its universal property. No abelian-category hypothesis or preservation of arbitrary epimorphisms has been introduced. This is a correction of an inference, not a statement dispute or change of the unit route.

The new snapshot's item has neither `chapter` nor `unit` fields, and the corresponding `dag/chapters/sec-proetale-coefficients.json` and `dag/units/sk-prop-sfb-module-category.json` do not exist. I read the actual main-20261015 chapter and unit `_section.md` files instead and preserved all maintainer-owned metadata. This lemma realizes the cokernel part of unit clause 1 and is not the key node responsible for realizing the whole unit.

The first Mathlib grep requested a nonexistent directory (`CategoryTheory/Monoidal/Mod`), and msearch.py misleadingly printed OK with zero hits. I recorded that result as inconclusive and repeated the search on the actual `Mod.lean` file and the CategoryTheory directory. The single-file Kernels.lean grep also printed malformed filename fields; I recorded them as printed and read the real file at its reported lines. Neither formatting issue is used as evidence of absence. Both semantic phrasings, Loogle queries, and actual grep patterns are recorded exactly from the log.

## What could not be finished

Nothing in the split remains open. No new unsplit children were necessary. The required dry run is recorded below after it is run; this worker will not push.

## Not duplicates

There are no new nodes to compare. Whole-DAG terminology searches and `tools/blueprint_refs.py search` for `cokernel`, `module objects`, `preserves cokernels`, and `cokernel of a morphism` found the item and neighboring kernel, abelian, right-exact-forgetful, and lifted-pullback statements. The abelian/right-exact results require an abelian ambient category and the lifted-pullback statement concerns exactness of a different functor; none states this lemma under its weaker ambient assumptions. I did not create a second cokernel, epimorphism, or preservation node: those particular facts are proved from definitions in steps 1–2. `blueprint.same_as` is therefore empty.

## Review by Q29

I read the main-20261015 chapter `_section.md`, the module-category unit `_section.md`, the item's statement `.md` and all three paragraphs of its `.proof.md`, and the full statement of `sk-def-sfb-module-objects` from the DAG. The statement retains exactly the source's assumptions: a preadditive monoidal category, additive tensor in each variable, a possibly noncommutative monoid object, preservation of finite colimits by tensoring on the left by that monoid, and this particular underlying cokernel. No zero object, general existence of cokernels, braiding, commutativity, flatness, or abelian structure is used. There are no new-node sources to audit.

For step 1, the only inputs are the given cokernel and the definitions of coequalizer, additivity, and preservation of finite colimits. The parallel-pair index category is finite. Additivity is used on zero morphisms (not an assumed zero object), so preservation gives a cokernel of Tf and then one of T²f. Both diagrams exist because the preceding step constructs/preserves the particular cocone. For step 2 I checked the uniqueness argument showing each projection is epic: two competing maps are factorizations of the same map annihilating the preceding arrow. The formulas relating the additional cancellation maps to π and T²π use the stated monoidal unitors and associator, with correct domains, so cancellation is legitimate without a general epi-preservation theorem. These two steps cite no extra result because they provide the arguments themselves.

In step 3, clause 2 of the cited module definition is precisely fγ_M = γ_N Tf. Composing it with π proves the annihilation needed to apply the known universal property. The conclusion here is uniqueness of the action morphism among all morphisms satisfying its defining equation, not only among already unital actions. In step 4, clause 1 of that same definition supplies the unit law for N. Naturality of η and λ and the computed equation give equality after precomposition with 1⊗π, and step 2 supplies exactly that cancellation. In step 5, clause 1 supplies the associative law for N. I checked the domains: a starts at (R⊗R)⊗N, α_Q a = T²π α_N, and both expanded composites end at Q. The right-hand expansion explicitly uses T(γ_Q Tπ) = T(πγ_N); there is no unproved claim that the action laws simply descend. Thus both sides cancel against the same epic a.

In step 6, clause 2 says exactly that the constructed projection is linear. I additionally wrote the zero-linearity equation so the module-category zero relation is meaningful without citing an unconstructed abelian structure. The underlying cokernel gives h for any module morphism g annihilating f. Step 7 invokes clause 2 for g and the same clause as the test for h; the displayed equality uses only that equation, functoriality and step 3. Cancellation of Tπ proves linearity, and cancellation of π proves uniqueness. The definition describes module morphisms as underlying maps with a property, so equality of underlying maps gives equality in the module category. The quotes in citations.json are the actual clauses 1–2 of this node, including both action axioms and the morphism equation; I did not use an implication hidden only in its proof.

I checked delivery-errors B–E against the files. B1–B9 introduce no new-node obligations: there are no new nodes, no disguised clauses, and no invented literature tag. The source locations and blueprint ancestor/same-as search are recorded. B10 was checked by source searches, with the limitations of the generic Lean construction explained above. C1–C4 are addressed by the explicit equations and universal-property arguments plus the sole cited definition; no non-elementary theorem is being borrowed from that definition. C5 found no duplicate to create, C6 introduces only the existing definition edge, and C7–C8 introduce no off-unit theorem. D1–D5 are addressed by doing the construction and verifications in the item's own proof rather than moving its clauses to children or invoking an omitted argument.

For E, the main danger was silently using abelianness to turn an arbitrary epi into a cokernel; this has been removed. I also checked small cases: f = 0 forces π to be an isomorphism by its universal property (its inverse comes from factoring the identity), so the construction transports the existing action; f = identity makes Q a zero object by the same universal property, with the unique action; the unit monoid R = 1 gives the canonical unitor action; in ordinary modules and R = Z the construction is the usual quotient action, including quotients with torsion. These checks expose no omitted noncommutativity or flatness hypothesis. Tensoring twice is used only to preserve a cokernel again, so no assertion of left exactness enters. The source's statement is correct; the proof's cancellation justification, missing zero-linearity explanation, and missing citations were the corrections made in this self-review.

## Second reading by Q29

- Statement: checked hypothesis by hypothesis against `lem-sfb-modobj-cokernels.md` and its proof in the main-20261015 blueprint; verdict: faithful, with no added abelian, zero-object, commutativity, or flatness assumption.
- Step 1: checked the finite parallel-pair/coequalizer argument against the stated preservation and additivity hypotheses; verdict: elementary and valid, preserving only the displayed cokernels.
- Step 2: checked epi cancellation for `π`, `Tπ`, `T²π`, `1⊗π`, and `(R⊗R)⊗π` against the preceding cokernel universal properties and coherence naturality; verdict: valid without arbitrary epi preservation.
- Step 3: checked the module-morphism equation in `sk-def-sfb-module-objects` and the underlying cokernel property; verdict: cited clause supplies exactly the annihilation and factorization used.
- Step 4: checked the unit calculation against clause 1 of `sk-def-sfb-module-objects` and unitor naturality; verdict: valid after cancellation by `1⊗π`.
- Step 5: checked both associativity expansions, their domains, and the associator naturality equation against clause 1; verdict: valid after cancellation by `(R⊗R)⊗π`.
- Step 6: checked the projection equation, zero morphism equation, and underlying factorization against clause 2 and the cokernel universal property; verdict: valid module-category cocone argument.
- Step 7: checked the displayed linearity calculation and uniqueness against clause 2 and cancellation by `Tπ` and `π`; verdict: valid, with equality of module morphisms reduced to underlying-map equality as defined.
- New nodes: none; checked the complete chapter/unit DAG search and the existing definition node `sk-def-sfb-module-objects`; verdict: no duplicate or missing dependency node.
- Mathlib/Lean search: checked all recorded Loogle, LeanSearch, LeanFinder, and grep results and read the reported source files; verdict: no exact abstract theorem, only stronger abelian or concrete-module results.
- Small cases: checked zero and identity maps, unit monoid, and ordinary `R=ℤ` modules including torsion quotients; verdict: no edge-case failure.
- Changes made: appended this itemized audit; no node, statement, proof step, citation, or search record required mathematical repair. The prior correction removing unsupported arbitrary-epimorphism preservation remains reflected in steps 1–2 and the report above.
