# Q12 stage-1 report: lem-sfb-stack-coherator-flat-test-restriction

1. Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stack-coherator-flat-test-restriction.json: statement, now split into seven proof steps; original statement and stmt_deps retained. New logged Mathlib searches give no match; inherited search evidence is retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-atlas-module-descent.json: new statement-only prerequisite, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-atlas-quasicoherent-source-maps.json: new statement-only prerequisite, unsplit; no Mathlib match.
- citations.json: one verbatim statement excerpt for every node used by every numbered proof step.
- report.md: this report. searches.jsonl contains the actual search-command records. prepare.py and finish_report.py are sandbox-only preparation scripts, not project changes.

2. Attachments

None. Searched lean/WeilConjectures for the item id, the exact blueprint tag, coherator, stack coherator, LQCoh and atlas/descent language. The scheme derived-coherator declarations concern a different construction. No project declaration states the item or either new atlas statement, and none is treated as finished merely because it has an imported name. No Lean was written and no compiler, Lake or build command was run.

3. WANTED

None: all mathematical sources used are present in literature/stacks-project/.

4. Findings and corrections

The item was statement-only, with no proof. I kept its full statement, all eight statement dependencies, its source and its recorded searches. There was no existing sandbox split to recover. There is no released repair note for this item. Stacks Tag 0GQK prints QCoh^{fbc}; the ambient category and the argument are those of the LQCoh^{fbc} construction in 0778, exactly as the item already spells out. There is no mathematical statement dispute or weakening.

I did not introduce a node saying that the counit's kernel and cokernel vanish on flat tests: that would repackage this item's conclusion. Instead the two new prerequisites are the geometric module-descent theorem of 06WT and the arbitrary-target morphism theorem of 076S. Neither refers to Q, a counit, or a flat test. The proof constructs the atlas descent datum, establishes a universal map M to H, identifies it with the specified counit, and then descends invertibility to the flat test. Thus the actual assembly argument stays in the item.

The automatic blueprint ancestor command prints None. Its inherited chain already has a null from.node and an explicit place beginning det-thm-sf-ctf-stability-direct-images, proof (3). I retained that provenance and via, filled is and same_as, and inherited it for the new nodes with this item prepended to via. I read the newest literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This is a generic quasi-coherent prerequisite of the existing deeper moduli chain, not a change of the unit's constructible direct-image route. Whole-blueprint searches for coherator, parasitic, locally quasi-coherent, smooth atlas, 06WT, 076S and map-from-quasi-coherent found no equivalent blueprint statement. No unit realization fields are changed because this item is not the unit's statement node.

5. Unfinished work

No required assembly step is left open. The two new nodes are intentionally statement-only and unsplit, as a one-level split requires. There are two new nodes and zero Mathlib leaves.

## Mathlib evidence

For each new node, I ran leanfinder twice with different phrasings, loogle, grep, and leansearch through the required msearch.py command. I also reran the same five kinds of evidence for the item. Each recorded query is copied verbatim from searches.jsonl and its results are the returned hit names/counts. All services answered. None was recorded as unavailable or as a match without reading it.

The closest hits were SheafOfModules local-presentation data, pushforwardPushforwardEquivalence, and Pseudofunctor.isEquivalence_toDescentData. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:285–355, PushforwardContinuous.lean:373–400 and CategoryTheory/Sites/Descent/IsStack.lean:66–74. The first is local presentation data and preservation under extra hypotheses; the second starts with an equivalence of the underlying sites; the third assumes that a pseudofunctor is already a stack. They do not prove quasi-coherent descent on an algebraic-stack atlas. The Hom hits are free-object, colimit or scheme-open universal properties, and do not prove arbitrary-target map descent from a quasi-coherent source. The item hits are scheme open-restriction and sheafification counits, not a quasi-coherator on stack modules.

## Review by Q12

I read stacks-cohomology.tex at lemma-flat-object-and-Q (Tag 0GQK), the full atlas argument and the counit comparison in lemma-adjoint-kernel-parasitic (0779), and the construction and Hom identifications in lemma-adjoint (0778). For the first new node I read stacks-sheaves.tex proposition-quasi-coherent (06WT), including the construction of the equivalence, and its application to an algebraic-stack presentation. For the second I read lemma-map-from-quasi-coherent (076S), its complete comparison diagram, and its proof by restriction to the prestack and stackification. The smooth-atlas formulation is obtained by the presentation lemma algebraic.tex lemma-stack-presentation (04T5). The hypotheses s,t flat locally of finite presentation in 076S hold because the atlas is smooth; no separated diagonal is assumed.

Step 1 uses the algebraic-stack definition to choose a smooth atlas, and the fibred-groupoid definition for 2-fibre products and their canonical 2-arrow. The chartwise calculus states base change and composition stability and smooth implies flat. The lqc-coherator statement explicitly defines H_U and the invertible flat comparisons: I use these clauses, not an unstated description of Q's construction. Space fppf quasi-coherent descent explicitly gives full faithfulness, which glues the compatible chart maps and checks the identity and cocycle. The module-functor definition specifies tensor pullback. The composition check is written on local tensors, and the cocycle cancels c_2 with its inverse. In particular the relation and triple relation are kept as algebraic spaces and no affine-intersection assumption enters.

Step 2 uses the exact effectiveness and map clauses of the new atlas-module theorem to obtain M with its specified atlas isomorphism. The new arbitrary-target map theorem supplies phi:M to H because the displayed compatibility equation is precisely the datum condition on eta. Applying the two stated bijections for every quasi-coherent A proves the universal property of phi. Neither new theorem states this universal arrow or any clause of the original flat-test conclusion.

Step 3 uses only that just-proved bijection and the counit-form Hom bijection actually displayed in lem-sfb-stack-lqc-coherator. It constructs both maps b and c and proves cb=1 and bc=1 by injectivity, rather than presupposing that the named adjunction was built by the source's atlas construction. Restricting q_H b=phi gives q_U=eta b_U^{-1}. I marked this elementary because the entire uniqueness-of-universal-arrow calculation is present; it does not invoke an unproved Yoneda or inverse-existence fact.

Step 4 uses the algebraic-stack definition for W=T times_Z U and the algebraic-space definition for a surjective etale scheme chart V. Its two projections are distinguished: W to T is smooth surjective by the atlas condition, while W to U is flat because z is flat on scheme charts. The chartwise-calculus statement gives the resulting properties for g:V to T and h:V to U. This is the only place the flatness of z is needed, and it is not silently replaced by finite presentation of z. The arbitrary-flat statement is retained.

Step 5 uses the explicitly stated flat comparisons for H and the arbitrary-arrow scheme-test comparisons for the quasi-coherent module jQH. I checked both statements at their actual quantifiers. The square for q_H is written explicitly, and its commutativity is verified on local tensors; the isomorphism over U from step 3 then proves invertibility after g^*. There is no claim that ordinary big-site kernels of quasi-coherent modules are quasi-coherent or that restriction on arbitrary H is exact.

Step 6 checks that both endpoints on T are quasi-coherent using exactly the two cited statements. The covering calculus defines fppf by flatness, local finite presentation and joint surjectivity. The chartwise calculus gives these properties of the smooth surjective g. The small-etale space descent theorem is fully faithful and does not assume quasi-compactness, so it applies to this singleton fppf cover even if the atlas or T is non-quasi-compact. I wrote out how the inverse respects descent data and how faithfulness verifies its inverse equations; reflection of isomorphisms is not taken from a node that only defines quasi-coherence.

Step 7 evaluates the sheaf inverse at the small-etale final object. It does not claim exactness or surjectivity of global sections: a functor carries an actual two-sided inverse to a two-sided inverse.

I reread every cited node's statement, and citations.json contains literal substrings witnessing these uses. All proof uses are listed in proof_deps. The cited statements are either in the item's unit or are definition nodes; no off-route non-definition tool is needed. I compared both new statements against the DAG by tag and concept and against the whole blueprint and project Lean source before writing them. They are not elementary two-line consequences of the cited existing statements: the missing general atlas descent and arbitrary-target map identification are exactly the substantial inputs. The elementary cocycle and universal-arrow computations remain proof steps instead of new nodes.

I checked the B–E checklist: statement-only children, introduced objects and meanings, valid definition citations, single-escaped TeX, verified tags and labels, actual searches only, nonmatching Mathlib generalities distinguished, no proof-of-a-cited-node reliance, no circular use of the item by a child, and no replacement of a unit route. Every proof step is under 2000 characters. I corrected the possible C4 shortcuts during drafting: the existing module-descent node has scheme relations, the existing tensor-equivalence node assumes Deligne--Mumford, and the smooth-atlas node concerns algebras; none was used as if it already stated general module descent.

Small cases: empty Z or empty T gives the unique zero module isomorphism; U=Z a scheme with identity atlas gives delta=1 and M=H; H=0 gives phi=q=0 between zero modules. A non-quasi-compact atlas still uses a small fppf covering with no quasi-compactness hypothesis in the cited descent theorem. A diagonal representable only by algebraic spaces can give nonschematic R and W, which is why all such spaces are treated on etale charts. For an arbitrary nonflat test h need not be flat, so the proof does not overclaim the conclusion there. The arbitrary-target child permits H non-quasi-coherent and leaves c_i^H uninvertible; it only asserts the precise comparison-diagram condition of 076S. No SGA source is used.

## Not duplicates

lem-sfb-smooth-atlas-quasicoherent-source-maps vs lem-sfb-smooth-cover-section-descent: the new node identifies maps from a quasi-coherent source into an arbitrary module; the existing node does not state that arbitrary-target comparison-diagram bijection.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-power-lifting-adequate-affine-quotient: it concerns adequate-moduli power lifting, not the module descent equivalence.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-finite-schemes-etale-stack-descent: it descends finite schemes, not arbitrary quasi-coherent modules.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-disjoint-closed-substacks-algebra-quotient: it constructs algebra quotients for disjoint closed substacks over a field, not general module descent.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-affine-action-quasicoherent-descent: it is an affine smooth-group action quotient over a field and concerns algebras, not arbitrary module data on a general stack.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-affine-groupoid-quasicoherent-algebra-descent: it assumes affine schemes and finite locally free relation maps and concerns algebras.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-flat-affine-action-algebra-descent: it assumes an affine finite-type group action and concerns algebra coactions.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-qcoh-presentation-tensor-equivalence: it assumes a Deligne--Mumford stack with etale atlas, which cannot handle the general smooth atlas here.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-groupoid-module-descent-tensor-cokernel: its groupoid is in schemes, whereas the general smooth atlas here has algebraic-space relations; no schematic diagonal is assumed.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-stack-quasifinite-relative-normalization: it constructs stack relative normalizations under extra hypotheses, not general module descent.

lem-sfb-smooth-atlas-quasicoherent-source-maps vs lem-sfb-adequate-algebra-pushforward: the new node identifies maps from a quasi-coherent source into an arbitrary module; the existing node does not state that arbitrary-target comparison-diagram bijection.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-smooth-atlas-algebra-descent: it descends commutative algebras and algebra maps; forgetting multiplication does not give essential surjectivity for arbitrary module descent data.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-finite-inertia-adequate-coarse-space: it proves existence of adequate coarse spaces under finite inertia, not general module descent.

lem-sfb-smooth-atlas-quasicoherent-source-maps vs lem-sfb-stack-relative-spec-construction: the new node identifies maps from a quasi-coherent source into an arbitrary module; the existing node does not state that arbitrary-target comparison-diagram bijection.

lem-sfb-smooth-atlas-quasicoherent-source-maps vs lem-sfb-stack-algebra-smooth-image: the new node identifies maps from a quasi-coherent source into an arbitrary module; the existing node does not state that arbitrary-target comparison-diagram bijection.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-power-lifting-quotient-submersive: it proves topological submersiveness from power lifting, not module descent.

lem-sfb-smooth-atlas-quasicoherent-source-maps vs lem-sfb-smooth-atlas-algebra-descent: the existing node descends algebra maps between quasi-coherent algebras; the new node has only a quasi-coherent source and an arbitrary module target, with possibly noninvertible comparison maps.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-smooth-atlas-quasicoherent-source-maps: the first is effective object descent and maps between descent objects, while the second identifies maps to an arbitrary, potentially noncartesian big-fppf module target. Neither implies the other's full statement by a one-line specialization.

lem-sfb-smooth-atlas-module-descent vs lem-sfb-action-groupoid-quotient-criterion: the existing statement identifies a finite-group action quotient with a stack under an etale lifting property and a specified relation isomorphism; it neither descends modules nor identifies module maps from a quasi-coherent source. Both cite 04T5 for presentation, but the new statement uses its general smooth-atlas presentation, with arbitrary algebraic-space relations.

lem-sfb-smooth-atlas-quasicoherent-source-maps vs lem-sfb-action-groupoid-quotient-criterion: the existing statement identifies a finite-group action quotient with a stack under an etale lifting property and a specified relation isomorphism; it neither descends modules nor identifies module maps from a quasi-coherent source. Both cite 04T5 for presentation, but the new statement uses its general smooth-atlas presentation, with arbitrary algebraic-space relations.

## Validation

The first dry run exited with a same-tag documentation request for 04T5 and lem-sfb-action-groupoid-quotient-criterion. I opened that node and added the two precise nonduplicate comparisons above; no mathematical change was required. The second dry run exited 0 and printed OK (not pushed), preflight passed, at 97c0434c219. This report now records that passing result; a final dry run validates the delivery including this report before push. No local check_dag.py, review_split.py or preflight_delivery.py invocation was made.
