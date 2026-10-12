## What changed

The signature and public imports of `CategoryTheory.exists_topological_leray_cartan_eilenberg_cocycle`
are unchanged. Its proof is now complete, combining two strictly smaller obligations.
`TopologicalLeraySpectralObjectAugmentation` supplies the topological spectral object, interval
and abutment comparisons, and its augmentation computation. It supplies no filtration or
spectral-sequence transition data. `SpectralObjectBottomFiltration` is independent of topology,
sheaf cohomology, injective resolutions, and the map a: it compares the graded pieces and
bottom projection of a specified image filtration of any first-quadrant spectral object.

The original module proves two private generic lemmas. `exists_bottom_page_transitions`
uses the natural-number complex shape to prove the outgoing bottom differential is zero,
inverts the cycles inclusion, and defines and verifies the transition iterates using
`Int.leInduction`. `spectral_object_page_stabilizes` compares arbitrary pages r >= p+q+2
with the stable spectral-object interval and then with pageInfinity. The main proof constructs
the integer-indexed image filtration explicitly and proves antitonicity and both bounds.
It constructs e2, e0 and bottom, and proves the required bottom composite by rewriting the
generic factorization and cancelling the canonical page-two isomorphism. No data definition
is chosen from an unproved existence theorem: all existential witnesses are eliminated
inside theorem proofs, and T, transitions, and iteration have concrete constructions.

The existing node's proof and proof dependencies were updated. The unit is
`sk-thm-curveestimate`, whose only realized statement is `thm-sc-proper-cohomology`; no
unit statement or step is bypassed. The generic closed source-library spectral-object
abutment node is used as a tool; its explicit image quotient result is needed, and the
curve unit has no replacement for this general abelian-category fact.

## Proved and sorry left

Closed the single hole in `CategoryTheory.exists_topological_leray_cartan_eilenberg_cocycle`.
There is no sorry in the delivered original module or in its two private lemmas.

Added exactly two holes, each the entire proof of a public theorem in its own module:

- `CategoryTheory.exists_topological_leray_spectral_object_augmentation`
  (`lem-sc-topological-leray-spectral-object-augmentation`).
- `CategoryTheory.exists_spectral_object_bottom_filtration`
  (`lem-sc-spectral-object-bottom-filtration`).

This is a decomposition, not a proof free of postponed dependencies: one upper hole
closed and two strictly smaller holes added. Both new holes have source citations,
complete mathematical proof descriptions and matching DAG nodes.

All three modules compile together without warnings using lcompile.py, and the delivery
dry run printed OK. A separate compiled instance check confirms that Mathlib supplies
both IsGrothendieckAbelian and EnoughInjectives for the displayed abelian sheaf categories.
The import graph of the delivered route has no path to RingedSiteKInjectiveResolutions.
The proofs of
transitions, iteration, stabilization and filtration bounds are generic, so they also
cover p=0, q=0 and zero objects. For the new statements, the following edge cases were
checked mathematically: for p=0 the stable bottom page is page two and b is the identity;
for the identity map the augmentation sends s=z to the same Ext class; for zero sheaves
the cohomology groups vanish. An arbitrary abutment isomorphism h causes the same
transport in the filtration and bottom edge. The transition and iterate hypotheses in
the generic lemma uniquely fix t and b, since cycles inclusion is invertible and b starts
with the identity. Thus they do not allow an arbitrary bottom edge or a sign change.

## No longer needed

Removed the direct proof imports `Sheaf.CategoryTheory.GrothendieckSpectralSequence`
and `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions` from the original module.
The former is still needed by the new topological augmentation obligation and is
imported there; it is not claimed as pruned from the dependency closure.

`prop-pur-kinjective-resolutions-exist` and
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions` are not needed on this route:
Mathlib supplies the Grothendieck abelian and enough-injectives properties for abelian
sheaves on the small opens sites directly (`Sheaf.instIsGrothendieckAbelian` in
GrothendieckAxioms/Sheaf, with AddCommGrpCat's Grothendieck instance). The construction
uses bounded-below ordinary injective and Cartan--Eilenberg resolutions. No unbounded
K-injective existence or localized module-sheaf generator is needed. This is pruning
of this item's route, not a claim that no other target imports that module.

No public import was removed, and no interface or definition used by another module changed.

## Where the brief, the DAG or earlier work was wrong

The existing generic Grothendieck construction is objectwise and integer-indexed. Its
interface does not directly supply this module's natural-number pages in the functor
category together with the terminal-representable Ext cocycle calculation. The new
augmentation obligation records this genuinely missing specialization rather than
pretending that the whole result follows by one application of thm-sp-grothendieck.

STATEMENT-DISPUTED: the unrelated declaration
`CategoryTheory.topological_induced_cocycle_formula` in
`Sheaf.Topology.TopologicalInducedCocycleFormula` quantifies over an arbitrary edge and
never requires it to be the canonical induced map. For f the identity of a one-point
space, HX and HZ the stated cohomology functors, a the identity, edge the zero natural
transformation, p=0, and F the constant integer sheaf, take I=J, phi the identity, and
a degree-zero cocycle representing 1. All its hypotheses hold, but its conclusion is
0=1. This lemma was read during the shorter-route search and is not imported or used.
Its module is outside this item's owned/forced-adaptation set, so it is reported here
for its holder rather than changed in this delivery. The new augmentation lemma fixes
bottom by an actual spectral-object edge and does not repeat this flaw.

The blueprint ancestor helper prints None for this existing node because its creation
chain contains module names. The delivered new nodes preserve the already-reviewed
parent's ancestor `lem-sc-pic-proper-ntorsion` and prepend the item node to its via chain.
Blueprint searches for Leray spectral and bottom edge found no duplicate of either new
statement (the Leray search returned scheme/quasi-coherent statements and a pro-etale
comparison). LeanFinder and local searches found comparison and page APIs, not the
complete missing statements. LeanSearch returned Internal Server Error; the node
records this as unavailable, never as evidence of absence.

## New nodes

`lem-sc-topological-leray-spectral-object-augmentation`, module
`Sheaf.Topology.TopologicalLeraySpectralObjectAugmentation`: isolates construction of
the natural spectral object and augmentation computation (parent steps 1 and 3),
without transition iteration or filtration factorization. Source: Stacks Tags 015N,
015J and 01F2, read at their official pages.

`lem-sc-spectral-object-bottom-filtration`, module
`Sheaf.CategoryTheory.SpectralObjectBottomFiltration`: isolates the compatibility
between the specified image-filtration graded comparisons and the iterated bottom
projection, for arbitrary abelian categories (the remaining portion of parent step 2).
The parent already constructs the filtration and proves its bounds and stabilization;
the new lemma does not postpone those proved steps. Source: the spectral-object image
quotient construction in the source library, Stacks Tags 015J, 015N and 012K.

No change records or forced adaptations are required: all existing signatures and
visibility are unchanged, and the only added imports of the original module are proof imports.

## Second reading by H1

1. I compared the delivered parent module with the repository version. The public theorem signature and all existing declaration signatures are unchanged; the edits are proof imports, private helper proofs, and the parent proof. The two new modules contain only the split-off declarations named in the report. Verdict: pass.

2. I compiled all three delivered modules with `python3 /home/ubuntu/weil-launcher/lcompile.py --all`; compilation completed without errors or warnings. The only remaining `sorry`s are the two named public split theorems, and there are no axioms, unsafe declarations, hollow definitions, or forbidden implementation commands. Verdict: pass.

3. I checked the split statements against their uses and nodes. The spectral-object augmentation supplies only the construction, comparisons, and cocycle computation; the bottom-filtration theorem supplies only the generic graded and bottom factorization. Both are strictly smaller than the parent and retain the hypotheses needed by the parent. Local edge-case review covers p=0, q=0, identity and zero objects. Searches recorded in the nodes found no existing duplicate declaration. Verdict: pass.

4. I reviewed the proof route top-down. The parent uses the two split obligations, the natural-number spectral-sequence APIs, and the filtration definition; it does not use the removed direct proof imports. The realized unit route remains the spectral-object construction followed by filtration and bottom computation. Verdict: pass.

5. I checked the DAG records against the Lean declarations. The parent proof and `proof_deps` match the imports and helper applications; each new node has its declaration, source, proof, dependencies, blueprint, and split status. Verdict: pass.

I changed only this report by adding the second-reading record. No Lean source or node content required repair.
