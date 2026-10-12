## What changed

Replaced the whole proof of
`CategoryTheory.exists_topological_leray_bottom_realization` by a complete Lean
reduction. Its existing signature and public imports are unchanged. The proof extracts
Leray construction data, represents every input class by an injective-resolution
cocycle using `InjectiveResolution.extMk_surjective`, lifts that cocycle, compares the
supplied `hedge` computation with the constructed bottom-map computation, cancels the
cohomology transports, and uses concrete-group and natural-transformation extensionality.
Two elementary private lemmas prove cancellation of `eqToHom` on group elements.

Added the separate statement modules
`Sheaf.Topology.TopologicalLerayCartanEilenbergCocycle` and
`Sheaf.Topology.TopologicalResolutionCocycleLift`. The first isolates the original
Cartan--Eilenberg construction, finite filtration and augmentation computation; it has
no supplied `edge` or `hedge` input. The second supplies only a chain comparison and
compatible cocycle, with no spectral sequence or cohomology-map equality. Their
combination requires the actual surjectivity and equality proof in the original module.
No data definition or existing statement was changed. The construction names its
bottom map separately and records its factorization, avoiding repeated unfolding of
its long composite while checking the cocycle equality. The parent node now records
this route. The curve-estimate unit's statement and steps are untouched.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.exists_topological_leray_bottom_realization`
(`lem-sc-topological-leray-bottom-realization`). No `sorry` remains in the item module.

Added two whole-theorem holes:

- `CategoryTheory.exists_topological_leray_cartan_eilenberg_cocycle`
  (`lem-sc-topological-leray-cartan-eilenberg-cocycle`).
- `CategoryTheory.exists_topological_resolution_cocycle_lift`
  (`lem-sc-topological-resolution-cocycle-lift`).

This is a decomposition, not a proof free of `sorry`: one hole closed and two added.
Each new declaration has its source and complete proof in words in its docstring and
node. The final equality proof and both private transport lemmas are fully proved.
The lifting lemma's argument uses only exactness of J and injectivity of the terms of
f_*I; it does not assume direct image is exact. Degree zero and the zero sheaf obey the
same argument. The construction introduces no extra acyclicity hypothesis on F.

## No longer needed

Removed these direct proof imports from the item module:

- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`: its construction is now the
  dependency of the new Cartan--Eilenberg statement module, not a pruning of that route.
- `Sheaf.CategoryTheory.GrothendieckComposablePair`: available through the construction
  dependency, and unused directly in the final cocycle equality proof. Its node
  `def-sp-composite-acyclicity` is no longer a direct parent proof dependency; the
  construction still checks injective-to-sections acyclicity through Grothendieck.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`: retained as a proof dependency
  of the new construction module, not pruned from its planned construction.
- `Sheaf.Topology.TopologicalInducedCohomologyCocycle`: the item already receives the
  cocycle characterization as `hedge`, so its existential theorem is unnecessary here.
  Its node `lem-sc-topological-induced-cohomology-cocycle` is no longer a direct proof
  dependency of this item; the caller still uses it to obtain `edge`, so this does not
  claim that the whole targets' import closure loses that module.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`: the displayed
  final argument does not use a long exact sequence or the general acyclic-resolution
  theorem. The construction uses injective preservation and the Grothendieck theorem.
  Node `lemma-weil-pbc-leray-acyclicity` is unnecessary as a separate direct dependency.
- `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`: its first spectral-sequence
  existence statement does not provide the required second-filtration interface.
  The Cartan--Eilenberg Grothendieck theorem already carries that construction;
  `thm-sp-double-complex-spectral-sequences` is not separately needed at this node.

The definition nodes `def-sp-filtration`, `def-sc-topological-abelian-cohomology`,
and `def-sp-spectral-sequence` remain relevant to the statements. Construction nodes
`thm-sp-grothendieck`, `lem-sc-topological-pushforward-injective`, and
`prop-pur-kinjective-resolutions-exist` are retained below the new construction node.
No entire unit, and no claimed globally unreachable module, is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt treated the missing natural Cartan--Eilenberg/cocycle interface
as a reason to stop. Those are isolatable steps, as the brief allows. The final
cocycle-surjectivity and extensionality argument compiles once these steps are stated.
The existing Grothendieck theorem exposes objectwise spectral sequences and natural
comparison equations, rather than the required natural-indexed spectral sequence in
the functor category. The new construction theorem isolates this assembly and
terminal-section/Ext transport, without restating the theorem about a supplied edge.

LeanSearch returned an internal server error. LeanFinder and source searches were
used instead; this unavailability is recorded, not treated as an absence result.
The Stacks sources were read at Tags 015N and 01F2 because their local TeX copies
were absent on this machine.

## New nodes

`lem-sc-topological-leray-cartan-eilenberg-cocycle` isolates the construction, finite
filtration and augmentation computation from parent steps 1--2 and the first part of
step 3 (Stacks 015N, 015J and 01F2). It retains the Grothendieck construction route.
Its spectral data are independent of any supplied `edge`, and it computes the named
bottom map on resolution cocycles. Three kinds of searches are recorded, with
LeanSearch marked unavailable.

`lem-sc-topological-resolution-cocycle-lift` isolates the existence of phi and z in
parent step 3 (Stacks 01F2, injective-resolution comparisons and terminal sections
01DZ). Its proof in words details extension along the exact source resolution and
the sheafification/free-forgetful/Yoneda representation. It asserts no edge equality
and no spectral-sequence construction. Three kinds of searches are recorded, with
LeanSearch marked unavailable. There are no interface changes, forced adaptations,
or change records.

## Second reading by A3

1. **Interface: PASS.** Compared every delivered module against the repository.
   Only the item module exists there; its existing theorem signature is byte for
   byte unchanged, as are its public imports and docstring. The new modules add
   only theorem statements; there are no definition changes or forced adaptations.
2. **Proof and trust: PASS as a decomposition.** Compiled all three modules with
   lcompile.py in dependency order (21.7 s, 5.4 s, 37.8 s), without warnings or errors.
   A scratch copy with explicit `#print axioms` for all three public theorems
   compiled and reported only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx`. Exactly the two reported new whole-theorem holes remain; no forbidden
   declaration, hollow definition, or arbitrary-witness data definition occurs.
   The parent proof represents each input by extMk_surjective, applies the two
   computations to the same lifted cocycle, cancels transports, and extends the
   equality to natural transformations. It does not replace the supplied edge.
3. **Split statements: PASS.** Read both docstring proofs and their matching nodes.
   The construction statement has no supplied edge or hedge and establishes the
   geometric construction and augmentation computation. The lifting statement
   contains no spectral sequence or equality of cohomology maps. They are strictly
   parts of the argument and require the parent's substantive equality proof.
   In the lift, exactness is needed only for J; the target f_*I need not be exact.
   Terminal-section representation makes the lifted z unique for a fixed phi.
   Degree zero, the zero sheaf, identity maps, and empty spaces introduce no missing
   hypotheses. In the construction, first-quadrant bounds stabilize at p+q+2;
   the zero denominator in the bottom graded piece gives the stated k equation.
   Checked the source arguments at [015N](https://stacks.math.columbia.edu/tag/015N)
   and [01F2](https://stacks.math.columbia.edu/tag/01F2).
   [01DZ](https://stacks.math.columbia.edu/tag/01DZ) supplies the cohomology convention;
   the free-terminal representation itself follows from the explicitly described
   sheafification/free-forgetful/Yoneda adjunctions, rather than a separate theorem
   in that section. Independent searches used an exact-augmented-complex comparison
   query (LeanFinder), `presheafToSheaf, yoneda` (Loogle, unknown identifier, hence
   inconclusive), and free-Yoneda/sections-equivalence terminology (grep), plus rg
   over the library and Mathlib. Found resolution desc primitives and module-sheaf
   freeHomEquiv, but no duplicate of either combined statement. Neither remaining
   theorem can be closed from those primitives in a few minutes.
4. **Route and pruning: PASS after report correction.** Read the original proof
   dependencies and Grothendieck construction declaration. The construction and
   finite-filtration route remain below the new construction node; this is not a
   claim of global module pruning. All ten old dependencies are accounted for in
   No longer needed, including the previously omitted def-sp-composite-acyclicity.
   The curve-estimate unit's realized statement thm-sc-proper-cohomology and its
   empty steps list are untouched; no unit route is bypassed.
5. **DAG: PASS.** The parent changes only proof, proof_deps, and proof_origin.
   Each node's stored Lean statement exactly matches its module, and proof_deps
   equals the union of its steps' uses. New nodes have source, proof in words,
   searches, creation, blueprint, chapter/unit, and Lean records. The parent
   records precisely the two lemmas and the extMk/extensionality reduction used.

Changed only this second-reading record and the missing pruning explanation for
`def-sp-composite-acyclicity`. No Lean or node repair was needed. This remains one
original hole closed, two holes added (net minus one), with no entire module
claimed pruned from the targets' closure.
