## What changed

Repair of the returned delivery: removed the duplicate private theorem
`CategoryTheory.sectionsEquiv_naturality` entirely. The existing
`CategoryTheory.Sheaf.sectionsEquiv_naturality` is private to
`Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections`, so it cannot be reused by
importing that module. Instead the section isomorphism construction uses the existing
Mathlib theorem `Adjunction.homEquiv_naturality_right` directly. All three downstream
naturality calculations now use `NatTrans.naturality` of that isomorphism, evaluated by
`ConcreteCategory.congr_hom`. No replacement copy or renamed duplicate theorem is added.
Both sandbox modules compile without warnings (1.4 and 22.7 seconds). The second-reading
section below records the earlier delivery; the repaired version needs its new second reading.

Replaced the whole proof of
`CategoryTheory.exists_topological_terminal_resolution_ext_comparison` without changing its
signature or existing docstring. Constructed the additive section representation on each
site from the sheafification, free-abelian and Yoneda adjunctions. Constructed terminal-section
transport along `Opens.map_top`, proved its compatibility with the generator hypothesis,
and proved the required homology equation using cycle inclusions, homology projections,
`InjectiveResolution.rightDerived_app_eq`, and inverse identities.

The sole remaining step is the general, single-category normalization theorem in
`Sheaf.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison`. It has no pushforward,
no two-site comparison and no comparison morphism phi. The main proof applies it independently
on X and Z and performs the cross-site calculation in Lean. Its normalization determines the
comparison on every Ext class because `InjectiveResolution.extMk_surjective` represents every
class, so no arbitrary object is constructed from mere unproved existence.

Added a proof-only import of the new normalized comparison module. The abelian-group
cycle and adjunction whiskering APIs are already available through the public imports. Removed the unused proof imports of ExtRightDerivedHom and
CohomologyRightDerivedSections. Updated the original node's proof route and dependencies.
Removed all instance caches and the extra heartbeat setting from the earlier attempt;
the complete proof now compiles against the canonical instances in 24 seconds.

## Proved and sorry left

Closed the original hole:
`CategoryTheory.exists_topological_terminal_resolution_ext_comparison`
(node `lem-sc-topological-terminal-resolution-ext-comparison`). Its proof contains no sorry.

Added one hole:
`CategoryTheory.exists_ext_rightDerived_cocycle_comparison`
(node `lem-sc-ext-right-derived-cocycle-comparison`), whose proof is exactly `by sorry`.
There are no other remaining holes in the delivered modules. This is a decomposition,
not a net reduction in holes: one closed and one added. The sheaf-section identifications,
terminal transport, cycle transport and combination of normalization equations are proved.

## No longer needed

The duplicate private helper `CategoryTheory.sectionsEquiv_naturality` is removed;
Mathlib's general adjunction and natural-transformation naturality theorems supply its uses.
No extra import or node is required for this repair, and no additional hole is introduced.

Removed the original proof-only imports of the two modules listed below. Existing public
imports are retained to preserve the interface.

The second reader also removed the first worker's redundant proof imports of
`Mathlib.CategoryTheory.Adjunction.Whiskering` and
`Mathlib.Algebra.Homology.ShortComplex.Ab`; both APIs are already available.

The original proof route no longer directly uses:
- `lem-sc-site-cohomology-right-derived-sections`, module
  `Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections`;
- `lem-sc-ext-right-derived-hom`, module
  `Sheaf.CategoryTheory.Abelian.ExtRightDerivedHom`.

Neither module is imported by this delivery. Their public comparison theorems supply bare
natural isomorphisms but do not state the normalization needed here. The normalized generic
comparison replaces these two dependencies. This reports pruning from this item's route,
not a claim that the modules are globally unreachable through other targets.
`lem-sp-derived-well-defined` remains used through Mathlib's resolution computation API.
No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned version copied the private section-naturality lemma already present in
`CohomologyRightDerivedSections`. The landing checker correctly rejected that duplicate.
Importing the existing helper is unavailable because its visibility is private; the repair
therefore removes the duplicate declaration and reuses Mathlib's general naturality API.
No library visibility, existing signature, or other group's module is changed.

The DAG's instruction to use the underlying Hom-complex construction is mathematically
correct, but the existing comparison modules expose only unnormalized existence theorems;
the relevant component constructions are private. Their public signatures therefore cannot
supply the required extMk equation. The new node isolates this missing normalization.
No statement is disputed or weakened. Empty spaces, zero cocycles and degree zero are
covered by the same constructions; the new theorem needs no projectivity of the representing
object and no exactness of the represented additive functor.

The earlier attempt's locally cached `terminalAbelian` instance caused a kernel-checking
timeout, even when the proof body was reduced to constructing the comparison witnesses.
Removing that data-valued instance made the full proof compile in 15 seconds; removing the
remaining caches and redundant theorem-local options leaves a clean 24-second compile.
No definition or statement change was needed. The retry also corrects the new node's
Loogle search result to match the preserved search log: homologyπ_naturality was found.

## New nodes

`lem-sc-ext-right-derived-cocycle-comparison` is the normalized comparison between a
represented additive functor's right derived functors and Ext, valid in one abelian category.
Its module is `lean/Sheaf/CategoryTheory/Abelian/ExtRightDerivedCocycleComparison.lean`.
The node and declaration give the full Hom-complex construction, comparison-map naturality,
and extMk normalization argument, with Stacks Tags 06XR and 013P as sources.
LeanSearch was unavailable; LeanFinder, Loogle and source grep were run and recorded.

Change record: `coord/changes/T1-terminal-resolution-ext-normalization.md`.

## Earlier second reading (a previous round; superseded)

1. **Unchanged interface: PASS.** Compared the delivered terminal-resolution module with
   the repository using `diff`, and compared the full existing theorem header byte for
   byte through `:= by`: identical. Its existing docstring and all public imports are
   unchanged. The other delivered module is new, and its declaration is recorded in the
   change record. No existing definition is modified and no forced adaptation is needed.
2. **Proof and axioms: PASS as a decomposition.** Compiled both delivered modules in
   import order using `lcompile.py --all`: both passed, without warnings (1.5 s and
   22.8 s before import pruning). Explicit `#print axioms` in a scratch copy gives exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for both public theorems.
   A source scan finds exactly the one named, reported `by sorry` in the new module and
   no prohibited declarations or attributes. There is no sorry in any definition.
   The main theorem eliminates the existence witnesses inside a proof; it creates no
   data definition by choosing a witness from an unproved mere existence statement.
3. **Split statement: PASS.** Read the new theorem, its full proof docstring, node, and
   change record. It isolates the one-category normalized Ext/derived-Hom computation;
   it contains neither a continuous map nor the two-site compatibility conclusion.
   The main module supplies the actual sheaf and cross-site argument. Checked degree
   zero (ordinary kernel classes, with no negative boundary), zero cocycles, the zero
   representing object, and empty spaces; none needs an extra hypothesis. An arbitrary
   given natural isomorphism e transports the comparison, so no choice of generators
   or exactness of H is required. Normalization determines the inverse on every Ext
   element by `InjectiveResolution.extMk_surjective`; the resolution isomorphism is
   injective, and inverse natural transformations determine the forward ones uniquely.
   Verified the cited [Stacks 06XR](https://stacks.math.columbia.edu/tag/06XR) and
   [Stacks 013P](https://stacks.math.columbia.edu/tag/013P) supply the Ext computation
   and comparison-lift argument. Repeated LeanFinder with "injective resolution Ext
   cocycle class homology additive coyoneda right derived normalization" and Loogle
   with `"extMk", "surjective"`; only the cocycle/comparison building blocks were found.
   Independently searched `lean/Sheaf`, `lean/WeilConjectures`, and pinned Mathlib with
   cocycle, normalization, extMk/homology and comparison terminology. Existing public
   comparison results do not give this normalization. Completing its Hom-complex and
   resolution-transfer construction is substantial proof work, rather than a short
   overlooked application; its hole remains explicitly reported.
4. **Top-down proof and pruning: PASS, with redundant imports removed.** Read the
   section adjunctions, terminal equality transport, use of ha at top, cycle construction,
   homology naturality, and derived-isomorphism cancellation in order. The augmented
   comparison assumption is unused because the equation already follows from the
   stipulated cocycle relation; its signature remains unchanged. The report lists both
   removed old proof dependencies, and retains `lem-sp-derived-well-defined` through
   Mathlib's API. Checked `dag/units/sk-thm-curveestimate.json`: its sole realized
   statement is `thm-sc-proper-cohomology`, and it has no realized proof steps. This
   local reduction bypasses no realized unit statement or step. Compilation experiments
   showed that both newly added Mathlib proof imports are redundant; removed them.
5. **DAG and Lean agreement: PASS.** Diffed the existing node: only proof, proof_deps,
   and proof_origin change. Its route matches the Lean argument, and its statement and
   lean record remain unchanged. The new node has matching chapter/unit, source,
   searches, provenance, dependencies, and its exact Lean statement. There is one hole
   closed and one added, hence zero net holes closed; this remains a decomposition.

Changes by this second reader: removed redundant proof imports of
`Mathlib.CategoryTheory.Adjunction.Whiskering` and
`Mathlib.Algebra.Homology.ShortComplex.Ab`; corrected the import description above;
added this independent review and its search evidence. No proof or existing statement
needed repair. The delivery dry run rechecks the final files and all their declarations.

## Second reading by T1

Independent reading of the repaired delivery, after the duplicate-naturality return:

1. **Interface: PASS.** Diffed the delivered main module against the read-only repository.
   Programmatically compared the existing theorem header through `:= by`: byte identical.
   Its docstring and public imports are unchanged. No existing definition or statement
   changes; the added theorem is covered by the normalization change record.
2. **Proof: PASS as a decomposition.** Ran `lcompile.py --all` on the final modules:
   the new module compiled in 1.4 seconds and the main module in 23.2 seconds, without
   warnings. An independent scratch audit printed the axioms of both public theorems:
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Source inspection
   found only the reported new named theorem's `by sorry`; no prohibited declaration,
   kernel-check bypass, or sorry in a definition. All private data definitions are
   actual constructions. The main proof eliminates the normalized comparison witnesses
   locally in a proposition; it adds no definition choosing an arbitrary existence witness.
3. **Split statement: PASS.** Read its signature, docstring, node, and change record.
   The one-category normalization omits all two-space, pushforward, generator, and
   comparison-map data, so it is strictly a part of the original argument, not a renamed
   copy of its conclusion. For degree zero the Hom complex has no incoming negative
   boundary; the zero cocycle and zero representing object give zero classes. Empty
   spaces pose no obstruction to the section adjunction. An arbitrary additive natural
   isomorphism e transports the computation and requires no projectivity assumption.
   For any Ext element, `InjectiveResolution.extMk_surjective` supplies s; naturality
   of e gives the corresponding cycle, and monicity of iCycles makes that cycle unique.
   The normalization and invertibility of the resolution comparison therefore determine
   the inverse of x on every element, hence determine x itself.
   Repeated LeanFinder with "Ext additive representable derived functor canonical
   comparison evaluation on a cocycle" and Loogle with `"extMk"`: only constituent
   Ext mapping and cocycle lemmas appeared. Independently searched the project and
   pinned Mathlib with normalization, cocycle, rightDerived and extMk terminology.
   Read the existing derived-Hom comparison and resolution-cohomology constructions:
   their public statements do not expose this normalization. Their implementation
   components are private. Closing the remaining Hom-complex/resolution-transfer proof
   would require substantial new work, not a short application overlooked in this audit.
   Verified the supporting source statements at
   [Stacks 06XR](https://stacks.math.columbia.edu/tag/06XR) and
   [Stacks 013P](https://stacks.math.columbia.edu/tag/013P).
4. **Route and pruning: PASS.** Read the proof downward: additive section representation,
   normalized comparisons at X and Z, terminal transport, generator identity at top,
   cycles, homology naturality, and right-derived cancellation. The repair now applies
   `Adjunction.homEquiv_naturality_right` directly and uses naturality of sectionsIso
   thereafter; the rejected duplicate theorem is absent. The augmented-map assumption
   is not needed for the cocycle calculation, which follows from hsz; it is retained
   verbatim in the existing signature. The report names every removed old proof
   dependency: the site-derived-sections and derived-Hom comparison nodes/modules.
   `lem-sp-derived-well-defined` remains in use via the resolution API. The unit record
   `sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology`, with no realized
   steps; this local reduction changes neither that statement nor its route.
5. **DAG: PASS.** The existing node diff changes exactly `proof`, `proof_deps`, and
   `proof_origin`; its steps track the actual Lean calculations. The new node has the
   required source, searches, provenance, parent, chapter/unit, and exact Lean signature
   (checked programmatically against its module). All new dependencies are accounted
   for. One original hole is closed and one new hole is added: net zero, explicitly a
   decomposition, not a completed axiom-free proof of the item.

Changes in this reading: appended this current independent review and renewed search
and compile evidence. No further Lean or DAG repair was necessary. The prior review
above remains marked superseded and is not the review of this repaired delivery.
