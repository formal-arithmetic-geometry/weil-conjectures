## What changed

Repaired reviewer X-656a9's return on head 656a9eff7. Removed
`isIso_constantModulePushforwardColimitDesc`, its comparison node, and
`coord/changes/isIso_constantModulePushforwardColimitDesc.md`. Restored the original
target theorem's full docstring and kept its signature unchanged.

The replacement proof presents the existing diagram and cocone using identity
isomorphisms, proves both presentation equations by simplification and definitional
equality, applies two separate continuity halves to obtain a monomorphism and an
epimorphism, and combines them using `isIso_of_mono_of_epi` in the abelian category
of module-valued sheaves. The standard colimit comparison criterion then establishes
`isColimit_constantModulePushforwardCocone`.

Added two modules with one named public sorry each:
`Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitInjectivity` and
`Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitSurjectivity`.
The first asks only for injectivity, the second only for surjectivity. Neither
asserts an isomorphism or colimit property. Their common presentation hypotheses
explicitly specify every scheme, ring, module, diagram, cone, isomorphism and
compatibility equation; no reference to unnamed target hypotheses is used.

Both docstrings describe directed reindexing, constant-sheaf pullback coherence,
degree-zero identification including comparison components, and coefficient
forgetting. The injectivity proof uses eventual equality of sections, whereas
surjectivity uses local descent of sections. The source argument was checked against
Stacks Tags 09Z1, 09Z6 and 09YQ at their canonical online pages. The two obligations
are left for subsequent workers; no application of continuity is claimed to be
formalized yet inside either helper.

Updated the original node's `proof`, `proof_deps`, and `proof_origin` to describe
this actual replacement proof and its two remaining dependencies. New nodes carry
the precise signatures and separate proof plans. All new imports in the item are
proof-only. No existing definition or statement changes, so no change record is
needed.

## Proved and sorry left

The item's one original sorry is closed:
`AlgebraicGeometry.Etale.isColimit_constantModulePushforwardCocone` is proved from
these two strictly smaller remaining statements:

- `AlgebraicGeometry.Etale.mono_constantModulePushforwardComparison`, in
  `Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitInjectivity`, node
  `lem-weil-pbc-constant-module-pushforward-limit-injectivity`, remains `sorry`.
- `AlgebraicGeometry.Etale.epi_constantModulePushforwardComparison`, in
  `Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitSurjectivity`, node
  `lem-weil-pbc-constant-module-pushforward-limit-surjectivity`, remains `sorry`.

Neither half alone is equivalent to the target: a monomorphism need not be epic,
and an epimorphism need not be monic, even in an abelian category. The target proof
requires both. The diagram and cocone definitions remain unchanged and contain no
sorry. This delivery does not claim closure under the project's final axiom check:
the two named continuity halves still depend directly on sorry.

## No longer needed

Removed the rejected duplicate declaration, node
`lem-weil-pbc-constant-module-pushforward-limit-comparison`, and its change record.

Removed these direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem`;
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`;
- `WeilConjectures.ConstructibleSheaf.Defs`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The first two remain in the new continuity-half modules as dependencies of their
proof plans. The last two are available through the unchanged public import of
`ConstantModulePushforwardFunctoriality`. Thus these removals shorten the item's
direct imports; they do not prune any original continuity node from the targets'
closure. No original proof-dependency node or module is claimed globally redundant.
The original unit route is retained below the two remaining continuity obligations.

The target no longer directly uses these original proof-dependency nodes (all remain
below the continuity halves, so none is globally pruned):

- `def-weil-pbc-direct-image`;
- `lem-weil-pbc-colimit-constant-connected-diagram`;
- `lem-weil-pbc-constant-module-pushforward-functoriality`;
- `lem-weil-pbc-filtered-category-exists-directed-final`;
- `lem-weil-pbc-module-sheaves-colimits-forgetful`;
- `lemma-constructible-pullback-constant`;
- `sbc-lem-higher-direct-image-limit`.

## Where the brief, the DAG or earlier work was wrong

The previous delivery moved the entire mathematical obligation into an equivalent
comparison-isomorphism statement. Its categorical proof did not constitute a
reduction. The first and second readings incorrectly called that statement strictly
weaker than the colimit assertion. The rejected statement is removed, addressing
D1/D2 and B2; the full original docstring is restored.

For E5, each remaining sorry has a complete proof in words including the four
previously omitted steps. The eventual-equality and section-descent halves are
separate mathematical obligations. For F2 the original node now describes exactly
the Lean proof written here rather than the old rejected comparison proof. The
original node's statement, unit and other fields are not changed.

The existing higher-direct-image continuity theorem is a directed, abelian-sheaf
statement. Applying it to the two remaining half-lemmas still requires the
presentation and coefficient identifications spelled out in their docstrings.
The module-sheaf forgetful theorem concerns `SheafOfModules`; its application to
constant-ring module-valued sheaves requires that standard identification as part
of the remaining coefficient step. No such identification is silently claimed
proved in this delivery.

## New nodes

`lem-weil-pbc-constant-module-pushforward-limit-injectivity` is realized by
`Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitInjectivity`. Its conclusion
is only `Mono (colimit.desc K c)`. Its proof plan uses eventual equality on the
affine etale basis, sheaf separation, and faithful coefficient forgetting.

`lem-weil-pbc-constant-module-pushforward-limit-surjectivity` is realized by
`Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitSurjectivity`. Its conclusion
is only `Epi (colimit.desc K c)`. Its proof plan uses local lifting on the affine
etale basis and faithful coefficient forgetting, without eventual equality.

Both statements include all data and compatibility equations explicitly. Both
cover zero modules, empty limit schemes and singleton indices; cofilteredness
excludes empty indexing categories. No change records are added.

## Earlier second reading (a previous round; superseded)

Correction of the earlier second reading, explicitly requested by reviewer
X-656a9 (F, brief point 7):

The comparison theorem is equivalent to the target colimit assertion by IsColimit.nonempty_isColimit_iff_isIso_desc; the proposed split moved the mathematical obligation without reducing it.

The rejected declaration, node and change record are now absent. This correction
supersedes the previous second reading's claims about that equivalent helper being
strictly weaker and about the old DAG recording the actual categorical proof.
A fresh independent second reading must assess the replacement two-half reduction,
its updated DAG and the named remaining sorries before delivery. This worker has
not performed or certified that independent second reading.

## Second reading by N1

1. I diffed the delivered target module against the repository version. The target theorem
   signature and all existing declarations are unchanged; the proof only replaces the
   original `sorry` and the direct proof imports are narrowed to the two helper modules.
   Verdict: pass.

2. I compiled all three modules with `lcompile.py --all`. They compile without errors.
   The only remaining `sorry`s are the named Mono and Epi helper theorems, and neither
   occurs in a definition. No forbidden declarations were added. Their proof obligations
   are explicitly documented and represented by DAG nodes; the target proof itself is
   kernel-valid relative to those open statements. Verdict: pass subject to the two
   declared split obligations.

3. The two split statements assert only `Mono (colimit.desc K c)` and `Epi
   (colimit.desc K c)` under the complete presentation hypotheses. They are strictly
   smaller than the target colimit assertion and are not duplicate comparison-isomorphism
   statements. I searched the local library and the stated Mathlib search results; no
   existing declaration duplicates them. Verdict: pass.

4. The target proof follows the unit route by presenting the explicit diagram and cocone,
   applying the two continuity halves, and combining Mono plus Epi in the abelian category.
   The removed direct imports are proof-only dependencies no longer used by the target;
   the helper modules retain the continuity and forgetful imports required by their plans.
   Verdict: pass.

5. The target and helper DAG nodes match the Lean declarations, proof dependencies, and
   proof origins. The unit `sk-thm-p1` remains the recorded route, and the new nodes are
   marked split with complete sources and proof plans. Verdict: pass.

I changed only this second-reading report section; no Lean statements or proofs required
repair after compilation and comparison.

Additional checks: scratch-copy `#print axioms` for both helpers, the target,
and the two existing diagram/cocone definitions returned exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`. The definitions' `sorryAx` comes
from existing named proof dependencies, not hollow data. Independent Loogle query
`"Epi", "colimit.desc"` had no hits; LeanFinder query "monomorphism epimorphism
etale sheaf constant coefficients inverse system continuity" returned condensed
sheaf and general categorical results, none for this etale comparison. Local
search found coefficient-forgetting support in `ConstantModuleSheavesForgetColimits`,
but no result closing either full continuity half in a few minutes.
I checked Stacks 09Z1 and 09YQ at their canonical pages: qcqs base-change test
schemes and degree-zero continuity give both halves without finite-generation
hypotheses. For singleton indices the limit projection and comparison are
isomorphisms; for zero coefficients the comparison is between zero objects;
for an empty limit the same qcqs continuity applies, and the source colimit
also vanishes. No unit-realizing node is bypassed or removed.

Second reading changed this report only: supplied the independent review,
axiom/search/edge-case evidence, and the explicit replaced dependency list.
