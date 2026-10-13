## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.StalkFreeResidueCohomologyComparison` with a complete
Lean proof from the existing K-flat resolution, exact stalk, bounded-flat K-flat,
and stalk K-flatness declarations. The original theorem signature, visibility,
three universes, and all its hypotheses are unchanged.

The proof constructs a sheaf K-flat resolution P of G, derives preservation of
homology by the stalk functor from module_stalk_exact, and constructs the derived
isomorphism K ≅ P_x using the inverse localized resolution map. Termwise freeness
and the given upper bound prove K-flatness of K. It then composes the residue
cohomology comparison for P with the inverse scalar-extension homology comparison.

Added three modules, each with one public theorem:

- `Sheaf.Algebra.Homology.KFlatScalarExtensionDerivedIso`: proved the generic
  ring scalar-extension comparison. The two private helpers are proved. The proof
  uses an actual derived-category roof, a source-library K-flat resolution of its
  source, and mixedTensor_kFlat_quasiIso. The single-complex tensor comparison and
  left unitor identify the resulting mixed tensor maps with ordinary scalar
  extension; arrow naturality is proved in Lean.
- `Sheaf.AlgebraicGeometry.KFlatStalkResidueCohomology`: proved the K-flat
  cohomology comparison from the recorded derived-pullback counit and the ordinary
  residue global-sections comparison below. Evaluation on Spec kappa(x) is exact
  because the existing one-point module-evaluation theorem makes it an equivalence.
  The scalar restriction is exact. The short-complex homology comparison and the
  natural isomorphism lifted to complexes complete the proof.
- `Sheaf.AlgebraicGeometry.ResiduePullbackGlobalSections`: states the remaining
  ordinary natural isomorphism of module-sheaf functors, with source and a complete
  natural-language proof. This has no complexes, derived categories, upper bounds,
  or freeness assumptions. It is strictly the residue-section/stalk identification
  part of the original argument, rather than a restatement of the item.

The original TensorPullbackStalk proof import moved to the ordinary comparison
module. Added only proof imports to the existing item; its public imports are
unchanged. Updated the parent proof route and added the three matching DAG nodes.
No existing interfaces, definitions, target declarations, or other groups' modules
were changed. The unit sk-prop-av-cube and its route are unchanged.

All four modules compile together using lcompile.py. The main item and the generic
scalar-extension theorem also compiled independently. No declaration data is
constructed from a new unproved existence statement: the remaining natural
isomorphism is only used to prove a proposition, and no new definition is added.

## Proved and sorry left

Closed the item's original hole:
`AlgebraicGeometry.Scheme.nonempty_stalkFree_residueCohomology_linearEquiv`
(node `lem-sc-stalk-free-residue-cohomology-comparison`). The item has no sorry left.

New proved public theorems:
`CochainComplex.nonempty_kFlat_scalarExtension_homology_linearEquiv`
(node `lem-sc-kflat-scalar-extension-derived-iso`) and
`AlgebraicGeometry.Scheme.nonempty_kFlat_stalk_residueCohomology_linearEquiv`
(node `lem-sc-kflat-stalk-residue-cohomology`).

Added exactly one hole:
`AlgebraicGeometry.Scheme.nonempty_residuePullback_globalSections_iso`
(node `lem-sc-residue-pullback-global-sections`). Its proof is exactly `:= by sorry`
and its docstring gives the singleton germ, scalar transport, tensor-stalk,
inverse-map, and naturality argument.

This is a decomposition, not a sorry-free proof of the target closure: one original
hole closed, one smaller ordinary-sheaf hole added, net zero new-hole progress.
The new comparison theorem has no finiteness or quasi-coherence assumptions. Edge
cases checked mathematically: zero sheaves, zero complexes, unbounded-below models,
infinite free ranks, negative homology degrees, arbitrary residue characteristic,
and a non-flat residue map. The generic ring theorem additionally handles zero
rings and identity scalar maps. An empty scheme has no x, so the residue-point
statement has no extra nonemptiness hypothesis.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk` from the item. It is still
needed through `ResiduePullbackGlobalSections`, so this is an import relocation,
not pruning. No original dependency node or module is globally pruned. In
particular the KFlatResolution, ModuleStalkExact, KFlatStalkCriterion, and
BoundedFlatKFlat modules are used by the main proof and must remain.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt contained only the original unchanged sorry. The DAG's
mathematical plan is sound, but the cited stalk-pullback theorem is stated for
ordinary stalks. It does not itself supply the global-section scalar identification
on Spec kappa(x), nor does the bounded-flat K-flat theorem supply invariance of
scalar extension under an arbitrary derived isomorphism. The delivery fills the
second gap in Lean and isolates only the first gap as an ordinary natural
isomorphism. No statement is disputed.

The local paths literature/stacks-project/cohomology.tex, more-algebra.tex, and
sheaves.tex are not populated on this machine. I read the source on the official
Stacks site: [06YI](https://stacks.math.columbia.edu/tag/06YI),
[06YJ](https://stacks.math.columbia.edu/tag/06YJ),
[064L](https://stacks.math.columbia.edu/tag/064L),
[06Y0](https://stacks.math.columbia.edu/tag/06Y0), and
[0098](https://stacks.math.columbia.edu/tag/0098).

Searches used msearch.py and are recorded in searches.jsonl: LeanSearch returned
Internal Server Error, recorded as unavailable; LeanFinder, Loogle and Mathlib
source grep ran. LeanFinder found localization/homology APIs for the algebraic
comparison, which are used in the proof. Its residue searches found scalar maps
and tilde-stalk APIs, but no natural comparison for arbitrary module sheaves.
Repository searches found the existing one-point evaluation equivalence and mixed
tensor quasi-isomorphism theorem, both used. Blueprint searches for K-flat residue,
residue pullback, and K-flat scalar extension found no duplicate statement.

## New nodes

`lem-sc-kflat-scalar-extension-derived-iso` records the proved generic ring
comparison, using the existing mixed tensor quasi-isomorphism theorem. Sharing
Tags 064L/06Y0 with that dependency does not duplicate it: the existing result
preserves a specified quasi-isomorphism of models; this result starts from an
arbitrary derived isomorphism and constructs homology equivalences through a roof.

`lem-sc-kflat-stalk-residue-cohomology` records the proved K-flat sheaf comparison.
It shares derived-pullback sources 06YI/06YJ but is not a new definition or duplicate
of derivedPullback: it computes the particular vector space defined by
DerivedFiberBetti using exact one-point evaluation and the ordinary comparison.

`lem-sc-residue-pullback-global-sections` records the sole remaining hole. It shares
Tag 0098 with TensorPullbackStalk but identifies different functors: globally
normalized residue-point pullback versus scalar extension of the source stalk,
not target stalk versus extension along a scheme stalkMap. Passing from the
existing stalk theorem to this statement requires the singleton germ and ring
scalar identifications written out in its docstring. It is needed by the proved
cohomology comparison. No change record or forced adaptation is required.

## Second reading by T3

1. Compared the delivered main module with the repository version. The theorem
   signature and all existing declarations are unchanged; only proof imports and
   the proof body changed. The three added declarations are in new modules and
   have matching DAG nodes.
2. Compiled all four sandbox modules with `lcompile.py --all`. They compile
   without errors or warnings. There is no `sorry` in the main theorem or either
   proved comparison theorem; the sole remaining `sorry` is the named ordinary
   natural-isomorphism theorem, with its docstring and node. No forbidden
   declarations or hollow definitions were introduced.
3. Read the three new statements and tested their edge cases conceptually
   (zero complexes and sheaves, arbitrary degrees, non-flat residue maps, and
   infinite free terms). They are strictly smaller than the original target;
   the remaining ordinary comparison is the only unresolved ingredient and is
   not a restatement of the target.
4. Checked the proof routes against the imported declarations and DAG nodes.
   The unit `sk-prop-av-cube` route remains present, and every proof dependency
   used by the Lean terms is recorded. The residue pullback import is relocated
   to the module that states the ordinary comparison; no dependency is claimed
   as pruned.
5. Checked the module interfaces and imports. Public imports are used by the
   statements, proof-only imports are private, and no target or definition was
   changed. The remaining hole is documented as a decomposition with its source.

The second reading made no mathematical changes. It added this review record
and confirmed that the delivery is ready for `deliver3.py`.
