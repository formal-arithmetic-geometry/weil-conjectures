## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.depth_two_hartogs_algebra_comparison`
with a complete Lean reduction to the general Hartogs restriction theorem in the new
module `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction`.
The original statement is unchanged. The second reader removed the unused public imports
`Mathlib.AlgebraicGeometry.Morphisms.Finite` and
`Mathlib.AlgebraicGeometry.Morphisms.Etale`. Added two proof-only imports:
that module and `Sheaf.Algebra.Homology.ModuleStalkFunctor`.

The direct-image algebra module identification is proved by definitional equality.
`pushforwardComp` puts it in the essential image of the open pushforward, whose full
faithfulness makes its restriction unit invertible. Composing the Hartogs unit, the
pushed-forward supplied isomorphism, and the inverse algebra unit proves the module
comparison. The private `algebra_stalk_linearEquiv` is fully proved: use preservation
of filtered colimits for the additive comparison, check scalar compatibility on
common-neighborhood germs, then upgrade by bijectivity. Apply the existing module
stalk functor and compose linear equivalences for the second conclusion.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.depth_two_hartogs_algebra_comparison`
(node `lem-sbc-depth-two-hartogs-algebra-comparison`). No sorry remains in the item.
The two private helpers are fully proved/constructed without sorry.

Added one hole:
`AlgebraicGeometry.Scheme.isIso_restrictAdjunction_unit_of_depth_two`
(node `lem-sbc-depth-two-hartogs-restriction`). This is a decomposition, not a
sorry-free proof: one upper hole closed, one lower hole added, net zero. The new
statement concerns only a coherent module and an open complement; it has no algebra,
no morphism f, no supplied restriction isomorphism and no ring-valued stalk conclusion.
All categorical glue and scalar-compatible stalk comparisons are proved in the item.

Checked the new statement against Stacks Tag 0E9I and its proof (Tags 0AVM, 0AVN,
05AM). It includes zero modules and empty schemes; U = top makes the unit invertible
without a depth condition, and U empty forces N = 0. There is no extra global
quasi-compactness or finiteness/etaleness condition on f.

## No longer needed

The old node had no proof dependencies, so no old dependency node is omitted.
Removed the unused imports `Mathlib.AlgebraicGeometry.Morphisms.Finite` and
`Mathlib.AlgebraicGeometry.Morphisms.Etale`: neither the statement nor the proof uses
finite or etale morphisms. No existing Sheaf node or module is pruned.
No finite-etale extension, coherent-extension existence, normalization, purity or
base-ring depth theorem is imported by this proof. The only new unfinished dependency
is the general Hartogs restriction theorem; the module stalk functor is already proved.

## Where the brief, the DAG or earlier work was wrong

The item's old proof step combined Hartogs, direct-image functoriality and the
scalar-compatible algebra stalk comparison without any named dependencies. The node
now records the actual reduction. The ancestor script returns None for this newly
created item's chain because older created.item entries contain module names; the
new node instead follows the recorded blueprint ancestry of the pushforward-coherence
node to `sbc-thm-spreading-finite-etale-galois`. The unit route is unchanged.

Mathlib searches found no general Hartogs theorem. LeanSearch was unavailable
(HTTP internal server error), LeanFinder returned other affine restriction facts,
and grep found no Hartogs/depth restriction theorem. Stacks pages were read directly
at https://stacks.math.columbia.edu/tag/0E9I and the linked proof tags because this
machine has no literature/stacks-project directory.

## New nodes

`lem-sbc-depth-two-hartogs-restriction` states the invertibility of the restriction
adjunction's canonical unit for a quasi-coherent module with finite affine sections
and depth-two finite boundary stalks. Its sole sorry is in the corresponding new
module `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction`. This isolates
the classical Hartogs input and leaves the actual algebra and stalk comparison proved.
No statement or definition changes or forced adaptations are needed. Public import
pruning is recorded in
`coord/changes/depth_two_hartogs_algebra_comparison_imports.md`.

## Second reading by M2

1. **Unchanged interface: pass.** Read the repository and sandbox modules in full and
   compared them with `diff -u`. Extracted the existing theorem signature up to `:= by`
   and checked byte-for-byte equality. No existing definition or statement changed,
   and the public import pruning has its required change record. The existing node
   changes only `proof`,
   `proof_deps` and `proof_origin`. The two added helpers are private; the direct-image
   isomorphism is real data (`Iso.refl`), not a witness selected from an open theorem.

2. **Proof and axioms: pass, conditional on the listed Hartogs hole.** Both delivered
   modules compiled in import order with `lcompile.py`, without errors or warnings.
   The item contains no sorry; the new restriction theorem has the sole named
   `:= by sorry`. No forbidden declaration or attribute occurs. A scratch copy with
   `#print axioms` checks both private helpers, the item theorem and the new theorem.
   The helpers use only standard axioms; the two Hartogs theorems additionally use
   `sorryAx`, exactly as reported. In particular the scalar comparison is proved on
   common-neighborhood germs, not assumed from an additive equivalence.

3. **New statement: pass as a strictly smaller classical input.** Read
   [Stacks Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I), and its proof inputs
   [0AVM](https://stacks.math.columbia.edu/tag/0AVM),
   [0AVN](https://stacks.math.columbia.edu/tag/0AVN) and
   [05AM](https://stacks.math.columbia.edu/tag/05AM).
   Quasi-coherence and finite affine sections on a locally Noetherian scheme give
   coherence. The boundary condition is on the finite module stalk, not on the base
   ring. On Noetherian affine opens the open immersion is quasi-compact and separated,
   so the direct image is quasi-coherent and 0AVN applies; 05AM turns exclusion of
   weak associated points into exclusion of associated points. The unit's section map
   is restriction, as checked against `Modules.restrictAdjunction_unit_app_app`.
   The docstring supplies the full natural-language reduction. Tested the zero module,
   empty scheme, U = top and U empty. For the last case a nonzero coherent module has
   an associated point of depth zero, so the hypotheses force N = 0. The affine plane
   with its origin removed gives the familiar nontrivial example; a punctured affine
   line fails the required depth condition. This new statement has neither an algebra
   pushforward nor a supplied comparison nor a scalar-compatible stalk conclusion.
   It therefore isolates a proper part of the original argument, rather than renaming
   it. Independent LeanFinder search for "restriction adjunction unit coherent sheaf
   depth two isomorphism" returned categorical restriction facts only. Loogle query
   "SheafOfModules, IsIso" could not resolve the unqualified identifier `IsIso`;
   it is not evidence of absence. Searches of Mathlib, upstream WeilConjectures and
   lean/Sheaf for Hartogs, boundary depth and restriction found only stronger special
   cases (integral regular/UFD schemes) or users of this item. No replacement theorem
   was found. Closing this general Hartogs input requires substantial commutative
   algebra and sheaf formalization, beyond a few-minute repair.

4. **Route and pruning: pass after import repair.** Checked the composition direction
   of `Modules.pushforwardComp`, full faithfulness of open pushforward in Mathlib's
   Modules/Sheaf, and `Adjunction.isIso_unit_app_of_iso`. The isomorphism assembled
   from the unit on N, the pushed restriction isomorphism, and the inverse unit on B
   has exactly the required endpoints. The module stalk functor is already proved,
   and the ring-to-additive colimit comparison uses Mathlib's filtered-colimit
   preservation instances. Both new proof dependencies are plain imports. Removed
   unused finite and etale public imports and recompiled successfully; retained the
   imports needed by signatures. The old `proof_deps` was empty, so the report omits
   no obsolete dependency. Read `dag/units/sk-prop-input-spreading.json`: the
   depth-two extension route is retained and its `realized` record is unchanged.

5. **DAG agreement: pass.** The item node records the Hartogs unit, categorical
   comparison, proved germ calculation and module stalk functor in the order used
   by Lean. Its dependencies are exactly the new restriction node and the existing
   `def-pc-module-stalk-functor`. The new node has the required source, statement
   dependencies, search records, creation/blueprint ancestry, chapter, unit and Lean
   signature. Its signature agrees verbatim with its module; its statement describes
   the actual unit isomorphism with all hypotheses. It records a sourced proof plan,
   not a claimed Lean proof of the still-open classical theorem.

**Changed in the second reading:** removed the two unused finite/etale imports,
corrected the report's claim that all public imports were retained, and added
`coord/changes/depth_two_hartogs_algebra_comparison_imports.md`. The first dry run
required this record because public import removal is an interface change. Read the
sole direct importer, which publicly imports Finite and Etale itself, and compiled
its unchanged source against the delivered modules; it needs no adaptation. No proof, signature,
definition or node was rewritten. One original hole closed and one strictly simpler
hole added: decomposition, net zero; no sorry-free target is claimed.
