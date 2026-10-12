## What changed

Completed `AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap_naturality` in
`Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`. Unfold the adjoint-defined
map and apply `Adjunction.homEquiv_naturality_right_square`. The remaining square is
naturality of the composite natural transformation: whisker the top-arrow adjunction
unit by `pushforward f`, then compose with the whiskered pushforward composition,
congruence, and inverse composition comparisons. This proves the equality without
sectionwise calculations or additional intermediate theorems.

The whiskering operations are already available through the existing imports;
no import was added. All existing signatures, definitions, public imports, and
docstrings are unchanged. No new nodes or interface changes.

The module compiles locally through `lcompile.py` without warnings. Searches used
LeanFinder for adjunction naturality, Loogle for
`CategoryTheory.Adjunction.homEquiv_naturality_right_square`, and grep/rg for
module base change and restriction comparisons in Mathlib and both project roots.
The proof follows the naturality argument already recorded in the declaration's
docstring; the four-step plan of the remaining restriction theorem is unchanged.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap_naturality`.

One original hole remains, untouched:
`AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap_open_restriction`
(blueprint: `lem-weil-pbc-module-base-change-map-open-restriction`). Its named theorem,
source, complete proof in words, and DAG node remain present. No holes were added,
no holes were split off, and no private helper or definition contains a hole.

## No longer needed

Removed the redundant proof-only direct import
`Sheaf.AlgebraicGeometry.TensorPullback`. The same module remains available through
`public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`; this is removal of
one redundant import edge, not pruning of that module from the targets' closure.
No DAG proof dependency or module is claimed unnecessary for the still-unproved
open-restriction theorem.

## Where the brief, the DAG or earlier work was wrong

The planned use of `moduleBaseChangeMap_pasting` cannot currently be implemented by
importing its module here: `Sheaf.AlgebraicGeometry.ModuleBaseChangeMapPasting`
publicly imports this item's module, where `moduleBaseChangeMap` is defined. The
project's `tools/import_direction.py may` confirms that adding the reverse import
would close a cycle. The pasting theorem has a correctly typed statement, but its
current placement prevents this item's restriction proof from using it directly.
No circular import was added. A future full restriction proof needs a shared lower
module for the base-change definition and appropriate dependency restructuring, or
a direct verification of the mate-pasting identity. This delivery completes the
independent naturality clause and leaves restriction explicit rather than moving
its whole statement to a new hole.

The open-immersion restriction dependencies are Mathlib leaves, not modules named
`Sheaf.AlgebraicGeometry.OpenImmersionModulePullbackRestriction` and
`Sheaf.AlgebraicGeometry.ModuleRestrictionOpenImmersionColimits`: their recorded
matches use `restrictFunctor`, `restrictAdjunction`,
`restrictFunctorIsoPullback`, and `Adjunction.unit_leftAdjointUniq_hom_app`.
For the project's tensor-formula pullback, the relevant comparison is instead the
uniqueness isomorphism between `restrictAdjunction` and the chosen
`exists_tensorPullbackAdjunction`; its unit compatibility is the same Mathlib
uniqueness theorem. This does not dispute any mathematical statement.


## Second reading by Q3

1. Compared the sole delivered module with the repository using `diff -u`. Every
   existing signature, visibility, docstring and definition body is byte for byte
   unchanged. Only the naturality proof and redundant proof imports differ. No
   change record is needed; no target or other module was changed. Verdict: pass.
2. Compiled the delivered module locally with `lcompile.py`. Also compiled a scratch
   copy with `#print axioms` for all three declarations. `moduleBaseChangeMap` and
   `moduleBaseChangeMap_naturality` use only `propext`, `Classical.choice`, and
   `Quot.sound`; the unchanged `moduleBaseChangeMap_open_restriction` additionally
   uses `sorryAx`. The only textual hole is the entire proof of that named original
   theorem. No prohibited declaration or hollow definition was introduced. The
   existing adjunction choice is pinned by its sectionwise unit formula (which
   determines the Hom equivalence), rather than an arbitrary existence witness.
   Verdict: pass, with the reported original restriction hole still open.
3. No statement was split off and no new declaration or node was introduced.
   Reviewed the remaining statement and its full-inverse-image assumptions: the
   identity and empty-open cases do not expose an omitted condition. Searched
   Mathlib's module-sheaf file and project/upstream sources under base-change,
   restriction and adjunction-square terminology; no ready-made replacement for
   the remaining restriction theorem was found. Verdict: pass.
4. Read Mathlib's `Adjunction.homEquiv_naturality_right_square`: it transfers exactly
   the square of the pushed-forward unit and comparison transformations to the
   requested pullback square. The final natural-transformation naturality supplies
   that premise directly. This is a short general categorical argument, without
   new holes. Tested removal of the added Whiskering import: the scratch proof
   compiled, so removed it. TensorPullback is publicly provided by
   TensorPullbackAdjunction, so its direct proof import is redundant too. No old
   proof dependency is removed: the four-step restriction route is still open.
   Read `dag/units/sk-thm-p1.json`; its `realized` route is unchanged and no unit
   step is bypassed. Verdict: pass after import cleanup.
5. Read the item's node, its source, proof steps, `proof_deps`, `proof_origin` and
   Lean record. The node records the still-open restriction theorem and its same
   four-step plan; its statement also includes the naturality clause now proved
   by the docstring's adjunction argument. No new nodes need records, and no
   dependencies of the remaining proof plan have been dropped. Confirmed the
   pasting module imports this module, so the reported import-cycle obstacle is
   real. Verdict: pass.

Second reading changed only the redundant Whiskering import and the corresponding
report text. Closed one original hole, added zero holes; no decomposition and no
module pruned from the targets' closure.
