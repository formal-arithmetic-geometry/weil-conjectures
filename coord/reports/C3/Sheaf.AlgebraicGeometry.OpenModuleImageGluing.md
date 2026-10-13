## What changed

Replaced the whole-proof hole of
`AlgebraicGeometry.schemeOpenModuleImage_isPullback` with a compiling
pullback-cone construction, preserving its signature, visibility and original
docstrings. Its square commutes by the existing
`schemeOpenModuleImage_unit_restriction` identity. The existence theorem gives
a cone lift and its two factorization equations; the uniqueness theorem proves
the final universal-property clause. `PullbackCone.IsLimit.mk` and
`IsPullback.of_isLimit'` assemble these components.

Added proof-only imports of `Sheaf.AlgebraicGeometry.OpenModuleImageAmalgamation`
and `Sheaf.AlgebraicGeometry.OpenModuleImageSeparated`. Each is a new module with one public intermediate theorem, a source,
a complete proof in words and its matching node. The second reading proved
the uniqueness theorem directly; only existence retains an exact `by sorry` body. The target node's route now
records this decomposition.

All three modules compile together with the prescribed launcher. Mathlib
searches found the sectionwise `TopCat.Sheaf.isLimitPullbackCone` ingredient,
but no theorem directly identifying the transported image diagram. LeanSearch
was unavailable; LeanFinder, Loogle and grep returned usable ingredients.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.schemeOpenModuleImage_isPullback`
(node `lem-pc-open-module-image-gluing`). Its proof still depends on `sorryAx`
through the existence theorem below, so this is a decomposition, not a completed
sorry-free proof of the item.

The second reading also closed the first worker's new uniqueness hole:
`AlgebraicGeometry.schemeOpenModuleImage_pullback_unique`, in
`Sheaf.AlgebraicGeometry.OpenModuleImageSeparated`, node
`lem-pc-open-module-image-gluing-uniqueness`. Its axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.

One lower hole is added and remains:
`AlgebraicGeometry.schemeOpenModuleImage_pullback_exists`, in
`Sheaf.AlgebraicGeometry.OpenModuleImageAmalgamation`, node
`lem-pc-open-module-image-gluing-existence`. Existence is strictly part of the
universal property: it assumes compatibility and concludes existence of a lift;
it does not assert commutativity or uniqueness. The upper proof proves
commutativity and uses the now-proved uniqueness theorem separately.
Relative to the repository, one original hole is closed and one lower hole added,
net zero before the pinned closure ledger; the uniqueness hole was only in the
worker's sandbox and is not counted as a repository hole closed.

No definitions or existing statements were changed. The local cone lift is
uniquely determined by its two factorization equations, using the proved
uniqueness theorem; it is not an arbitrary witness of a holed existence theorem.

Empty X and an empty test open have unique sections. If U is empty, hcover
forces V to be top. If U=V, hcover forces both to be top. In all cases the
same cover axiom applies, with no injectivity hypothesis.

## No longer needed

No imports or modules pruned. The original direct proof dependency
`def-pc-derived-open-restriction-maps` is no longer a direct dependency of the
upper theorem; its constructions remain required through the data module and
the two intermediate statements. It is not globally pruned.

## Where the brief, the DAG or earlier work was wrong

The first dry run rejected the absent `## Earlier second reading (a previous round; superseded)` section.
The dispatcher brief explicitly reserves that section for the independent
second worker and forbids this worker from writing it. No second-reading
section has been fabricated. The final dry run recognizes this reservation and passes without that section.

A transient SSH fetch timeout resolved on retry. The final dry run printed
OK: compilation and preflight passed except for the independent second reading,
which the second reader writes. Nothing was pushed.

## New nodes

`lem-pc-open-module-image-gluing-existence` records compatible-map amalgamation
on a two-open cover, in the new OpenModuleImageAmalgamation module. Its
sectionwise proof identifies the transported units and overlap maps, glues
sections, and uses uniqueness to prove naturality and linearity.

`lem-pc-open-module-image-gluing-uniqueness` records joint injectivity on
morphism sets of the two units, in the new OpenModuleImageSeparated module.
Its completed Lean proof cancels the unit comparison isomorphisms and applies
Mathlib sheaf separatedness on the intersected cover. No change record is needed.

## Second reading by C3

1. **Unchanged interface: pass.** Compared OpenModuleImageGluing.lean with
   the repository using diff. Its existing theorem signature, universes,
   cover hypothesis, arbitrary module sheaf, four square arrows, visibility,
   and docstring are byte-for-byte unchanged. Only two plain proof imports
   and the proof body changed. The other two modules are new; there are no
   definition changes or forced adaptations and no change record is needed.
2. **Proof and axioms: pass with the reported remaining hole.** Compiled
   all three modules in import order through lcompile.py. The upper proof
   establishes commutativity using schemeOpenModuleImage_unit_restriction,
   supplies the cone lift with its two equations, and proves uniqueness;
   PullbackCone.IsLimit.mk gives the claimed pullback. Closed the uniqueness
   theorem using TopCat.Sheaf.eq_of_locally_eq₂. Axiom probes on scratch copies
   show standard axioms only for uniqueness, and standard axioms plus sorryAx
   for existence and the upper theorem. Only the named existence theorem has
   sorry; no forbidden declaration or hollow definition is introduced.
3. **Split statements: pass.** Read Stacks Tags
   [01EB](https://stacks.math.columbia.edu/tag/01EB), first sentence of the
   proof, and [08BV](https://stacks.math.columbia.edu/tag/08BV), sectionwise
   sequence. Their sheaf-condition argument needs no injectivity for the
   kernel/gluing assertion. Both new statements quantify arbitrary Z and M;
   existence uses precisely the overlap compatibility, uniqueness uses precisely
   the two equal restrictions. The existence docstring explains transport,
   section gluing, naturality and linearity; its node matches the Lean.
   Tested empty X, empty T, U empty, and U=V as described above. Neither
   statement restates the whole pullback. Searched with the launcher's
   LeanFinder query about equality of sheaf morphisms on two covering opens,
   Loogle on IsSheaf/hom_ext, and grep on eq_of_locally_eq₂/overFunctor maps;
   also searched lean/Sheaf and the upstream Modules sources. Found Mathlib
   separatedness, used it to close uniqueness; found no already-stated
   transported compatible-map amalgamation theorem.
4. **Shortest route and pruning: pass.** The upper construction already uses
   the standard pullback universal property. Kept it. Added only a plain
   proof import of Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing in
   the uniqueness module. Each retained import supplies a statement or proof
   ingredient. No module is pruned. The old direct proof dependency
   def-pc-derived-open-restriction-maps is accounted for under No longer needed;
   it remains indirectly needed by the data construction and existence lemma.
   Opened dag/units/sk-thm-picard-duality.json: its realized.statement and its
   sole realized.steps entry are empty. No realized unit node or route is bypassed.
5. **DAG agreement: pass after repairs.** The upper node's two steps match
   commutativity and the IsLimit construction, with the two helper nodes cited.
   Rewrote the uniqueness node's proof and proof_deps to match its completed
   cancellation and separatedness proof; it no longer directly uses the
   derived nested-open comparison. Checked new Lean records against the exact
   signatures. Repaired both new nodes' statements to self-contained TeX and
   their source places to named Stacks labels. Filled blueprint.same_as and
   inherited the upper node's finite-duality blueprint ancestor and route,
   after searching imported blueprint gluing nodes; no matching blueprint
   statement was found.

Changes by the second reader: proved schemeOpenModuleImage_pullback_unique,
added its proof-only Mathlib import, corrected the two new nodes' metadata and
uniqueness proof route, and corrected the hole accounting in this report.
