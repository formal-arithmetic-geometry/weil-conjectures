## What changed

Replaced the original sorry in
`AlgebraicGeometry.Etale.isZero_constant_cohomology_one_of_isIntegrallyClosed`
by a reduction to torsor triviality and the torsor-to-derived-cohomology bridge.
The target signature and docstring are unchanged. The two intermediate statements
are in new modules `Sheaf.AlgebraicGeometry.GabberH1TorsorCohomologyBridge` and
`Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial`, imported only for proofs.
Each new module publicly imports Torsor because its statement mentions torsors.

## Proved and sorry left

The one original theorem now has a proof combining two strict intermediate claims.
It still depends on sorryAx through those claims; this is a partial reduction, not
an axiom-free proof of the target.

Two named public theorems remain sorry:

- `AlgebraicGeometry.Etale.isZero_constant_cohomology_one_of_torsors_trivial`, in
  `GabberH1TorsorCohomologyBridge`, node
  `lem-weil-pbc-gabber-h1-torsor-cohomology-bridge`.
- `AlgebraicGeometry.Etale.torsors_trivial_of_finite_etale_sections`, in
  `GabberFiniteConstantTorsorsTrivial`, node
  `lem-weil-pbc-gabber-h1-torsors-trivial`.

Their docstrings give full natural-language arguments and the Stacks sources.

## No longer needed

No original dependency node or module is pruned from the transitive proof route.
The direct imports of `Sheaf.AlgebraicGeometry.FiniteEtaleClosedSubschemeSection`
and `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence` move to
`GabberFiniteConstantTorsorsTrivial`; `WeilConjectures.CategoryTheory.Sites.Torsor`
is now imported by both split modules. All six original dependencies remain
in the intermediate nodes' proof plans or statement dependencies. Geometry dependencies were removed from the
cohomology bridge's plan, and torsor classification from the geometry plan.

## Where the brief, the DAG or earlier work was wrong

The first worker placed new statements in the original module, instead of separate
modules as required by the dispatch brief. Its new nodes assigned the same proof
dependencies to both steps, including geometric dependencies not used by the
cohomological argument, and their docstrings did not spell out the derived/Ext
comparison. The second reading repairs these issues.

The repository contains `isZero_constant_cohomology_iff_subsingleton_H_of_iso`,
which together with upstream `Sheaf.subsingleton_H_one_iff` could close the first
bridge. A scratch compilation reported that its module's olean does not exist in
the last green build. The project contract prohibits recreating a declaration
that is waiting for that build. It therefore remains a documented open bridge.

## New nodes

`lem-weil-pbc-gabber-h1-torsor-cohomology-bridge` is the cohomological comparison,
in `Sheaf.AlgebraicGeometry.GabberH1TorsorCohomologyBridge`.

`lem-weil-pbc-gabber-h1-torsors-trivial` is the geometric section/trivialization,
in `Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial`.

No existing statement or definition changes; no change record is required.

## Second reading by K1

1. Compared the original and delivered target module with diff. The existing
   signature and docstring are byte-for-byte unchanged. New public statements
   live in separate modules; the original module adds only proof imports.
2. Compiled the delivered modules in dependency order using lcompile.py. No
   forbidden declaration, hollow definition, or hidden sorry is present. Only
   the two named split theorems retain sorry. Axiom checks allow the three
   standard axioms and sorryAx from these open steps.
3. Read the upstream torsor classification and representability declarations,
   and checked the proof against [Stacks 09ZB](https://stacks.math.columbia.edu/tag/09ZB)
   and [03AJ](https://stacks.math.columbia.edu/tag/03AJ). These two statements are
   true strict parts of the argument. The empty scheme and trivial group are
   covered: torsors admit a unique empty global section or are trivial locally
   and globally, respectively. No assumption that Z is integral or reduced is made.
   Independent leanfinder, loogle, and grep searches found no direct Mathlib
   replacement. The useful library comparison is awaiting a compiled artifact.
4. The unit sk-thm-p1 and its realized steps were read and are unchanged. The
   torsor/finite-etale/section route is retained. Proof imports are private to the
   original module; geometric imports reside in the geometric split module.
5. Checked the nodes' Lean signatures and module paths, source, proof steps and
   union of proof dependencies. Corrected mismatched dependency assignments;
   the target's two-step proof exactly matches its node.

Second reading changed the split-module layout, completed proof docstrings,
corrected DAG dependencies and statements, and repaired this report. The
original target proof needed no change.
