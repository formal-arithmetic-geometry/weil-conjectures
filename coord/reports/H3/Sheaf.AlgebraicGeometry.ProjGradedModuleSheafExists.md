## What changed

Replaced the sorry in `AlgebraicGeometry.Proj.gradedModuleSheaf_exists` by a complete Lean
reduction, keeping its statement unchanged. The proof extracts chart submodules, ambient and
homogeneous ring maps, additive restriction maps, fraction formulas, semilinearity, identity and
composition from `LocalizedModule.gradedModuleAwayRestriction`. `standardOpenProperties`
converts inclusions into homogeneous divisibility relations. Reverse restrictions are explicitly
proved to be two-sided inverses for equal charts. The ambient ring maps provide the canonical
coefficient maps needed for basis extension.

Added three modules: `ProjGradedModuleSheafExtension` for basis extension, uniqueness and
quasi-coherence; `ProjGradedModuleSheafStalks` for the prime-localized stalks; and
`ProjGradedModuleSheafGlobalSections` for the degree-zero global-section maps. The
global-section theorem is fully proved: equal-degree fractions m/1 are compatible, sheaf unique
gluing gives gamma, the same argument gives the coefficient ring map eta, and chartwise equality
proves additivity, the ring laws and scalar compatibility. The main proof separately proves
restriction compatibility by presheaf composition, and global uniqueness using the standard-open
cover and sheaf separatedness.

All four modules compile together through lcompile.py. The main proof requires 800000 heartbeats
for elaboration of its dependent witnesses and compiles within the single-file wall-clock limit.
Every new module has explicit universes and no auto-bound variables. Empty Proj, nilpotent
denominators, zero modules, arbitrary fraction representations and denominator exponent zero
were checked in the mathematical arguments.

Searches: LeanFinder returned structure-sheaf and ring-stalk results, not the general module
statement; Loogle returned homogeneous ring localization results; Mathlib grep for
gradedModuleSheaf, gradedModuleAwayRestriction and degreeZeroFractions found no hits. LeanSearch
returned HTTP Internal Server Error and is recorded as unavailable. Blueprint searches for
graded module, 01M7 and 01MB found no blueprint statement to reuse. The existing graded-module
chart-data and tilde nodes for projective lines are special cases and do not supply this general
Proj construction. No unit-level route is bypassed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Proj.gradedModuleSheaf_exists` (node
`lem-weil-pbc-proj-graded-module-sheaf-exists`) by decomposition, not an unconditional
sorry-free proof. There are no sorries in the item's module.

Fully proved `AlgebraicGeometry.Proj.gradedModuleSheaf_globalSections` (node
`lem-weil-pbc-proj-graded-module-sheaf-global-sections`); this adds no hole.

Two new holes remain, each exactly a public theorem with proof `:= by sorry`:

- `AlgebraicGeometry.Proj.gradedModuleSheaf_extension`
  (`lem-weil-pbc-proj-graded-module-sheaf-extension`): steps 3--6, construction and uniqueness
  of the basis extension and its quasi-coherence, with fixed chart data as hypotheses.
- `AlgebraicGeometry.Proj.gradedModuleSheaf_stalks`
  (`lem-weil-pbc-proj-graded-module-sheaf-stalks`): step 7, identification of stalks for
  a supplied sheaf with the specified charts; it neither constructs that sheaf nor
  asserts quasi-coherence or global sections.

The already stated dependencies `gradedModuleAwayRestriction` and `standardOpenProperties`
remain dependencies; their holes were not worked on or duplicated in this delivery.

## No longer needed

Removed the item's direct proof imports `Sheaf.RingTheory.CoverModuleExact`,
`Sheaf.Topology.SheafOfModulesFromBasis`, and `Sheaf.Topology.PresheafModuleStalkFunctor`. The
first two remain needed by the extension or stalk subproblems and are imported there. The last
is still reached through the basis-extension module. Thus no entire dependency node or module is
claimed pruned from the targets' closure. Public imports of the existing module were preserved.
All nine old proof dependencies remain needed either directly or by the new subproblems; the
parent node now records its direct dependencies on those subproblems instead. The following old
direct proof dependencies move to the extension or stalk argument:
`lem-weil-pbc-proj-structure-sheaf-standard-sections`, `lem-weil-pbc-cover-module-exact`,
`lem-weil-pbc-sheaf-of-modules-from-basis`, `lem-weil-pbc-proj-basic-open-intersection`,
`lem-weil-pbc-spec-module-tilde-sections`, `pqf-def-coherent`, and `def-weil-pbc-module-stalk`.
None is claimed globally pruned. The second reader removed the stalk module's redundant proof
imports of `Sheaf.Algebra.Module.GradedModuleAwayRestriction` and
`Sheaf.Topology.SheafOfModulesFromBasis`: its fraction map needs only the supplied chart
restriction formula and Mathlib's basis germ lemmas. Its node now cites
`lem-weil-pbc-stalk-germs-on-basis` directly. Both removed imports remain needed by the
extension module, so this does not prune them from the targets' import closure. The
global-section module also removes its proof import of ProjStandardOpenProperties, using
Mathlib's proved positive homogeneous affine cover instead. The new stalk and global-section
modules import `Sheaf.Paper.DerivedHomMayerVietoris` publicly for `moduleRings`, replacing the
broader public import of `Coherent`; neither statement mentions quasi-coherence.

## Where the brief, the DAG or earlier work was wrong

The DAG's stalk injectivity argument uses c^m y = 0 from c y = 0, which does not follow when m =
0. The new stalk lemma's complete proof sketch uses the fact that the new denominator f*c
annihilates the numerator in that case, so its fraction with denominator one is zero after
localization. Also an annihilator obtained in the ordinary prime localization need not be
homogeneous; internality and homogeneity of the numerator allow a homogeneous component outside
the homogeneous prime to be selected. Neither issue changes the theorem.

The Stacks source is absent at the repository's literature path on this machine, but its text
was available read-only at `/home/ubuntu/c1-stacks-review/constructions.tex`. Read the
construction of the basis presheaf, its stalks, finite-cover sheaf condition, Definition
structure-sheaf, Lemma proj-sheaves and Lemma proj-scheme there. The node's canonical literature
citation is preserved. No statement or definition was changed.

## New nodes

`lem-weil-pbc-proj-graded-module-sheaf-extension` states the extension and quasi-coherence of
the specific chart system, corresponding to steps 3--6. It requires canonical ambient ring maps;
arbitrary semilinear coefficient maps alone are insufficient to identify O_X.

`lem-weil-pbc-proj-graded-module-sheaf-stalks` states the stalk computation for any sheaf
already supplied with the prescribed scalar-compatible and restriction-compatible charts. It
corresponds only to step 7 and includes the germ formula for every representative.

`lem-weil-pbc-proj-graded-module-sheaf-global-sections` states and proves the ring map eta and
additive map gamma with chart restrictions and scalar compatibility, step 8. The final
compatibility and uniqueness clauses are proved in the item's module.

No change records are needed: every existing signature and definition is unchanged.

## Second reading by H3

1. I compared the delivered item module with the repository version. The declaration
`AlgebraicGeometry.Proj.gradedModuleSheaf_exists` has the same statement byte for byte; the
proof only adds imports for the three split modules and the unique-gluing theorem. The existing
local scalar-action instance and all notation also remain unchanged. The three new declarations
are separate intermediate statements and do not alter an existing declaration.

2. I compiled all four delivered modules with `lcompile.py --all`; compilation is clean. The
item has no `sorry`. The extension and stalk declarations are the two explicitly named split-off
holes, each with a source, proof docstring, and matching node. There are no axioms, unsafe
declarations, hollow definitions, or forbidden constructs. The main proof uses the existing
graded restriction theorem, standard-open properties, and the three new intermediate theorems.
The extension sketch uses basis extension and Mathlib's tilde; the stalk sketch uses the
existing Mathlib basis-germ statements and structure-sheaf germ formula. The global-section
theorem has no local hole. After the Mathlib cover replacement its #print axioms also contains
no sorryAx; the other three declarations contain sorryAx only through the explicitly reported
open statements, and their other axioms are propext, Classical.choice, and Quot.sound. The
delivery closes one original hole and adds two, so the raw net is -1; this is a decomposition.

3. I searched the repository, Mathlib, LeanFinder, Loogle, and the recorded search log for an
existing graded-module-on-Proj theorem. The searches found only ring structure and stalk
declarations, so the three split statements are needed. The extension node matches the
basis-extension and quasi-coherence argument; the stalk node matches the colimit calculation and
germ formula; the global-section node matches the gluing construction. The extension assumes
already supplied chart data and proves only extension, uniqueness, and quasi-coherence; the
stalk lemma assumes an existing sheaf and chart identifications and proves only the stalk
comparison. The global-section lemma assumes the chart sheaf and constructs only eta and gamma.
Thus none restates the parent item. Testing S=k with grading in degree zero makes Proj empty and
the chart modules zero; M=0 gives zero stalk and section modules. A homogeneous nilpotent chart
denominator also gives a zero localized module. For a nonzero chart and exponent zero,
restriction of m/1 is m/1; for a zero germ y/1 the new chart denominator annihilates y. The
hypotheses impose neither finite generation nor generation of S in degree one, and the sketches
and gluing proof use neither assumption.

4. I read the source passage in `constructions.tex` (the presheaf construction, stalk
calculation, cover-module exactness, Lemma 01M7, and Lemma 01MB). The proof sketches in the
nodes preserve the unit-level route: standard-open basis and restriction maps, basis sheaf
extension, stalks, then global sections. Edge cases mentioned by the source and report (empty
Proj, nilpotent denominators, zero modules, and exponent zero) are accounted for; the stalk
sketch uses the new denominator itself as an annihilator in the exponent-zero case. The
implemented global-section proof uses Mathlib's proved affineOpenCover for its cover, preserving
these same charts. The updated parent `proof_deps` records exactly the declarations used by its
Lean proof; imports removed from the old direct proof are no longer needed there.

5. I checked every node's Lean record against its declaration and verified that the parent
node's proof steps and dependencies agree with the implemented reduction. No unit statement or
realized route is bypassed. I expanded the extension proof sketch in both its docstring and
node: the chart coefficient maps are forced by ordinary localization, equalizer maps agree with
the principal-localization comparisons, and for an arbitrary principal generator a/f^n the
positive homogeneous denominator f*a gives the required principal open. I expanded the stalk
sketch to justify well-definedness on representatives, closure under scalar action, homogeneous
annihilators, exponent-zero injectivity, and the formula for arbitrary representatives. I
replaced its basis-extension dependency by the existing Mathlib basis-germ leaf and removed the
two redundant proof imports. I narrowed the new stalk and global-section public imports to the
module defining `moduleRings`. I also replaced the global-section proof's use of the still-open
standardOpenProperties by Mathlib's Proj.affineOpenCover and opensRange_awayι
(Basic.lean:336--348 and :196), removing its private proof import and direct DAG dependency.
This is a shorter cover argument for the same positive homogeneous chart family. No theorem
signature or definition changed.
