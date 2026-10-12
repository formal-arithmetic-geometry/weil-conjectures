## What changed

Replaced the sorry in
`AlgebraicGeometry.supported_derived_generated_perfect_core` by a compiling reduction
using `supported_compact_detector_model`, the existing
`CategoryTheory.compactGenerators_buildObjects`, and the newly proved
`CategoryTheory.generator_tower_normalize`. Every existing signature and visibility
is preserved. All new imports in the item are proof-only.

The main proof applies the compact-generator theorem to the singleton indexed by
`ULift Unit`, removes its redundant singleton-label maps, normalizes its actual
sequence and triangle witnesses, and packages the resulting objects with their
quasi-coherence proofs. The universe-u Hom model is necessary because the original
localization morphism universe w is arbitrary whereas the summand indices must
remain in universe u.

`GeneratorTowerNormalize.lean` proves the full formal glue. It constructs the
cofan after prepending zero using the old coproduct point, proves its universal
property, checks identity-minus-transition equations, rotates the cone triangles,
uses shift-addition and exact-functor comparison isomorphisms to identify the
summands, and transports the telescope to Q. Its private helpers are fully proved
noncomputable constructions of colimit witnesses, with no holes.

Compiled the three delivered modules in import order with lcompile.py, without
warnings. Read duality.tex, lemma-when-sheafy, proof of (3), and derived.tex,
lemma-write-as-colimit, from the local literature mirror. Tested the smallness
instance in a scratch compile: after installing
`SheafOfModules.isGrothendieckAbelian`, the proved source instance
`DerivedCategory.locallySmall` supplies local u-smallness for arbitrary w.
The remaining model lemma can use this instead of redoing the quotient argument.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.supported_derived_generated_perfect_core`
(node `lem-sc-supported-derived-generated-perfect-core`). No sorry remains in the item.

Proved the new theorem `CategoryTheory.generator_tower_normalize`
(node `lem-sc-generator-tower-normalize`) completely. This proves rotation, mapping,
zero-prepending and reindexing for any already supplied generator tower; it assumes
neither compactness nor generation. Its zero-first-transition and successor
transition branches compile separately, and its coproduct proof works with the
zero summand and with empty families of generator shifts.

Added one whole-proof public sorry:
`AlgebraicGeometry.supported_compact_detector_model`
(node `lem-sc-supported-compact-detector-model`). Its complete proof plan constructs
ShrinkHoms of the supported full subcategory, transfers its structures, and proves
compactness and singleton generation. It asserts no sequence or telescope. Edge
cases checked: V empty, V the whole scheme, E zero, Q zero, and empty coproducts.
When E is zero, the assumed detection makes the supported category a zero category,
so the singleton still generates. No quasi-compactness assumption is needed: the
category preparation only uses the supplied detector and triangulated closure.

The existing `CategoryTheory.compactGenerators_buildObjects` is used as stated;
its existing sorry is not changed or counted as a newly added hole.

Hole accounting: one old hole closed, one new hole added. This is a decomposition
with net zero holes, plus a fully proved new normalization theorem, not a claim
that the original theorem is sorry-free transitively.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums`.
- `Sheaf.Topology.StalkDirectSums`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
- `Mathlib.CategoryTheory.EssentiallySmall`.
- `Sheaf.CategoryTheory.WeakTriangulatedGenerator`.

The ambient sums, stalk sums, quasi-coherent sums, K-injective resolutions and
weak-generator definition are still needed by the preparation lemma, and are
recorded below that node. They have been moved out of the item's direct proof;
none of those mathematical nodes is claimed globally pruned. The K-injective
morphism proof can be replaced by the source library's already proved local-smallness
instance, as verified in scratch. EssentialSmall's ShrinkHoms construction remains
the intended model. No unit statement or unit proof step was bypassed; the inspected
unit record has no realized statement or step node identifying this below-unit glue.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original DAG's quasi-coherent coproduct step
needs the ambient closure interface `schemeDerivedQCohClosedUnderCoproducts`
(node `lem-pc-derived-qcoh-closed-coproducts`), in addition to mere existence of
coproducts in D_QCoh; the preparation node now names it explicitly.

The smallness argument already has a proved source-library instance and need not
be reconstructed from chain maps. The generic telescope glue can also be proved
without selecting a new coproduct point: using the old point and proving its
new cofan universal property makes the identity-minus-shift compatibility literal.

The ancestor helper returned None because the created.item field is a module name;
new nodes inherit the explicit existing blueprint ancestor `lem-sc-finite-duality`
and prepend the core node to its recorded via chain. No blueprint field of the
existing item was changed.

A transient /tmp inode exhaustion interrupted writing a heredoc. Setting TMPDIR
to the sandbox scratchpad resolved it; no other worker's files were removed.

## New nodes

`lem-sc-supported-compact-detector-model`, module
`Sheaf.AlgebraicGeometry.SupportedCompactDetectorModel`, is the single remaining
preparation obligation: construct a supported small-Hom triangulated category with
its compact singleton detector, its coproduct-preserving exact inclusion, and the
lifts of E and Q. Its conclusion has no tower or telescope.

`lem-sc-generator-tower-normalize`, module
`Sheaf.CategoryTheory.GeneratorTowerNormalize`, is fully proved. It normalizes a
given tower after mapping by an additive exact coproduct-preserving functor.
It has no compactness or generation assumptions and does not construct the tower.
Both nodes inherit the item's chapter, unit and explicit blueprint ancestry.
No change record is needed: no existing interface, statement or definition changes.

## Second reading by U1

1. I compared the delivered item module with the repository version. The target
   declaration has the same signature byte for byte; only its proof and proof-only
   imports changed. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile
   without errors or warnings. The only remaining `sorry` is the named theorem
   `AlgebraicGeometry.supported_compact_detector_model`; no definition contains a
   `sorry`, and no forbidden declaration forms occur. Verdict: pass.
3. I checked the split-off theorem and its DAG node. Its conclusion is the strict
   preparation result required by the item and does not restate the target; the
   docstring gives the construction and edge cases, and the node records its
   source, proof plan, dependencies, and Lean declaration. Verdict: pass.
4. I checked the proof route and pruning. The target uses the supported model,
   the existing compact-generator construction, and the fully proved normalization
   theorem. Removed imports are listed under `No longer needed`; no unit statement
   or realized unit step is bypassed. Verdict: pass.
5. I checked the DAG proof, proof dependencies, origins, and the unit/chapter
   ancestry against the Lean proofs. The item node and both new nodes agree with
   the declarations and the route. Verdict: pass.

I changed only this report section; no Lean statement or proof was altered during
 second reading.
