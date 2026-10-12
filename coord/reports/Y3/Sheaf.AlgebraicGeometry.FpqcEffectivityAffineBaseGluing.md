## What changed

Replaced the sorry in AlgebraicGeometry.fpqc_effectivity_of_affine_bases by a
compiling reduction. Its signature and docstring are unchanged. The proof constructs
the datum over every affine open from the already proved canonical pullback datum,
restricts its transport from the composite map to the open base, proves the covering
is fpqc by base-change stability, and applies hbase and hlocal.

Added Sheaf.AlgebraicGeometry.FpqcEffectivityOpenLocal with the proved theorem
AlgebraicGeometry.fpqc_isEffective_of_affine_open_restrictions. It turns a global
pullback projection invariant on affine-open test schemes into an effective datum:
cover an arbitrary test scheme by inverse images of affine opens, lift its points,
use transport naturality, and apply open-cover morphism extensionality. A private,
proved congruence lemma handles dependent transport arguments.

Added Sheaf.AlgebraicGeometry.FpqcAffineModelsGlue for the remaining construction:
gluing the local effective models, with their locally invariant projection.
All three modules compile together without warnings with lcompile.py --all.
The second reader restored the morphism-descent and relative-gluing proof imports
in FpqcAffineModelsGlue, where the remaining hole's recorded plan uses them.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.fpqc_effectivity_of_affine_bases
(node lem-galois-fpqc-effectivity-affine-base-gluing). This is a decomposition,
not a sorry-free proof: one original hole closed and one strictly lower hole added,
net zero. The affine-restriction step and the global transport-locality step are
proved in Lean, not postponed.

AlgebraicGeometry.fpqc_isEffective_of_affine_open_restrictions is proved from the
construction lemma (node lem-galois-fpqc-effectivity-open-local).

The only sorry in the delivery is
AlgebraicGeometry.fpqc_affine_effective_models_glue
(node lem-galois-fpqc-affine-models-glue). It states existence of a global pullback
projection with invariance only for points over affine opens. It has no morphism
property P, no base-change stability hypothesis, and no universal affine-base
hypothesis. This is the remaining model-comparison and relative-gluing part of
the argument, strictly below the original theorem. No data are chosen from it
inside a definition.

## No longer needed

Removed the direct proof imports Sheaf.AlgebraicGeometry.FpqcMorphismsDescend and
Mathlib.AlgebraicGeometry.RelativeGluing from the original module; their role is
now in the construction lemma's plan. They are still mathematically needed there,
so neither those modules nor their nodes are claimed as globally pruned.

The original module no longer directly needs
lem-galois-fpqc-morphisms-descend,
lem-weil-pbc-relative-glueing-affine-opens, or
lem-weil-pbc-scheme-morphism-gluing. The last is used in the proved locality
criterion; all three remain dependencies below the construction. No globally
unneeded node or module was established. The fpqc-covering-base-change node,
fibre-product node, and descent-datum node remain needed.

## Where the brief, the DAG or earlier work was wrong

The planned APIs do not directly supply a transport-compatible relative gluing
datum; the missing interface is isolated in the construction lemma. The earlier
canonical pullback construction is proved and reusable, but it keeps the old
base S. The original proof explicitly restricts its transport to obtain a datum
relative to X_U -> U; no new hole is used for that restriction.

The source files literature/stacks-project/descent.tex are not present in this
machine's checkout. Read the authoritative sources online instead:
https://stacks.math.columbia.edu/tag/02W3 (general-base paragraphs) and
https://stacks.math.columbia.edu/tag/01LH. Their affine-open comparison and relative
gluing route is retained. The unit sk-prop-h2 has no realized node tied to this
auxiliary statement; no unit statement or step was changed or bypassed.

Edge cases checked mathematically: empty S is covered by the empty affine-open
family and forces empty X and V; identity coverings yield the existing scheme
as effective model; empty V yields empty local and global models. The new
construction imposes no finiteness, quasi-separatedness, or affineness on X or V.
Existential effective models are used only in theorem proofs, never to define
an arbitrary object from an unproved existence statement.

## New nodes

lem-galois-fpqc-affine-models-glue records the remaining local-model comparison and
relative gluing construction from Stacks 02W3 and 01LH. Its complete proof sketch
is in its node and docstring, with the existing morphism-descent and gluing nodes
as dependencies. Module: Sheaf.AlgebraicGeometry.FpqcAffineModelsGlue.

lem-galois-fpqc-effectivity-open-local records the proved transport-locality
argument following Stacks 02W3's final paragraph. Module:
Sheaf.AlgebraicGeometry.FpqcEffectivityOpenLocal. Both nodes inherit the original
item's chapter, unit and blueprint ancestry. Searches inspected Mathlib's
relative-gluing, directed-cover and general stack APIs and the source library's
effectivity declarations. LeanSearch returned an internal server error and is
recorded unavailable; LeanFinder/Loogle and grep were actually run. Blueprint
searches for effectivity, 02W3 and gluing found no existing statement of the new
transport-form criterion. No change record is needed: no existing statement or
definition changed.

## Second reading by Y3

1. Compared the existing module with the repository by diff and checked its
   signature and docstring byte for byte. Both are unchanged. Only its proof and
   private proof imports change; neither targets nor existing definitions change.
   The other two modules are new. No change record is required. Verdict: pass.
2. Compiled all three modules in import order with lcompile.py --all, without
   errors or warnings. Scratch copies with #print axioms for all three public
   theorems show only propext, Classical.choice, Quot.sound and sorryAx. There is
   exactly one direct sorry, the named gluing theorem reported above; no new data
   definition, forbidden trust feature, or hidden proof hole occurs. Verdict:
   valid decomposition, not a sorry-free proof.
3. Read the new statements, their nodes and complete docstring arguments against
   Stacks 02W3's general-base paragraphs and 01LH. Compatibility with D determines
   the local transports, since a point of V_U is determined by its two pullback
   projections. Nested affine-open comparisons descend uniquely; overlaps are
   covered by smaller affine opens, so no affine-intersection assumption is made.
   Checked empty base, empty V and identity-cover cases. Independent LeanFinder
   search for effective restrictions on a basis of opens, Loogle search for the
   relative-gluing API, and grep for transport/effectivity and equifibered returned
   general APIs, not a duplicate of the new theorem. The existing invariant-affine
   neighbourhood theorem requires a finite covering and an affine cover of V,
   so it cannot replace this arbitrary-fpqc construction. The remaining hole is
   the model-comparison/gluing step, with the affine reduction and the global
   locality step genuinely proved. It cannot be closed in a few minutes from the
   available API. Verdict: true, needed and strictly a part of the argument.
4. Read the proof top down: canonical pullback construction, restricted transport,
   fpqc base change and the affine hypothesis supply the local models; the new
   locality proof uses open-cover morphism extensionality. Public imports supply
   signature notions; proof helpers are private imports. Every removed old
   proof dependency is listed in No longer needed, with no global pruning claim.
   sk-prop-h2.realized has empty statement and step lists, and no realized unit
   node is bypassed. Verdict: pass after the import repair below.
5. Checked the node records against Lean, including the verbatim signatures,
   source/proof sketches, creation and blueprint fields of new nodes, and the
   equality between proof_deps and the union of proof-step uses. The existing
   node differs only in proof and proof_deps. The gluing node keeps the original
   morphism-descent/relative-gluing route; the locality node records hom_ext's
   morphism-gluing leaf. Verdict: pass.

Changes: added private imports Sheaf.AlgebraicGeometry.FpqcMorphismsDescend and
Mathlib.AlgebraicGeometry.RelativeGluing to FpqcAffineModelsGlue so the remaining
hole's dependency plan is available in its module. Removed one trailing space
in the proved locality module. No statements, definitions or proof bodies were
otherwise changed. Holes remain one closed and one added, net zero.
