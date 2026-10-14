## What changed

The original module now proves `AlgebraicGeometry.quasiCoherentSymmetricAlgebra_affine_comparison`
from a local stalk comparison, without changing its signature or its existing docstring.

`Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineComparisonMap` constructs the comparison
`affineComparison` by the Mathlib tilde adjunction. Its data are explicit: the sectionwise
ring sheafification unit is made linear and transported through the existing upstream `Scheme.Modules.sectionsTopRestrictFromSpecEquiv`
between sections on an affine open and global sections on its Spec chart. The adjunction constructs the
map; no object is chosen from an unproved existence statement. The module proves
`affineComparison_top` and its restriction formula `affineComparison_toOpen`.

`Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineComparisonStalks` isolates steps 5 and 6 of the
original plan as one named theorem about the stalks of that particular local map. This lemma
asserts neither global quasi-coherence nor bijectivity of the affine section unit. The original
module combines it with stalk conservativity, transports explicit tilde presentations, glues
them along all affine charts, and proves the affine-unit conclusion by composing three
bijections and the adjunction identity. Thus this is a decomposition with substantive Lean
construction and assembly, not a renaming of the original conjunction.

The DAG copy follows this route. The unit `sk-thm-p1` and its realized statements and steps are
unchanged; this local algebra lemma is below that unit's route.

Sources read: the original node's full four-step plan and signatures of its dependencies;
Mathlib Modules/Tilde.lean and Modules/Sheaf.lean; the proved upstream
Modules/QuasicoherentKernel.lean and Mathlib/AlgebraicGeometry/Modules/Tilde.lean extensions;
and the official Stacks pages [01CG](https://stacks.math.columbia.edu/tag/01CG),
[01CH](https://stacks.math.columbia.edu/tag/01CH),
[01I7](https://stacks.math.columbia.edu/tag/01I7), and
[01I8](https://stacks.math.columbia.edu/tag/01I8).
The local checkout does not contain the corresponding literature/stacks-project .tex files;
the original node's source labels are retained, and the official tagged statements were read.

## Proved and sorry left

Closed in the assigned module:
`AlgebraicGeometry.quasiCoherentSymmetricAlgebra_affine_comparison`
(node `lem-weil-pbc-quasi-coherent-symmetric-algebra-affine`). There are no textual sorries
left in that module. Its private `AlgebraicGeometry.affineComparison_isIso` is proved.

Added one hole, in a separate module:
`AlgebraicGeometry.SymmetricAlgebraSheaf.affineComparison_stalk_bijective`
(node `lem-weil-pbc-symmetric-algebra-affine-comparison-stalks`). It is exactly `:= by sorry`,
with its source and full proof in words. This is a decomposition: one upper hole closed,
one lower hole added; net hole change zero. The original theorem still depends on that hole.

The new map module has no sorries. The following are constructed or proved:
`AlgebraicGeometry.SymmetricAlgebraSheaf.sectionLinearMap`,
`AlgebraicGeometry.SymmetricAlgebraSheaf.affineComparison`,
`AlgebraicGeometry.SymmetricAlgebraSheaf.affineComparison_top`, and
`AlgebraicGeometry.SymmetricAlgebraSheaf.affineComparison_toOpen`.

Edge cases of the remaining statement: an empty affine chart or zero ring has no point x,
so the stalk assertion is vacuous; F = 0 gives the usual structure-ring comparison; modules
of arbitrary rank are allowed, with no finite-generation assumption; a nonseparated X causes
no problem because an intersection of affine neighbourhoods is refined by an affine, rather
than assumed affine. The construction works for all F; quasi-coherence is used only in the
remaining tensor comparison. The proof in words explains both injectivity and surjectivity,
and the restriction compatibility needed by injectivity.

The three delivered Lean modules compile locally in import order with no warnings.
The second reader is authorized to run the final dry run and push the delivery.

## No longer needed

Removed from the assigned module:
`Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange`,
`Sheaf.RingTheory.SymmetricAlgebraBaseChange`, and
`Sheaf.Topology.PresheafModuleStalkFunctor`.

The first two imports are relocated to the remaining stalk-comparison module: their nodes
`lem-weil-pbc-quasi-coherent-affine-section-base-change` and
`lem-weil-pbc-symmetric-algebra-base-change` are still needed there, not pruned.

The custom presheaf-module stalk functor is genuinely unnecessary for this proof route.
The module `Sheaf.Topology.PresheafModuleStalkFunctor` and its node
`def-weil-pbc-module-stalk` are removed from this item's proof-dependency route. Stalks and
stalk maps here are Mathlib's underlying abelian presheaf stalks; the custom scalar-linear
presheaf-module stalk functor is not used. Other target branches may still need that module.

The other original nodes remain in the route: the affine-chart, restriction, tilde-section,
adjunction, and symmetric-sheaf-construction nodes are used in the map or assembly;
`lem-weil-pbc-ring-sheafification-space-underlying-abelian` and
`lem-weil-pbc-stalk-sheafification-space` are relocated into the remaining stalk lemma;
`lem-weil-pbc-module-iso-on-stalks` is realized by Mathlib conservativity; and the scheme
and quasi-coherence definition nodes are used by descent. No other node or module is claimed
pruned. Public imports of the assigned module are unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed target was found. The stated proof dependencies supply the
algebraic ingredients but do not already state the local comparison's stalk bijectivity;
that is the remaining named intermediate theorem. The comparison construction and final
descent are now implemented instead of left in prose.

`tools/blueprint_refs.py ancestor lem-weil-pbc-quasi-coherent-symmetric-algebra-affine`
returns None because its created.item is a stage-3 module name rather than a DAG node id.
The existing explicit blueprint.from field does identify
`lemma-weil-pbc-h1-constructible-representation`; the new nodes preserve that ancestor,
its place and via chain, and identify the exact local steps they implement. The global
blueprint search for symmetric algebra found only the unrelated vector-bundle zero-section
node, so there is no duplicate comparison node.

## New nodes

`def-weil-pbc-symmetric-algebra-affine-comparison-map`, despite the definition prefix, is a
statement node recording an explicit construction together with its defining identity and
naturality. Its Lean record lists the four declarations of the new map module. The proofs
are complete and require no quasi-coherence.

`lem-weil-pbc-symmetric-algebra-affine-comparison-stalks` records the one remaining local
stalk assertion, with the affine tensor identifications, pure-tensor compatibility,
sheafification stalk bijection, and separate injectivity and surjectivity arguments. It does
not restate either conjunct of the assigned theorem. Three kinds of Mathlib search were run
for both nodes; LeanSearch returned an internal server error and is recorded as unavailable.
No interface or definition of an existing module changed, so there is no change record and
no forced adaptation.

## Second reading by E2

1. Compared all three delivered modules with the repository. The two helper modules are
   new. The original theorem signature and declaration docstring are byte for byte unchanged,
   with no changed hypothesis, definition, or conclusion. Its public imports are unchanged.
   Restored the original module heading and blueprint tag, which an accidental text
   replacement had altered. No change record or consumer adaptation is required.
2. Compiled the three files in import order through lcompile.py. The only textual sorry is
   the named `AlgebraicGeometry.SymmetricAlgebraSheaf.affineComparison_stalk_bijective`.
   No prohibited declaration or hollow definition occurs. Explicit #print axioms checks
   showed only propext, Classical.choice and Quot.sound for the comparison construction and
   its identities; the original theorem and remaining stalk lemma additionally use sorryAx.
   The comparison is constructed by the adjunction from a concrete linear section map.
3. Read the remaining theorem, its full docstring proof, and its node. The tensor comparison
   on affine neighbourhoods and sheafification stalk bijection prove the assertion; the
   zero-kernel argument correctly shrinks a representative before using tensor injectivity.
   Empty affine charts have no points, zero modules give the structure-ring case, and neither
   finite rank nor separatedness is required. This is the local stalk step of the parent
   argument, leaving global descent and affine-section bijectivity to the implemented proof.
   Fresh leanfinder search for localization of symmetric algebras and associated-sheaf stalks
   found general ModuleCat.Tilde.stalkIso results, not this comparison. Loogle search for
   SymmetricAlgebra and stalk returned no hit. Repository searches found no existing local
   symmetric-algebra stalk comparison. The remaining formalization requires the tensor,
   chart-transport and germ-compatibility argument; it is not a few-minute omitted tactic.
4. Read from the original theorem down through the adjunction construction, naturality,
   stalk conservativity and descent of presentations. A broader search found the duplicate
   affine section equivalence upstream in Modules/ClosedImmersion. Removed the new
   affineSectionsEquiv definition and reused Scheme.Modules.sectionsTopRestrictFromSpecEquiv.
   Removed imports supplied by that public upstream import: Mathlib Modules/Tilde in the
   map, Coherent and Topology.Sheaves.Stalks in the stalk file, and the proof-only upstream
   QuasicoherentKernel import in the assigned file. The new public upstream import is needed
   by the comparison identity statements. The old dependency accounting is complete above;
   only the custom scalar-linear module stalk route is pruned. Read sk-thm-p1.realized and
   verified that none of its statement or step nodes is bypassed or changed.
5. Checked all three JSON records against the Lean declarations and argument. The parent
   record changes only its owned proof fields; its statement and Lean signature remain fixed.
   The new records have source, statement dependencies, proof steps, dependency union,
   origin, three search records, creation metadata, blueprint ancestry and Lean records.
   Updated the map node to cite the existing section equivalence and list four declarations,
   and the parent assembly step to name that equivalence. Each proof_deps list is exactly
   the union of its proof-step uses. The one new hole and the net-zero decomposition are
   explicitly reported, with no claim of a sorry-free proof.

Changes in this reading: restored the original heading/tag, removed a duplicate construction,
reused the upstream linear equivalence, removed redundant imports, updated the node and report
accounting, and wrapped the resulting long lines. The mathematical reduction is otherwise kept.
