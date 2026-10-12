## What changed

Replaced the original sorry in `affine_module_tensor_coherenceComparisons` with a
reduction along the existing Stacks 01SB tensor route. Quasi-coherence follows from
existing scalar restriction, pullback and algebra change-of-rings declarations,
plus the new pushout-algebra quasi-coherence lemma. The comparison maps are assembled
from objectwise factors/lifts by private generic categorical helpers; their naturality
is proved in the item using cancellation
of an epimorphism and injectivity of restriction of scalars on morphisms.
All original signatures and public imports stay unchanged. Three new statement modules
isolate the remaining tensor calculations.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Scheme.Modules.affine_module_tensor_coherenceComparisons`.
This is a decomposition, not a sorry-free proof of its dependencies: one hole closed,
three holes added (net minus two). No sorry remains in the item.

New named holes:

- `AlgebraicGeometry.Scheme.Modules.affine_module_tensor_algebra_quasiCoherent`
  (node `lem-weil-pbc-affine-module-tensor-algebra-quasi-coherent`).
- `AlgebraicGeometry.Scheme.Modules.affine_module_tensor_counitFactor`
  (node `lem-weil-pbc-affine-module-tensor-counit-factor`).
- `AlgebraicGeometry.Scheme.Modules.affine_module_tensor_unitLift`
  (node `lem-weil-pbc-affine-module-tensor-unit-lift`).

The algebra lemma has only the pushout and affineness hypotheses. The other two lemmas
need no affineness or quasi-coherence. Counit factors are uniquely determined by the
epic comparison, and unit lifts by injectivity of restriction on morphisms; the proof
therefore chooses no arbitrary undetermined data.

## No longer needed

Removed the direct proof import `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
from the item; its declarations remain necessary in the signatures and are already
publicly available through `TensorPullbackAdjunction`. No mathematical tensor-product
node is pruned from the closure. The node `def-pur-sheaf-tensor-product` is removed from the item’s direct
`proof_deps` and retained in the counit-factor and unit-lift nodes. No existing
dependency node or module is otherwise pruned: the original six dependencies
are used directly or in the three split nodes.
The second reading also removed redundant imports of
`Mathlib.AlgebraicGeometry.Morphisms.Affine` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` from both new comparison
modules; neither supplies a declaration unavailable through their other imports.

## Where the brief, the DAG or earlier work was wrong

The original proof plan silently used quasi-coherence of the ring-sheaf pushout B,
which none of its six stated dependencies directly asserts. The new algebra lemma
isolates precisely that fact. The plan also did not provide a declaration for the
B-linearity of the counit or A-linearity of the adjoint; the other new lemmas record
these objectwise facts without moving either full natural transformation statement.
The unit route is preserved; this node is not a unit realization in sk-thm-p1.

Stacks 01SB was read at https://stacks.math.columbia.edu/tag/01SB because the local
literature source named by the node is not present on this machine. The added details
are marked agent-written in proof_origin. Searches used LeanFinder, Loogle, and
Mathlib grep; LeanSearch returned Internal Server Error. No exact existing sheaf-level
statement was found. Blueprint searches for 01SB, affine modules, tensor algebra,
counit and scalar restriction found no duplicate of the three new statements.

## New nodes

`lem-weil-pbc-affine-module-tensor-algebra-quasi-coherent`:
`Sheaf.AlgebraicGeometry.AffineModuleTensorAlgebraQuasiCoherent`, quasi-coherence of B
as an O_U-algebra from its pushout universal property. Its proof follows pullback of
the quasi-coherent direct-image algebra and identifies the sheafified tensor algebra.

`lem-weil-pbc-affine-module-tensor-counit-factor`:
`Sheaf.AlgebraicGeometry.AffineModuleTensorCounitFactor`, the objectwise counit factor
and epimorphy of gamma_RF. The item proves the naturality of these factors separately.

`lem-weil-pbc-affine-module-tensor-unit-lift`:
`Sheaf.AlgebraicGeometry.AffineModuleTensorUnitLift`, an objectwise algebra-linear lift
of the adjoint of gamma. The item proves uniqueness and naturality after restriction.

All three were checked against empty schemes/opens, zero rings and zero modules:
tensor balancing, local generation and adjunction triangles remain valid. No change
record is required: no existing statement or definition is changed.

## Second reading by N1

1. Compared the item with the repository using `diff` and checked the entire
   existing theorem signature byte for byte: identical. Only private proved
   helpers, proof imports, and the proof body were added. No existing definition,
   target statement, or public import changed; no change record is needed.
2. Compiled all four modules in import order through `lcompile.py`. The only
   sorries are the three named new theorems listed above. Inspected all source
   for forbidden declarations and hollow definitions: none. Checked axioms of
   the main theorem, the three new theorems, and all six private helpers in a
   scratch copy. Only the permitted logical axioms and the reported `sorryAx`
   from open dependencies occur. All five categorical assembly/injectivity helpers, including the
   specialized wrapper, have no `sorryAx`. The quasi-coherence helper and
   the main theorem inherit the reported open dependencies. The factor and lift choices are
   determined by epimorphism cancellation and scalar-restriction injectivity.
3. Read each split statement and its full docstring proof, and compared its
   recorded Lean signature with the source: exact. Checked empty schemes,
   zero modules/rings and the identity morphism; the pushout tensor algebra,
   balanced identities and adjunction triangles remain valid. The counit and
   unit statements require no affineness. Each is strictly a part of the
   argument: quasi-coherence of B, objectwise counit factorization/epimorphy,
   or objectwise A-linearity. None restates the original conjunction and
   natural transformation conclusions. Independent LeanFinder, Loogle and
   Mathlib grep searches used pullback algebra, linear lifts, counit factors,
   epimorphisms and scalar restriction; repository searches included existing
   change-of-rings adjunction and tensor extension unit. No existing theorem
   closes a split statement directly; completing one requires additional
   sheafified tensor calculations, not a short application. Read Stacks 01SB
   online and confirmed the construction and comparison route.
4. Read the proof top downward: existing affine-algebra, scalar-restriction,
   pullback and change-of-rings declarations prove the quasi-coherence part,
   and proved generic categorical arguments assemble both comparisons. Checked
   the complete old proof-dependency list against the report; the tensor node
   is now indirect, not pruned from the closure. All remaining imports serve
   signatures or proofs. Read `dag/units/sk-thm-p1.json` realized statement and
   steps: this node realizes none of them and bypasses no unit step.
5. Checked all delivered JSON: existing node changes only proof, proof_deps and
   proof_origin; proof_deps equal the union of uses; every dependency exists.
   New nodes have sources, searches, creation and blueprint provenance,
   chapter/unit and matching Lean records. The main node describes the Lean
   proof's actual quasi-coherence and naturality reductions. Verdict: valid
   decomposition, one original hole closed and three holes added, net minus
   two; no claim of a dependency-free proof or mathematical module pruning.

Changes in this reading: made type transparency explicit locally in the main
proof, isolated scalar-restriction injectivity in a private proved helper,
and specialized categorical assembly in a small private proof context, with
category inference from the typed functors, to reduce dependent elaboration; removed
redundant imports from the new counit/unit modules; corrected the algebra
module heading and blueprint tag; expanded the counit docstring and its node
step to explain why hP pins the supplied κ on local generators; clarified the
indirect tensor dependency in No longer needed. Statements and hole counts
are unchanged.
