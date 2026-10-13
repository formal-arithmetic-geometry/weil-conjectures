## What changed

Repaired reviewer X-18d42, head 18d421c33, E2/E7 point 4. Removed the false
`AlgebraicGeometry.torsionControlled_completion_hom_lift_completion` and its
arbitrary-raw-lift proof route. The replacement retains θ in a concrete finite
graph: in the pullback of a and a', take the kernel of the difference of the
second quotient projection and the first quotient projection followed by θ_n.

Added `TorsionControlledFiniteGraphEpi.lean`, with four concrete graph definitions
and a surjectivity lemma, and `FormalMapTorsionFiniteDetection.lean`, with a
finite-level equality detection lemma. The item's module proves
`torsionControlledGraphFst_mono` by kernel factorization, cancellation at the
separating quotient, and pullback extensionality. It proves
`torsionControlledGraphFst_isIso` from monomorphy and the graph epi lemma.
`torsionControlledCompletionHomLift` is inverse(first projection) followed by
second projection. Its data are actual kernel/pullback constructions and the
unique inverse of an isomorphism; no arbitrary existence witness is chosen.
`torsionControlled_completion_hom_lift_constructed` proves both equations:
the pullback identity gives g≫a'=a, and the graph kernel equation gives the
θ_n component. Functoriality and finite torsion detection give completion(g)=θ.

Adapted `TorsionControlledCompletionHomLiftExists.lean` without changing its
signature, visibility, or docstring. Artin--Rees supplies a separating depth;
the constructed map and the joint construction theorem supply its witness and
both equations. Its proof import of Raw is replaced by
`CoherentMapTorsionCompletionExtZero`. The item publicly imports the graph module
because its public definitions need that module, and privately imports finite
detection. CoherentFormalModule remains publicly available through the graph
module. Updated both affected existing DAG nodes and added the two new nodes.

## Proved and sorry left

The original false hole is retired, not proved. The replacement joint construction
is completely proved from two strictly smaller new statements. This is a
construction repair and decomposition, not a net sorry reduction: one original
hole removed, two new holes added. No sorry remains in the item's module or in
the adapted existence module. The already proved existence theorem is preserved
with a sound replacement reduction.

Proved declarations in the item:
`AlgebraicGeometry.torsionControlledGraphFst_mono`,
`AlgebraicGeometry.torsionControlledGraphFst_isIso`, and
`AlgebraicGeometry.torsionControlled_completion_hom_lift_constructed`.
The constructed map is a definition with no sorry in its body.

Every new sorry (each is the entire proof of its public theorem):

- `AlgebraicGeometry.torsionControlledGraphFst_epi`, node
  `lem-weil-pbc-torsion-controlled-finite-graph-epi`, in
  `Sheaf.AlgebraicGeometry.TorsionControlledFiniteGraphEpi`.
- `AlgebraicGeometry.formalMap_torsion_finite_detection`, node
  `lem-weil-pbc-formal-map-torsion-finite-detection`, in
  `Sheaf.AlgebraicGeometry.FormalMapTorsionFiniteDetection`.

These supply only surjectivity of a specified graph projection and equality
of formal maps under two independently verified comparisons, respectively.
Neither restates existence of the desired lift. Their docstrings give affine
proofs using finite-module exact completion, Nakayama, and torsion separation.
Edge cases checked: J=0 gives the actual graph of θ and quotient detection is
immediate; J=O_X makes a' invertible and the formal category zero; zero modules
and the empty scheme satisfy the categorical construction as well.

All four delivered Lean modules compile together without errors or warnings
using lcompile.py. The original existence module was separately compiled
against the changed dependency and fails precisely at the removed declaration.
The delivery dry run checks all declarations with its axiom/sorry probe.

## No longer needed

Removed the proof import of
`Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftRaw` from the
existence module. Node
`lem-weil-pbc-torsion-controlled-completion-hom-lift-raw` and that module are no
longer needed by this lifting route. The completion node's former raw-lift
proof dependency is removed. The existence node's previous DAG dependencies
(formal-gluing exactness, affine tilde/gamma adjunction, and sheaf gluing) are
replaced by Artin--Rees separation plus the joint construction. The affine
tilde/gamma adjunction is still needed by the graph-epi node; it is not globally
pruned. The formal-gluing and sheaf-gluing nodes are no longer needed by this
route. There are no base DAG citers of the completion node, despite its existing
Lean caller; the caller's updated DAG now records the actual dependency.

The direct public import of CoherentFormalModule in the item is replaced by
the graph module's public import of it; CoherentFormalModule itself is still
needed and is not pruned. The six diagnostic private counterexample/cancellation
helpers from the rejected sandbox are removed: they are unnecessary for the
correct construction. No unit statement or realized proof step is bypassed;
`dag/units/sk-thm-p1.json` stays unchanged. Global pruning of Raw depends on any
other routes that reach it; this report asserts pruning from this route only.

## Where the brief, the DAG or earlier work was wrong

The former theorem asserted compatibility of every g with g≫a'=a. At J=0,
a=a'=g=0 and θ=id on a nonzero module contradict that conclusion. Equality
after postcomposition with completion(a') does not allow cancellation of its
torsion kernel. The rejected sandbox diagnosed this but retained the false sorry.
This repair removes it instead of assuming monicity or reasserting it as a helper.

The source is the omitted comparison/uniqueness argument of Stacks Tag 0889(1),
not an arbitrary-lift cancellation assertion. Checked the source at
https://stacks.math.columbia.edu/tag/0889 and the related use of uniqueness at
https://stacks.math.columbia.edu/tag/088A. The finite graph supplies an explicit
comparison retaining the prescribed formal datum. The new construction only
needs the torsion hypotheses on a'; the caller's existing ha binder is preserved.

Searches: msearch Loogle found Preadditive.mono_of_cancel_zero, used in the actual
proof. LeanFinder returned generic adic quotient/extensionality lemmas, with no
coherent finite-graph surjectivity or torsion finite-detection match. LeanSearch
was unavailable (Internal Server Error), so no verdict is claimed for it. msearch
grep and direct searches of both library roots found no matching graph/detection
declarations. Mathlib's pullback, kernel, and inverse APIs supply all categorical
glue in the item.

## New nodes

`lem-weil-pbc-torsion-controlled-finite-graph-epi`: the actual graph projection
is epi at every positive quotient depth. The affine proof uses exact finite
completion, its section induced by θ, Nakayama near V(J), and invertibility of
a' away from V(J). Its own module contains the concrete graph definitions.

`lem-weil-pbc-formal-map-torsion-finite-detection`: formal maps with equal
comparison composites are equal if they agree at a quotient separating the
torsion kernel. The affine proof identifies the completed kernel with the
original annihilated kernel and uses the separating quotient's injectivity.
Search records and the complete proofs in words are in both nodes/docstrings.

Change record: `coord/changes/torsionControlled_completion_hom_lift_completion.md`.

## Forced adaptations

`Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftExists` (unclaimed):
its original compiled against the changed item fails at line 42:16 with
`error(lean.unknownIdentifier): Unknown identifier
 torsionControlled_completion_hom_lift_completion`.
The adapted version compiles. Replaced only proof import line 4 and the proof
body at lines 41–46. The new import supplies the separating depth, and the new
body constructs g and obtains both equations jointly. Destructuring ha preserves
use of the unchanged hypothesis for the unused-variable linter. Every existing
binder, universe, declaration name, visibility, conclusion, and docstring is
unchanged. No other existing module needs adaptation: downstream.py --uses
finds only this caller and the item itself.

## Second reading by S1

1. Interface check: diffed both existing modules against the repository. The
   existence theorem's signature and docstring are byte-for-byte unchanged;
   only its proof and proof import change. The item retires the false arbitrary-g
   theorem under the explicit change record, rather than claiming it proved.
   Its Spec(k), J=0, a=a'=g=0, theta=id counterexample is valid. No target or shared
   definition changes. The only caller found by rg is the adapted existence module.
2. Proof check: independently compiled all four modules with lcompile.py. No
   errors or warnings. Only the two reported public theorems contain sorry;
   no forbidden declarations or holed definitions occur. A scratch copy with
   #print axioms checked the graph monomorphy, isomorphy, lift definition, joint
   construction theorem, and both new lemmas: only propext, Classical.choice,
   Quot.sound and the expected sorryAx occur. The graph is a concrete pullback
   kernel; the inverse used for data is uniquely determined by its isomorphism.
3. Split-off statements: read both new modules and nodes, and checked the source
   at Stacks Tags 0889 and 088A. The graph-epi claim follows from exact finite
   completion, its section (id,theta), reduction modulo J and Nakayama for the
   finite cokernel at primes containing J; outside V(J), a' is invertible and
   the quotient condition vanishes. Detection follows from exact completion of
   ker(b), its identification with the J-power-annihilated kernel, and injectivity
   into the separating quotient. These claims are true for J=0, J=1, zero modules,
   and the empty scheme; neither restates the old false claim or lift existence.
   Independent LeanFinder search for equal composites plus equal reductions,
   Loogle search for AdicCompletion map lemmas, msearch grep for formal ext/mono
   and pullback epimorphy, and rg in both Lean roots found no direct replacement.
   CoherentMapTorsionCompletionExt concerns algebraic source maps, not arbitrary
   formal maps; FormalCompletionExact and CoherentFormalModulesAffine supply
   useful future infrastructure but do not close either lemma in a few minutes.
4. Route and pruning: traced kernel cancellation, pullback extensionality,
   isIso_of_mono_of_epi, the quotient epimorphism, and finite detection. Each
   import supplies public data or an actual proof dependency, with detection
   and the adapted caller's extra imports private. All former proof_deps are
   accounted for: raw lift, formal-gluing exactness, affine tilde/gamma adjunction
   (retained in the new graph node), and sheaf gluing. sk-thm-p1's realized nodes
   are untouched and none is bypassed. Pruning is only asserted for this route.
5. DAG check: existing node edits are confined to proof fields, lean, and the
   recorded statement correction. Both new nodes have source, full proof plan,
   search records, creation and blueprint records, matching chapter/unit, and
   verbatim Lean signatures. proof_deps equals the union of step uses; the
   existence node uses separation and the joint construction as written.

Second reading changes: replaced the change record's abbreviated New code with
verbatim signatures, added the missing isomorphism signature and the complete
lift definition. The dry run requires the legacy statement_change.by value
"S1 stage 2" even for this stage-3 correction, so that field was retained.
No Lean proof or statement needed repair. The retired original hole counts as
zero original statements proved out of one; two smaller holes are added. This
is a sound construction repair/decomposition with local net holes minus one,
not a claim of proving the former theorem.

## Forced adaptations

### Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftExists
Original against changed dependencies failed:
```
/tmp/forced-adaptation-zjl6t4cm/lean/Sheaf/AlgebraicGeometry/TorsionControlledCompletionHomLiftExists.lean:41:20: error: Function expected at
  torsionControlled_completion_hom_lift_raw J H F F' a a' ha ha'
but this term has type
  ∃ g, g ≫ a' = a

Note: Expected a function because this term is being applied to the argument
  θ
/tmp/forced-adaptation-zjl6t4cm/lean/Sheaf/AlgebraicGeometry/TorsionControlledCompletionHomLiftExists.lean:41:9: error: Tactic `rcases` failed: `x✝ : ?m.152` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-zjl6t4cm/.lbuild) [2.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
