## What changed

Proved `AlgebraicGeometry.coherentMap_completion_torsion_kernel_reflection` from the
existing affine-limit annihilation theorem, a new local completion calculation, and
an independently proved supported-zero reflection theorem. The existing signature
and docstring are unchanged. The argument takes the affine limit bound on X first;
only the coherent submodule H = K^(2s) kernel(a) is descended to V(K^q).

Added `Sheaf.AlgebraicGeometry.CoherentKernelIdealProductCompletionZero` for the
remaining finite-module completion and affine-to-sheaf comparison obligation.
Added `Sheaf.AlgebraicGeometry.SupportedCoherentCompletionReflectsZero` and proved
its theorem using the existing coherent closed-pushforward equivalence, natural
completion comparison, affine annihilation criterion, and full faithfulness.
All new imports in the original module are proof-only. No existing interface changed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.coherentMap_completion_torsion_kernel_reflection`
(node `lem-weil-pbc-coherent-map-completion-torsion-kernel-reflection`).
Its proof computes the affine 2s bound, constructs the coherent ideal-product
submodule and its monic inclusion into F, and applies supported-zero reflection.

Also proved the new theorem
`AlgebraicGeometry.supportedCoherent_completion_reflects_zero`
(node `lem-weil-pbc-supported-coherent-completion-reflects-zero`).
Its proof derives support from injectivity on affine sections, descends the object,
compares completion diagrams, reflects zero componentwise through closed pushforward,
and finally reflects zero through the assumed global equivalence.

One new hole remains, as the entire proof of the public theorem
`AlgebraicGeometry.coherentKernel_idealProduct_completion_zero`
(node `lem-weil-pbc-coherent-kernel-ideal-product-completion-zero`).
It states the local exactness/image calculation and quotient vanishing, with no
completion equivalence or thickening assumption and arbitrary exponent t.
Its docstring and node give the finite-module tensor argument and the affine gluing.
This delivery is a decomposition: one original hole closed, one lower hole added;
net hole reduction is zero. No sorry remains in the original module or the reflection
helper, and there is no sorry in a definition.

All three modules compile locally without warnings. The original theorem retains
the target-annihilation hypothesis hG, although the new argument only uses hF.

## No longer needed

Removed these direct proof imports from the original module:
- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`:
  now used only by the supported-zero reflection helper.
- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalenceCompletion`:
  now used only by that helper.
- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers`:
  no separate identification of the pushed kernel or its ideal product is required;
  the existing completion comparison still uses it transitively.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`:
  its comparison belongs to the remaining local calculation's proof plan.
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`:
  the reflection proof uses the existing affine zero criterion; the local calculation
  still needs the affine product and quotient formulas.
- `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`:
  the remaining local calculation's proof plan uses its tensor and flatness results.

Replaced the original node's direct proof dependencies by the affine-limit node and
the two new nodes. The old dependencies remain needed behind those nodes, or
transitively behind their existing dependencies. No whole dependency module is
claimed as globally pruned, and no unit statement or unit step is bypassed.
The descent of F, G and a and the separate pushed-kernel comparison are unnecessary.

For clarity, these seven old direct `proof_deps` are no longer direct dependencies
of the original proof (they remain in the supporting proof plans or transitively):
- `lem-weil-pbc-closed-immersion-coherent-equivalence`
- `lem-weil-pbc-closed-immersion-coherent-formal-equivalence-completion`
- `lem-weil-pbc-closed-immersion-pushforward-ideal-powers`
- `lem-weil-pbc-coherent-formal-modules-affine`
- `lem-weil-pbc-completion-finite-module-tensor`
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
- `lem-weil-pbc-noetherian-completion-flat`

The second reading also removed the redundant direct public import
`Mathlib.Algebra.Category.ModuleCat.Limits` from the new local-calculation module;
its signature still elaborates through `CoherentFormalModule` alone.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned descent of the entire map is unnecessary:
the existing affine-limit theorem applies on X, and only zero reflection needs the
closed-thickening equivalence. The positivity assumptions and hG remain unchanged
in the original statement. The remaining local theorem also works for t = 0,
I = 0, I = O_X and the empty scheme: it does not assert local faithfulness.
The new reflection theorem covers empty thickenings and zero objects.

LeanSearch returned Internal Server Error, recorded as unavailable. LeanFinder found
`AdicCompletion.map_exact` and other ring-level results, not the required sheaf-level
comparison. Loogle and grep searches are recorded in searches.jsonl. Blueprint searches
for `kernel completion`, `completion zero`, and `ideal product kernel` found no match.
The Stacks source files are not present locally; Tags 088A, 0888 and 00MB were read
on the Stacks website. The source argument agrees with the chosen reduction.

## New nodes

`lem-weil-pbc-coherent-kernel-ideal-product-completion-zero` states the affine finite
completion calculation needed between the numerical limit bound and global zero
reflection. It is strictly part of the original argument: there is no thickening,
completion equivalence, or termwise kernel/cokernel bound in its hypothesis.
Its one public theorem is the only new sorry.

`lem-weil-pbc-supported-coherent-completion-reflects-zero` states and proves zero
reflection for an arbitrary coherent submodule of a K^q-annihilated coherent module.
It contains neither a map F→G nor a numerical torsion estimate. The proof is complete.
No change record or forced adaptation is needed.

## Second reading by P4

1. **Interfaces — PASS.** Compared the original module with the repository by
   `diff -u`: the entire theorem header, hypotheses hq/hcompletion/hF/hG/hs/h,
   conclusion and existing docstring are byte-for-byte unchanged. Only proof-only
   imports and the proof body changed. The two other modules are new. No definition,
   existing public import, or existing declaration signature changed; no change
   record or forced adaptation is needed. Existing node differences are confined to
   `proof`, `proof_deps` and `proof_origin`.

2. **Proofs and trust — PASS as a decomposition.** Compiled all three modules in
   import order with `lcompile.py`, without errors or warnings. A scratch copy printed
   axioms of all three public theorems: the supported-zero reflection helper has only
   `propext`, `Classical.choice`, `Quot.sound`; the original theorem and the new local
   completion lemma additionally have `sorryAx`. The only literal sorry is the whole
   named theorem `coherentKernel_idealProduct_completion_zero`. There is no forbidden
   declaration/attribute, anonymous hole, or hollow definition. The coherent object H
   in the original proof uses an explicitly constructed image object; the missing
   theorem supplies only its coherence proof. The reflection proof's L is determined
   up to isomorphism by the equivalence and its specified pushforward comparison,
   rather than an arbitrary object chosen from a bare existence claim.

3. **New statements — PASS.** Read [088A](https://stacks.math.columbia.edu/tag/088A),
   [0888](https://stacks.math.columbia.edu/tag/0888),
   [087W](https://stacks.math.columbia.edu/tag/087W),
   [00MB](https://stacks.math.columbia.edu/tag/00MB),
   [087T](https://stacks.math.columbia.edu/tag/087T) and
   [0880](https://stacks.math.columbia.edu/tag/0880). The remaining completion lemma
   is the finite-module calculation: flat completion identifies the completed kernel
   with the kernel of the completed map and the completed ideal multiple with its
   ideal-action image. Annihilation makes this image zero, and the surjective positive
   quotient projections give precisely its conclusion. It assumes neither support on
   a thickening nor a completion equivalence, and takes arbitrary t, so it is strictly
   part of the original argument, not a renamed reflection theorem. Its docstring
   supplies the coherence, natural affine comparison and gluing arguments; its node
   records the corresponding sources and dependencies.

   Checked t=0 (the completed kernel itself must be zero), K=0 with t>0
   (the ideal product is zero), I=0 (completion is constant and the assertion reduces
   to the given annihilation), I=O_X (all positive quotients are already zero), zero
   maps and zero objects, and the empty scheme. Completion need not be locally
   faithful: for example Z/3 over Z has zero (2)-adic completion and zero positive
   (2)-adic quotients, which is consistent with the local lemma. In reflection,
   injectivity of j transfers K^q-annihilation from F to H; no annihilation of a
   second object is smuggled in. The empty thickening forces the supported object
   to vanish, and the assumption of an equivalence is used only after descent.

   Independently searched with LeanFinder for exact finite completion and vanishing
   of ideal multiples, Loogle for `AdicCompletion.map, LinearMap.ker`, and grep for
   `completion.*(reflect|IsZero)|IsZero.*completion`; results are in searches.jsonl.
   LeanFinder returns `AdicCompletion.map_exact`, a ring-level ingredient, not the
   sheaf-level conclusion. Searches in both local Lean roots and the upstream roots
   found no exact duplicate. `formalCompletion_exact` and
   `formalCompletion_affine_kernel` were read as possible alternatives: they give
   categorical exactness but still require the affine ideal-action and section-limit
   comparison. They do not close this obligation in a few lines.

4. **Route and pruning — PASS after report repair.** The original proof first applies
   `coherentFormalModule_annihilated_affine_limit` on X with t=s, then applies the
   local lemma with t=2*s, and constructs the monic composite H→kernel(a)→F before
   supported reflection. Each application matches the cited declaration, including
   positive level n+1 and the unchanged exponent 2*s. In the reflection proof, the
   affine zero criterion and monicity give hsupp, the coherent equivalence gives η,
   the natural completion comparison gives hpush, and fully faithful pushforward
   reflects zero at every level. The coherent formal inclusion and the assumed
   completion equivalence then reflect zero before η returns to H. No full
   faithfulness of affine completion is used. Public imports in the new modules are
   for their signatures; proof imports remain private. Removed the redundant new
   public ModuleCat.Limits import after a successful compile without it. Added the
   exact seven removed direct dependency-node names above. No global module pruning
   is claimed. Checked `dag/units/sk-thm-p1.json` and its `realized` statement and step
   lists: this item is below that route, and none of those realized nodes is bypassed
   or changed.

5. **DAG agreement — PASS.** Read all three delivered nodes and the declaration
   records of every cited dependency. The original node's three steps and their
   union of uses match its Lean body; the reflection node matches support transfer,
   descent/comparison, componentwise zero reflection and global zero reflection.
   The local node records the actual remaining finite-module obligation. The new
   node statements agree with the Lean signatures, including Noetherianity,
   monicity, the universally quantified Noetherian instance in hcompletion,
   arbitrary t for the local lemma, and positive quotient indexing. Both new nodes
   have source, complete proof steps, searches, creation/blueprint provenance,
   chapter/unit, status and Lean records; their proof dependencies do not cite the
   item and introduce no cycle.

Changed in this second reading: removed one redundant import from the new local
lemma module, completed the removed-node list, and wrote this independent review.
No proof body, statement, definition, node, or hole count needed repair. One existing
hole is closed and one lower hole is added; the new reflection helper is independently
proved. This remains a decomposition with net hole reduction zero.
