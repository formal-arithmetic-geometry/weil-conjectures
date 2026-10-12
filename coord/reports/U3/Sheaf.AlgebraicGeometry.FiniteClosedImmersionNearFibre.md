## What changed

Proved `AlgebraicGeometry.exists_isClosedImmersion_restrict_of_fiber` without changing its
signature. Choose an affine neighbourhood and form the finite section-map cokernel. The
residue-field tensor vanishes by a new strictly smaller affine fibre calculation. Mathlib's
finite-module Nakayama/support criterion makes its prime localization zero; the existing
localized-cokernel criterion and finite-module spreading lemma produce a principal open.
The second new theorem, proved completely here, identifies localized module-map
surjectivity with surjectivity on basic-open sections and applies the affine
closed-immersion criterion. The target combines these steps and proves membership of s.

Added two proof-only Sheaf imports and a proof-only Mathlib.RingTheory.LocalRing.Module import. Updated the target
node to describe the actual Lean route. No statement or definition changed.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.exists_isClosedImmersion_restrict_of_fiber`.
Also proved `AlgebraicGeometry.isClosedImmersion_restrict_basicOpen_of_localizedMap_surjective`
and its private algebraic helper `surjective_awayMap_of_localizedMap_surjective`.

Added exactly one hole: `AlgebraicGeometry.subsingleton_fibreTensor_sectionCokernel`
(node `lem-weil-pbc-finite-fibre-cokernel-tensor`). It is the affine fibre identification
and right-exact tensor calculation only; it does not assume or conclude existence of a
neighbourhood. Thus the result is a decomposition (one hole closed, one added), with
the Nakayama and finite localization steps proved. All three modules compile cleanly.

## No longer needed

No original imports removed (both public imports are needed by the unchanged signature).
The new proved bridge imports only ClosedImmersion and Localization.Module for its statement,
and LocalizedModule.IsLocalization for its proof; unnecessary Fiber, Finite and LocalRing.Module
imports were removed from that new module. The second reading narrowed its public localization
import to Mathlib.Algebra.Module.LocalizedModule.Basic and removed the unnecessary public
Mathlib.RingTheory.LocalRing.Module import from FiniteFibreCokernelTensor.
The target proof no longer directly needs nodes `lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-spec-residue-field-identification`,
`lem-weil-pbc-closed-immersion-affine-cover-criterion`,
`lem-weil-pbc-principal-localization-open-immersion`. The fibre, residue and closed-immersion criteria
remain needed below the new tensor node; principal localization and the closed-immersion
criterion remain needed by the proved bridge. No corresponding module is globally
claimed pruned: they are Mathlib interfaces or used by the new nodes.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The DAG's residue-field identification and right-exactness glue
were not supplied as a directly applicable library declaration. This is isolated as a
strictly smaller named public theorem with the source and complete proof in its docstring.
The final bridge initially encountered module/ring localization and dependent restriction
coercions; those are now proved. The finite support argument uses Mathlib's combined
residue-tensor/Nakayama lemma and localized-map spreading theorem. The unit route is kept:
this node is below the unit's realized statements and steps.

Edge cases checked: empty fibre has zero tensor algebra, and the tensor cokernel is zero;
zero ring has no prime points; a=0 gives empty basic opens in the bridge. No nonempty-fibre,
Noetherian or finite-presentation hypotheses were introduced. Source read: Stacks Tag 04DG,
proof last two sentences (https://stacks.math.columbia.edu/tag/04DG); its affine finite
module argument applies here once fibre surjectivity is given. Local etale.tex was absent.

## New nodes

`lem-weil-pbc-finite-fibre-cokernel-tensor` states the vanishing of κ(p) tensor the affine
section-map cokernel. It isolates the first step, not the neighbourhood conclusion.
Its module is Sheaf.AlgebraicGeometry.FiniteFibreCokernelTensor and remains sorry.

`lem-weil-pbc-closed-immersion-localized-section-map` states the affine principal-open
criterion for an arbitrary affine morphism. Its module is
Sheaf.AlgebraicGeometry.ClosedImmersionOfLocalizedSectionMap and is proved completely.

Both use the source's affine algebra steps. LeanSearch was unavailable (HTTP 500);
LeanFinder, Loogle and grep queries ran and found building blocks but no direct theorem.
Blueprint searches for cokernel, residue field tensor and closed immersion found no
matching blueprint statement. No change record is needed because all imports are
proof-only and all existing signatures are unchanged.


## Second reading by U3

1. Compared every delivered module with the read-only repository. Only the target module
   already exists there; its sole declaration signature and docstring are unchanged.
   Restored its original spacing before `:=`. The other two modules are new. There are
   no definition or existing-statement changes and no change records are required.
2. Compiled all three modules in import order with lcompile.py, without errors or warnings.
   There is exactly one delivered sorry, in the reported public tensor theorem; no axioms,
   unsafe/opaque declarations, foreign implementations, or hollow definitions occur.
   Scratch copies with #print axioms show only propext, Classical.choice, Quot.sound for
   the closed-immersion bridge, and additionally sorryAx for the tensor theorem and target.
   The target therefore remains a decomposition, with net zero holes closed.
3. Read the tensor theorem and its node against the affine pullback formula, Spec residue
   field identification and right exactness. It is true: tensoring A -> B -> coker with
   kappa(p) identifies the first map with the surjective scalar map of the closed fibre,
   so the tensor cokernel vanishes. Empty fibre is allowed; a zero base ring has no point
   s; no nonempty fibre or Noetherian hypothesis is needed. This is strictly a part of
   the target argument and does not assert a neighbourhood. Its full written proof and
   node are present. The proved bridge also handles a=0 and arbitrary affine morphisms.
   Independent LeanFinder, Loogle and source searches used coordinate-ring scalar
   surjectivity, tensor cokernels, and localized module maps. They found useful building
   blocks, including Spec.fiberToSpecResidueFieldIso, but no duplicate or short direct
   replacement. Closing the remaining geometric identification needs more than a short
   repair; no further hole was added.
4. Read the proof from the target down: finite cokernel, residue tensor, Mathlib's support
   criterion, localized cokernel criterion, finite spreading, then the proved affine
   bridge. This keeps the unit sk-thm-p1 realized statements and steps, all above this
   auxiliary node; no unit route is bypassed. Removed an unused public LocalRing.Module
   import from the tensor module and narrowed the bridge's public localization import
   to LocalizedModule.Basic. Its IsLocalization import stays proof-only. Both original
   target public imports stay for its signature. No module is claimed globally pruned.
5. Checked all three node statements, Lean records, sources, proof steps and dependencies.
   Corrected the target DAG and pruning report: affine-spectrum and localization-at-prime
   definitions remain used directly by the Lean proof. The four removed direct proof
   dependencies are the affine fibre product, Spec residue identification, affine closed
   immersion criterion and principal-localization open immersion; they remain represented
   under the new nodes where needed. Recorded independent searches in the new nodes and
   made their Lean statement fields verbatim multiline signatures. The source argument
   was checked at https://stacks.math.columbia.edu/tag/04DG, final Nakayama/localization
   sentences. The new-node fields required by brief-stage3.md §3 are present.

Changes made in this reading: signature whitespace restored; imports pruned/narrowed;
DAG dependencies and pruning report corrected; new-node signatures and search evidence
updated. The proof terms and mathematical statements were retained.
