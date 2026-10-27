## What changed

Preserved the exact signature and all public imports of
`AlgebraicGeometry.ProEtale.supported_image_torsion_reductions_cohomology_vanishes`.
The module now also proves `supported_finite_image_cohomology_vanishes`, a separate
finite-coefficient part of its conclusion. It uses the actual abelian image and the
actual path extension and inverse image. It needs no prime-power annihilator or
affineness of X: a module over any finite ring is torsion.

The private helper `torsion_cd_proAffineEtale` unpacks the stated pro-affine-etale
presentation, installs affine and etale instances for its stages, and applies the
existing affine-transition limit theorem. The finite theorem then obtains a torsion
etale antecedent, transports derived sections, converts q>d to a positive natural
degree, applies torsion dimension, and transports the zero object along homology.
This Lean assembly is complete; it does not call the original holed theorem.

Added `ClassicalInternalModuleSections` and `SupportedFiniteImageClassicalOrigin`,
each with one public named obligation, its source, proof in words and DAG node.
These separate scalar-forgetting/classical derived evaluation from finite-image
classicality and support transport. They contain no geometric dimension estimate,
no integral reductions and no hidden definition holes.

The original docstring and DAG now expose the invalid integral step rather than
continuing to present it as an applicable proof. No existing declaration, definition,
instance or target signature changes. No source-library file changes, consumer
adaptations or statement-change record is needed. New public theorems are additive.

Compilation: `lcompile.py --all` compiled the finite assembly and both new modules.
The first delivery compile also compiled the final three-module packet; its sole
docstring-spacing linter warning was repaired before repeating delivery. The earlier separate finite module was
folded into the item itself; it is not part of this delivery.

## Proved and sorry left

Original holes closed: **0 of 1**. This is partial finite-branch work, not a proof
of the original conjunction and not net sorry reduction.

Proved, relative to the two new comparison obligations:
`AlgebraicGeometry.ProEtale.supported_finite_image_cohomology_vanishes`
(node `lem-sfb-supported-finite-image-cd`). Its dimension-limit and final zero-object
assembly are Lean proofs. The private `torsion_cd_proAffineEtale` has no sorry.

Every remaining hole (three total in the delivered Lean files):

- `AlgebraicGeometry.ProEtale.supported_image_torsion_reductions_cohomology_vanishes`
  (`lem-sfb-supported-image-torsion-reductions-cd`): the original hole is retained
  whole, with its signature unchanged, because the unrestricted integral route is
  unresolved. The new finite theorem isolates the valid finite portion.
- `AlgebraicGeometry.ProEtale.classical_internal_module_sections`
  (`lem-sfb-classical-internal-module-sections`): added hole. Assemble internal/section
  equivalence, forgotten-injective evaluation acyclicity, bounded-below classical
  comparison and Leray into the stated derived-object isomorphism.
- `AlgebraicGeometry.ProEtale.supported_finite_image_classical_origin`
  (`lem-sfb-supported-finite-image-classical-origin`): added hole. Assemble finite
  local-model encoding, classical descent and weak Serre closure, exact support-path
  transport and arbitrary pullback; descend the finite-ring annihilator.

Thus two holes are added, neither inside a definition. Neither is a restatement:
the first has arbitrary commutative coefficients and an explicitly supplied classical
underlying sheaf but no supported image or bound; the second constructs a torsion
antecedent but asserts no cohomology vanishing. Their combination with the proved
limit argument gives the finite clause. No arbitrary data is defined by choosing a
witness from either unproved theorem; the witnesses are used only in theorem proofs.

## No longer needed

Removed the following original private proof imports from the item:

- `Sheaf.AlgebraicGeometry.ClassicalModuleWeakSerre`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.Paper.FiniteDiscreteScalarConstantModels`
- `Sheaf.Paper.PrincipalReductionConeCalculus`
- `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.CategoryTheory.Sites.UnboundedLeraySections`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`
- `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`

Replaced them with proof imports of the two comparison obligations and the affine
limit dimension theorem. The finite proof uses dimension of U directly, so it does
not need an additional colimit-of-cohomology calculation over its affine presentation.
The origin and evaluation dependencies have moved into the corresponding new nodes.

No module is withdrawn. No integral dependency is claimed globally pruned: its old
route remains a recorded unresolved mathematical obligation. In particular, the
principal cone, integral DVR, truncation and Leray nodes may still be needed by a
valid future integral argument. Removing unused proof imports from a holed theorem
is not counted as mathematical progress or source-library pruning.

## Where the brief, the DAG or earlier work was wrong

The old item docstring said its step-5 local comparison was not yet stated in Lean.
It is now stated as `supported_image_koszul_comparison_nonpositive`, but its reviewed
statement requires `[CompactSpace S] [IsLocallyNoetherian S]`. The current parent has
no locally Noetherian hypothesis. The path's geometric finiteness does not imply it.

STATEMENT-DISPUTED: the original integral proof route needs re-review. The Q09 report
`coord/reports/Q09/lem-sfb-supported-image-koszul-comparison-nonpositive.md` explicitly
refutes the old unrestricted local relative nonpositivity assertion and names this
parent as a broken citer. Its example is multiplication by the continuous function
2^m (zero at infinity) on a rank-one integral model on the affine scheme of eventually
constant rational sequences. This produces a positive comparison direct image.
It refutes the local prerequisite, not necessarily global vanishing above d.
No counterexample to the parent's global conclusion is claimed here.

I read HRS Section 8, condition (8.1) and Lemma 8.6 in the local PDF: the latter
uses hearts of constructible complexes and its stated geometric hypotheses. It
does not assert this arbitrary-image local prerequisite. Applying classical
comparison to a nonclassical integral image quotient would not repair the proof.
Accordingly I did not add a purported unrestricted nonpositivity theorem, silently
assume Noetherianity, weaken the parent or reuse the refuted statement as a hole.
The finite proof is unaffected by this error, because finite discrete local models
and their images are classical without Noetherianity.

The new nodes remain below `sk-prop-sf-comp-coherence`; no UNIT statement or realized
step is bypassed. Searches covered the whole blueprint and the source library.
The existing module/abelian evaluation comparison is degreewise, while the new
lemma assembles a derived-object comparison with internal coefficients and a
specified underlying classical sheaf; the finite-origin lemma adds the actual-image
and path transport to the existing separate classicality interfaces.

## New nodes

`lem-sfb-classical-internal-module-sections`, in
`Sheaf.Paper.ClassicalInternalModuleSections`: the derived sections comparison for
an internal module with a specified classical underlying abelian sheaf. It is a
scalar-forgetting and bounded-below comparison assembly, not a dimension estimate.

`lem-sfb-supported-finite-image-classical-origin`, in
`Sheaf.Paper.SupportedFiniteImageClassicalOrigin`: the classical torsion antecedent
of an actual supported finite-coefficient image, after any inverse image. Its
proof plan reuses the parent's finite classicality/support steps and records
zero rings, empty paths and schemes, zero maps and unrelated local-model covers.

`lem-sfb-supported-finite-image-cd`, attached to the proved finite theorem in the
item module: the two preceding comparisons plus the affine-limit dimension bound
and the integer/natural degree conversion. Its finite coefficient statement is a
strict part of the parent's conjunction. All three nodes inherit chapter, unit
and blueprint ancestor. No change record (existing signatures unchanged).

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
