## What changed

Proved `AlgebraicGeometry.Etale.residue_tor_amplitude_test` in the assigned module, with
its original signature and residue-module construction unchanged. The proof computes
nilpotence and maximality of the quotient uniformizer ideal and applies the existing
categorical residue criterion on the small etale site. It converts both standard
t-structure bounds to the explicit homology vanishing in the statement. Only the
proof imports of the existing generic sheaf lemmas and the étale Tor-amplitude comparison
were added; public imports are preserved.
The theorem docstring and its DAG proof now describe this route. A local instance-priority
annotation keeps the quotient ring on the same `CommRing.toRing` path as the generic
criterion, avoiding repeated unfolding during kernel checking. Local braiding priorities
also match the existing étale derived tensor construction. These local annotations are
recorded in `coord/changes/residue-tor-instance-path.md`; they export no instance changes.

The route uses three already implemented source declarations which had no DAG attachment.
Their new nodes attach the existing declarations; they add no Lean files or obligations.
The unit record attaches no nodes to its statement or proof steps, so no unit-level
route is bypassed.
The pro-etale-named imported module contains site-general lemmas; its pro-etale theorem
is never used, and there is no site comparison.

On resumption, checked the retained proof against the current sources, including the
landed `H2-coefficient-extension-ring-instance` repair. Preserved the current source's
public imports instead of restoring the older constructibility wrapper import.
The resumed delivery dry run compiled the proof and passed preflight and the axiom probe.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Etale.residue_tor_amplitude_test`
(node `lem-exc-residue-tor-test`). Added 0 holes; split off 0 statements.
No `sorry` remains in any delivered Lean file.

The coefficient construction and all public statements are unchanged. The proof works
for an arbitrary K and retains the original bounded constructibility hypothesis.
The generic criterion does not require a<=b, and its zero-object induction covers the
empty interval and empty-site cases. At n=1, the same maximal-ideal and nilpotence
calculations apply. Tensor monicity uses vector spaces over A/(r) sectionwise, rather
than asserting that the sections of its constant sheaf are a field.

## No longer needed

Removed proof imports:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
- `Mathlib.CategoryTheory.Sites.Abelian`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.Algebra.Homology.HomologySequence`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldTensorCohomology`

The following original proof dependencies are not required as separate statements by
this proof (other consumers can still require them):

- `lem-weil-valued-dvr-finite-quotients`
- `def-weil-pbc-constant-sheaf`
- `lem-weil-pbc-site-module-presheaf-sheafification-exact`
- `lem-pc-kflat-resolution`
- `lem-exc-constant-field-sheaf-tensor-cohomology`
- `lem-pc-sites-module-sheafification-tensor`
- `def-pur-sheaf-tensor-product`
- `def-pc-flat-sheaf-modules`
- `lem-weil-pbc-complex-ses-homology-long-exact`

The categorical criterion supplies the K-flat calculation and finite-filtration
induction in the actual `Sheaf (ModuleCat A)` encoding. Thus the separate
`SheafOfModules` K-flat, tensor/cohomology and sheafification bridges, and the
explicit long-exact-sequence proof modules are unnecessary here. The original DVR
finite-quotient leaf is also unnecessary: maximality follows directly by mapping
the uniformizer ideal, and nilpotence follows directly from the quotient definition.
All obsolete top-level tool approvals except the DVR theorem are removed.
No statement module is withdrawn; the construction remains needed by its consumers.

## Where the brief, the DAG or earlier work was wrong

The original plan overlooked the existing proved categorical residue criterion and
the site-general cokernel and tensor-monomorphism lemmas. Their declarations are in
source modules under `WeilConjectures`; despite one module's name mentioning ProEtale,
the helper hypotheses permit any essentially small site and apply to T.smallEtaleTopology.
No mathematical statement was changed and no definition repair was needed.

Searches: LeanFinder returned standard t-structure and projective-Tor results;
Loogle returned unrelated residue-field group facts; LeanSearch returned ordinary Tor
functors; Mathlib grep found no matching residue criterion. Direct library rg found
the existing implementation. Direct DAG rg found no node attached to any of the three
reused declarations. Source signatures and complete implementations were read.

## New nodes

`lem-exc-categorical-nilpotent-residue-test` attaches the existing
`DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor_singleFunctor`.
Its hypotheses and conclusion are categorical and independent of the site.

`lem-exc-constant-quotient-sheaf-cokernel` attaches the existing
`CategoryTheory.Sheaf.constantSheafQuotientIsoCokernel`, which identifies the
constant scalar quotient with the cokernel of the scalar on the tensor unit.

`lem-exc-residue-sheaf-tensor-monomorphism` attaches the existing
`CategoryTheory.Sheaf.mono_whiskerRight_of_smul_id_eq_zero`, using the
field quotient and sectionwise split monomorphisms. All three nodes record
complete proofs in words and the searches actually performed. The local elaboration
annotations are documented in `coord/changes/residue-tor-instance-path.md`; no mathematical
definition, statement, or public import changed.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
