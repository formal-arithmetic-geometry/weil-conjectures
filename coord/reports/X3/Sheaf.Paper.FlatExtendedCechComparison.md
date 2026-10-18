## What changed

Kept the statement and public imports of `Sheaf.Paper.FlatExtendedCechComparison` unchanged.
Its proof now constructs the natural transformation of finite Koszul stages and uses the
proved general theorem that exact filtered colimits preserve quasi-isomorphisms.
Restriction of scalars preserves coproducts and sequential colimits, proved through the
faithful forgetful functor to abelian sheaves. The empty-family case is proved from the
cokernel comparison equation, and degrees outside [0,r] are handled by zero objects.

Added `Sheaf.Paper.FlatLocalizationKoszulHomotopy`. Its theorem
`SheafOfModules.LocalizationCech.koszul_ideal_power_annihilates_homology` proves the full signed
removal contraction, constructs a null-homotopic scalar endomorphism, and identifies its
homology map with sectionwise scalar multiplication on the cohomology sheaf. The sign cancellation is
proved for both orders of two distinct indices; no annihilation assertion is assumed.
A finite-set induction using the ideal supremum power inequality then proves annihilation
by the uniform positive power r*(n+1)+1 of each sectionwise generated ideal. This step is
proved even for r=0, and makes no assumption that sections preserve cohomology.

Added `Sheaf.Paper.FlatLocalizationKoszulCohomologyComparison` for the remaining finite-stage
flat torsion tensor data in a single degree. Also proved the exact-functor homology
naturality step: the induced homology map of the tensor unit transformation is invertible
because its conjugate by the canonical exact-functor homology isomorphisms is invertible.
The finite complex factorization then gives the desired stage homology isomorphism.
Updated the parent DAG proof to match these
arguments and added the two corresponding nodes. No existing definition or signature
changed and no existing consumer needs adaptation.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.flat_extendedLocalizationCech_comparison_quasiIso`
(node `lem-weil-pbc-flat-extended-cech-comparison`). Its proof is complete from the stated
intermediate theorem and the fully proved annihilation theorem.

Added exactly one hole:
`SheafOfModules.LocalizationCech.flat_koszul_tensor_comparison_data`
(node `lem-weil-pbc-flat-localization-koszul-cohomology-comparison`).
This is a decomposition: one upper hole closed, one lower hole added, net zero holes.
It remains to formalize the tensor comparison for module sheaves annihilated by a positive
ideal power, its induction through short exact sequences, and the finite free tensor
complex isomorphism compatible with `comparisonStage`. The exact-functor homology step
is proved in the item, rather than deferred. The remaining theorem is
restricted to r>0 and 0<=q<=r, and takes the already-proved uniform ideal-power annihilation as an input.
Its docstring and node give the complete sheaf-theoretic argument and sources.

`SheafOfModules.LocalizationCech.koszul_ideal_power_annihilates_homology`
(node `lem-weil-pbc-localization-koszul-contractions`) has no holes.
The delivery leaves no `sorry` in the item module, no private hole, and no data definition
with a hole. Existing holes in imported declarations are unchanged.

Validation: single-file server compiles and the sandbox import-order compilation are used;
the final delivery dry run performs the required independent mechanical checks.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`: retired re-export; use the
  already proved source theorem in `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: the proof uses the stated `IsFlat`
  directly through the finite cohomology comparison; no second flatness definition is used.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`: the fixed universe of
  the item uses the established `monoidalCategory R`; no universe-extension tensor is used.
- `Sheaf.CategoryTheory.RingedSiteModules`: already public through `ExtendedLocalizationCech`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`: already public through the
  proved generic exact-colimit/quasi-isomorphism modules.

The project modules removed from this item's entire import closure are exactly
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`, and
`Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.

Removed the parent proof-dependency entries `def-pc-quasi-iso-modules`,
`def-weil-sheaf-of-modules-category` and `def-weil-abstract-derived-category`: these
interfaces remain statement dependencies, but their constructions are not additional
steps of this proof. The tensor definition node `def-pur-sheaf-tensor-product` is used by
the finite tensor lemma rather than directly by the parent. Flatness remains a direct
parent proof dependency because it supplies the exactness instances there.

The parent no longer needs a separate localization/tensor construction or a proof of the
Koszul-to-Cech colimit identification: `LocalizationCech.complex` is that colimit by its
existing definition. The existing finite-stage definitions and transition maps remain used.
The exact-functor cohomology lemma remains needed directly by the parent, through
`NatTrans.app_homology`. The generic
module-sheaf colimit and abelian-sheaf exactness nodes remain needed. No blueprint unit or
its realized statement/steps is bypassed, and no existing DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The fixed-universe item statement uses the existing `SheafOfModules.IsFlat` from
`Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`. The current flatness node also records the
independent-universe `IsFlatOnSite` interface. This proof uses exactly its given `IsFlat`
hypothesis and its two exactness fields, and assumes no comparison with `IsFlatOnSite`.

No statement dispute. The old node called the concrete Koszul corollary Tag 0626;
the local Stacks tag table identifies the abstract homotopy identity as 0626 and the
concrete annihilation corollary as 0663. The new proof cites both correctly.

The declaration's finite signed Koszul contraction and sheaf torsion
tensor comparison were prose steps in the original node, rather than separately stated
Lean lemmas. The former is now proved explicitly. The latter is the one remaining node.
The original plan's localization comparison and fraction-cocone construction do not need
to be rebuilt here because the existing interface defines the extended complex as the
sequential Koszul colimit. Ordinary-ring torsion base change from the source library does
not directly prove the missing assertion on an arbitrary site: neither enough points nor
sectionwise exactness of sheaf tensor products may be assumed.

## New nodes

`lem-weil-pbc-localization-koszul-contractions` is the proved sheaf Koszul scalar-annihilation
statement. Its proof uses signed subset removal, Mathlib's null-homotopic-map construction,
naturality of sectionwise scalar multiplication on cycles and homology, and finite-set
induction into the section module annihilator ideal. It applies to every r, n and integer
degree, with the uniform positive exponent r*(n+1)+1.

`lem-weil-pbc-flat-localization-koszul-cohomology-comparison` is the remaining fixed-degree
flat torsion tensor data. It excludes the empty-family and zero-term cases already
proved in the item. It states invertibility of the explicit tensor unit transformation on
one cohomology object and the compatible finite free tensor complex isomorphism. It states
neither the homology comparison nor the colimit comparison nor the annihilation result.
Its proof follows Tags 099H, 0GLY and 05E9; sheaf quotients and sheaf tensor products are used
throughout, avoiding an invalid reduction to sectionwise quotient isomorphisms.

The change record `coord/changes/X3-flat-extended-cech-proof-opens.md` documents the
file-local namespace opens required by the private proof helpers. The checker conservatively
classifies those command changes as an interface change. Existing public signatures,
definitions and imports are unchanged, and no consumer needs adaptation. All additional
public declarations are in new modules with new nodes.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
