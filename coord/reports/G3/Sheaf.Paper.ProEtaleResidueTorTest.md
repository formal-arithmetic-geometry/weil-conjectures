## What changed

Replaced the sorry in `Sheaf.Paper.ProEtaleResidueTorTest` by a complete Lean argument
from the declared K-flat resolution theorem and the new ordinary field-module tensor lemma.
The existing public theorem's signature and visibility are unchanged. No existing definition
or statement was changed, and no consumer adaptation is needed.

The proof establishes tensor-homology independence of K-flat representatives using mapping
cones, a resolution of the other factor, and localization at quasi-isomorphisms. It compares
total tensor with a module in degree zero to ordinary termwise tensor. It proves a general
nilpotent-natural-endomorphism induction using images and cokernels, then applies the
homology exact sequence to tensor with a flat-term resolution. The coefficient uniformizer
is proved nilpotent in the quotient and its image generates a maximal ideal. The argument
supplies every representative and resolution quantified over by Tor amplitude.

Added and proved
`PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses` in
`Sheaf.Paper.ProEtaleSheafificationTensorComparison`. It is the tensor/sheafification
interface needed by the remaining field-node proof, with site object universe u+1,
Hom universe u, and coefficient/module universe u+1. The proof constructs the
comparison and inverse through bilinear extension and proves their naturality; it
contains no sorry.

Added `Sheaf.Paper.ProEtaleResidueModuleTensorHomology` for precisely the one-degree field
calculation in the original proof's step 3. Updated the parent DAG proof to match the Lean
argument. The unit has no realized entries that this route bypasses.

## Proved and sorry left

Closed the original syntactic hole:
`AlgebraicGeometry.Scheme.proEtale_torAmplitude_iff_residue_tensor`
(node `lem-sf-proetale-residue-tor-test`). Its proof contains no sorry. All private helpers
in that module are proved.

Added one hole:
`AlgebraicGeometry.Scheme.proEtale_residue_module_tensor_homology`
(node `lem-sf-proetale-residue-module-tensor-homology`). Its proof is exactly `by sorry`.
It still needs to construct the residue-field complex and factored module, and to
transport vanishing through scalar restriction and the balanced tensor associativity
maps. The tensor/sheafification comparison in the required universes is now proved in
the other new module. The existing declared node
`lem-exc-constant-field-sheaf-tensor-cohomology` supplies the field cohomology/tensor
identity; its recorded module is absent from this read-only source snapshot. This
existing declaration should be used when implementing that step, rather than restating
its cohomology theorem. The new obligation's source and complete proof in words are
in its docstring and node. It is a strictly smaller
part of the original argument: one ordinary tensor degree, arbitrary complex, arbitrary
principal field quotient; no K-flat resolution, derived representative, nilpotence,
filtration, constructibility or amplitude interval.

The additional public theorem
`PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses`
(node `lem-sf-proetale-sheafification-tensor-comparison`) is proved and adds no sorry.

This is a decomposition of the assigned hole: one original hole closed and one new
hole added. The delivery adds no other hole; the closure ledger separately accounts
for any removed dependencies. It is not reported as a completed proof of the residue criterion. Edge cases checked include
zero modules and complexes, unbounded complexes, arbitrary integer degree, and the empty
scheme. Maximality excludes the zero quotient ring.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.Algebra.Homology.KFlatResolutionGeneral`: use the node's declared independent
  coefficient API, `KFlatResolutionIndependentCoefficients`, instead.
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`: the field calculation
  is isolated in the new node, so the main proof does not use this directly.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`: the main proof uses
  the recorded monoidal category directly; no scalar-extension construction is needed.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: use the flat-term resolution's
  exact-functor conclusion directly.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`.
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`.
- `Mathlib.CategoryTheory.Sites.Abelian`.
- `Mathlib.CategoryTheory.Sites.Sheafification`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
- `Sheaf.Algebra.Homology.DerivedTensor`: already public through the statement imports.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`: this is a different
  module-sheaf encoding and supplies no necessary step of the final proof.

Removed the parent's direct proof dependencies and top-level tool-use entries
`lem-pc-sites-module-sheafification-tensor` and
`lem-weil-pbc-site-module-presheaf-sheafification-exact`. The equal-universe tensor comparison is replaced by the proved new comparison;
the exact-sheafification argument is packaged in the existing constant-field
tensor/cohomology node. These are not claimed globally pruned. The remaining
tool-use entries retain their original order. The existing equal-universe tensor bilinear universal-property declaration is also
unneeded as a black box: the new comparison constructs its required instance of the
universal property directly from sheafification and sectionwise tensor. A read-only import-closure comparison additionally finds these seven modules absent
from this item's new transitive import closure: `Mathlib.CategoryTheory.Abelian.FunctorCategory`,
`Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`,
`Sheaf.Algebra.Homology.KFlatResolutionGeneral`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`,
`WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex`, and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`.
No module is withdrawn or claimed unreachable from all other targets.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan does not give the required Lean glue for
independence of the arbitrary K-flat resolution and representative in the target's Tor
amplitude definition; that glue is now proved explicitly.

The source library has a proved residue criterion for fixed-ring module sheaves, whereas
this item's unchanged signature uses intrinsic modules over a constant ring sheaf. These
encodings require a tensor-compatible comparison. The recorded tensor/sheafification
comparison also specializes the site object, Hom and coefficient universes to coincide;
the pro-etale site's object and Hom universes differ. The remaining field node records the
comparison and exactness argument rather than asserting that section rings of the constant
field sheaf are fields. The DVR declaration `Padic.extension_integers_dvr` is additionally used as a generic tool
to identify the recorded maximal ideal and prove maximality after quotienting; no node of
the localization unit supplies this coefficient-ring fact. Its tool-use approval, if
required, is left to the maintainer. No target signature was weakened and no arbitrary data was chosen
from an unproved existence theorem.

## New nodes

`lem-sf-proetale-residue-module-tensor-homology`, in
`dag/nodes/sec-smooth-purity/`, isolates the ordinary residue-field calculation used by the
main proof. Its module is `Sheaf.Paper.ProEtaleResidueModuleTensorHomology`; its three kinds of
Mathlib search, sources, edge cases, proof and exact Lean statement are recorded in the
node. The command-scaffolding change record is
`coord/changes/proEtaleResidueTorTest-private-proof-scaffolding.md`. The scanner flags
new local proof commands; the record confirms the unchanged public interface and the
absence of downstream consumers. No existing definition or statement changed.


`lem-sf-proetale-sheafification-tensor-comparison`, also in
`dag/nodes/sec-smooth-purity/`, is proved in
`Sheaf.Paper.ProEtaleSheafificationTensorComparison`. It supplies the actual natural
tensor comparison, including its canonical pure-tensor normalization, in the site
universes required by the new field node. The node records all three kinds of
Mathlib search and the Stacks universal-property proof. It adds zero holes.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
