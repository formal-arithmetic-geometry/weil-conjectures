## What changed

Filled the scalar-model comparison by explicit forward and backward maps on scalar
constant generators, using the ordinary scalar-extension adjunction for the backward
map. The scalar-tower comparison remains the specified existing isomorphism.

Constructed the natural immersion comparison from inverse image and scalar-extension
adjunctions, the natural square of continuous coefficient maps, and scalar towers.
Its formula retains the original pulled-back pure tensors and localization unit.

The specified-presentation theorem remains an original hole. Its candidate proof
constructs the ordinary and sheaf cokernels and transports the supplied matrix normal
form, including empty matrices and zero tail rank, but did not pass the file compilation
limit. That unfinished candidate and its private presentation helpers are omitted from
the delivery.

For each chosen local integral model, rationalization is finite dimensional over the
coefficient field. Transport a finite basis to a finite free sheaf, retaining the given
covering object. Finally compare the continuous/lattice coefficient presentations to
supply rational constructibility on the given finite stratification and covers.

All original public signatures, definitions and public imports are unchanged.
The cached sheafification instances and local transparency settings control elaboration;
the essentially-small sheafification fallback is disabled inside this module to avoid
repeating that inference. All retained helpers are private and proved. No source-library file was changed.
The node proof and dependencies describe this route. Private scalar comparison and scalar-tower helpers are proved over an abstract site
and then specialized. The immersion comparison is assembled as a natural isomorphism,
so its naturality follows directly from its construction. Cached
ring sheafification instances prevent repeated inference through concrete continuous
coefficient sheaves; no public construction is changed.

## Proved and sorry left

The original five holes are in
`AlgebraicGeometry.ProEtale.RationalStratum.scalarModels`, `immersionComparison`,
`presentationModels`, `chosenLocalModel`, and `rationalStratumFiniteFreeModel`, all
attached to `lem-per-rational-stratum-finite-free-model`.

Closed four original holes: `scalarModels`, `immersionComparison`,
`chosenLocalModel`, and `rationalStratumFiniteFreeModel`.

The one remaining `sorry` is
`AlgebraicGeometry.ProEtale.RationalStratum.presentationModels`, attached to
`lem-per-rational-stratum-finite-free-model`. Its original signature and mathematical
content are unchanged. There are zero holes added elsewhere, no split-off statements,
and every retained private helper is proved.

The four-proof candidate compiled successfully through `lcompile.py` in 53.6 seconds.
The final packet also removes unused presentation-only proof imports and helpers.
Compilation and delivery validation for that cleaned packet are recorded by the tools.

## No longer needed

Removed these proof imports and their planned proof dependencies:

- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`
  (`lem-pc-sites-module-sheafification-tensor`): the scalar comparison is constructed
  directly from constant-generator universal properties and ordinary scalar extension.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
  (`lem-pc-sites-sheaf-tensor-bilinear-universal`): the same direct construction supplies
  its inverse identities.
- `Sheaf.AlgebraicGeometry.ContinuousFieldMatrixElimination`
  (`lem-weil-pbc-continuous-field-matrix-elimination`): a finite basis of the ordinary
  rationalization gives local finite freeness directly. The retained presentation plan proves its normal-form clause for supplied invertible
  matrices and therefore does not require existence of matrix elimination.
- `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`
  (`lem-weil-pbc-independent-sheaf-tensor-colimits`): scalar extension preserves
  cokernels by its explicit adjunction.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
  (`lem-weil-pbc-ringed-topoi-module-pullback-tensor`): overFunctor and scalarOverIso
  retain the specified slice.
- `Mathlib.LinearAlgebra.TensorProduct.RightExactness`
  (`lem-weil-pbc-tensor-right-exact`): ordinary scalar extension preserves the
  specified cokernel by its adjunction.

Removed unused proof-only imports of the tensor Pi calculation, module kernels and
cokernel-preservation tactics after omitting the unfinished presentation candidate.

Removed the corresponding five obsolete top-level tool approvals from this node;
there was no approval for the last Mathlib dependency. These are dependencies pruned
from this item's proof, not module withdrawals. Existing upstream declarations and
other consumers are preserved.

## Where the brief, the DAG or earlier work was wrong

No false public statement was found. The planned use of continuous matrix elimination
on a point is unnecessary for the local freeness conclusion: an ordinary finite basis
suffices after the scalar comparison. The specified-presentation clause nevertheless
requires its matrix cokernel and coordinate calculation; that original hole remains. The
full candidate exposed expensive definitional conversion between scalar-extension
functors and in the cokernel quotient equation. The retained immersion proof avoids
the first issue by constructing the entire natural isomorphism before taking components.

The public inverse-image scalar comparison is stated for an isomorphism of schemes;
its proved private adjunction construction and unit equation work for arbitrary maps.
The immersion proof uses that construction and proves the required normalization
without adding an isomorphism hypothesis to the scheme immersion.

The unit record `sk-p-dl-a1-perverse` realizes its own two target statements and proof
steps in `thm-a1-curve-perverse-heart` and `thm-a1-fourier-t-exact`; this item's internal
route change does not bypass those statements or steps. New dependencies are generic
scalar/constant-module, slice, and coefficient-transport tools, not perverse results.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
