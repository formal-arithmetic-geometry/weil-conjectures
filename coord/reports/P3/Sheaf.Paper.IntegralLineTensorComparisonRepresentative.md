## What changed

Filled `WeilConjectures.integralLineTensorComparison_representative` in
`Sheaf.Paper.IntegralLineTensorComparisonRepresentative`, preserving its entire signature.
Private proof imports supply the existing line K-flatness/flat-term theorem,
the flat-term total tensor theorem, and the normalized scalar tensor comparison from the integral tower module.
The integral operations module is imported with `all` to use its proved private
normalization equation for maps of the actual reduction functor. The tensor-tower
module is imported with `all` for its proved private `scalarTensorTotal` helper.

The proof specializes `line_unbounded_derived_tensor` and
`kFlat_total_tensor_model` for the two K-flat/good witnesses. For each quotient,
`scalarTensorTotal` applies directly to the recorded reduction functor and its
object and map normalizations. Evaluating that natural isomorphism gives the
chain isomorphism and its scalar-one formula. Two proved private linearity helpers extend that formula to
every finite coefficient. No new public declarations, definitions, hypotheses,
or arbitrary choices from unproved existence assertions are introduced.

Updated the item's DAG proof, proof dependencies and proof origin to match this
assembly from existing declarations. The unit's statement and realized steps
are untouched. Searches used the launcher's LeanFinder, Loogle and grep, plus
repository `rg`: LeanFinder returned ordinary module flatness, Loogle did not
know the project's locally free class, and local source search found the exact
line and chain-comparison APIs.

## Proved and sorry left

Closed one original hole:
`WeilConjectures.integralLineTensorComparison_representative`
(node `lem-sf-integral-line-tensor-comparison-representative`).
Added zero holes and split off zero statements. No `sorry` remains in the
item module. This is a proof from existing library declarations, not a new
decomposition. The two private scalar-linearity helpers are proved. The complete proof compiled
on the project server in 22.5 seconds. The original signature names witnesses
`hT` and `hS` that are not used in subsequent binder types; a declaration-local
unused-variable linter setting preserves those binders verbatim.

## No longer needed

No original import was removed: the sole original public import supplies the
statement and remains verbatim. No module is withdrawn.

The item's direct proof dependencies no longer include
`lem-pur-site-restriction-module-adjunction-exact`
(`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`),
`lem-weil-pbc-independent-bounded-flat-kflat`
(`Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`), or
`lem-pur-independent-ringed-tensorator-existence`
(`Sheaf.SecSmoothPurity.CochainTensoratorExistence`). These are superseded here by
the existing line theorem and the existing chain scalar-extension comparison.
They may remain required transitively by those existing proofs; no claim is
made that their modules can be withdrawn from the library.

The direct dependency `lem-pur-kflat-total-tensor-model` is retained. The proof
uses `lem-pur-line-unbounded-derived-tensor` and
`lem-pur-integral-tensor-reduction-tower-comparison` as its other direct dependencies.

## Where the brief, the DAG or earlier work was wrong

The old plan names the normalized sheaf tensorator, but the library now has its
signed total-complex specialization with the exact coefficient tensor convention.
Using that specialization avoids reconstructing its coproduct/differential glue.
The line K-flatness and termwise flatness are also already packaged together.
The general coefficient formula still needs a genuine linearity argument:
the existing chain theorem states it at coefficient one only.

The construction treats n = 0 as the already defined first positive-power quotient;
it uses neither boundedness of P, nonzero rings, nor flatness of the quotient map.
Proof irrelevance identifies different proofs of the fixed object equality, and
the scalar-tensor helper uses both object and map normalizations of reduction.

The published cochain-model record lacks the pointwise field present in the
readable source, and its private reduction-map normalization has a different
slice-parameter interface. The proof avoids unpacking the record and uses the
common normalization application supported by both interfaces. The existing
ordinary-functor scalar-tensor helper gives precisely the needed comparison.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
