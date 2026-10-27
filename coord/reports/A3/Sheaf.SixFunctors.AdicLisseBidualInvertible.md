## What changed

Proved `AlgebraicGeometry.ProEtale.isIso_adicNativeBidual_of_isLisse` in
`Sheaf.SixFunctors.AdicLisseBidualInvertible`, with its signature unchanged.
All new helpers are private and completely proved. The public imports are unchanged.
Added proof imports for `AdicModuleSliceHomComparison`, the source presheaf bidual
calculation's sum lemma, finite-free section coordinates, and conservative pro-etale restriction.
No existing module besides the item was changed; no shared interface was changed.

The proof first constructs the dual and double-dual comparison isomorphisms from
`homIso` and `unitIso`. The supplied bidual/evaluation normalization identifies the
transported native map with evaluation on each further slice. The finite dual-basis
calculation gives its inverse on a finite-free chart: a bidual section Psi is evaluated
at the finite sum of Psi(c_i) times the basis sections. The total-coordinate equation
proves both bijectivity assertions, including the empty-coordinate case. Reflection
through the comparison gives local native invertibility. Finally `bidual_slice` and
the proved conservative restriction theorem give global invertibility on the lisse cover.
This keeps the unit's finite-free evaluation and locality argument.

Validation: the complete module compiled through lcompile.py in 23.9 seconds, with
no warnings and no textual sorry. Delivery also runs the declaration/axiom probe.
Searches: LeanFinder on locally finite-free evaluation found only free-module maps;
Loogle found `Module.IsReflexive.of_finite_of_free`, which concerns ordinary modules;
source rg found the comparison, sectionwise biduality, and cover-conservativity proofs.
The latter two supplied the coordinate and locality arguments used here.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.isIso_adicNativeBidual_of_isLisse`
(node `lem-sf-adic-lisse-bidual-invertible`).
Added 0 holes; split off 0 statements. There are no sorry declarations in the delivery.
The proof uses the existing `adicModuleSliceHomComparison` declaration and its
recorded dependencies as intended by stage 3; it does not prove those dependencies.

## No longer needed

The planned dependency `lem-sf-locally-free-sheaf-evaluation-biduality`, module
`Sheaf.Algebra.Category.ModuleCat.Sheaf.LocallyFreeEvaluationBiduality`, is not
needed by this proof. It was not imported originally and has not been added.
Its finite dual-basis argument is proved privately in the required site universes,
and the existing source conservative-restriction theorem supplies locality.
The corresponding edge was removed from this item's proof_deps and proof steps.
The comparison and native-bidual dependencies remain needed.
No original public import was removed, no Lean module was withdrawn, and no
source-library declaration was removed or changed.

## Where the brief, the DAG or earlier work was wrong

The suggested direct application of `locallyFreeEvaluationBiduality` (and the
source `SheafOfModules.isIso_bidual`) does not fit this site's universes:
they require `C : Type v` with `Category.{v} C`, whereas `X.ProEt` has objects
in `Type (u+1)` and morphisms in `Type u`, and coefficients and modules in `u+1`.
The first compiler run confirmed that mismatch. The proof therefore generalizes
the source's finite-coordinate computation privately, accepting a linear map with
the actual evaluation formula instead of defining another bidual object.
No statement or definition was weakened or changed. The item's DAG proof now
records the implemented normalization, finite-coordinate calculation and locality.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
