## What changed

Filled `AlgebraicGeometry.ProEtale.padic_constant_local_model_tor` in
`lean/Sheaf/Paper/PadicConstantLocalModelTor.lean`, preserving its statement and public
imports. The proof stays in the internal-module category. Private helpers evaluate scalar
rings at the profinite point, produce finite free scalar models over fields and finite
free kernels over PIDs, transport the exact scalar realization, compute the two-term
mapping-cone Tor bound, and descend it over the given pro-etale cover. The algebraic
closure case uses precisely finite-subextension-valued functions: evaluation at a point
is the full algebraic closure because each individual algebraic element lies in a finite
subextension. Neither compactness nor a Noetherian assumption on the scheme is added.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.padic_constant_local_model_tor`.
No holes added, no split-off statements, and no remaining `sorry` in the delivery.
The final import-pruned module compiled without errors or warnings in 37.9 seconds.
`#print axioms` reports `propext`, `Classical.choice`, `Quot.sound`, and inherited
`sorryAx`: existing derived inverse-image tensor comparisons under
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` still contain holes.
Thus this closes this item's declaration from existing stated dependencies; it does not
claim that its full transitive dependency closure is axiom-clean.

## No longer needed

No original public import is removed. The planned independent section-module scalar
resolution (`lem-sfb-scalar-model-finite-flat-resolution`,
`Sheaf.Paper.ScalarModelFiniteFlatResolution`) and its internal-model resolution wrapper
(`lem-sfb-finite-constant-model-two-term-free-resolution`,
`Sheaf.Paper.FiniteConstantModelResolution`) are not imported: a kernel of a finite free
presentation over a PID, followed by exact scalar realization and the generic bounded-flat
Tor theorem, suffices directly. The planned sectionwise local detection
(`lem-sfb-tor-interval-local-detection`,
`Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection`) is not imported: restriction
of internal derived tensor and the proved cover zero-detection helper give the bound
without changing encodings. These are dependencies pruned from this item's proof;
no files or declarations are withdrawn. The proof import
`Sheaf.Paper.ConstantToContinuousScalarFlat` was also removed: its argument is specialized
to the original coefficient universes in a proved private helper; its public lemma is not used.

Redundant direct proof imports removed (their declarations remain available through
the imports actually needed):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat`
- `WeilConjectures.CategoryTheory.Monoidal.Dualizable`
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `Mathlib.LinearAlgebra.FreeModule.PID`
- `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`
- `Mathlib.RingTheory.Flat.TorsionFree`
- `Mathlib.RingTheory.Flat.EquationalCriterion`
- `Mathlib.CategoryTheory.Sites.LocallySurjective`

## Where the brief, the DAG or earlier work was wrong

The declared scalar-resolution statements use a different module encoding from this
item. Their resolution data alone do not provide the comparison with the internal
scalar-extension local model. Staying internal avoids those comparisons. The existing
constant-to-continuous flatness lemma ties the coefficient carrier's universe to the
site's universe, whereas this item's original coefficient rings live in Type 0 and its
site has arbitrary universe. Its torsion-free/local-relation proof is specialized here
as a proved private helper with those universes independent. The source-library
signatures and bodies are unchanged. The unit record has no realized steps to bypass.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
