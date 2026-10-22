## What changed

The assigned theorem `FiniteFieldDerivedTensor.exists_diagonal_derived_tensor_summand`
has a complete proof from named declarations, with its original signature unchanged.
Mathlib supplies the separability element. The proof constructs tensor presentations,
proves restriction preserves representatives, lifts the ordinary sheaf retraction to
unbounded total complexes, and descends its ring action and split identities with
both required comparison squares.

This repairs the return on `a536bb87b12`. The missing unrelated upstream source is
present again, as recorded in `coord/rework-done.tsv` at `dfb3ecd2cd`; this packet
neither edits nor withdraws it. The delivery tool rebases the packet on current
`sheaf-dag`. No source-library declaration is changed.

The original interfaces are extracted into
`Sheaf.Paper.FiniteFieldDerivedTensorComparison` to avoid an import cycle. The
chain proof's expensive totalization conversion is now proved for arbitrary
categories before specialization. A canonical model contains the total functor
and its bidegree inclusions. `exists_model` is proved by the concrete Mathlib
construction, and `model_eq` fixes the entire model by equality with that
construction. Thus the model has no undetermined data. `totalFunctor_eq_mathlib`
identifies its functor with the original functor. The derived presentation uses
this proved equality explicitly; the generator uses the same fixed inclusions.
The ordinary tensor wrapper is still definitionally the original curried tensor.
All proofs of the chain retraction and its totalization stay in the chain file.
The model construction and its equality API live with the definition. The compile
limit is unchanged.

## Proved and sorry left

Closed one original hole:
`FiniteFieldDerivedTensor.exists_diagonal_derived_tensor_summand`.
Added one lower hole:
`FiniteFieldDerivedTensor.exists_separableFieldTensorSheaf`, in its own module and
node `lem-pur-separable-field-tensor-sheaf`.
This is a decomposition: one hole closed, one added, net zero. The assigned
module has zero holes. The packet has exactly one `sorry`, in that named theorem.

The lower theorem is the ordinary module-sheaf separability retraction from the
original argument, for a given separability element. It involves no complexes,
derived categories, representative choices, or finite-field hypothesis. Its
source, full proof in words, and pure-section normalizations are recorded in its
docstring and node. The chain lift, representative compatibility, algebraic
existence, presentation existence, and final descent are proved in this packet.
All definitions and private helpers are sorry-free. In particular, the canonical
model is chosen from a proved equality specification, not an unproved existence claim.

Final server validation passed with `LCOMPILE_NO_LOCAL=1` through `lcompile.py --all`:
all six packet modules and the unchanged direct importer
`Sheaf.RingTheory.FiniteAlgebraExternalTensorFiltration` compiled without errors or
warnings. The interface took 12.6 seconds, the chain proof 48.0 seconds, the assigned
proof 37.9 seconds, and the consumer 2.7 seconds. The consumer is excluded from the
delivery because its source is unchanged. The assigned signature is byte-for-byte
identical to current sources; all node JSON is valid and all Lean lines are at most
100 characters. No diagnostic heartbeat or profiler options remain.

The packet is submitted through the delivery tool for its compile, preflight and
independent review. No whole-library build was run by this worker.

## No longer needed

The finite-field Frobenius/product construction is replaced by Mathlib's
`Algebra.FormallyUnramified.of_isSeparable` and `iff_exists_tensorProduct`.
Nodes `def-weil-finite-field-q-elements` and `lem-weil-finite-field-pow-card` are
not used by this proof. Their unit-level route is not bypassed: the item's unit has
no realized statement or proof step assigned to this item.

The separate finite-basis argument making scalar extension exact is unnecessary.
Restriction compatibility instead uses all-constant-field-module flatness and
upper-truncation colimits. Consequently this proof does not need
`lem-weil-pbc-site-r-module-presheaf-sheafification-exact` or
`lem-pc-sites-sheafification-underlying-sets` for coefficient extension.
`lem-pc-kflat-resolution` is used transitively through the existing proved site
tensor-descent theorem, not through a new chosen-resolution construction here.

Removed proof imports from the item: `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`,
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
`Mathlib.CategoryTheory.Sites.PreservesSheafification`,
`Mathlib.CategoryTheory.Sites.LeftExact`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
`Sheaf.Algebra.Homology.KFlat`, `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
and `Sheaf.Algebra.Homology.KFlatCoefficientUniverse`.
The original public imports move verbatim to the interface module; none is hidden.
The underived sheaf node retains the sheaf tensor, bilinear sheafification extension,
and module sheafification dependencies. The chain node uses it together with the
existing total-bifunctor comparison and preservation of sheaf colimits. Those source
nodes are not pruned. The extracted interface retains only its needed private
`CochainTensorUniverses` import; all original public imports remain verbatim.
The chain file also drops `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
and its direct DAG dependency `lem-weil-pbc-module-sheaves-colimits-forgetful`:
`SheafOfModules.preservesColimitsOfShape_toSheaf` in the existing source sheafification
module supplies exactly the required property. This does not assert that the old
module is unreachable from other targets.
Removed direct tool_uses entries for bilinear extension and K-flat resolution;
bilinear extension remains below the chain node and resolution below site descent.
No whole module is asserted unreachable from all targets.

## Where the brief, the DAG or earlier work was wrong

The original mathematical plan is valid. Mathlib's separability criterion avoids
the longer Frobenius construction, and constant-field flatness plus truncation
colimits avoids the separate finite-free coefficient-extension argument. The
ordinary balanced sheaf retraction is a genuinely separate part of the proof;
the existing declarations do not already provide its full generator formulas.

The returned landing and previous artifact failure were infrastructure problems,
now resolved by the restored source and current published build. The current
compile additionally exposed costly conversion of chosen totalization coproducts.
The canonical model and the generic equality-transport proof address that
conversion without changing the mathematical construction or target statement.

## New nodes

`def-pur-finite-field-derived-tensor-comparison`: the extracted original comparison
interfaces and their canonical totalization model, fixed to the Mathlib construction
by proved equality of both the functor and its inclusions.

`lem-pur-separable-field-tensor-chain`: the proved lift from ordinary sheaf tensors
to unbounded total complexes, including both split identities and generator formulas.

`lem-pur-separable-field-tensor-sheaf`: the remaining ordinary balanced retraction,
with its original source and complete proof in words.

`lem-pur-constant-field-restriction-representatives`: proved using constant-field
flatness and exact filtered upper-truncation colimits.

`lem-pur-descent-split-tensor-action`: proved categorical descent of a ring action
and split retraction, with both comparison normalizations.

Change record: `coord/changes/R1-finite-field-tensor-interface.md`.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
