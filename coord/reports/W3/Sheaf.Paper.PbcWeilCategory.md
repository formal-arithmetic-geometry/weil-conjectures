## What changed

Fill `WeilConjectures.weilScalarAssociator_exists` by a private proved categorical
lifting lemma. Lift each coefficient associator with `Algebra.isoMk` and
`ObjectProperty.isoMk`. The rational scalar/automorphism compatibility square,
followed by naturality of the coefficient associator at the structure arrow,
proves the Weil commuting equation. Underlying naturality gives the natural
isomorphism. Equality of underlying components proves its uniqueness.

Import `Sheaf.Paper.PbcRationalAutomorphismScalarCoherence` privately. Its existing
DAG attachment is `lem-sf-pbc-rational-automorphism-coherence`. That module's source
and compiled object were absent from the current checkout/build, although its node
and the parent proof dependency remain. Restore exactly its recorded public theorem
statement, with the existing source and full proof in words. This is the genuine
coefficient compatibility obligation, strictly below the Weil lift: it quantifies
only over coefficient objects and assumes no Weil structure or lifted associator.
Its proof remains the separate assigned work of that module (claim G8).

Add only local irreducibility annotations on scalar-localization category,
additive/linear structures, composition, and the integral linear structures.
These fold large data during elaboration and have no exported attribute effect.
The new lifting helper uses the project transparency setting unchanged.

Keep all pre-existing signatures, definitions, instances, instance proof bodies,
and public imports unchanged. In particular, do not repeat the earlier F4 change
sharing the noetherian instance construction. The parent node retains its proof
steps and dependencies; update only its proof origin to describe this implementation.

## Proved and sorry left

Closed in the item: `WeilConjectures.weilScalarAssociator_exists`, 1 of 1 holes.
Remaining in the item: none, 0 holes.
Restored lower hole: `AlgebraicGeometry.Scheme.pbcIsoRationalScalarComparison_comp`,
node `lem-sf-pbc-rational-automorphism-coherence`, 1 hole in the restored module.
Thus this packet is a decomposition, not a net reduction in holes or an axiom-free
proof of the completed coefficient compatibility. The private lifting lemma is
fully proved and adds no hole. No new DAG node or statement is introduced. Include the existing lower node
copy with its restoration recorded in `proof_origin`, as required by preflight
for the newly restored source file.

Edge cases of the restored statement: repeated fields are included, using the
existing normalized units; the identity automorphism gives the tensor associator
square; zero objects give the zero-arrow equation. No object is selected from an
unproved mere-existence statement. The chosen Weil associator is uniquely fixed
by the normalization already present in its unchanged theorem statement.

## No longer needed

None. No existing import, declaration, node, or module is removed. All seven
recorded proof dependencies remain needed. The unit `sk-rem-sf-pf-done` has no
realized statement or proof steps, and its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The brief says all proof dependencies have Lean declarations available. The DAG
records `pbcIsoRationalScalarComparison_comp`, but neither its source nor its
compiled object is present. The first compile confirmed the missing object file.
The restore preserves that existing mathematical obligation and attachment,
rather than dropping it or introducing a second lemma with the same statement.
There is no row for this dependency in `coord/rework.tsv`, no quarantine path,
and no Lean source under the named library trees. Its node survived the F4
landing rollback. G8's existing proof claim is noted above; this packet restores
its recorded interface without changing its statement or claiming its proof.

The prior F4 return reports a universe failure in `WeilTensorProduct`. Its current
source already includes the B7 repair of that inference conflict. This packet
preserves the parent's existing noetherian proof bodies verbatim, all public
imports and definitions, and the complete public interface. No tensor consumer
adaptation is required by these proof-only changes. An exploratory consumer
compile hit its time limit; profiling found slow existing private instance
searches in `WfTensorLinearity.additive_of_localization` and
`AlgebraicGeometry.Scheme.scalarLocalization_precomp_injective`. Explicit
`Functor.op_additive` and `TensorProduct.isScalarTower_left` applications reduced
those searches in the experiment, but the full consumer check remains incomplete.
The experiment is outside the delivery: no tensor declaration or proof is changed.
The maintainer's global build remains the independent consumer check.

Validation: the restored lower module and the final item both compiled through
`lcompile.py` with exit code 0 (request `c02edb3adda40c20f0e6392c`). All debug
profiling options have been removed. Existing public signatures, instance proof
bodies and definition bodies in the item are preserved. The change record is
`coord/changes/W3-weil-scalar-lift-proof-context.md`.

The parent's historical source path is absent in the current blueprint. The
current `sec-six-functors-basics/sk-def-sf-admissible/` file
`def-weil-weil-sheaf-complex.proof.md`, paragraph Extension of scalars, gives the
canonical pullback/scalar compatibility. The existing DAG expands it to the
specified raw PBC model; no identification with the newer condensed model is made.

Searches: LeanFinder and Loogle locate `Endofunctor.Algebra.isoMk`, the generic
component constructor used here. Source grep also finds
`IsoAlgebra.mapOfNatIsoCompIsoOfIso`; its required coefficient compatibility is
the same square and brings in derived-functor commutation infrastructure. The
componentwise proof uses constructors already imported by the item. No shorter
route eliminates the coefficient square. Mathlib/source search,
the recorded dependency statements, and the current blueprint were read before
writing the lift.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
