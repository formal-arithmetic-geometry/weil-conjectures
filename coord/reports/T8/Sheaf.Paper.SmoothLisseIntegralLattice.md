## What changed

Completed `AlgebraicGeometry.ProEtale.exists_smooth_lisse_integral_lattice` from an
abstract integral-model theorem, with the existing statement and all public definitions
unchanged. The proof constructs the actual adjoint inclusion, proves it is monic on finite
free charts, and proves exactly the required equation on `1 ⊗ m`.

The coefficient argument is proved directly for the recorded inverse limit of constant
quotient sheaves: a quotient transition kills the uniformizer annihilator; local lifts
carry this to constant sheafification; limit projections give torsion freeness; local
equality and separatedness prove injectivity after sheafified localization. Thus the
embedding does not assume an unproved identification with continuous functions.

Added `Sheaf.Paper.NormalCompletedIntegralModel`, containing the independent abstract
normal-scheme integral-model assertion. Its conclusion supplies no embedding or injectivity.
It carries the source's monodromy, invariant lattice, completion and component-gluing part
of the argument. The original item's node now records the actual geometry/model/embedding
route. No existing statement, definition, signature, visibility or target changed.
The auxiliary coefficient module now proves both commutativity lemmas directly
from its inverse-limit projections, with a private Mathlib import. No
arbitrary witness from an existence theorem is put inside a definition.

## Proved and sorry left

Original module: one original hole, now closed in
`AlgebraicGeometry.ProEtale.exists_smooth_lisse_integral_lattice`.
Added: one hole, exactly
`AlgebraicGeometry.ProEtale.exists_normal_completed_integral_model`, node
`lem-a1-normal-completed-integral-model`. Its proof is exactly `by sorry`; its docstring
contains its source and complete argument in words. There are no other holes in the packet.

Also closed in the unclaimed coefficient dependency:
`WeilConjectures.completedIntegralCoefficient_mul_commUnrestricted` and
`WeilConjectures.completedIntegralCoefficient_mul_comm`. Both statements are unchanged.
Thus three existing holes are closed and one is added; the main-item change itself
remains a decomposition. The auxiliary closure does not establish the remaining model.
This is a decomposition (one upper hole closed, one lower hole added), with net zero holes
closed in the main-item decomposition, not a claim of an axiom-free proof of the integral-model theorem.

The following private helpers in the main module are proved without new holes:
`localizationCoefficient_injective`, `latticeModelEmbedding_apply`,
`tensorUnit_injective`, `tensorUnit_injective_at_basis`,
`latticeModelEmbedding_injective`, `latticeModelEmbedding_mono`,
`quotient_transition_kills_annihilator`, `constantSheaf_kills_annihilator`,
`smoothLatticeUniformizer_ne_zero`, and `smoothLatticeUniformizer_regular`.
The actual maps `latticeTensorMap` and `latticeModelEmbedding` have explicit data.

The final pruned main module compiled with no errors or warnings in 19.4 seconds
(`scratchpad/pruned-main-05.log`). The abstract-model module compiled separately earlier.
The final three-module packet compiled cleanly in import order: coefficient module
6.2 seconds, model module 5.2 seconds, main module 28.2 seconds
(`scratchpad/final-with-coefficient-proofs.log`). The final dry run passed:
`OK (dry run): commit b0fcacc26c compiles and passes the preflight; nothing pushed`
(`scratchpad/dry-final-04.log`). Its optional axiom probe on the main module hit the
60-second limit; the tool accepted the ordinary compilation and reports that the
merge runs the probe again. The other delivered files passed their probes. Review
class is CODEX: new node/module, auxiliary proof module, and proof-context record.

## No longer needed

Direct proof imports removed from the main module:

- `Mathlib.CategoryTheory.Abelian.Basic`
- `Mathlib.CategoryTheory.ObjectProperty.Kernels`
- `Mathlib.RepresentationTheory.Rep.Basic`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`
- `Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized`
- `Sheaf.Paper.GaloisLisseRepresentations`
- `Sheaf.Paper.LisseAdicFiberFunctors`
- `Sheaf.Paper.LisseCompletedSystemComparison`
- `Sheaf.Paper.LisseModuleSheaves`
- `Sheaf.Paper.LisseTensorScalarExtension`
- `Sheaf.Paper.NormalProEtaleMonodromy`
- `Sheaf.RepresentationTheory.LAdic`
- `Sheaf.RepresentationTheory.ProfiniteStableLattice`
- `Sheaf.SixFunctors.IntegralLisseReductionEquivalence`
- `WeilConjectures.Mathlib.Topology.NoetherianSpace`

The main proof now directly imports `Mathlib.RingTheory.Flat.Basic` for tensor-unit
injectivity and `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic` for the
sectionwise limit argument.

The main proof does not use the continuous-function coefficient identification for
injectivity. In particular, its old step 6 dependence on
`lem-sfb-integral-lisse-reduction-equivalence` and
`def-weil-pbc-lisse-lattice-coefficients` is replaced by the explicit quotient-limit proof.
The former remains part of the abstract model's coefficient-transport plan, so it is not
claimed pruned from the targets' entire closure.

The original connected-component, monodromy, stable-lattice, finite correspondence and
completion arguments are retained in the new abstract-model node. They are not globally
pruned: `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`,
`lem-sfb-noetherian-connected-components-open`,
`lem-weil-pbc-noetherian-open-subscheme-noetherian`,
`lem-a1-normal-proetale-monodromy`, `lem-pod-profinite-stable-lattice`,
`cor-galois-lisse-representations`, and `lem-per-lisse-completed-system-comparison`.
The geometry nodes `lem-pod-separated-finite-type-base-change`,
`lem-weil-pbc-finite-type-over-noetherian`, and `lem-trf-smooth-geometrically-normal`
remain used by the main proof. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's compile-server communication failures are preserved in scratchpad.
The current resumption reached the compiler successfully. No interrupted delivery existed
and no push had been attempted before this report. The first dry run refused the
unfinished split at 23 minutes on its reference clock. Preserved search/compile records
start at 04:31 UTC and show work through multiple interrupted attempts; the current
reference clock was reset by later resumptions. This is a resumption clock reset; no clock or
launcher metadata was changed by this worker. The preserved attempt markers are
`.brief2`, `.brief3`, `.brief4`, `.brief5` (no numeric session identifiers are exposed).

The normal monodromy declaration and the completed-system base fix the coefficient field
in `Type (u+1)`, whereas this item permits an independent coefficient universe `v`.
Moreover `SfLatticeNormalization` records an integral inverse limit and its rationalization
but does not itself assert that its integral module is locally finite free. Consequently
these declarations cannot simply be applied to produce the displayed abstract model:
coefficient transport, normalized finite-tower local freeness, and component gluing remain
part of the retained theorem. This is an interface/glue gap, not an objection to using
existing theorems whose proofs still contain sorry.

Small cases checked mathematically: rank zero uses the zero free module, the empty scheme
uses empty gluing, and disconnected normal Noetherian schemes have finitely many clopen
components with potentially different ranks. The injectivity argument needs only the
recorded nonzero DVR uniformizer and local finite freeness, and imposes no constant rank.
The base-change proof does not require the field extension to be finite type.

## New nodes

`lem-a1-normal-completed-integral-model`, in
`dag/nodes/sec-purity-real-sheaves/lem-a1-normal-completed-integral-model.json`, states the
abstract normal-scheme integral model before the submodule construction. It follows
Bhatt--Scholze 7.4.7, 7.4.10 and 6.8.4(1),(4), with the existing stable-lattice theorem.
Its strict difference from the original item is the absence of an integral embedding,
monicity, and the inclusion-induced tensor equation; all of those are proved in Lean in
the original item. Actual LeanSearch, Loogle and grep searches are recorded in its node.
The proof-context and auxiliary-proof change record is
`coord/changes/T8-smooth-lattice-proof-context.md`. No existing interface changed.

The resumed server preflight requested a change record for the main module’s
section variables and elaborator options. Added
`coord/changes/T8-smooth-lattice-proof-context.md`, including the unclaimed auxiliary
module’s proof changes and the unchanged consumers. No other group’s module is edited.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
