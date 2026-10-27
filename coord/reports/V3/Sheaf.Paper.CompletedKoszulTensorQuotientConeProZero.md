## What changed

Replaced the one hole in
`AlgebraicGeometry.Scheme.completedKoszulTensorQuotientConeProZero` by a complete
assembly proof from the existing Noetherian Koszul augmentation theorem and two
finite comparison statements. The theorem's signature and original public import
are unchanged. The additional imports of the item are private proof imports.

The assembly works over `ULift A`, transports Noetherianity along its ring
isomorphism, and uses exactly the algebraic augmentation, diagonal maps, quotient
maps and strict cone squares supplied by
`ExteriorAlgebra.noetherian_koszul_augmentation_pro_zero`. The proved private
helper `proZero_of_exact_realization` uses exactness to preserve quasi-isomorphisms,
then the localization universal property to preserve zero maps. Its final
cancellation uses the natural level isomorphisms. K-flat tensoring preserves
quasi-isomorphisms by the existing signed tensor-cone argument; a second application
of localization preserves the derived-zero maps. A strict tower isomorphism then
identifies these maps with the actual transitions in the conclusion.

Added `Sheaf.Paper.CompletedKoszulCoefficientConeRealization` and
`Sheaf.Paper.CompletedKoszulTensorConeComparison`. The first also specializes the
existing cochain monoidal structure to completed coefficients, with explicit site
and coefficient arguments. Its two instance declarations are disabled globally
and enabled locally where used. They construct existing tensor data and have no
proof holes. No shared definition or statement was changed, and no existing module
besides the assigned item was edited.

The comparison statements are finite model identifications, rather than renamed
pro-zero obligations. The coefficient statement has no variable complex P, no
K-flatness and no eventual vanishing conclusion. It records exact realization and
naturality for all the specified strict squares. The tensor statement asserts a
strict isomorphism of towers for arbitrary P before localization; it has neither
a K-flatness assumption nor a pro-zero conclusion. Both have complete proof plans
and sources in their docstrings and DAG nodes.

## Proved and sorry left

The original module had one hole. Its theorem
`AlgebraicGeometry.Scheme.completedKoszulTensorQuotientConeProZero` is now proved
from named statements and has zero local holes. The private helper
`proZero_of_exact_realization` is also completely proved.

Two holes are added, each in a separate new module:

- `AlgebraicGeometry.Scheme.completedKoszulCoefficientConeRealization`, node
  `lem-weil-pbc-completed-koszul-coefficient-cone-realization`.
- `AlgebraicGeometry.Scheme.completedKoszulTensorConeComparison`, node
  `lem-weil-pbc-completed-koszul-tensor-cone-comparison`.

This is a decomposition: one upper hole replaced by two strictly finite comparison
holes, not a sorry-free proof of the original obligation or a claimed net reduction
in holes. No data definition contains a hole or is chosen from either comparison
statement. The existential exact functor is used only inside the theorem proof.

Remote compilation succeeded: the coefficient comparison took 10.5 seconds,
the tensor comparison 9.7 seconds, and the assembly proof 14.3 seconds. The only
warning in the last run was the inherited unused binder name `hq` inside the
statement of `hz`. The signature is preserved verbatim, with that stylistic
linter disabled only for this theorem. The delivery command checks the final
files again. Plain-text checks also verified identical original theorem signatures,
100-character line limits, zero holes in the item, one hole per new module, and
changes restricted to the existing node's proof, proof_deps and proof_origin fields.

## No longer needed

No original import was removed; the original public augmentation import is still
needed for the statement's functors, units and summand maps. No module is withdrawn
and no whole-library pruning is claimed.

The item's direct proof-dependency list now follows the actual assembly. The
following old direct entries are not separately invoked by that assembly:

- `lem-pur-kflat-tensor-quasiiso-independent`: replaced by the already proved
  `flatConstantTensor_preservesQuasiIso` API, which directly matches total left
  tensor and acyclic-tensor K-flatness in the independent coefficient universes.
- `lem-weil-pbc-completed-constant-sheaf-reduction`: retained as a dependency of
  the new coefficient realization node, where exactness and the finite quotient
  identifications are needed.
- `lem-weil-pbc-completed-koszul-tensor-quotient-augmentation`: its existence and
  uniqueness theorem is not needed because beta is supplied. Its definitions
  remain statement dependencies, and its normalized equations are hypotheses.
- `def-weil-pbc-koszul-reconstruction-models`: the definitions are retained
  transitively through the unchanged public augmentation import; the original
  direct proof-dependency entry is redundant with those statement dependencies.

None of these entries is a claim that its source module may be deleted.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan needs explicit finite comparisons
between its actual completed exterior-Koszul presentation and the algebraic
augmentation. The fully proved `AdicResidueKoszulCoefficientConeComparison` and
`AdicResidueKoszulTensorConeProZero` concern the coefficient-slice dual Koszul model;
their signatures do not identify the completedAdic presentation of this item.
They were read as analogues, not applied across different coefficient categories.
The existing generic exact-functor and signed tensor-cone APIs do apply and are
used in the assembly.

Stacks `lemma-sequence-Koszul-complexes` is Tag 0921 in the checked source; the
item's inherited source metadata labels it 091N. The new nodes cite its actual
label and tag. The item's source metadata is left unchanged because this delivery
updates only its permitted proof-route fields.

Before introducing the comparisons, searched all DAG nodes and the imported
blueprint for Koszul coefficient/cone and tensor mapping-cone identifications.
The generic `lem-pc-tensor-mapping-cone-iso` is reused; it is an already proved
source-library tool, not a replacement for the unit's proper-base-change route.
LeanSearch, LeanFinder/Loogle and local Mathlib searches found generic tensor,
localization and constant-sheaf APIs but no one-line match for either new actual
model comparison. Queries and results are recorded in the new nodes and the
launcher's search log.

Edge cases checked mathematically: r=0 gives the rank-one degree-zero Koszul
complex; the zero ring, the unit ideal, the empty scheme and P=0 require no
nontriviality or nonemptiness assumptions. The tensor comparison imposes no
boundedness, termwise flatness or interchange of tensor with infinite products.
The degree-zero unit is invertible by its actual scalar-extension construction,
not by assuming regularity of the generators. Every cone comparison is natural
in the specified strict square, so it does not select independent derived cone
fillers.

## New nodes

`lem-weil-pbc-completed-koszul-coefficient-cone-realization`, realized by
`Sheaf.Paper.CompletedKoszulCoefficientConeRealization`, isolates exact realization
of the algebraic coefficient cones and all their actual transitions. Its proof
uses completed constant flatness, finite quotient identification, the exterior
complex construction and additive cone naturality. Source: Stacks 099M,
`lemma-naive-completion`; 0921, `lemma-sequence-Koszul-complexes`; and 093M,
`lemma-completion-flat`.

`lem-weil-pbc-completed-koszul-tensor-cone-comparison`, realized by
`Sheaf.Paper.CompletedKoszulTensorConeComparison`, isolates normalization of beta
under the tensor unit, the total-tensor/degree-zero comparison, and the natural
signed tensor-cone isomorphism. Source: Stacks 099M, finite Koszul tensor argument;
06YP, `lemma-K-flat-quasi-isomorphism`, and the existing
`CochainComplex.mapBifunctorMappingCone₂Iso` tool. The original unit and chapter
are retained. There are no change records because no existing interface changes.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
