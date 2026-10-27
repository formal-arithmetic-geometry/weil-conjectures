## What changed

Replaced the hole in `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_adjoints`
by a categorical construction from two pointwise geometric statements. The original theorem
signature and both original public imports are unchanged. Only the assigned module, its node,
and the two new statement modules and their nodes are included.

The proof constructs a tensor bifunctor from individual left adjoints of the curried Hom.
Its maps in the tensor parameter are inverse mates of the contravariant Hom maps.
`conjugateEquiv_symm_id` and `conjugateEquiv_symm_comp` prove functoriality. The unit and counit
mate equations prove parameter naturality. The restrictions of the tensor bifunctor are
identified with the original individual left adjoints by identity-component natural
isomorphisms; transport preserves their units and counits.

The proof then constructs the ordinary-to-forgotten-tensor natural transformation by the
specified transpose of the forgotten unit. Naturality in the first variable follows from
unit naturality, Hom-comparison naturality, and inverse-adjunction naturality. Naturality in
the tensor parameter uses the proved parameter-unit equation and the ordinary evaluation
naturality field. Factoring an arbitrary product morphism combines these two squares.
Pointwise invertibility then gives a natural isomorphism. Taking its inverse gives exactly
`tau`, with the required component formula by construction.

All of this categorical glue is proved in private declarations in the assigned module;
none is admitted. Chosen left adjoints have their adjunction universal property and are
unique up to the compatible natural isomorphism. No object is defined using an arbitrary
witness of a sorried mere-existence theorem.

Validation: `lcompile.py --all` compiled both new statement modules; the subsequent
single-file compile of the corrected assigned module succeeded without warnings in 7.7 s.
The original theorem signature and public imports were compared verbatim. All three node
proof-dependency lists equal the union of their proof-step uses, and both new Lean signatures
match their node records. All Lean lines have at most 100 characters.

## Proved and sorry left

The original module contained one hole. Its theorem now has a complete proof from two new
statements. This is a decomposition, not a net reduction in admitted obligations.

Closed upper hole:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_adjoints`
  (`lem-sf-native-weil-tensor-adjoints`).

Added holes, each exactly `:= by sorry` in a separate module:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_hom_isRightAdjoint`
  (`lem-sf-native-weil-hom-right-adjoint`): existence of an individual left adjoint for a
  fixed source of native Hom. It has no tensor bifunctor or comparison in its conclusion.
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_unit_mate_isIso`
  (`lem-sf-native-weil-unit-mate-iso`): invertibility of one explicitly specified arrow for
  an already supplied individual adjunction. It asserts no adjoint existence, parameter
  naturality or natural isomorphism.

There are zero holes in the assigned module and two in the added modules: closed 1,
added 2, net -1. No private declaration or definition contains a hole. The generic assembly
proves the functor laws and both naturality assertions rather than assuming them in either
residual statement.

## No longer needed

No original public import was removed; there were no original private proof imports.
No module or node is withdrawn, and no module is claimed pruned from the target closure.

The assigned node now depends directly on the two new pointwise nodes. Its five previous
geometric dependencies remain in their proof plans: Frobenius action-site resolutions,
ringed derived tensor-Hom adjunction, the two-injective Hom comparison, ringed closed tensor
models, and K-flat tensor descent. They have not become unnecessary mathematics. Tensor
localization is no longer needed to assemble the bifunctor, prove parameter naturality or
extend the mate as a natural transformation: these parts are proved categorically. It is
retained for the geometric pointwise adjoint and invertibility arguments.

The pointwise adjoint statement does not need ordinary closed models, symmetry or the
ordinary normalization. The pointwise invertibility statement does not need any monoidal
constraints on the native category. These distinctions make both obligations smaller than
the assigned theorem and keep the earlier coherence obligation separate.

## Where the brief, the DAG or earlier work was wrong

No original statement was found false. The original plan combined constructing an adjoint
bifunctor with descent of its parameter naturality, and combined pointwise invertibility
with descent of a comparison and its inverse. These formal portions can be removed from
the geometric obligations. Mathlib's parametrized-adjunction file explicitly lists assembly
from pointwise adjoints as a TODO, so the construction here is supplied rather than assumed.

Searches through `msearch.py` found general mate identities, module-sheaf adjunctions and
generic derived closedness, but no theorem specialized to the native representative models
with the required normalized mate. Local source searches found the underived native
`tensorIhomAdjunction` and the generic `tensorHomAdjunctionQhObj`; the native action-site
transport and representative normalization needed to specialize them remain geometric work.

Edge cases: the generic proof works for arbitrary categories and uses no nonzero objects,
faithfulness, boundedness or constructibility. The pointwise proof plans retain zero
complexes and the empty scheme. Their universal-property arguments do not introduce an
exception for either case. No unit's realized statement or route is bypassed.

## New nodes

`lem-sf-native-weil-hom-right-adjoint`, in `Sheaf.Paper.NativeWeilHomRightAdjoint`, isolates
only pointwise adjoint existence. Its source is the adjoint-construction portion of native
tensor lift step 1, via the blueprint internal-Hom paragraph and Stacks 06YS, 08J9 and 0A97.
Its docstring gives the K-flat/K-injective construction, native row-sign identification,
and target localization argument. It does not restate the bifunctor and mate conclusion.

`lem-sf-native-weil-unit-mate-iso`, in `Sheaf.Paper.NativeWeilUnitMateIsIso`, isolates the
pointwise normalization and invertibility calculation of native tensor lift step 2. Its
source is the same blueprint paragraph and Stacks 06YS, 08J9 and 0A97. Its proof plan computes
the canonical mate on representatives, then treats any supplied adjunction using the unit
identity for uniqueness of left adjoints. Neither new node depends on the assigned node.

No change record is required: no other existing module or node was changed.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
