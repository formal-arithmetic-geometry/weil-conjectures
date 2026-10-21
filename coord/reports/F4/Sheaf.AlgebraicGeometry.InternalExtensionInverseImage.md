## What changed

Proved `AlgebraicGeometry.ProEtale.internal_extension_inverse_image` in
`Sheaf.AlgebraicGeometry.InternalExtensionInverseImage`, preserving its complete statement,
universe, visibility and public imports. The proof composes the existing
`Mod.extendRestrictAdjunction` and `Adjunction.mapModAdjunction` adjunctions. Naturality of
the adjunction unit, `Mod.comapComp`, `Mod.comapCongr` and `Functor.mapModComapIso` identify
the composite right adjoints. `Adjunction.ofNatIsoRight` and
`Adjunction.leftAdjointUniq` then give the stated natural isomorphism, over the actual
inverse-image rings.

Updated the theorem's proof documentation and the node
`lem-sfb-internal-extension-inverse-image` to this shorter route. The newly cited
`def-sfb-modobj-transport-adjunction` is already closed in the source library;
`lem-sfb-finite-monoidal-adjunction` is also an existing proved input. No new declarations,
definitions, statements, nodes or change records are required.

Remote single-file compilation succeeded after removing the unused proof import.
An explicit `#print axioms` check reported only `propext`, `Classical.choice`, and
`Quot.sound`; the temporary diagnostic command was removed. The argument uses arbitrary
scheme and ring morphisms, including identities and zero ring objects, without any new
hypotheses. Naturality and linearity hold because the resulting isomorphism lives directly
in the functor category of the stated module categories.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.internal_extension_inverse_image`
(node `lem-sfb-internal-extension-inverse-image`).

Holes added: 0. Split off: 0. Holes left: 0. No `sorryAx` occurs in this theorem's axioms.

## No longer needed

Removed the private proof import `Sheaf.CategoryTheory.SheafTensor`. Relative to this
module's former import closure, this also removes
`Sheaf.CategoryTheory.SheafTensorStructure`,
`Sheaf.CategoryTheory.PresheafTensorInternalHom`, and
`Sheaf.CategoryTheory.SheafificationTensorLocalIso`. No files are withdrawn, and these
modules may remain needed by other consumers.

The node's former explicit balancing-coequalizer construction, its tensorator-arrow
identifications, quotient-map linearity cancellation and quotient-map naturality proof
are unnecessary: the existing adjunctions already give all of that structure.
Removed `def-sfb-strong-monoidal-functor` and `sk-def-sfb-sheaf-tensor` from the direct
proof dependencies. The sheaf tensor is still part of the unchanged statement's meaning
and remains in `stmt_deps`; ambient tensor-colimit infrastructure is still provided by
the retained public imports. The braided inverse-image input remains needed to give
commutativity of the actual inverse-image source ring. All other former direct proof
inputs remain recorded. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The proposed coequalizer proof is valid but longer than necessary. The existing
`Adjunction.mapModAdjunction` reduces the compatibility to the square of restriction
functors induced by unit naturality. The DAG and docstring now record that argument.
No statement or definition repair was necessary.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
