## What changed

Proved `cartierPairTensor_frames` by constructing the tensor pairing of actual local
frames, proving its restriction and scalar identities, and applying the sheaf
quotient universal property. Its distinguished section is the tensor of the two
restricted canonical sections. The relative class equation follows by adding
injective lifting-torsor coordinates and checking the specified signed-cone
restriction.

Proved `cartierPairTensor_extensions` using the existing relative extension
cohomology normalization and enlargement theorem. A pole-boundary specification
identifies its extension with the unique relative extension of the canonical
pointed frame torsor. Injectivity of the comparison gives the derived Ext
addition equation; the additive Yoneda comparison gives the stated Baer equation.

Added three fully proved modules: `TensorPullbackFrames`, `BinaryTorsorQuotient`,
and `RelativeTorsorAddition`. The first supplies monoidal pullback coherence and
scalar/restriction identities; the other two supply local sheaf gluing and
addition of pointed relative classes. Proof-only imports supply the existing
Cartier complement frame and extension normalization APIs.

Normalized `cartierPairTensorFrames` to the proved general tensor pairing.
`tensorPullbackFrames_eq_unit` proves equality with the original formula, including
its unit comparison. The change record is
`coord/changes/cartier-pair-tensor-normalization.md`. The downstream-use check
reports only the item itself. No other module requires adaptation.

Made `cartierPairFrameVal` the direct projection `x.down.1`, definitionally equal
to its former instance-wrapped `etaleIsoTorsorVal` expression. The additional
change record is `coord/changes/cartier-pair-frame-value-projection.md`. Private
proved extension-specification and addition lemmas, together with local
irreducibility of the frame interfaces, prevent repeated large reductions.

## Proved and sorry left

Closed the two original holes: `AlgebraicGeometry.Etale.cartierPairTensor_frames`
and `AlgebraicGeometry.Etale.cartierPairTensor_extensions` (both belong to
`lem-pur-cartier-pair-tensor-addition`). Added zero holes. No `sorry` remains in
any delivered module. The geometry proof is retained. The naturality proof now states the coefficient-map
squares explicitly before applying the same connecting-map naturality theorem.
No unfinished theorem was split off.

## No longer needed

Removed the public import
`WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation`. The statement
expresses its required quotient by a universal property; the new
`binaryTorsorQuotient_universal` proves that property directly by local gluing.
The statement dependency on `def-sc-contracted-product-presentation` remains as
mathematical terminology in the node.

The item no longer directly needs
`lem-amb-relative-torsor-forget-normalization`,
`lem-weil-pbc-open-closed-short-exact`,
`lem-weil-pbc-extension-by-zero-adjunction`,
`lem-coef-yoneda-baer-existence`,
`lem-weil-pbc-pushout-short-exact-sequence`, or
`def-weil-pbc-inverse-image`. Their former calculations are supplied by the
existing `lem-pur-relative-extension-cohomology-normalization` interface, or by
addition of actual lifting coordinates and the additive Yoneda comparison.
The obsolete direct proof dependencies and corresponding top-level tool-use
entries were removed. These nodes may remain transitively needed by other
modules, including extension normalization; no upstream declaration is removed
and no global withdrawal is claimed.

The private affine-descent import is unnecessary in the item after moving its
ordinary scheme-pullback coherence into `TensorPullbackFrames`; that new module
uses the proved affine-descent API. No unit statement or realized unit step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

The cited frame-torsor declaration supplies individual frame torsors but does not
provide the full tensor pairing, its restriction equation, or the binary quotient
universal property. Those steps required the proved new APIs below. Relative
cocycle coordinates already supply the correct signed cone, but addition under
a pairing required a separate proof. The extension normalization theorem already
packages the open-closed and extension comparison calculations, so repeating the
planned Baer extension construction was unnecessary.

The original explicit tensor-unit formula is mathematically correct. Replacing
it by an equal monoidal-normalized expression avoids expensive reductions of
ordinary scheme pullback comparisons. Explicit site objects and presheaf map
identities avoid ambiguous inference between etale and pro-etale frame objects.

## New nodes

`lem-pur-tensor-pullback-frames`, in
`Sheaf.AlgebraicGeometry.TensorPullbackFrames`, records the actual tensor-frame
construction and its proved map, composition, scalar, unit, and presheaf
restriction equations. Its statement works for arbitrary schemes and arbitrary
module maps, including empty schemes and zero scalars.

`lem-pur-binary-torsor-quotient-universal`, in
`Sheaf.CategoryTheory.Sites.BinaryTorsorQuotient`, proves that an equivariant
binary pairing of abelian sheaf torsors has the antidiagonal quotient universal
property. Local nonemptiness is used only on covering sieves; no global frame is
chosen.

`lem-pur-relative-torsor-pairing-addition`, in
`Sheaf.AlgebraicGeometry.RelativeTorsorAddition`, proves addition of pointed
relative classes under such a pairing for an arbitrary abelian sheaf. It adds
both the global cocycle and the negative open-lift coordinate. The statements
remain valid for an empty or disconnected open.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
