## What changed

Prove `AlgebraicGeometry.Etale.cartierPoleBoundary_pullback` without changing its
statement or either original public import. Identify both normalized pole classes
with relative extensions of their canonically framed torsors. The ordinary
pullback of the dual ideal preserves its canonical section, and its frame map
preserves the complementary frame. The framed-extension square then proves the
required equation.

Add two proved modules. `Sheaf.AlgebraicGeometry.CartierPairPullbackSection`
bridges the existing tensor-pullback equality for dual maps of ideal inclusions
to the ordinary-pullback equality for the actual divisor section.
`Sheaf.AlgebraicGeometry.RelativeFramedExtensionPullback` extracts the
arbitrary-morphism extension-square argument from the etale normalization proof.
Its private helpers construct the frame map and prove naturality, equivariance,
and compatibility with global sections. The assigned module privately combines
these facts with the normalized pole specification.

Profiling located expensive unfolding of the frame map and concrete torsor data.
The new private frame map has a value API and is kept locally irreducible after
its value lemma. The complementary frame is an abstract witness of the proved
pole specification, retaining its canonical value equation. Its choice is inside
a proof; no definition chooses arbitrary data from an unproved existence result.
After these improvements, the self-contained framed-pullback API was moved into
its own module to keep compilation within the per-file limit. No shared
definition or interface is changed.

All three delivered Lean modules compiled successfully through `lcompile.py`.
Profiling options have been removed for delivery.

Only the assigned module, the two new modules, their DAG nodes, and this report
are changed. No existing signature, instance or public import is changed.

## Proved and sorry left

Close the original hole in
`AlgebraicGeometry.Etale.cartierPoleBoundary_pullback`
(`lem-asd-cartier-pole-boundary-pullback`). One original hole closed; zero holes
added; zero holes left in the delivered modules. This is a proof, not a
reduction to new unproved statements.

The two new public declarations
`AlgebraicGeometry.Etale.cartierPair_pullback_section` and
`AlgebraicGeometry.Etale.relative_extension_pullback_square`, and every private
helper, are proved. There are no split-off unproved statements.

## No longer needed

The direct proof-dependency edge from
`lem-asd-cartier-pole-boundary-pullback` to
`lemma-weil-pbc-finite-exchange` is unnecessary: the argument uses the exchange
morphism and its unit compatibility, not an exchange isomorphism. No module is
withdrawn. The existing relative-extension normalization module still uses
finite exchange in other declarations, so its dependency is not globally
pruned.

No original public imports were removed. The new geometry proof avoids
`WeilConjectures.AlgebraicGeometry.TheoremOfCube.Slices`: its kernel-comap
identity follows directly from the three-line Mathlib argument. Its public
statement import is `OrdinarySupportedKummerBoundary`.

The proof imports of the arbitrary extension construction and
`GmPicardPullback` are in the new framed-extension module. The assigned module
uses that module's API rather than importing those implementations directly.
The supported-Cartier comparison, relative free-torsor extension,
normalization, complementary-frame API, and pole-existence dependencies remain
needed. No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan asked for an identification of quotients by an exchange isomorphism.
Naturality of extension classes only needs the canonical exchange map. The
existing `relative_extension_pullback` theorem assumes an etale base map, but
its extension-morphism argument works for any scheme map. The new proved square
states precisely that part, without changing the shared theorem or consumers.

No statement was found false or weakened. Both Cartier hypotheses remain in
force. Empty schemes and empty support are allowed by the same constructions.

A dependency-closure audit also detected the pre-existing DAG cycle
`lemma-weil-pbc-derived-exchange-replacement` →
`lem-weil-pbc-derived-exchange-termwise` →
`lem-weil-pbc-derived-exchange-bounded-comparison` →
`lemma-weil-pbc-derived-exchange-replacement`. None of the changed nodes participates;
no new dependency returns to a changed node. This is reported for the maintainer,
with those shared nodes unchanged.

## New nodes

`lem-asd-cartier-pair-pullback-section` records the proved ordinary-pullback
section comparison, a strict geometric step of the original node's first proof
step. It reuses the canonical ideal comparison, evaluation-transpose identity,
invertible dual comparison and monoidal unit normalization. No ideal-localization
proof is duplicated. Its source is Stacks Tag 0C4U.

`lem-asd-relative-framed-extension-pullback-square` records the proved general
relative-extension square, for arbitrary abelian coefficients and an equivariant
map of framed torsors. It assumes neither Cartier ideals nor pole classes. Its
proof constructs a morphism of representing extensions using the exchange unit
identity, takes its adjoint, and applies `ShortExact.extClass_naturality`.
Its sources are the relative framed refinement of Stacks 03AJ and 0A45. The
module also contains the private frame-map API used by the assigned proof.

Both nodes contain three actual Mathlib searches, full proof steps, provenance,
and exact Lean signatures. There are no new unproved nodes and no change
records for existing interfaces.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
