## What changed

Replaced the hole in `AlgebraicGeometry.WeilSheaf.exists_lisse_subobject_clopen_return`
by the explicit Frobenius saturation construction and a complete categorical assembly.
The original theorem signature and public imports are preserved.

The lifted all-proetale Weil object is the categorical image of the map from the
existing free Frobenius algebra on extension by zero of the initial carrier. Its
image inclusion and the map from the zero-th generator are explicit constructions.
Their factorization equation is proved from the image factorization and adjunction.
The canonical generator is monic by the given injection, and its equivariance follows
by cancellation against an equivariant monomorphism. Its inverse gives the requested
restriction isomorphism and equation after restricting to constructible Weil objects.

Proved that the specified geometric sheet is an open and closed immersion, using
weakly etale and integral cancellation. Proved lissity of the saturation: the source
is a countable sum of lisse translates, and its image in a lisse sheaf equals a finite
lisse image. The latter statement is proved by maximizing the total stalk rank at
finitely many detecting geometric points, then factoring every summand through the
maximal finite image. This proof needs neither irreducibility nor simplicity.

The final assembly keeps both restriction functors abstract until the last application.
Profiling identified kernel conversion of their concrete definitions as the cause of a
deterministic timeout; the abstract assembly compiles in 3.4 seconds, with 107 ms of
kernel checking. No shared definition or compile limit was changed.

Validation: `lcompile.py --all` compiled all seven sandbox modules successfully.
The unchanged direct consumer `Sheaf.DeligneLaumon.ClopenReturnRestriction`
also compiled successfully against the delivery; its temporary copy was removed.
The final sources contain no profiling options. Local checks also confirmed that
the original signature and public imports are unchanged, every proof dependency
matches a step's uses, and the sole remaining local hole is the named epimorphism.

Six new modules provide these constructions, their proved interfaces, and the one
remaining sheet calculation. No existing module other than the assigned item changes.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.WeilSheaf.exists_lisse_subobject_clopen_return`.
The item now has zero local holes.

Added one hole:
`AlgebraicGeometry.WeilSheaf.epi_clopen_return_saturationUnit`, in
`Sheaf.DeligneLaumon.ClopenReturnSaturationEpi`, node
`lem-zl-clopen-return-saturation-epi`.
It asserts surjectivity of the fixed canonical generator map on its return sheet.
It does not assert existence of a lifted object or lissity, and assumes neither
constructibility nor injectivity of the input morphism. Its docstring gives the
positive and negative translate calculation, the disjoint-sheet argument, and the
zero-map edge case. Thus this is a decomposition: one upper hole closed, one
strictly smaller hole added, net zero holes closed. It is not reported as a complete
proof of the original mathematical obligation.

All five other new modules have zero holes. In particular the finite-rank
stabilization theorem `AlgebraicGeometry.ProEtale.isAdicLisseSheaf_image_sigma`,
the two sheet immersion theorems, the saturation factorization and equivariant
lifting helpers, and `AlgebraicGeometry.WeilSheaf.isLisse_frobeniusSaturation`
are proved. No data definition contains a hole or chooses an arbitrary witness
from an unproved existence theorem.

## No longer needed

No original public import is removed, and no module is withdrawn or claimed pruned.
The proof does not need a newly constructed finite cyclic Weil object or a separate
existence theorem for an invariant subobject: the existing free algebra and its
categorical image supply that object explicitly.

The old proof dependencies `def-weil-weil-sheaf-complex` and
`def-pod-lisse-l-adic-sheaves` remain statement dependencies. Their common-stage
attachments (`Sheaf.Paper.SfWeilSheafComplex` and
`Sheaf.Paper.LisseIntegralSmallCoefficients`) are not imported to prove this native-category statement. The new route
uses the adopted native Weil and adic categories, their proved free algebra,
extension-by-zero, image, kernel-cokernel and finite-stalk APIs. The powered-pullback
definition remains used through its carrier and inclusion comparisons. The node's
proof dependencies now name precisely the new construction and property nodes.
The unit statement and its Frobenius-orbit route are preserved.

## Where the brief, the DAG or earlier work was wrong

The original dependency declarations define categories, lissity and powered pullback;
they do not state the cyclic-sheet subobject calculation. Their category/lissity
attachments use common-stage categories, whereas this item uses the native source
Weil category. The missing calculation is now isolated as a property of an explicit
map, after constructing the object and proving its lissity and the categorical glue.
No original statement, shared definition or target is changed.

## New nodes

`def-zl-frobenius-saturation`: explicit free-algebra image, inclusion, generator,
factorization equation and equivariant factor through a monomorphism. Fully proved.

`lem-zl-clopen-return-sheet-open`: both open and closed immersion properties of the
specified geometric sheet. Fully proved.

`def-zl-powered-pullback-carrier`: natural carrier and constructible-inclusion
comparisons for the existing powered pullback. Fully proved.

`lem-zl-lisse-countable-image`: lissity of an integer-coproduct image inside a lisse
sheaf on a finite-type geometric fibre, proved by finite-rank stabilization.

`lem-zl-lisse-frobenius-saturation`: lissity of the explicit saturation, using the
preceding image theorem and clopen extension by zero. Fully proved.

`lem-zl-clopen-return-saturation-epi`: the single remaining cyclic-return calculation,
with no lissity, constructibility, injectivity or lifted-object existence conclusion.

Change record: `coord/changes/e3-clopen-return-subobject-proof-scope.md` documents
the added proof-scope commands flagged by preflight, with the original signature
verbatim on both sides. The signature and public imports are preserved. There are
no forced adaptations; the sole direct consumer is compiled unchanged and its
temporary sandbox copy is removed before delivery.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
