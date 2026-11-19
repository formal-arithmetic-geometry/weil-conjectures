# PR #2122 classification

The old [module](Before.lean) compiles in 347.37 user CPU seconds at
16,321,824 KB peak RSS. The current [module](After.lean) compiles in 29.87
seconds at 5,285,748 KB. In the old module, Kernel checks of 15.6, 64.3,
and 176 seconds dominate its 269-second checking total; the new module has
a 27.2-second check. **Phase: primarily Kernel.** The comparison also
includes module splitting and precompiled helper imports, so the full
317-second saving is not assignable to one target proof term.

The [PR diagnosis](https://github.com/formal-arithmetic-geometry/weil-conjectures/pull/2122)
identifies concrete versus abstract category representations, including
`DiagonalAb T` versus sheaf categories, `(F ⋙ G).obj` versus `G.obj (F.obj)`,
and `ULift.ring` versus `CommRing.toRing`, below derived-category/`Quiver.Hom`
structure. The fix pins named categories and propositions, factors a generic
Kummer lemma, and moves helpers out of this module. **E (representation
mismatch) primary, A (reduction) contributing**, based on the historical
expression diagnosis and the 4.35.0 Kernel timing. The exact inner comparison
was not independently dumped on 4.35.0.
