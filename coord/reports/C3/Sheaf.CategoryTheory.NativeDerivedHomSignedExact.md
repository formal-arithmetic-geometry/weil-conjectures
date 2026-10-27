## What changed

Replaced the sorry in `AlgebraicGeometry.ProEtale.nativeDerivedHom_signed_exact` by a complete
Lean reduction to two strictly smaller calculations. The original theorem signature is unchanged.
The proof constructs every signed component explicitly, proves its naturality by adjunction mate
composition and tensor-shift naturality, assembles a CommShift using zero/addition equations, and
checks exactness on ordinary localized cones. Mathlib's opposite-triangle characterization and
`DerivedCategory.mem_distTriang_iff` transport that cone calculation to every distinguished triangle.
The normalization formula in every integer degree then holds by construction.

Moved `siteHomTensorParameterShift`, `siteHomSourceShift` and `siteHomOppositeSourceShift` verbatim
(names, signatures, attributes, docstrings and bodies) into the new lower module
`Sheaf.CategoryTheory.NativeHomSignedShiftLaws`, publicly reexported by the item. This avoids an
import cycle with the cone calculation. Added the explicit map `siteHomSignedSourceComponent`.
No data are selected from an unproved existence statement: the maps and their inverse isomorphisms
are scalar multiples of the existing explicit mates, and only their equations are postponed.

The new module `Sheaf.CategoryTheory.NativeHomLocalizedConeBoundary` isolates the ordinary-cone
boundary calculation with exactly the degree-one corrected mate, without assuming a CommShift
structure or arbitrary-triangle exactness.

Validation: all three delivered Lean modules compile without warnings (2.0, 2.1 and 5.1 seconds
in the final sandbox compile). Both unchanged direct importers also compiled against the final interface (4.4 and
31.8 seconds respectively): `Sheaf.CategoryTheory.ExactDerivedHomComparisonShift` and
`Sheaf.AlgebraicGeometry.SiteHomComparisonThick`. Their temporary copies are not delivered.
Development checks compiled the formulas at n=0, n=1 and n=-1 and the quadratic identity for
arbitrary integers. The native cone signs were checked against the existing signed product-Hom
model and `SignedBifunctorConeIso`: y_j=(-1)^(j-1)a_(j-1), differential
(-d*y-U(f)*x,d*x). For the zero map and either zero source summand this specializes to the
usual split/shifted cone; in characteristic two all sign corrections become identity.

## Proved and sorry left

Original holes: 1. The proof of `AlgebraicGeometry.ProEtale.nativeDerivedHom_signed_exact` is now
complete from the two named lower statements; the item module contains zero sorry tokens.
This is a decomposition, not a completed proof independent of new holes: zero of the original one
is counted as fully proved, one upper hole is closed by reduction, and two lower holes are added.
The net hole count of this packet is +1.

The delivery leaves exactly these two sorries, each as the whole proof of a public named theorem:

- `AlgebraicGeometry.ProEtale.siteHom_signed_source_shift_laws`, node
  `lem-sf-native-hom-signed-shift-laws`: only the zero and addition component equations in a
  generic closed additive monoidal category; no triangulatedness or existence conclusion.
- `AlgebraicGeometry.ProEtale.nativeHom_localized_cone_boundary`, node
  `lem-sf-native-hom-localized-cone-boundary`: only ordinary localized cone inputs and the
  specified degree-one boundary; no CommShift structure or all-integer coherence conclusion.

The proved private helpers are `rightAdjointUniq_ofNatIsoLeft`,
`leftShiftMateIso_naturality`, `siteHomSourceShift_naturality`, `shiftEquality_naturality`,
`oppositeSource_naturality` and `signedSource_naturality`. They use no split-off theorem.
The explicit `signedSourceIso` uses those proved naturality calculations. Its zero/addition
axioms are the only remaining input for `signedSourceCommShift`.

## No longer needed

The item no longer depends on `lem-coef-signed-derived-internal-hom-exact` or its module
`Sheaf.Algebra.Homology.SignedDerivedInternalHomExact`. That theorem concerns the ringed-site
functor, rather than the arbitrary native closed derived category in the item. It remains needed
elsewhere; this packet does not withdraw it or any source-library declaration.

Removed direct public imports from the item: `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`,
`Mathlib.CategoryTheory.Triangulated.Opposite.Functor`, `Mathlib.CategoryTheory.Adjunction.Unique`
and `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`. The required generic
shift and mate interfaces are publicly supplied by the lower shift module; the derived instances
come from the retained derived closed-category imports. Added only proof imports of the cone
lemma and Mathlib adjunction mates to the item. No module is globally withdrawn.

No additional proof-dependency imports are added just to follow the previous ringed-site analogy.
The unit `sk-prop-sf-rf-shriek-preservation`, its realized steps and its comparison route are kept.

## Where the brief, the DAG or earlier work was wrong

The old proof dependency `lem-coef-signed-derived-internal-hom-exact` supplies a ringed-site
analogue, not a theorem directly applicable to arbitrary C. The already proved
`DerivedCategory.nativeInternalHom_contravariant_exact` gives an existential shift structure
with no equation for the prescribed mates, so exactness alone does not identify this normalization.
The old DAG called the normalized cone boundary an elementary step; it includes a substantive
comparison of the evaluation-adjoint mate with the signed chain-level boundary. It is now its own
explicit statement. Naturality itself has been proved rather than included in the new hole.

The historical `created.item` module name prevents the blueprint ancestor utility from resolving
this item's ancestor automatically. The new nodes explicitly point to the existing blueprint lemma
`lem-weil-finite-duality-site-comparison`, through the assigned node and
`lem-sf-site-hom-comparison-thick`, in its thick-generation/triangulated-comparison argument.
Whole-blueprint searches for Hom shift and Hom cone found no equivalent imported statement.

## New nodes

`lem-sf-native-hom-signed-shift-laws`, in `NativeHomSignedShiftLaws`: the prescribed component
maps satisfy exactly the zero and addition equations needed for CommShift. Its proof gives the
raw tensor-interchange sign and the integer quadratic correction. The three existing mate
constructions and the new explicit scalar component are attached to this lower module's node.

`lem-sf-native-hom-localized-cone-boundary`, in `NativeHomLocalizedConeBoundary`: the signed
native-Hom triangle of one localized ordinary cone is distinguished. Its proof records the
product-Hom cone coordinates, the explicit degree-one mate coefficient and the evaluation
comparison to the native derived closed structure. Its planned dependencies are the existing
proved generic bifunctor homotopy exactness and signed cone isomorphism.

Change record: `coord/changes/C3-native-hom-signed-assembly.md`, including the conservative
transitive consumer list and direct-importer checks. No forced adaptation was necessary, and
no existing module or node besides the assigned one is changed.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.CategoryTheory.NativeDerivedHomSignedExact": "b9982a76d0884b2e6e9a1d8271d551afb48f585b", "Sheaf.CategoryTheory.NativeHomLocalizedConeBoundary": "b8a7d73d2a449e7470afeb9981ab2a5142e66c4d", "Sheaf.CategoryTheory.NativeHomSignedShiftLaws": "6031a26b15a6d6381081da586d1bea7c232a1bd8"}, "results": {"Sheaf.AlgebraicGeometry.SiteHomComparisonThick": {"hash": "29d7a19d3a524d0b2a51e0b5702a9ddfe30b5f2d", "status": "OK"}, "Sheaf.CategoryTheory.ExactDerivedHomComparisonShift": {"hash": "03f29c69ca8e34c2d96b041defa9db9587265b29", "status": "OK"}}, "seconds": 54, "time": "2026-10-28T06:58:39+0800", "transitive": 0, "version": 1}
```

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
