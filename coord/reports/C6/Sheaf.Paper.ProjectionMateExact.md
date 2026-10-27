## What changed

Proved `SheafOfModules.ringedProjectionMateExact` from the declared normalization,
localization and exact-projection-mate APIs. Its theorem signature is byte-identical.
The proof compares the recorded tensor models with the published tensor on resolving
representatives, transports the canonical shifts and unitors, proves exactness, identifies
the canonical pullback comparison, and applies the formal exact projection-mate theorem.

The item's ordinary tensor and degree-zero unit use definitionally equal native
presentations. Named representative source, target and comparison interfaces and generic
normalization predicates avoid repeated expansion of totalization and localization data.
The original shift and unit formulas are retained by definitional equality, with no new
hypotheses or weakened conclusions. The new equality API is proved by rfl.

In the unclaimed `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`, `derivedTensor`
now curries the published tensor directly, rather than projecting the identical tensor
from the selected descent record. The representative construction and all theorem
signatures remain unchanged. In the unclaimed `Sheaf.Paper.PullbackTensorCanonicalShiftUnit`,
added `canonicalRepresentativeIso_naturality`, a proved public wrapper around its existing
private fixed-factor naturality argument. It constructs no new tensor data.

All other new helpers are private and proved in the item. Elaboration settings, instance
priorities and irreducibility attributes are local. The compile limit remains 60 seconds.
The change record is `coord/changes/C6-projection-mate-proof-settings.md`; it lists the
old and new definitions and their textual users. Unchanged consumer copies and diagnostic
probes are temporary verification inputs, removed from the packet before delivery.

## Proved and sorry left

Hole closed: `SheafOfModules.ringedProjectionMateExact` (the single original hole).
Holes added: zero. Holes left in the three changed modules: zero. Split off: zero.
The existing canonical-comparison naturality API addition is fully proved.

The changed tensor module and canonical-comparison module compiled together in 35.4 and
41.9 seconds respectively. The complete item initially compiled in 43.2 seconds without warnings; after adapting to the
retired resolution API it compiled in 36.1 seconds without warnings.
The old and new shift and unit predicates are definitionally equivalent (`Iff.rfl`);
the native unit complex, ordinary tensor and direct published derived tensor also agree
with the original expressions by `rfl`. These checks compiled in 12.8 seconds initially
and 9.9 seconds after the resolution compatibility repair.
`#print axioms SheafOfModules.ringedProjectionMateExact` reports exactly `propext`,
`Classical.choice` and `Quot.sound`. The diagnostic module's private-module style warning
concerns only the removed diagnostic file; the delivered item has no warnings.
Consumer verification: 23 unchanged modules compiled successfully against the changed
sandbox artifacts, including all nine textual users of the changed shift, unit and ordinary
tensor definitions and the additional direct fixed-tensor users. No consumer adaptation
was required. The largest measured consumer compile was 59.3 seconds.

The broader 72-consumer batch stopped at `Sheaf.AlgebraicGeometry.EtaleKFlatSupportComparison`
because the published build lacks the aggregate `Mathlib.olean` artifact, before checking
that consumer's proof. Nine consumer modules preceding it passed. This unrelated build
artifact limits the broader check; it is not a proof failure or a reason to edit that
unchanged consumer. The 14 additional consumer checks ran individually and all passed.
The temporary consumer and diagnostic sources have been removed from the packet.

## No longer needed

The edge already contains the specified derived adjunction. Mathlib's
`Adjunction.rightAdjointCommShift`, `commShift_of_leftAdjoint`, and
`isTriangulated_rightAdjoint` give its compatible right-adjoint shift and exactness.
The proof therefore does not reconstruct the right-derived functor or derived adjunction.
Its direct dependencies no longer include `lem-pc-derived-adjoint-functors`,
`lem-pc-right-derived-functor-triangulated`,
`lem-weil-pbc-adjunction-of-natural-bijection`,
`lem-weil-pbc-derived-adjunction-shift`,
`lem-weil-pbc-ringed-topoi-module-adjunction`, or
`prop-pur-kinjective-resolutions-exist`. The last remains an unchanged statement
dependency. No declaration or module is withdrawn.

The direct proof dependency on `lem-weil-pbc-site-derived-tensor-descent` is also
unnecessary: canonical normalization supplies the needed natural computation isomorphisms.
The descent module remains needed transitively by the published tensor construction.

The signed total-shift formulas are used through Mathlib's bifunctor-shift API and the
canonical normalization theorem. `lem-weil-pbc-total-tensor-integer-shifts` is not applied directly by this assembly. The unit statement and realized steps are preserved.

Removed private proof imports:

- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Paper.DerivedAdjunctionShift`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Algebra.Homology.KFlatResolution` (retired; use the current independent-coefficient API)

Removed obsolete tool-use approvals for `prop-pur-kinjective-resolutions-exist`,
`lem-pc-derived-adjoint-functors` and `lem-pc-right-derived-functor-triangulated`.
Their declarations remain in the library; the unchanged statement dependency on K-injective
resolutions remains in the item node. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan reconstructed a derived adjunction already supplied by the edge.
Mathlib gives its compatible right-adjoint shift and exactness directly. The node now
records the actual proof route and its direct proof dependencies, including the flatness
comparison through the site tensor-right presentation.

The published normalization uses an uncurried curried tensor; its product-map equation
is propositional, rather than definitional. The proof explicitly uses the currying
comparison and a congruence equation to pass to the recorded tensor bifunctor.

The earlier missing published-artifact failure has cleared. Scratch files outside the
sandbox's lean root did not see changed sibling artifacts; that verification error was
corrected by compiling changed modules together and testing consumers under the lean root.
No launcher tool or build artifact was modified. Busy-server responses are retried.

The first preflight found additional textual derivedTensor users after the item's new import
enlarged the fixed-tensor module's downstream closure. The change record now uses the combined
downstream scan of all three changed modules and covers every resulting textual user.

During resubmission, the same-universe KFlatResolution module was retired and became empty.
The four private resolution calls now use a proved private wrapper around the current
`CochainComplex.exists_isKFlatResolutionIndependentCoefficients` declaration, which is the
existing resolution node's Lean attachment. Its independent K-flat predicate is converted
using the already proved equivalence; all flatness, quasi-isomorphism and epimorphism
conclusions are retained. No public statement or definition changes in this compatibility repair.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
