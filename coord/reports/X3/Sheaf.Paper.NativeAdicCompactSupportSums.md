## What changed

Proved `AlgebraicGeometry.ProEtale.nativeAdicCompactSupport_localizing_preservesCoproducts`
with its statement, universes, hypotheses, two defining abbreviations, and all public imports
unchanged. Only proof imports, private proved helpers, the proof, and its documentation changed.
The existing compact-support realization supplies preservation of bounded constructible
generators. Applying that realization to the open compactification, and cancelling the right
derived identity, supplies the open factor's generator preservation.

Added two proved modules. `NativeAdicEncodingConstructible` transports finite free models,
small pro-etale covers, native finite stratifications, finite presentation, and derived
cohomology through the specified native encoding. Its comparison is one-way, on arbitrary
Noetherian schemes, and uses the adopted source library's actual constructible module predicate.
`NativeAdicProperCoproducts` lifts this encoding to the constructible hull, applies the already
proved condensed proper-image coproduct theorem with its ell-adic heart hypotheses, and
reflects coproducts through the target derived equivalence.

The main assembly lifts open extension between hulls, composes with proper direct image,
and uses localizing-closure minimality to obtain target-hull membership. The restricted
functor is triangulated, and the target inclusion reflects its coproduct preservation.
No absolute separatedness was introduced. No existing module besides the assigned item was
changed, and no source-library declaration was changed or removed.

## Proved and sorry left

Closed the original single hole:
`AlgebraicGeometry.ProEtale.nativeAdicCompactSupport_localizing_preservesCoproducts`.
The item's original count is 1; its remaining count is 0.

Also proved, with no new holes:

- `AlgebraicGeometry.ProEtale.NativeEncoding.encoding_boundedConstructible`
  (`lem-sf-native-adic-encoding-bounded-constructible`).
- `AlgebraicGeometry.ProEtale.nativeAdicProper_preservesCoproducts`
  (`lem-sf-native-adic-proper-coproducts`).

Holes closed: 1. Holes added: 0. Split-off sorry declarations: none. All private helpers
are proved. This proof uses existing declared geometric finiteness inputs as permitted
by stage 3; it does not claim their transitive axioms are already eliminated.

Validation: all three modules compiled with `lcompile.py`; the compile service accepted
every Lean run within its 60-second limit. The item signature, definitions, and public
imports were compared verbatim with the original, and all new node signatures and proof
dependency unions were checked. Profiling also confirmed that no declaration was expensive; the temporary profiler options
were removed. Delivery preflight is run by the delivery command.

## No longer needed

The following proof imports were removed from the item (all public imports stay):

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts`.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`.
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`.
- `Sheaf.AlgebraicGeometry.ModuleObjectPostnikovRoos`.
- `Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares`.
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`.
- `Sheaf.Paper.CondensedConstantConstructibility`.
- `Sheaf.Paper.OpenExtensionConstantModelConstructible`.
- `WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`.
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`.

The following original direct proof dependencies are no longer direct obligations of the
item; its node and its obsolete `tool_uses` approvals were pruned accordingly:

- `def-kun-truncations`.
- `det-def-sfb-constructible-local-model`.
- `lem-derived-exact-equivalence-squares`.
- `lem-module-object-postnikov-roos`.
- `lem-pc-separated-quasi-separated`.
- `lem-pur-ringed-site-grothendieck-abelian`.
- `lem-sf-derived-homology-long-exact`.
- `lem-sf-derived-truncation-triangle`.
- `lem-sf-locally-finite-coefficient-ring-realization`.
- `lem-sf-open-extension-zero-constant-model-constructible`.
- `lem-sfb-adic-proper-bounded-below-coproducts`.
- `lem-sfb-bounded-heart-amplitude-devissage`.
- `lem-sfb-grothendieck-k-injective`.
- `lem-sfb-internal-module-operations-transport`.
- `lem-sfb-proper-serre-heart-qbar`.
- `lem-weil-pbc-unbounded-derived-iso-cohomology`.
- `sk-def-sfb-constructible`.
- `sk-def-sfb-module-lower-shriek`.
- `sk-def-sfb-module-pushforward-pullback`.

The native open factor uses the existing compact-support realization rather than separately
reproving constant-model preservation. The fixed native encoding supplies the exact equivalence
and operation square. The adopted condensed `ProperLowerStarHeartHypotheses.preservesColimitsOfShape`
packages Postnikov--Roos, bounded devissage, and the unbounded truncation-window argument;
these were not reproved. Inputs still imported by these existing proved declarations remain
needed transitively. No library module or declaration is withdrawn, and no unit statement
or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The original twelve-step plan was longer than necessary:
the source library already proves the unbounded condensed coproduct consequence, and the
existing compact-support realization supplies native generator preservation without requiring
an independent open-extension stratification argument. The existing public
`nativeModuleConstructibilityComparison` uses a sectionwise presentation and separated
finite-type hypotheses, so its full statement is not a direct substitute for the one-way
fixed-encoding comparison needed here. The latter was proved directly from native
stratification and the existing fixed encoding, preserving the nonseparated scope.

## New nodes

`lem-sf-native-adic-encoding-bounded-constructible`, realized by
`Sheaf.Paper.NativeAdicEncodingConstructible`, records the generator comparison only:
there is no proper morphism or coproduct conclusion. Its proof treats rank zero, empty
covers/stratifications, arbitrary cohomological degrees, and the original finite support bounds.

`lem-sf-native-adic-proper-coproducts`, realized by `Sheaf.Paper.NativeAdicProperCoproducts`,
records the proper factor only, on the native source hull with ambient target. It assumes
no open factor and makes no assertion that arbitrary ambient coproducts are preserved.
Both nodes have complete Lean proofs, sources, proof steps, searches, and Lean attachments.
No change record is required: no existing statement or definition changed.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
