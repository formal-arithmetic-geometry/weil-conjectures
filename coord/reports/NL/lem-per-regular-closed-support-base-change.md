## Worker report

The module `Sheaf.AlgebraicGeometry.RegularClosedSupportBaseChange` states
`AlgebraicGeometry.Etale.regular_closedSupport_baseChange`. Its binders render the node as follows:
`ell` is a natural number with `Fact ell.Prime`; `X` and `P` are Noetherian schemes;
`r : P ⟶ X` is flat and `hreg` states geometrically regular fibres after every finite
residue-field extension; `hX` and `hP` state that ell is invertible on all stalks;
`i : Z ⟶ X` and `i' : Z' ⟶ P` are closed immersions and `sq : IsPullback q i' i r`
introduces the Cartesian base-change square. The coefficient object is
`ModuleCat (ULift (ZMod ell))`, the finite field coefficient ring in the site universe.

The conclusion is a conjunction. The first clause is `IsIso` of the ordinary derived
base-change map. The second is `IsIso` of the supported comparison
`closedSupportBaseChangePlus`; the third is its `NatTrans.CommShift` compatibility over
`ℤ`. The fourth clause is the displayed counit equation, for every bounded-below derived
object `M`: applying ordinary base change to the supported object, then the derived closed
pushforward and supported comparison, then the supported counit, equals pullback of the
original supported counit. Naturality is part of the natural-transformation type. The
module also gives the canonical non-hollow definitions `closedSupportCompPlus` (successive
closed supports), `supportTensor`, `supportTensorPullback`, `supportTensorProjection`,
`supportTensorProjectionPlus`, `supportTensorMatePlus`, and their canonical coefficient
transport maps; these are the maps used to express the Tate-twist and pasting compatibilities
in the proof docstrings. Every theorem proof is `sorry`; no theorem is asserted as proved.

Dependencies used are `Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange` for
`closedSupportPlus`, `closedSupportPlusAdjunction`, `closedSupportBaseChangePlus`, and the
derived base-change map; `Sheaf.AlgebraicGeometry.IsRegularScheme` for
`IsRegularScheme`; `Mathlib.AlgebraicGeometry.Morphisms.Flat` for `Flat`;
`Mathlib.AlgebraicGeometry.Fiber` for `fiberToSpecResidueField`; Mathlib's
`IsNoetherian`, `IsClosedImmersion`, `pullback`, `IsPullback`, `ULift`, and `ZMod`;
and `CategoryTheory.mateEquiv` for the canonical mate constructions. The recorded
`geometric_inverse_image_exact` dependency is imported as required by the node plan.

Edge cases checked: `ZMod ell` is used without assuming `ell > 0` beyond `Fact ell.Prime`;
`ULift` changes only the coefficient universe; the pullback square allows identity and
empty-support cases; Noetherianity and invertibility are imposed on both ambient schemes;
no excellence, finite-type, compactifiability, or constructibility assumption is introduced.
Searches in `searches.jsonl` used LeanSearch, LeanFinder, Loogle, and grep over Mathlib,
the source `WeilConjectures`, and `lean/Sheaf`; all returned no declaration for regular
closed-supported étale base change. The source was checked at Illusie--Laszlo--Orgogozo,
Exposé XVII, Corollary 4.2.3, Proposition 4.2.1, and Lemma the project server.

## Second reading by NL

I reread the DAG statement and the Lean signature. The Noetherian, flat, geometrically
regular-fibre, closed-immersion, invertibility, Cartesian-square, bounded-below, and all
four conclusion clauses are present with the same objects. `hreg` quantifies over every
finite residue-field extension exactly as the node requires. No excellence or finite-type
hypothesis was added. The coefficient universe is lifted with `ULift` only to match the
small étale site. The displayed counit composite has the same order and endpoints as the
node's mate normalization.

## New nodes

None. All notions used by the statement are recorded dependencies or Mathlib declarations.

## Dependency modules

None. The recorded dependency declarations are usable and imported directly.
