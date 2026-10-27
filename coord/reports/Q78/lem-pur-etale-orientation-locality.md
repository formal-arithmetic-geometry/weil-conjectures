## Worker report

The delivery states `AlgebraicGeometry.ProEtale.RegularImmersionPurity.etale_orientation_locality`
in `Sheaf.Paper.EtaleOrientationLocality`. Its conclusion is the node's etale-locality assertion in
the fixed finite-coefficient coordinates already used by `pur9-rg-def-phi`: the canonical
five-arrow exceptional comparison, the unit-normalized rank-zero orientation, the
co-projection compatibility square for every invertible finite-Tor input, and the equation
`Phi_iU` transported by the comparison. The proof is `sorry` as required for stage 2.

The binders render the node as follows. `P : PurityFiniteSetting` is the fixed
`k, ell, E, n, Lambda` datum; all four schemes share universe `u` and have the required
`Over (Spec k)`, finite-type, separated, and quasi-compact structure hypotheses. The maps
`i`, `u`, `v`, and `iU`, their `IsOver` instances, the closed immersion `i`, and the etale
hypothesis on `u` are explicit. The closed-immersion property of `iU` is a conclusion. `sq : IsPullback iU v u i` is the fibre-product square.
`c : Nat` and `hi : PurityConventions.IsRegularOfPureCodimension i c` render the regular
closed immersion and allow `c = 0` (the empty regular sequence). `[Smooth (X ↘ Spec k)]`
and `hZ : IsRegularScheme Z` render the ambient smoothness and source regularity.

The conclusion is `@EtaleOrientationConclusion ...`, with all inferred instances made
explicit through the displayed `letI` binders in that definition. It supplies the
base-change conclusions (`IsClosedImmersion iU`, `Etale v`, finite type, quasi-compactness,
and separatedness of `V` and `iU`), smoothness of `U` and `V`, regularity of `V`, and the
same codimension predicate for `iU`. It then asserts both `EtaleUnitOrientation P u` and
`EtaleUnitOrientation P v`; these are the rank-zero chart identities identifying the
relative-dimension-zero diagonal orientations with `FiniteEtaleNormalization.eta`.
`etaleOrientationComparison` is the five-arrow paste: inverse normalized rho for `u`,
inverse exceptional compositor for `(iU,u)`, the equality transport from `sq`, the
compositor for `(v,i)`, and normalized rho for `v`. The conclusion asserts that this map
is an isomorphism. `EtaleCoprojectionCompatibility` universally quantifies the two
co-projections with their exact projection/counit characterizations and states the
co-projection square for arbitrary invertible finite-Tor inputs, hence for all Tate
shifts. Finally `EtaleOrientationEquation` states
`Phi_iU ; B = Lv^* ; Phi_i`, with the canonical zero-shift pullback comparison.

The dependency declarations used are: `Sheaf.Paper.RegularImmersionPurityComparison`,
`AlgebraicGeometry.ProEtale.RegularImmersionPurity.comparison` (restored in this delivery);
`Sheaf.Paper.PurityConventions`, `WeilConjectures.PurityConventions.IsRegularOfPureCodimension`;
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`,
`AlgebraicGeometry.SmoothOfRelativeDimension`, and `AlgebraicGeometry.Etale`;
`Sheaf.Paper.PurityDiagonalDualizingObject`,
`WeilConjectures.PurityFiniteSetting.diagonalDualizingObject`;
`Sheaf.Paper.DiagonalDncChartNormalization`,
`WeilConjectures.PurityFiniteSetting.diagonal_dnc_chart_normalization`;
`Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization`,
`AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.eta`, `rho`, `comp`, and
`finite_etale_dualizing_normalization`;
`Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility`,
`AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.etale_coprojection_rho_compatibility`;
`Sheaf.Paper.PurityTwistCancellation`,
`AlgebraicGeometry.ProEtale.purityTwistCancellationComposite`;
`Sheaf.Paper.PurityCompositionCoherence`,
`WeilConjectures.PurityFiniteSetting.compositionTwistPullback` and `compositionPowerAdd`;
`Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure`,
`AlgebraicGeometry.regularImmersion_smooth_structure_and_stalk_dimension`;
`Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`;
`Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`;
`Mathlib.RingTheory.Regular.RegularSequence`, `RingTheory.Sequence.IsRegular`; and
`Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`.

Edge cases checked are the empty scheme and empty inverse image (the comparison is the
zero map under the finite-clopen characterization), `c = 0` (empty regular sequence and
rank-zero/unit orientation), identity etale maps, disconnected schemes with components
of different dimensions, and arbitrary finite coefficient level `n >= 1`. No Kummer or
fundamental-class identification is included.

Searches for an existing statement or definition: `msearch.py ... leanfinder "Etale locality
of the exceptional smooth purity orientation of a regular closed immersion"` returned only
ordinary `IsEtale`, smoothness, and base-change declarations (no match); `msearch.py ...
loogle "AlgebraicGeometry.Etale, CategoryTheory.Iso"` returned 0 hits; `msearch.py ... grep
"etale.*orientation|exceptional.*pullback|upperShriek.*baseChange" AlgebraicGeometry`
returned 0 hits; and `rg` over `lean/Sheaf` and `lean/WeilConjectures` found no declaration
for this node. The recorded `pur9-rg-def-phi` interface was unusable because its module had
been deleted as unreachable, so the exact dependency module is restored under §1(B).

## Dependency modules

`pur9-rg-def-phi`: the recorded `Sheaf.Paper.RegularImmersionPurityComparison` had been
deleted from the live source although this item needs its canonical `comparison`. The
restored module states the dependency's exact notion: connected comparison fixed by the
positive cancellation equation, componentwise finite-clopen assembly, empty cases, and
canonical rho/compositor pasting. Its node `lean.note` records this interface repair. Its old signature also used the
obsolete `IsRegularImmersionOfPureCodimension`, which hard-codes `1 <= c`; the item
explicitly permits `c=0`. The restored definition therefore uses the existing
`PurityConventions.IsRegularOfPureCodimension`, which includes the empty regular
sequence, exactly as the recorded sk-def-purity-conv and sk-lem-regular-smooth interfaces
do. Over a smooth finite-type scheme the regular-sequence dimension formula recovers
the same stalkwise codimension equality. This is an interface repair of the old
signature, preserving the source's canonical composite, with no weakened conclusion.
The positive-only def-pur-regular-immersion module is still imported as recorded but is
not used to exclude the expressly required zero case.

## Second reading by Q78

No second reading by another worker: the dispatcher brief prohibits starting other agents.
The maintainer supplies the independent review after delivery. A final self-review matched
the hypotheses and all conclusion clauses as detailed above.

Validation: every delivered file compiled separately through scompile.py against the
live server build, with no errors or warnings. The initial dry run caught only node
signature-record mismatches; both records were repaired to match their files verbatim.
