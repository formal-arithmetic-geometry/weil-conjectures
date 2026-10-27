## Worker report

The main module is `Sheaf.AlgebraicGeometry.LogarithmicCoefficientTestEquivalence`.
It states the node without changing its natural-language statement. Every theorem has
proof `sorry`; every definition has real data. Four public theorems, all owned by the
same DAG node, state the main equivalence and its choices, smooth-pullback and zero-component
clauses. The thirteen-step proof is included in the main theorem's docstring, with the
relevant steps repeated in the companion theorem docstrings.

Hypothesis and clause correspondence:

- The rational ground field is `ULift.{u} ℚ`, permitting arbitrary scheme universes.
  `S : HilbertSamuel.Embedded (ULift ℚ)` contains `Z`, its rational structure map `p`,
  smoothness of `p`, and the finite ordered list `S.boundary`. Its intrinsic scheme,
  embedding and numerical level are unused bookkeeping: the marked test and equivalence
  predicates place no locus or presentation hypothesis on them.
- The smooth closed support `N ↪ Z`, coherent ideal `K`, and positive integer mark `d`
  are exactly `M : HilbertSamuel.Marked S`: `M.N`, `M.j`, `M.closed`, `M.smooth`,
  `M.ideal`, `M.coherent`, `M.marking`, and `M.positive`. Coherence uses the recorded
  finite-type quasi-coherent predicate on a smooth locally Noetherian support, as explained
  in the existing Marked docstring. `D.finite` and `D.supportFinite` give finite type
  together with smoothness (which already implies locally of finite type).
- The ordered SNC boundary and transversality to `N` are `D.boundary`, using the existing
  simultaneous etale-coordinate flag with both support and center equal to `M.j.ker`.
  This allows disconnected smooth boundary entries and absent labels; it does not impose
  irreducibility or a preferred coordinate chart.
- Order is the existing `HilbertSamuel.order`, the supremum of stalk-ideal containment
  thresholds. Cosupport is the existing `Marked.cosupport`, viewed by image in the ambient.
  `D.maxOrder` gives an open neighbourhood containing cosupport with order at most the mark;
  no global order bound and no closed-point restriction are imposed.
- `logDerivativeStep` retains the ideal and adjoins all derivatives of its elements by
  integer derivations preserving every boundary ideal individually. On rational algebras
  these are exactly rational derivations: derivations kill integers and inverses of nonzero
  integers. `logDerivativeIdeal` iterates it, so it includes every derivative of length at
  most j. `logDifferential` uses `IdealSheafData.ofIdeals` on this compatible affine family.
  Localization compatibility in this smooth setting follows from localization of the
  tangent module (the boundary equations are independent parameters); `ofIdeals` is a real
  construction, not a choice from an unproved existence statement.
- The chosen section, its derivative membership, smooth hypersurface, equation, order-one
  condition, and boundary transversality are `D.h`, `D.contact`, `D.H`, `D.i`, `D.closed`,
  `D.smooth`, `D.equation`, `D.orderOne`, `D.transverse`. Order one is imposed at its zeros,
  including nonclosed points; away from H a defining section has order zero. The hypotheses
  assert a chosen section and never infer existence of maximal contact from the order bound.
- `logarithmicCoefficientIdeal` is precisely the finite sum over `j ∈ Finset.range d` of
  `((logDifferential ... j).comap i) ^ (d.factorial / (d-j))`. Each denominator is positive
  on this range and divides `d!`. `IsLogCoefficient` identifies the specified H and ideal
  by an isomorphism over Z and sets `Q.marking = M.marking.factorial`.
- The main theorem asserts existence of a coherent marked realization and, for EVERY such
  realization, `M.cosupport = Q.cosupport ∧ RestrictedEquivalent M Q`. This identifies
  every permissible center and all subsequent cosupports, not just the initial sets.
- Existing `Step` and `Step.Transforms` supply smooth cosupport blowups, strict supports,
  division via the marking-th exceptional power, line products appending zero section,
  and distinct-labelled-boundary-intersection blowups with ordinary pullback. The new
  `RestrictedEquivalentThrough` uses these exact tests and transforms and adds the missing
  open restriction at EVERY intermediate stage, with existence and universal quantification
  over the actual cartesian marked pullbacks. Depth zero is cosupport equality; all depths
  give `RestrictedEquivalent`. No arbitrary maps replace the canonical geometric operations.
- `logarithmic_coefficient_choices` compares arbitrary two sections and supports of any two
  already test-equivalent representatives in a common ambient. Coordinates do not enter any
  constructed ideal; computing the same construction in any etale chart changes no input.
- `logarithmic_coefficient_smooth_pullback` handles any smooth f between finite-type rational
  ambients; it has no constant-relative-dimension, surjectivity or nonempty assumption. It
  asserts existence of the pulled-back coefficient data, cartesian support and hypersurface
  maps, equality of the pulled-back section and actual coefficient ideals, equality of
  cosupports by inverse image, and the marked pullback and test identification for all
  coefficient realizations. Open restrictions are included as smooth morphisms. All support
  and ideal identifications are canonical via the displayed cartesian relations, including
  identity maps and arbitrary isomorphic realizations of their pullbacks.
- `logarithmic_coefficient_zero_component` takes any open irreducible component U of the
  smooth H, with actual coefficient ideal zero on U. It states that its whole ambient image
  is in cosupport, existence of a permissible blowup of its scheme-theoretic image, and
  vanishing of the transformed cosupport over that image for EVERY such blowup and
  transform. This includes zero-dimensional components and the entire hypersurface. No
  nonzero-coefficient assertion is present.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact` (finite type is their conjunction).
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType`, through the existing `Marked.coherent`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`,
  through the existing Step geometry. `WeilConjectures.Compactification.StrictTransform`:
  `strictTransform`, `strictTransformMap`, `strictTransformToSource`, through Step.Transforms.
- `Sheaf.AlgebraicGeometry.HilbertSamuelPresentation`: `Embedded`, `Marked`,
  `Marked.cosupport`, `Step`, `Step.Admissible`, `Step.Transforms`, `EquivalentThrough`,
  `MarkedPullback`; `Sheaf.AlgebraicGeometry.MarkedIdealOrder`: `stalkIdeal`, `order`.
- `Sheaf.AlgebraicGeometry.EtaleCoordinateFlag`: `HasEtaleCoordinateFlag`.
- Mathlib's `Derivation ℤ R R`, `IdealSheafData.ofIdeals`, `ofIdealTop`, `comap`, actual
  ideal sums and powers, factorial, and `IsPullback`; no copies of those notions.

Every presently recorded proof dependency module is imported privately. The only unstated
proof dependency at the time of writing is `lem-trf-logarithmic-derivative-single-transform`;
it is not needed to TYPE this statement and has no module to import. Its single-transform
and smooth-base-change arguments are explicitly named in the proof plan; no wait or cycle
is introduced. Proof imports include the recorded regular-local, associated-graded,
etale-coordinate/Taylor, formally-etale lifting, marked-blowup, permissible-chart and
smooth-tangent-cone modules.

Edge cases checked: empty ambient and support; empty boundary; unit ideal and empty
cosupport; zero ideals with infinite order; d=1 (the sum has only j=0 with exponent one);
vanishing coefficient on a positive- or zero-dimensional open component; deletion of an
entire support component; absent boundary labels; products with a line; distinct labels
for exceptional intersections; open restrictions at any finite stage; nonclosed points;
non-surjective smooth pullback; variable relative dimension; identity pullbacks; arbitrary
isomorphic realizations. The maximum-order hypothesis rules out a zero original ideal on a
nonempty open neighbourhood of its cosupport but does not rule out a zero coefficient ideal.

Sources read: ILO PDF printed pp.93--94, VIII 2.3.11--2.3.13; BMT original paper online,
https://arxiv.org/html/0905.3580 sections 5.1--5.4. ILO attributes the algorithm; BMT 5.4
explicitly gives coefficient restriction equivalence and the logarithmic construction.
The node's detailed thirteen-step argument supplies the factorial convention and zero case.
No statement correction or statement dispute was needed.

Searches: the prescribed msearch LeanFinder, Loogle, grep and LeanSearch calls are preserved
in `mathlib_searches` of each new node, including their exact returned records. Queries:
"Logarithmic differential coefficient ideals preserve finite test sequences of marked ideals
on smooth schemes" (ordinary differential and smooth-chart hits); Loogle
`"Derivation", "Ideal"` (two Lie-derivation hits); grep
`logarithmic.*ideal|coefficientIdeal|testSequence` in AlgebraicGeometry (0);
LeanSearch "Ideals generated by logarithmic derivations and factorial weighted coefficient
restriction to hypersurfaces" (ordinary differential/log-derivative and polynomial ideals);
LeanFinder "Equivalence of marked ideal test sequences including arbitrary open restrictions"
(local scheme-equality hits); grep `EquivalentThrough|MarkedPullback|logDifferential|logCoefficient`
in Mathlib (0); LeanSearch on finite marked tests with restrictions (ordinary support/ideal
sheaf hits). None is the statement or missing notion. Direct rg in WeilConjectures found no
node-id match and only an unrelated private power-series coefficient ideal. Direct rg in
Sheaf found the existing HilbertSamuel marked-test definitions, which are reused. DAG and
blueprint searches for logarithmic differential ideal and logarithmic coefficient gave no
matching definition. The existing log-differential-stalk nodes concern log structures,
not derivative ideals in marked resolution. The existing test relation was opened in full:
`TestKind` has exactly three constructors, so it cannot express intermediate open restrictions.
Upstream declaration names were also searched; no name collision found.

Validation: all three files compiled through scompile.py on the live server, one file at a
time. The only initial interface issue was the missing public ULift-field instance import;
adding `Mathlib.Algebra.Field.ULift` repaired it. Final compiler output has no errors or
warnings. No local/global build or direct git command was used.

## New nodes

`def-trf-logarithmic-coefficient-ideal` owns
`Sheaf.AlgebraicGeometry.LogarithmicCoefficientIdeal`: the integer/rational logarithmic
single derivative, its iteration, the sheaf construction, factorial coefficient ideal,
chosen-section input data and marked coefficient realization predicate. Source: ILO VIII
2.3.13 and BMT 5.4. Searches above found no existing node or declaration for these notions.
The existing marked data, order, boundary-coordinate predicates and sheaf operations are
used directly. There are no proof placeholders in this definition module.

`def-trf-restricted-marked-tests` owns
`Sheaf.AlgebraicGeometry.RestrictedMarkedTests`: finite-depth equivalence with arbitrary
intermediate restrictions. Source: the node's explicit local-test convention and BMT 5.2.
It reuses the complete existing Step and transform relations and adds only the missing
open case, rather than introducing a second blowup or controlled-transform construction.
Searches above and reading every existing test constructor establish the missing case.
There are no proof placeholders in this definition module.

## Returned-delivery repair

The return for immutable head `7f7fd66be71d` identified a dangling statement dependency
`def-trf-marked-ideal-invariant-data` in the new coefficient-ideal definition node.
The retained packet repairs that dependency list: its marked datum is supplied by
`def-trf-hilbert-samuel-presentation`, whose recorded module
`Sheaf.AlgebraicGeometry.HilbertSamuelPresentation` defines `Embedded`, `Marked`,
`Marked.cosupport`, and the geometric test and transform relations actually imported here.
The coefficient definition's other direct dependencies are `def-trf-marked-ideal-order`,
`def-sbc-ideal-sheaf-powers`, and `def-trf-etale-coordinate-flag`. It no longer references
the missing invariant-data node. This is a dependency-record repair of a new definition
node; the item's mathematical statement and the three Lean modules are retained.

On this retry I checked every `stmt_deps` and `proof_deps` entry of all three packet nodes
against the repository's node IDs plus the packet's new nodes: all resolve. I reread the
coefficient and restricted-test definitions, their imported marked-data/order/coordinate
interfaces, and all four theorem signatures. The saved packet passed the initial
`deliver2.py --no-push` on the current server base as commit `73db9b32942`, including all
three per-file compiles. No auto-implicit binders or lines over 100 characters occur.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
