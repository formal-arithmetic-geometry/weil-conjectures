## Worker report

Item: lem-trf-generic-center-formal-normal-slice. The module is
`Sheaf.AlgebraicGeometry.GenericCenterFormalNormalSlice`; its main declaration is
`AlgebraicGeometry.exists_genericCenter_formalNormalSlice`. The sole postponed proof
is that theorem, with the twelve-step natural-language DAG proof in its docstring.
The four helper definitions contain real data or explicit propositions, never `sorry`.
The node's mathematical statement, proof, and proof dependencies are unchanged.
Its statement dependencies gain the already-landed definition nodes
`def-trf-marked-ideal-order` and `def-per-adapted-normal-crossings-center` because their
existing notions occur in the signature. The repair additionally records the existing parameter-chart data in the new definition
node `def-trf-parameter-chart-ring` and adds `def-nagata-blowup-chart-ring` to
statement dependencies, as requested by the return. No dependency modules are needed.

Hypothesis-by-hypothesis reading:

- The ambient rational scheme is `Z : Scheme.{u}` with
  `p : Z ⟶ Spec (.of (ULift.{u} ℚ))`. The lift merely places Q in the scheme universe.
  `[Smooth p]`, `[LocallyOfFiniteType p]`, and `[QuasiCompact p]` say smooth and finite
  type over Q, with no separatedness, equidimensionality or rational-point assumption.
- `E : List Z.IdealSheafData` is the finite ordered boundary, and `hE` applies the
  recorded `IsStrictNormalCrossingsBoundary` to `E.prod`. `hlabels` says its component
  supports are distinct; `hcomponents` says the labelled entries are integral closed
  components. Together with the reduced effective Cartier product, these express that
  E lists the boundary components, rather than labelling arbitrary grouped divisors.
  Their regularity and regular intersections follow from the recorded SNC predicate.
- `s`, `hs : 1 ≤ s`, `N`, and `i` give the finite nonempty list of supports and their
  closed immersions. `[∀ j, Smooth (i j ≫ p)]` gives their smoothness; their finite
  type follows from closed immersion into the finite-type ambient scheme.
- `htransverse` is the existing `HasAdaptedNormalCrossingsCenter` on the zero ideal
  of each support with the restricted labelled boundary. The zero ideal has the whole
  scheme as support, so this condition is imposed at every point. In its definition
  the center equation list must be empty: a nonempty sublist of regular parameters
  cannot generate the zero ideal. Thus its remaining content is precisely that the
  boundary equations through each point are distinct regular parameters, with unit
  ideals for the other labels. This is not an additional adapted-center hypothesis.
- `x`, `y`, and `hy` specify the common point and its preimage in each closed support.
  Closed immersions are injective, so choosing these preimages is exactly membership
  in every support, and imposes no extra condition on the point or its residue field.
- `I j` is the quasi-coherent ideal on `N j`, using `IdealSheafData`. `hI` uses the
  recorded exact coherence predicate `RingedSpace.IsCoherent` on `(I j).toModules`;
  it includes the finite-type-kernel condition, not just finite generation.
- `d`, `hd : ∀ j, 1 ≤ d j`, and `horder` give the positive marks and the stalk
  containments in the corresponding maximal-ideal powers. `HilbertSamuel.stalkIdeal`
  is the existing germ-generated ideal, not a second stalk construction.

Conclusion-by-conclusion reading:

- `∃ U hx` is one ambient open neighbourhood common to all j. `T` is pinned by
  `T = genericCenterIdeal U.toScheme ⟨x,hx⟩`. This helper is the existing vanishing
  ideal of the topological closure of that singleton, hence the reduced closure.
- `Smooth (T.subschemeι ≫ U.ι ≫ p)` makes that actual reduced closed center smooth
  over Q. Its closed immersion is the canonical `T.subschemeι`.
- For every boundary label k, the two implications give scheme-theoretic containment
  of T in a component through x (the inequality of ideal sheaves is reversed from
  containment of closed subschemes), and the unit ideal for every component missing x.
- For each j, `(i j).ker.comap U.ι ≤ T` puts T inside the restricted support.
  `HasEtaleCoordinateFlag` is used verbatim for the ambient/support/center flag and
  the restricted ordered boundary. Its subsets B ⊆ A and disjoint boundary labels
  give the asserted local generation by etale coordinates on the support, including
  the boundary equations: the additional boundary-ideal containment forces every
  boundary coordinate through T to occur among the center coordinates.
- `T.comap ((i j) ∣_ U)` is the center ideal in the restricted support, using the
  canonical restricted immersion, not an arbitrary map. The following smoothness
  clause makes its subscheme smooth over Q. The power inequality gives the spread
  containment of the restricted I_j in its d_j-th power. The last implication spreads
  a zero stalk to the zero ideal on the restricted support, in particular near T.
- The second main conjunct works with the original stalks, canonically unchanged by
  shrinking. The Noetherian structure is in the conclusion as `∃ hR`; it is not an
  added assumption. `HasGenericCenterFormalCoordinates` supplies a finite parameter
  system and a *single* coefficient section c valid for *every* regular parameter
  system, so the universal assertion is not vacuous.
- The coefficient field is exactly `Z.residueField x`. `genericCenterResidueMap` is
  the canonical residue-field map of `i j`, transported along `hy j`. Its bijectivity
  is asserted, and `evalOneₐ (c b) = ε b` identifies the coefficient section with
  this specified residue field, not a freely selected field isomorphism.
- `IsRegularSystemOfParameters (List.ofFn v)` includes generation of the maximal
  ideal and `(List.ofFn v).length = ringKrullDim R`; thus the series ring has exactly
  n_j variables. The equivalence ψ sends constants to c and variables to the images
  of the prescribed parameters in the completion. Its ideal-comap equations express
  preservation of the adic filtration in both directions.
- The first ideal-containment iff in the formal predicate preserves and reflects
  containment in every maximal-ideal power. The second iff detects the zero ideal.
  For every prescribed parameter v_i, the later iff does the same for `(v_i)^q`.
  This covers every chosen boundary parameter and the case q = 0.
- For all affine-space dimensions r, all coordinate subsets J, and every permitted
  pivot, `HasGenericCenterChartCoordinates` uses the existing `ParameterChartRing`,
  its coordinate-origin ideal, its localization and its maximal-ideal completion.
  Origin maximality is asserted, and all following clauses quantify over its prime
  instance; there is no unproved instance installed in a definition.
- The completed structural map g is pinned at *every quotient level*, including
  its agreement with the actual `parameterChartStructuralMap` on original ring
  elements. The residue equivalence ε and the equation on g(c b) make the transported
  coefficient field precisely the same F. The equivalence Θ sends constants to g(c b)
  and each labelled chart variable to its actual coordinate germ in the completion.
- The Θ-comap equations give the completed coordinate filtration. The substitution
  equation sends the pivot to itself, other center coordinates to pivot times ratio,
  and outside coordinates to themselves. The total-degree truncation congruence
  states the resulting substitution on *all* series with those fixed coefficients,
  not merely its effect on polynomial variables. It works with every ψ having the
  stated constants and parameters. Compatibility on compositions follows from these
  specified actual completed maps and successive transport of c, as in proof step 12.
- The final algebra equivalence e identifies this displayed quotient with
  `AffineBlowup.chartRing` of the actual coordinate ideal in R[t], as an algebra over
  R[t], and sends each quotient variable to the specified chart fraction. Therefore
  the completion is the local completion of the coordinate blowup chart after
  localizing at the original point, not a completion at an unrelated F-rational point.
  The localization A[P/a] -> R[m/a] is the fraction identification in proof step 10.
  The case J empty, a none gives the product comparison; J nonempty gives the
  blowup charts. For the pair (N_j,T) take r=0 and J all parameter labels.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` (inside the imported flag).
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`, exposing
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`; and
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: `toModules`.
- `Sheaf.AlgebraicGeometry.EtaleCoordinateFlag`: `HasEtaleCoordinateFlag`;
  `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `IsStrictNormalCrossingsBoundary`;
  `Sheaf.AlgebraicGeometry.AdaptedNormalCrossingsCenter`:
  `HasAdaptedNormalCrossingsCenter`;
  `Sheaf.AlgebraicGeometry.MarkedIdealOrder`: `HilbertSamuel.stalkIdeal`.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`;
  `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` through the parameter predicate.
- `Mathlib.RingTheory.AdicCompletion.Basic/Algebra/LocalRing`: `AdicCompletion`,
  its algebra map and `evalₐ`/`evalOneₐ`;
  `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `C`, `X`;
  its `Trunc` module: `truncTotal`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`;
  `WeilConjectures.Blowup.Affine.ChartAlgebra`: `AffineBlowup.chartRing`,
  `chartFraction`, and its homogeneous-chart comparison;
  `Sheaf.RingTheory.ParameterChartCompletionSubstitution`: the recorded
  `IsLocalRing.parameterChart*`/`ParameterChart*` rings and canonical maps.
  Its main theorem is the proof dependency supplying the formal-chart comparison.
- All available recorded proof-dependency modules are imported, with plain imports
  when only the proof uses them. Mathlib leaves are imported by their recorded
  modules (prime-spectrum topology, separably generated fields, completion,
  faithfully flat modules). `lem-trf-etale-coordinate-derivations-jacobian` has no
  recorded Lean declaration, Mathlib match or closed upstream audit, so there is
  no module for it to import. Its proof role remains in the docstring.

Edge cases checked before writing and again against the finished signature:

- No boundary labels: the list, label function and all boundary quantifiers may be
  empty; no nonempty boundary assumption appears.
- Nonclosed x: no closed-point or Q-rationality premise appears; the coefficient
  field is κ(x), and the center is its entire reduced closure in U.
- n_j = 0: `Fin 0` and the empty parameter system are allowed. For r=0 no nonempty
  center has a pivot, and the only chart clause is the product/empty-center one.
  The completion equivalence is the zero-variable series ring F. The hypothesis
  I_x ⊆ m^d with d≥1 forces I_x=0, and the geometric zero-spreading clause applies.
- I_j=0, d_j=1, zero-dimensional or disconnected supports: none is excluded.
  An empty ambient scheme or empty support cannot supply the chosen common point,
  exactly as in the informal hypotheses; empty opens in coordinate covers remain allowed.
- r=0, arbitrary r, empty J, singleton J, a pivot among added affine variables,
  a center consisting only of some boundary parameters, and a center omitting
  some original parameters are all covered by the displayed chart quantifiers.
- No denominator is a nonexistent parameter. A one-generator chart has no ratio
  variables, with the original pivot unchanged. q=0 means the unit ideal as usual.
- All universes and variables are explicitly bound (`set_option autoImplicit false`).
  No equality of independent site or field universes is imposed: these rings and
  residue fields arise from the same Scheme universe.

Searches (2026-10-24; prescribed msearch.py, Q71/item):

- LeanFinder query: `A smooth scheme in characteristic zero admits a smooth reduced
  closure of a point locally and completed normal coordinates with boundary`.
  Result: 8 hits, including `IsSmooth.exists_isStandardSmooth` and
  `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`; none states this combined result.
- Loogle query: `AdicCompletion, IsRegularSystemOfParameters`.
  Result: zero hits; the public service does not know the project parameter predicate
  (`unknown identifier 'IsRegularSystemOfParameters'`). The recorded local definition
  was read directly and used.
- LeanSearch query: `Completion of a regular local ring over a field is a power series
  ring over the residue field`. Result: 8 hits, including
  `PowerSeries.residueFieldOfPowerSeries`, completion/residue-field constructions and
  Weierstrass division; no theorem with this geometric and chart statement.
- msearch grep query: `normalSlice|generic_center|coefficient.*field` under Mathlib
  AlgebraicGeometry. Result: zero hits.
- Direct rg of Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json for
  `GenericCenter|genericCenter|generic_center`: no declaration of this result.
  Direct rg of WeilConjectures for the item id: no matches. Wider searches for
  `generic.center|normal.slice|formal.normal` found unrelated support-coordinate and
  tame-normalization material, and the existing flag/parameter-chart declarations
  were read in full. Searching stalk-ideal and adapted-center definitions found the
  two landed interfaces cited above; they are reused rather than duplicated.
- Source places read locally: varieties.tex, lemma-dense-smooth-open-variety-over-
  perfect-field (0B8X); more-morphisms.tex, lemma-etale-local-structure (0FUE);
  algebra.tex, lemma-regular-complete-containing-coefficient-field (0C0S).
  The argument in the node explicitly combines these sources with ideal spreading
  and chart calculations; it is not claimed to be verbatim in any single tag.

No statement dispute or source-based correction was needed. The example module
`Sheaf/CategoryTheory/CompactObject.lean` is currently withdrawn and contains no
remaining declarations; its node records Mathlib's existing compactness predicate.
The required module-mode/public-interface conventions were followed.

Validation: scompile.py compiled the sandbox probe and the intended library module
without errors or warnings (10.8 s and 6.7 s). No local or global build was run.

## Second reading by Q71

I reread the original node beside the complete module after compilation. The ambient
hypotheses, labelled component assumptions, nonempty support family, common point,
coherence and positive order are each present as described above. The output is
one common neighbourhood, not a separate neighbourhood for each j. The center is
pinned to the reduced closure; the flag uses the recorded predicate with ideals in
the correct direction. The ideal containment and zero case use the restricted
support's center ideal, rather than the ambient center ideal. The formal half uses
the *ambient* κ(x) via the canonical residue map and one common coefficient section
for all parameter systems. Every chart carries the actual quotient-localization
structural map and a base-algebra equivalence to the fraction chart. Products,
partial coordinate centers, the empty parameter list, and arbitrary residue fields
remain covered. The only adjustment in this reading was to spell out the exact
etale-coordinate-Jacobian dependency identifier in the proof docstring. No theorem
signature or node statement changed. This is a separate reading pass by this worker;
the maintainer's independent review is still required and is not represented here
as having taken place.


## Repair of immutable head 2ccb842950bc

H2 is repaired by adding `def-trf-parameter-chart-ring` under §1(A), binding exactly
the thirteen existing `IsLocalRing.parameterChart*`/`ParameterChart*` definitions in
`Sheaf.RingTheory.ParameterChartCompletionSubstitution`, and adding that new owner
and `def-nagata-blowup-chart-ring` to the item's statement dependencies. The latter
owns `AffineBlowup.chartRing` and its fractions as described in its recorded note.
The statement source remains publicly imported, as does the affine fraction-chart
module. The theorem node remains a proof dependency for its completion comparison.

I checked `def-trf-parameter-blowup-chart-ring` and
`def-trf-permissible-coordinate-chart-ring` and read their recorded source definitions.
They own the fixed-pivot quotient and ratio/strict-transform equations. Neither owns
the option-pivot dummy-label encoding, origin ideal, prime localization, structural
and completion maps, completed ideal or power-series substitution used in this item.
The new definition node records existing code and cites the general quotient node;
it introduces no second construction or Lean source file. Its exact source signature
is copied through the keyword before `:=`; all thirteen names are listed in
`lean.declarations`. The node explicitly describes even the total definitions for
unusable optional pivots; no validity or primality theorem is claimed.

Advisory repaired: the `HasGenericCenterChartCoordinates` docstring now explicitly
says the fraction chart is taken after localizing at the original point x and that
these clauses provide no global blowup comparison. The previously reviewed theorem
signature and every helper body remain unchanged. The retained node was compared
field by field with current main: only the expected `lean` record and appended
statement dependencies differ. The delivery wrapper rebases onto its current base.

## New nodes

`def-trf-parameter-chart-ring`: the existing parameter chart over R[t], its
concatenated parameters, embedded center labels and optional pivot, quotient relations,
structural polynomial map, labelled coordinates, origin ideal, localization at a
prime origin, its structural map and maximal-ideal completion, completed ideal and
canonical map, and the variable substitutions. Source: the explicit construction in
Tag 0C0S's parameter-chart application, generic-normal-slice proof steps 10--12 and
the chart calculation of Tag 0804. All data are the existing thirteen definitions
in `Sheaf.RingTheory.ParameterChartCompletionSubstitution`. The node is
`existing:true`, with no new module. Its searches record LeanSearch (8 generic
localization/quotient hits), LeanFinder (8 Weierstrass quotient hits), Mathlib grep
(0 hits), project and DAG grep (only the theorem's existing source and record), and
blueprint search (21 unrelated or general parameter mentions). The two existing
fixed-pivot definition nodes were compared as above. None records the whole datum,
so this ownership node supplies the missing statement dependency without copying code.

Second reading of the repair: each new-node clause was compared to the thirteen
source bodies. The dummy label has value zero and never belongs to the embedded
center; option none uses that label. The coordinate origin uses the original n+r
labels, not the dummy. Localization definitions require primality, while the quotient
and substitution definitions are total. In the substitution, an absent pivot uses
the current index as its default, exactly as `a.getD i`. Empty labels and n=r=0
remain valid. The new node has no theorem or new sorry. The two new owner edges
match all definitions named in H2. No mathematical assertion was added or removed.
