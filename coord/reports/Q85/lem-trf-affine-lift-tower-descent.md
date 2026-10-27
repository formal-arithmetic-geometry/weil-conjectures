## Worker report

This delivery states `AlgebraicGeometry.Monoscheme.affine_lift_tower_descent`
in `lean/Sheaf/TraceFormula/AffineLiftTowerDescent.lean`. Its only theorem has
proof `sorry`. Its helper structures unpack this very statement; its helper
functions have explicit data. No new independent notion, dependency replacement,
statement correction, or disputed statement is needed. The node copy changes
only `lean`.

Read the current node and all its statement dependencies and proof dependencies,
the recorded declaration signatures and docstrings, ILO VIII 3.1.4(iii),
3.1.11, 3.1.25--3.1.27, and Remark 2.3.5(ii)--(iii) in the supplied PDF. Read
the current blueprint's `lem-trf-local-term-locality.proof.md`; this is the
historical monoidal-resolution subargument recorded by the accepted split, not
a change of the current unit's contracting-correspondence route.

The correspondence between the informal statement and Lean is as follows.

- The full category C is the existing `Monoscheme.ResolutionInput`: its
  `monoscheme : Fine`, `torsionFree`, `sharpTorsionFree`, and `finiteCover`
  retain both torsion-free stalk conditions and a finite affine cover.
- The arbitrary procedure R is the existing
  `Monoscheme.SmoothFunctorialDesingularization`. Its `resolution`,
  `comparison`, `identityIndex`, `identityMap`, `compositionIndex`, and
  `compositionMap` supply precisely the towers, contracted pullbacks with
  centers, and the identity/composition compatibility. No additional
  functoriality, equivariance, or surjectivity hypothesis is added.
- The arbitrary fine torsion-free fan with finite cover is
  `F : FineFan.ResolutionInput`. The given finite sharp affine atlas and its
  disjoint union of actual monoscheme lifts are `C : Monoscheme.AffineLiftCover F`.
  Read its `fanChart`, `sharp`, `total`, `monoChart`, `sameMonoid`, `disjoint`,
  `coversFan`, `coversTotal`, and `onChart` fields. In particular `C.total` is
  the specified disjoint union, not an arbitrary global monoscheme lifting F.
- The length n is always `(R.resolution C.total).length`. No chart is
  independently resolved or contracted. `AffineComponentRestriction` has a
  tower of exactly this length, recursive `pullback`, the specified `baseMap`,
  open immersion on each level, and `inverseImage` equations for the next
  component. Its `sharpPullback` and `sharpMap` are the sharpening of that
  very uncontracted restriction. `AffineLiftCover.towerChart` merely transports
  the chart along the existing resolution's base equality. The extra two
  torsion-freeness fields in the component restriction are conclusions showing
  the individual L_i belong to C; C.total already records this for L.
- For each i,j,x in the overlap, `AffineOverlapNeighborhood` gives F_x.
  `generalizations` says y belongs exactly when y specializes to x;
  `smallest` states containment in every neighborhood. `inCharts` puts it
  in both charts. Its affine `chart` has `chartMonoid` equal to the actual
  stalk B, and `germBijective` pins the sections-to-stalk identification to
  the canonical germ, not an arbitrary abstract isomorphism.
- For ANY finite generating tuple, `principal` identifies the same F_x with
  D(a), where `neighborhoodGenerator` is the product of precisely those
  generators outside the prime. The library uses multiplicative monoids:
  this is the node's sum, with empty sum 0 represented by empty product 1.
  `chartPrime` sends the actual point through the fixed chart isomorphism.
- `localChart`, `localOpen`, and `localization` specify the actual unsharp
  restrictions of L_i over F_x. `localizationNumerator` fixes the numerator
  homomorphism to the localization inside the canonical completion;
  `IsAffineMap` and the equation over L pin the localization isomorphism and
  its restriction map, including their prime inverse images and germs.
- The conditional splittings in the node are the universally quantified
  `AffineOverlapSplitting N i hi` and `AffineOverlapSplitting N j hj`.
  `split` has target B times the finite free group, and `canonical` and
  `overFan` require that it be over this B. `splittingSection` uses the
  explicit section b -> split.symm(b,1) to characterize the contravariant
  map of sharp spectra. No arbitrary map is substituted for that map.
- For EVERY such pair of splittings, `AffineOverlapCommonLift` supplies
  an object `input : ResolutionInput`, with `affineIso` to the explicit
  spectrum of B times Z^s_i times Z^s_j. This is canonically the displayed
  B times Z^(s_i+s_j); the two-factor form retains the two specified maps.
  `commonLiftLeft` and `commonLiftRight` are the explicit homomorphisms
  a -> (b,u,1) and a -> (b,1,v). `leftCanonical` and `rightCanonical`
  characterize their spectrum maps. `leftSmooth`, `rightSmooth`,
  `leftSurjective`, and `rightSurjective` are conclusions, not assumptions.
- `leftToTotal`, `rightToTotal`, `leftComposite`, and `rightComposite`
  retain the two composites to L, and their smoothness is asserted.
  `leftTower`, `rightTower`, their full `PullbackTower` data and base-map
  equations retain every original index. `comparison`, `sameIndex`,
  `baseComparison`, and `unique` assert the canonical identification over V.
  The existing `TowerIdentification.arrows` and `.centers` assert all arrow
  and ideal equations. `sharpComposite` is the common identity over F_x;
  `sharpComparison` gives the identity of the two sharpened maps at every
  original level. Thus these comparisons fix the common ideals and all
  fraction generators of the existing blowup charts.
- The descended tower is `D.tower` of EXACTLY n stages with base `F.fan`.
  `D.pullback` identifies its uncontracted pullback with the sharpened tower
  on the single disjoint union, and `D.baseMap` fixes this to the given
  covering map C.map. `D.componentOpen` and `D.cover` assert that these
  component restrictions are an open cover at every level.
- At every stage k, `D.membership` says that a section belongs to the
  descended center iff all its restrictions through these actual component
  maps belong to the given local centers. This includes the first center
  and every later identified level. On open immersions, this is exactly
  restriction to W intersect U_i, written in the source opens rather than
  after the open-immersion isomorphism.
- Each `D.tower.blowup k` is the existing `FineFan.IsSaturatedBlowup`.
  It includes `IsNonemptyCoherentIdeal` and the exact `BlowupPatch` fraction
  charts with canonical maps and prescribed overlap localizations. This
  retains the node's nonempty stalks, coherent centers, and localized
  fraction gluing, rather than merely asserting an abstract blowup.
- `D.finiteCover` retains finiteness at every level, and `D.smooth` is
  smoothness of the actual last fan. `D.contracted` excludes exactly a
  globally whole-ideal isomorphism stage. It places no such exclusion on
  any component restriction, so local identity stages remain indexed.
- Uniqueness is `forall E, exists unique c : TowerIdentification ...,
  IsAffineDescentIdentification D E c`. This predicate fixes every index
  and makes the isomorphism commute with all the maps from the original
  sharpened tower. Uniqueness is over those fixed charts, as the node's
  proof specifies, rather than literal equality of independently bundled
  spaces. The induced overlap maps are through these same global levels;
  their composites cancel the intermediate identification, giving the
  cocycle identity. On the common lifts `sharpComparison` states the same
  map equality. The fraction-chart `IsAffineMap` equations pin these maps
  to the identities of localized fractions; no unspecified transition is
  being chosen.
- `(IsEmpty F.fan.space -> ...length = 0)` explicitly covers the empty
  fan, including any empty atlas. No `Nonempty` assumption occurs. Fin 0
  has no centers and all component or overlap quantifiers over it are
  empty. A nonempty smooth fan can also have n=0.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`:
  `Monoscheme.Fine`, `Chart`, `Hom`, their smoothness and torsion predicates,
  `affine`, `Fine.toFan`, `Tower`, `PullbackTower`, and `IsAffineMap`.
- `Sheaf.AlgebraicGeometry.FineFanBlowup`:
  `FineFan.ResolutionInput`, `Fan`, `Chart`, `stalk`, `germ`, `basicOpen`,
  `Tower`, `PullbackTower`, `wholeIdeal`, `IsSaturatedBlowup` and its
  `BlowupPatch`, `IsAffineMap`, and `IsNonemptyCoherentIdeal` interfaces.
- `Sheaf.TraceFormula.SharpeningFanBijection` provides the EXISTING helper
  definitions `Monoscheme.ResolutionInput`, `SmoothFunctorialDesingularization`,
  `AffineLiftCover`, `Chart.asFine`, `Chart.inclusion`, `affineFine`,
  `Tower.toFan`, `Hom.toFan`, `sharpSpaceMap`, and both namespaces'
  `TowerIdentification`. The downstream theorem `sharpening_fan_bijection`
  is neither invoked nor added as a DAG prerequisite. The maintenance route
  note expressly authorizes importing these existing helpers.
- Proof imports: `Sheaf.GroupTheory.FineMonoidUnitSplitting` and
  `Sheaf.AlgebraicGeometry.AffineFanLocalizationSections`, whose recorded
  theorem signatures and docstrings were read. Other named proof nodes
  (minimal neighborhoods, chart comparison, synchronization) have no
  recorded Lean module, so no fabricated import is added for them.
- `Mathlib.Geometry.RingedSpace.OpenImmersion` supplies the usual
  `SheafedSpace.IsOpenImmersion`; `Opens`, `Specializes`, `Finset.prod`,
  and monoid homomorphisms use their existing Mathlib definitions.

Edge cases checked before writing: empty fan and empty atlas; n=0 with
nonempty base; the zero sharp monoid (multiplicative singleton) and empty
monoid generating tuple; unit ranks zero; generic-point overlap; repeated
charts and disconnected fans; a whole-ideal identity on one component but
not globally; whole-ideal nonidentity saturation, which `contracted` retains.
All variables and universes are explicit (`autoImplicit false`). The helper
`splittingSection` has separate universes for its two factors, so the finite
free group in universe 0 does not force u=0.

Searches actually run through msearch.py, 2026-10-24:

- LeanFinder: `Synchronized affine monoscheme lifts descend to a finite
  saturated fan blowup tower`: 8 unrelated scheme inverse-limit hits,
  including `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`.
- Loogle: `Monoscheme, KatoFan`: zero hits; unknown identifier Monoscheme.
- Mathlib grep: `Monoscheme|KatoFan|fan.*tower.*descent`: zero hits.
- LeanSearch: `gluing finite saturated monoidal blowup towers on fine fans`:
  8 ringed-space, scheme or general category gluing results, not this node.
- Mathlib grep: `AffineLiftTowerDescent|AffineComponentRestriction|
  IsAffineDescentIdentification`: zero hits.
- Project rg (including --hidden --no-ignore to include ignored source
  directories): `AffineLiftCover|TowerIdentification|tower.*descent` and
  all new helper names. Found the existing sharpening helper interfaces,
  which are reused; no existing exact theorem or helper copy was found.
  Upstream item-id grep found no attachment. Searched dag/lean_names_upstream.json.
- `tools/blueprint_refs.py search 'affine lift tower'`: zero blueprint nodes.

The old diagnostic report and search log are retained in the sandbox;
`scratchpad/report-history.md` preserves the prior report verbatim. They are
not deliverable modules. The earlier non-module artifact failure ceased during
this session: the retained module probe passed through the standard wrapper,
and the completed module now compiles through that wrapper without supplying
or editing any dependency source. No library source or launcher tool was edited.

Validation: the complete file passed scompile.py separately in sandbox and
library module mode with no errors or warnings, within the 60-second limit.
Delivery dry run and final delivery follow after this report is written.

## Second reading by Q85

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
