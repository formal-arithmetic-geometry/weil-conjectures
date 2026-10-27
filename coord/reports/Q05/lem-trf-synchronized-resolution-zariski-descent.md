## Worker report

The item is stated by `AlgebraicGeometry.exists_synchronized_resolution_zariski_descent` in
`Sheaf.AlgebraicGeometry.SynchronizedResolutionZariskiDescent`. Its only theorem proof is
`sorry`. The accompanying definition node supplies the missing labels, embedded-input
membership, open-only rule and affine synchronization predicates, using real structures and
predicates throughout. No definition chooses a tower, map or ideal from a postponed theorem.
The item's mathematical statement, accepted split and proof dependencies are unchanged.

Source read: ILO, Travaux de Gabber, VIII 2.3.1, 2.3.4 and Remark 2.3.5(ii), printed
pp.91--92 (PDF pp.97--98), and the ordinary-tower conventions 2.1.4--2.1.9.
The source explicitly distinguishes contracted chart resolutions from the uncontracted
restrictions of the resolution of the disjoint union. The node is the accepted conditional
labeled expansion of that argument, rather than the existence theorem for resolution.
The module docstring reproduces all ten accepted proof steps, with their dependency ids.

Hypotheses, individually:

- The totally ordered label set is `(L : Type w) [LinearOrder L]`; the label universe `w`
  is independent of the scheme universe `u`. `LabeledOrdinaryTower.label` is an order
  embedding `Fin tower.length ↪o L`, giving distinct increasing labels without any
  countability or finiteness restriction on L.
- Reduced finite-type rational schemes are exactly the recorded `RationalResolutionInput`:
  its fields are `scheme`, `structureMap`, `reduced`, `finiteType` and `quasiCompact`.
  Its base is `Spec (.of (ULift.{u} ℚ))`, which only lifts the size of the rational field.
  No separatedness, connectedness, dimension or nonemptiness hypothesis is imposed.
- The class C is `RationalResolutionInput.IsEmbeddable`: existence of the recorded
  `EmbeddedResolutionPair` and an isomorphism of the given scheme to its X, over Q.
  `EmbeddedResolutionPair` has the closed immersion into a smooth separated finite-type
  ambient. The input embedding is existential rather than part of the argument to A;
  therefore different choices cannot give different assignments on the same scheme.
  Finite disjoint unions satisfy precisely this condition, by disjoint union of the
  ambients; no component is required to be connected or to have a common dimension.
- A is the argument `OrdinaryZariskiResolutionRule L`. Its `tower` assigns the existing
  `OrdinaryBlowupTower` equipped with the labels, for every member of C.
- Its `resolves` field is the recorded `OrdinaryBlowupTower.IsRegularResolution`:
  every center ideal is `ofFiniteType`, has nonempty support, has nowhere dense support,
  and its subscheme is `IsRegularScheme`; the last level is `IsRegularScheme` too.
  Supports are closed sets, so `IsNowhereDense` is precisely empty interior here.
  The separate `coherent` field uses `RingedSpace.IsCoherent` on the actual ideal module,
  including the finite-type-kernel condition, not just quasi-coherent finite type.
- `A.empty` says `IsEmpty S.scheme → tower.length = 0`; empty inputs are not excluded.
- `A.comparison` ranges over every open immersion over Q between members of C.
  It uses `LabeledOrdinaryComparison`, extending the recorded
  `OrdinaryResolutionComparison`: all level squares are cartesian, transitions commute,
  the retained ideal is exactly `IdealSheafData.comap` of the old ideal, and
  `deleted_iff_unit` deletes precisely the unit ideals. Its extra `labels` field preserves
  the retained labels. A proper ideal whose blowup is already an isomorphism is retained.
  The comparisons are canonical ordinary blowup comparisons: cartesian squares and
  equality of the full ideals force the unique lifts at each successive ordinary blowup.
  No arbitrary comparison map is accepted in place of these conditions.

Conclusions, individually:

- `∃ R : ∀ S : RationalResolutionInput, LabeledOrdinaryTower L S.scheme` extends to all
  reduced finite-type Q-schemes, including nonseparated ones.
- `(∀ S, (R S).IsResolution)` retains the ordinary blowup equations in the underlying
  tower, coherent nonempty nowhere dense regular centers, and regular final level.
  The `IsResolution` predicate also records `LocallyOfFiniteType` and `QuasiCompact`
  of the composite structure morphism at every level, exactly the final finite-type clause.
- `(∀ S, IsEmpty S.scheme → (R S).tower.length = 0)` is the trivial empty assignment.
- On each original input, `Nonempty (Unique (LabeledOrdinaryCartesianMap (𝟙 _) ...))`
  compares R(S) with A(S), retaining all labels and full ideals. A cartesian square over
  the identity has an isomorphism as its top map, so these are canonical tower isomorphisms.
  This is a uniquely specified comparison structure, not an arbitrary Nonempty choice.
- `A.IsSynchronizedDescent S (R S)` quantifies over EVERY finite affine cover.
  `ResolutionAffineCover` records affine opens covering S, their actual disjoint union
  by `IsColimit (Cofan.mk ...)`, its map q, and the over-Q equation. The index is `Fin size`,
  allowing size zero. Every finite family can be enumerated in this way; duplicates and
  empty members are permitted. There is no affine-intersection hypothesis.
- Its `LabeledOrdinaryCartesianMap q (R S) (A.tower T hT)` extends the existing
  `OrdinaryTowerCartesianMap`: `length_eq` and `labels` give exactly the same ordered
  label list, `cartesian` gives every scheme-theoretic pullback square, `arrows` the
  transition squares, and `centers` equality of full extended center ideals. It has no
  retained-stage embedding and cannot contract a stage. `DescendsIdeals` additionally
  asserts uniqueness of the global quasi-coherent ideal with the given restrictions.
  Coherence and the next ordinary blowup are already asserted for R. Hence the ideal
  is descended at each label, including stages unit on individual charts.
- `A.HasPaddedOverlaps` explicitly gives a COMMON FULL tower P over an affine W for
  three open lifts into the covering total space over the same open map to S. For two
  chart restrictions use a repeated third lift. The cartesian maps preserve all labels
  and ideals. The contracted comparison from A(W) to P deletes exactly the unit ideals
  and retains its labels. Thus P restores exactly the missing unit-ideal identity stages.
  The same P on three lifts is the triple-overlap agreement, rather than an isomorphism
  only of terminal schemes. Any affine W in an overlap supplies these open lifts; W is
  not required to be the whole intersection. The conclusion quantifies over all affine W.
- The next conjunct asserts equality of the label ranges for ANY TWO covering total
  spaces. In particular take the second cover to be the combined covering family: neither
  original family loses a label. Since the label embeddings are increasing, this is
  equality of the ordered label lists, not merely an unordered relabeling.
- `A.IsAffineDescent S B` means B is a tower constructed using some finite affine cover.
  The next conjunct gives its UNIQUE full cartesian comparison with R(S), over the identity,
  preserving all labels and center ideals. It applies also to the construction for the
  combined covering family. Consequently the comparisons through that combined family
  give the very same canonical identification between two cover constructions.
- The last conjunct states transitivity directly: for ANY three cover constructions B,C,D
  and their comparisons bc,cd,bd, `bc.IsComposite cd bd` means
  `cd.map i ≫ bc.map (Fin.cast ... i) = bd.map i` at EVERY level. Equality of the ordered
  indices uses the comparisons' length equalities. Since the structures already preserve
  labels and actual ideals, this is the required transitivity of those identifications.
- Uniqueness of the extension is pointwise uniqueness against every affine descent B.
  An alternative extension satisfies the cover condition and hence is such a B at every S.
  The unique comparisons above are its canonical isomorphisms to R and the last conjunct
  gives their coherence.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`: `RationalResolutionInput`,
  `OrdinaryBlowupTower`, its `toBase` and `IsRegularResolution`,
  `OrdinaryResolutionComparison`. The smooth-rule structure is deliberately not used:
  the item assumes open comparisons only.
- `Sheaf.AlgebraicGeometry.LabeledEmbeddedResolution`: `EmbeddedResolutionPair`.
  Its stronger labeled EMBEDDED towers are not copied or used as ordinary intrinsic towers.
- `Sheaf.AlgebraicGeometry.OrdinaryTowerCartesianMap`: `OrdinaryTowerCartesianMap`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, the conjunction of local
  Noetherianity and stalkwise regularity.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes the exact
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`; this predicate is used for each center.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `IdealSheafData.comap`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Morphisms.ClosedImmersion`: `IsClosedImmersion`; `Morphisms.Smooth`: `Smooth`;
  `Morphisms.Proper` and `Morphisms.Separated`: `IsProper`, `IsSeparated`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and its
  projections (the comparison structures use `IsPullback`);
  `Mathlib.CategoryTheory.Limits.Shapes.Products`: `Cofan.mk` with `IsColimit`.
  The coproduct and scheme/affine notions use the existing definition nodes, not new copies.

All recorded original statement-dependency modules are public imports; the already stated
proof dependencies are plain imports. The two blowup flat-base-change proof prerequisites
have no recorded Lean declaration in this checkout and are not replaced by an invented
proof module. They are not needed to type this stage-2 statement.

Edge cases checked by reading the definitions and quantifiers: empty S, empty cover,
empty members of a cover, zero-length tower, empty label type, arbitrary label universe,
a proper Cartier ideal with identity blowup, a label unit on one chart but active elsewhere,
nonconnected inputs of different dimensions, and the doubled-origin line with nonaffine
intersections allowed. No small label universe or nonempty chart restriction occurs.
Every declared variable and universe is explicitly bound; `autoImplicit` and
`relaxedAutoImplicit` are both false. The only postponed theorem is the item itself.
No statement correction, disputed statement, or dependency repair was necessary.

Searches actually run, with the wrapper's logs retained in searches.jsonl:

- LeanFinder: “Zariski descent and cover independence of labeled ordinary blowup resolution
  towers” returned eight general cover/local-property declarations, no resolution theorem.
- Loogle: `AlgebraicGeometry.OrdinaryBlowupTower, AlgebraicGeometry.OrdinaryResolutionComparison`
  returned no hit and reported the first identifier unknown in Mathlib's index.
- Wrapper grep in Mathlib/AlgebraicGeometry: `synchron|OrdinaryBlowupTower|resolution.*tower`
  returned no hit.
- LeanSearch: “labeled ordinary blowup towers Zariski descent” returned local-property
  descent and the subcanonical Zariski topology, not descent of labeled towers.
- LeanSearch and LeanFinder: “finite labeled ordinary blowup towers and open immersion
  contraction comparisons” each returned eight open-immersion/gluing declarations, no
  labeled intrinsic ordinary tower or open-only rule.
- Wrapper grep: `LabeledOrdinary|OrdinaryZariskiResolution|ResolutionAffineCover` in
  Mathlib/AlgebraicGeometry returned no hit. Before writing the module, the same expression
  in `lean/WeilConjectures`, `lean/Sheaf` and `dag/nodes` returned no hit.
- Broader project searches for `synchron`, `OrdinaryBlowupTower`, `ResolutionComparison`
  and `ResolutionInput` found the reused OrdinaryResolutionRule, OrdinaryTowerCartesianMap
  and LabeledEmbeddedResolution, plus normalized/monoscheme towers of a different kind.
  Searching the item id in WeilConjectures and dag/lean_names_upstream.json returned no match.
- `tools/blueprint_refs.py search 'labeled ordinary resolution'` and
  `... search 'ordinary blowup tower'` both returned zero matches.
  `... ancestor` identified `lem-trf-local-term-locality`; the new node preserves its
  historical synchronization place and the full via chain.

## New nodes

`def-trf-labeled-ordinary-zariski-resolution-data` defines the missing labeled INTRINSIC
ordinary tower, label-preserving versions of the existing two comparison structures,
embeddable membership using the existing pair, finite affine covering data using actual
coproducts, the open-only rule, and its affine descent/padded-overlap predicates.
The composite predicate only writes the equality of given level maps. These data are
required to state this node and are absent from Mathlib, the upstream project, the
existing DAG and the current blueprint searches above. In particular the already existing
LabeledEmbeddedResolutionTower would impose different objects (ambient blowups and strict
transforms), extra regular-input/stop-at-regular conditions, and smooth functoriality;
it cannot represent this node's weaker hypotheses. OrdinaryBlowupTower and both ordinary
comparison definitions remain the single definitions of their respective notions.
The new node has its own full TeX definition, exact definition dependencies and real-data
module. Its three logged search kinds reproduce the actual results.

## Second reading by Q05

This is a second pass by the dispatched worker; the prompt prohibits starting another agent.
The maintainer will perform the independent delivery review. I reopened the original node
and the final two modules and matched each clause as above. The initial draft expressed
cover cocycles only through uniqueness. I changed it to include the actual equality of
composite comparison maps at every level, and added explicit equality of label ranges for
any two covering families, including the combined family. I checked the new definition
node against the final data module: no extra smooth functoriality, separatedness, chosen
embedding, resolution existence or regular-input stopping condition has entered A.
The full cartesian map retains center ideals, and the contracted map deletes exactly
unit ideals; these are different interfaces used in the right places. Coherence uses the
kernel condition from the upstream predicate. The zero cover is genuinely allowed.
No mathematical statement change was needed. Both modules are compiled separately by
the prescribed server wrapper; the final dry run also repeats those checks and preflight.
