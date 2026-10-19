## Worker report

This repairs the returned delivery at immutable head 3b6357d32749. The sole module is
`lean/Sheaf/SecSmoothPurity/ProperSupportPullbackSectionMap.lean`. It states
`AlgebraicGeometry.Etale.properSupportPullbackSectionMap`, with `sorry`, and constructs
three helpers with actual data: `properSupportBaseChangeProjection`,
`properSupportBaseChangeEtaleMap`, and `properSupportUnitPullback`. Each helper belongs
to this same canonical-map construction and is listed in `lean.declarations`.

Hypothesis-by-hypothesis correspondence with the unchanged node:

- The commutative coefficient ring is `{Λ : Type (u + 1)} [CommRing Λ]`.
- The four schemes and arrows are `{X X' Y Y' : Scheme.{u}}`, `a,f,b,f'`;
  `sq : IsPullback a f' f b` is the Cartesian-square hypothesis.
- Separatedness and local finite type are `[IsSeparated f] [LocallyOfFiniteType f]`.
  Local finite type of `f'` is obtained using
  `MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance`;
  the second application to the flipped test-object pullback gives local finite type
  of `pullback.fst V.hom f'`. No extra hypothesis on `f'` is imposed.
- `F`, `G`, and `H` are module-valued sheaves on the specified small étale sites.
  `ιG` and `ιH` have the exact ambient direct-image codomains in the node.
  `[Mono ιG] [Mono ιH]` make them subsheaves, rather than arbitrary maps with those images.
- `hG` identifies the image of `ιG` on every `U` with
  `SectionHasProperSupport Λ F (f.Etale.obj U) (pullback.fst U.hom f) s`.
  The file writes `f.Etale.obj U` as the definitionally equal
  `(MorphismProperty.Over.pullback @Etale ⊤ f).obj U`.
- `hH` gives the analogous image equality over every `V : Y'.Etale`, for `a^*F`,
  using that same landed support predicate and the explicitly derived local-finite-type
  instance. `SectionHasProperSupport` uses the nonzero-geometric-germ locus and
  `Scheme.IsClosedSubsetProperOver`, hence the reduced induced closed structure.

Clause-by-clause correspondence of the conclusion:

- `∃ α : G ⟶ (lowerStar (ModuleCat Λ) b).obj H` gives a linear sheaf morphism;
  its components are morphisms in `ModuleCat Λ`, not arbitrary functions.
- The first conjunct is the defining component equation
  `ιH_U' (α_U s) = properSupportUnitPullback ... F U (ιG_U s)`.
  By definition the right side is the unit component at `T_U`, followed by
  `(a^*F).obj.map (properSupportBaseChangeEtaleMap ... U).op`.
  This is exactly the requested unit-pullback formula. The lift `m` has first leg
  `properSupportBaseChangeProjection ... U` and second leg `T'_U → X'`.
  Its source is `T'_U` and its target is `Over.pullback a T_U`.
  Monicity of `ιH` makes this formula determine α uniquely, which expresses canonicity.
- The second conjunct tests every geometric point of `T'_U`: the image germ is
  nonzero iff the original germ at its composite with the displayed projection is
  nonzero. This is the exact inverse-image support equality. The universally
  quantified `t` is required to equal `α_U s`, so this concerns that very image section.
  Proper support of the image also follows from `hH` because it lies in H.
- The third conjunct explicitly states the naturality square
  `γ ≫ α₂ = α ≫ (lowerStar (ModuleCat Λ) b).map δ` for `φ : F ⟶ F₂`.
  The two preceding equations say precisely that γ and δ are induced by φ and a^*φ
  on the ambient subsheaves. The component-formula premise says α₂ is the canonical
  map for the second sheaf, rather than an arbitrary map. Applying this same existence
  theorem to the proper-support subsheaves of F₂ supplies such an α₂; the formula
  determines it uniquely. The naturality assertion is expressed for any subsheaf
  presentations and any maps satisfying those equations, so it is independent of
  presentation or choices. No second arbitrary choice of pullback is introduced.

Dependencies read and used (current published source was obtained with `scompile.py
--source` when the local upstream checkout did not contain it):

- `Sheaf.AlgebraicGeometry.EtaleSectionProperSupport`:
  `AlgebraicGeometry.Etale.SectionHasProperSupport`, the declaration of the landed
  `def-cbc-etale-section-proper-support` (NR). That existing node is added to stmt_deps.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `lowerStar`, `upperStar`, `upperStarLowerStarAdjunction` in `AlgebraicGeometry.Etale`.
  These are exposed by the support module's public upstream imports.
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`:
  `AlgebraicGeometry.inverseImage_stalk_germ` (proof dependency).
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact` (proof dependency).
- `Sheaf.EtaleCohomology.EtaleSectionZeroOpen`:
  `AlgebraicGeometry.Scheme.etale_section_zero_open` (proof dependency).
- `Sheaf.AlgebraicGeometry.ClosedProperSupportLocality`:
  `AlgebraicGeometry.Scheme.closed_proper_support_locality` (proof dependency).
- `WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`:
  `AlgebraicGeometry.Scheme.closed_subset_proper_over_base_properties` (proof dependency).
- Mathlib: `Scheme`, `IsPullback`, `IsSeparated`, `LocallyOfFiniteType`,
  `locallyOfFiniteType_isStableUnderBaseChange`, `Scheme.pointSmallEtale`,
  `Point.toPresheafFiber`, `pullback.lift`, and `MorphismProperty.Over.homMk`.
  Closed-subset properness is the recorded upstream `Scheme.IsClosedSubsetProperOver`,
  used through the landed section-support definition.

Edge cases checked: identity Cartesian squares give the ordinary unit component;
zero sections have empty geometric support, and the empty scheme introduces no
nonemptiness condition. Arbitrary commutative rings, including the zero ring, are
admitted. Test objects need not be quasi-compact. Every separably closed geometric
point in the scheme universe is tested by the support equality, including algebraically
closed points used in `SectionHasProperSupport`. The returned Z/2 and Z/4 example is
excluded at exactly the faulty hypothesis: reduction Z/4 → Z/2 is not monic, so cannot
be ιH. We do not impose any unjustified injectivity of the unit itself.

Searches for existing declarations: the saved packet's LeanFinder search for a
proper-support pullback section map found only ordinary pullback/direct-image maps;
Loogle `IsClosedSubsetProperOver, pointSmallEtale` gave no exact map; Mathlib grep
`ProperSupportSection|support.*proper` gave none. On repair, `msearch.py leanfinder`
with “Canonical unit pullback map on proper support sections of etale module sheaves”
gave eight ordinary module pullback/unit hits, none this map. `msearch.py loogle`
`CategoryTheory.Adjunction.unit, CategoryTheory.Mono` gave four general adjunction
monomorphism lemmas. `msearch.py grep` `properSupportPullback|properSupportUnitPullback`
in Mathlib/AlgebraicGeometry gave zero hits. `rg` over upstream WeilConjectures and
shared lean/Sheaf found the existing `SectionHasProperSupport` and its consumers,
not a declaration of this canonical section map. Searching the item's id in upstream
found no declaration. Existing DAG and recorded declarations were read; the duplicate
new node in the returned packet was therefore removed, along with its module.

No statement correction is needed: the original node already says subsheaves, unit
pullback, naturality, and exact support equality. No new node or dependency repair is
delivered. The only DAG changes are lean and addition of the landed support node to
stmt_deps. The theorem remains the sole postponed proof in this module.

## Second reading by NM

This is the author's repair self-check; the maintainer supplies the independent review.
I reread the current node, the returned module, the repaired module, the landed support
predicate, and Stacks Tag 0F55. The returned version's inclusions were not monic, its
first conjunct merely repeated hH, and coefficient naturality was absent. The repaired
binders add both Mono instances; the first conjunct now fixes the actual unit pullback,
and the final conjunct gives the requested square. I checked the direction of the lift:
`T'_U → a^*T_U`, so its opposite restricts the unit section to T'_U. Both sides of the
square go from G to b_*H₂. The geometric-germ equivalence remains about the very section
specified by the component equation. The support hypotheses now use NR's landed
predicate and its required local-finite-type instance. The removed definition node and
module are absent from this packet. All universes and variables are explicitly bound;
the three constructions have real data, and the one theorem has only `sorry` as proof.
