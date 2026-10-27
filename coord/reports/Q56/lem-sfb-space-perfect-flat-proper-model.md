## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePerfectFlatProperNoetherianModel` states
`AlgebraicGeometry.AlgebraicSpace.exists_etale_noetherian_perfect_flat_proper_model`.
Its only theorem proof is `sorry`. The item's mathematical statement, proof plan and
proof dependencies are unchanged. Its statement dependencies gain the landed owners
of the predicates and functors actually used, and the new canonical module transport.
No definition contains `sorry` data.

Clause-by-clause reading of the item:

- A scheme S and spaces X,Y over S are `{S : Scheme.{u}} {X Y : AlgebraicSpace S}`;
  their morphism is `f : X ⟶ Y`. Explicit universe `u` is arbitrary. The binder
  `[∀ (B : Scheme.{u}) (Z : AlgebraicSpace B), HasDerivedCategory.{w} Z.SmallModules]`
  fixes the common localization size for all spaces subsequently quantified. It is a
  size convention, not a geometric condition. The standard localization supplies a
  sufficiently large such universe. Site object/morphism universes are not equated:
  original sites have objects in u+1 and arrows in u, and the equivalent recorded
  affine small models live in u.
- Finite presentation is `hfp`: `MapIsLocallyOfFinitePresentation f` together with
  `MapIsQuasiCompact f.hom.hom` and `MapIsQuasiCompact (pullback.diagonal f.hom.hom)`.
  This is exactly lfp, qc and qs, with the existing chart definitions.
- `E : X.DerivedModules` uses the small model equivalent to the original module topos.
  `hE` is the existing `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`, applied to
  `X.smallStructureSheaf`; its local representatives are bounded complexes of
  finite-free retracts, with isomorphism to E in the derived category.
- `G : CochainComplex X.Modules ℤ` is the original-site coefficient complex.
  `hbounded` says its terms are zero outside an integer interval. `hG n` has four
  conjuncts: quasi-coherent, finitely presented, `ModuleIsFlatOver f`, and
  `HasProperAnnihilatorSupport f`. Thus neither relative flatness nor properness is
  imposed on f itself. Flatness is the recorded geometric-stalk-equivalent chart
  condition. Proper support is the actual annihilator ideal, not just a point set.
- `I`, `R`, `s`, `ua` give a family of `Spec (R a)` over S mapping to Y.
  `IsEtale (ua a).hom.hom` and `IsJointlySurjective` give exactly the jointly
  surjective affine etale family; no finiteness or nonemptiness is imposed on I.
- `Xa`, `va`, `ta`, `IsPullback va ta f (ua a)` specify X_a = X times_Y U_a and its
  two projections. Any cartesian representative is permitted.
- For each a, `R0 : CommRingCat.{u}`, `IsNoetherianRing R0`, `r : R0 ⟶ R a` give
  the Noetherian model ring and the required ring map, without demanding that R be
  Noetherian or that r be flat or injective.
- `X0` is a space over `Spec (ULift ℤ)` and `f0` maps it to `Spec R0` with its unique
  terminal-base structure. The three-conjunct finite-presentation condition is the
  same one as hfp. `E0` is perfect by the same existing perfect predicate. `G0` is
  a bounded complex, and each term has all four coefficient conditions over f0.
- Local Noetherianity is `∀ T : X0.EtaleSite, IsLocallyNoetherian (X0.etaleForget.obj T)`.
  Coherence is spelled out on every affine etale chart: its function ring is
  Noetherian and the Zariski-restricted term has `Module.Finite` global sections.
  Affine opens of an arbitrary etale chart are themselves affine etale charts, so
  this is exactly the node's chartwise meaning, not a different coherent predicate.
- `absoluteSpace Xa` is Xa with only its terminal-base structure. The square
  `IsPullback p (absoluteSchemeTargetMap (Over.mk (s a)) ta) f0 (...)` has bottom
  arrow the Yoneda image of `Spec.map r`. It specifies the required isomorphism
  over U_a with X0 times_(Spec R0) Spec (R a), and p is its first projection.
- `Nonempty ((derivedTensorPullback p).obj E0 ≅ ... )` is the required derived
  isomorphism. Its right side is `Lv_a^* E`, transported by the exact canonical
  equivalence of the identical etale ringed sites. The existing K-flat derived
  tensor pullback is used; no arbitrary comparison functor is assumed.
- The final `Nonempty (... ≅ ...)` is an isomorphism in `CochainComplex`, with
  `moduleTensorPullback p` and `moduleTensorPullback va` applied degreewise.
  The inverse of actual absolute chart restriction transports coefficients. There
  is no localization of G and no replacement of chain isomorphism by quasi-isomorphism.
- The two earlier conclusion conjuncts assert perfectness of `Lv_a^* E` and
  termwise `ModuleIsFlatOver ta` for `v_a^* G`, as requested.
- The models have no S-structure in their types. The lift of Z only places the
  terminal affine scheme in the same scheme universe; it imposes no characteristic
  or nonzero-ring assumption.

Recorded statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `Modules`, `IsEtale` and the existing chart representation.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`; def-weil-size-convention is metatheoretic, with explicit
  universes and localization binders here, not a new Lean object.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  slice instances; the actual predicate is Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleTensorPullback`,
  the left adjoint of the specified compatible-chart direct image, and its unit.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient`:
  `ModuleIsFlatOver`, `HasProperAnnihilatorSupport`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `SmallModules`, and the specified model equivalences.
- `Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback`: `derivedTensorPullback`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations`:
  `moduleTensorPullback_additive`, for ordinary cochain pullback.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocallyOfFinitePresentation`, and the properness definition used by support.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `IsJointlySurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`.
- New `Sheaf.AlgebraicGeometry.AlgebraicSpaceForgetAmbientBase`:
  `absoluteSpace`, `absoluteSchemeTargetMap`, `absoluteModuleEquivalence`,
  `absoluteDerivedTransport` (described below).

The module includes every recorded, presently stated proof-dependency module, as
plain proof imports when it is not needed publicly: affine etale atlas,
flat/proper/fp locality, module continuity, Zariski/etale quasi-coherent equivalence,
enlarged ringed site, fibre products, affine quasi-coherent finiteness, Nagata affine
approximation, finite-type Noetherian algebras, and locally Noetherian schemes.
The remaining proof nodes have no Lean record or Mathlib match in the read base;
they are not needed for typing this theorem and are named in the complete proof
docstring for stage 3. No proofs of these prerequisite theorems are attempted here.

Edge cases checked mathematically before writing: empty Y (the family may be empty),
empty X, zero E and G, the zero ring (empty affine charts), a complex concentrated
in one degree, arbitrary positive/negative shifts, non-Noetherian R, nonflat maps
R0 to R, an arbitrary non-Noetherian/non-separated S, and a model with no S-map.
The annihilator-support predicate handles the zero module through the empty closed
subspace. No amplitude bound is imposed uniformly across atlas members. All
coefficient terms, including the zero terms outside the bounded interval, satisfy
exactly the termwise hypotheses. No statement dispute or source correction was needed.

Searches: msearch.py leanfinder for Noetherian approximation of perfect complexes
and bounded finitely presented relatively flat proper-support modules returned
`IsNoetherian`, `IsLocallyNoetherian`, smooth-flat and finite-type facts, not the
space theorem. Loogle `AlgebraicGeometry.AlgebraicSpace, IsNoetherianRing` had no
known AlgebraicSpace identifier. Mathlib grep `AlgebraicSpace|perfect.*Noetherian|
Noetherian.*model` in AlgebraicGeometry had no hit. LeanSearch, LeanFinder, Loogle
and further grep records for the added canonical transport are retained verbatim
in its node. Direct rg searches of `lean/WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json` found no declaration of this theorem or of the
new named transport. The scheme-only `ProperFlatSingleNoetherianDescent` has
different objects and hypotheses. The final broad DAG source search found the
already landed `lem-sfb-space-change-base-to-integers` / `SpaceChangeBase`; this
was read in full and incorporated into the new construction's dependencies.

Validation: scompile.py compiled both delivered files, separately in dependency
order, against the live library; no errors or non-sorry warnings. A typeclass
search for the composite ordinary pullback was repaired by recording additivity
of the inverse module equivalence and composing the two cochain functors. No
compile timeout or resource-limit increase was used.

## New nodes

`def-sfb-space-absolute-module-transport` defines the missing named module and derived
transport, not a new mathematical base-change theorem. Its source is Stacks 03I4
and 04KK, building on `lem-sfb-space-change-base-to-integers` (the landed normalized
existential theorem `exists_spaceChangeBase`). That theorem has no named absolute
space/module functor available as a term. The present module supplies the explicit
sigma presheaf of that same theorem, not a choice of an arbitrary space, together
with the exact restriction-on-unchanged-charts functor. Its inverse is a specified
inverse equivalence; its small-model conjugate induces derived transport. The
helper scheme-target map is specified sectionwise, not an arbitrary map.

All 25 declarations are listed in lean.declarations. The named postponed obligations
are the section identity and composition laws, sheaf condition, algebraicity,
naturality of the scheme-target map, etaleness and naturality of chart maps,
continuity, equivalence of module restriction, additivity of its inverse, and
small-model equivalence and additivity. These properties are explicitly included
in this definition node's statement; every theorem has its own source and full
proof docstring. Definitions contain actual presheaf/section/functor data, and
inverse choices are solely inverses determined by equivalences. The source-based
sigma formula retains the canonical construction and does not select data from
mere nonempty existence. Searches and their actual results are in mathlib_searches.
The broader existing change-base node is explicitly cited and not re-stated.

## Second reading by Q56

I reopened both module files and both node copies and performed a separate
clause-by-clause self-review. No second agent was started, as the dispatcher brief
prohibits it; the maintainer's independent review remains the external reading.
I checked all four input coefficient properties, all four descended coefficient
properties, both boundedness clauses, both finite-presentation clauses, the two
restriction clauses, chartwise coherence, the two cartesian squares, the Spec ring
map direction, and the two different kinds of isomorphism. I checked the helper's
actual definitions against its expanded node statement, including every named
proof obligation. I found no remaining mismatch. During this reading I made the
new node's scope explicit as named absolute module transport, cited the landed
base-change theorem rather than claiming there was no base-change node, and kept
the absolute construction's section formula exactly that source's formula. The
item's own statement and proof remain byte-identical to the read repository.
