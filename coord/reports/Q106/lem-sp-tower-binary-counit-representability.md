## Worker report

The module `Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability` states
`AlgebraicGeometry.ProEtale.SpTowerBinaryCounit.binary_counit_representability`.
Its only theorem has proof `sorry`; all helper definitions contain actual terms.
The item changes only in `lean`. No new nodes, dependency replacements, or statement
corrections are required.

Source read: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md`, in full,
especially Gluing. The existing eight-step DAG proof is retained and included in
the theorem docstring: restricted adjunction; uniqueness of representing pairs;
signed open-cover triangle; exact counit lift; outer local bijections; both exact
five-term rows; all naturality squares including the connecting map; five lemma.

Hypothesis and clause correspondence:

- `l`, `[Fact l.Prime]`, `E`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]` give the specified finite coefficient extension.
  `SpTowerShriek.R l E n` is the actual ell-power quotient with exponent `n+1`.
  Thus every positive level is present, including exponent one; no uniformizer
  replaces ell in the statement.
- `p`, `hp : 0 < p`, `hlp : l ≠ p`, `k`, `[Field k]`, and `[CharP k p]`
  render the field setting. No perfectness or algebraic closure is assumed.
- `Z Y : Over (Spec (CommRingCat.of k))` with the three structure-map classes
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` render separated finite-type
  schemes. `h : Z ⟶ Y` is a k-morphism. For such objects every morphism is separated
  finite type, so no extra hypotheses on h are needed.
- `b : SpTowerShriek.Base l E` and `o : SpTowerShriek.Operations l E b` are the
  published section-normalized strict sequence-site operations, not arbitrary
  functors/maps. `D l E T` is an ordinary unbounded derived category of the actual
  varying-ring systems; `Base.realization` fixes sections, transitions and morphisms.
  `q : SpTowerCalculus.Coordinates l E b` gives the canonical exact evaluation
  coordinates. `good` is precisely `spConstructibleTorTowers` transported through
  `(SpTowerCalculus.realization ...).inverse`; it imposes uniform cohomology and
  Tor intervals and intrinsic constructibility, with no normalization condition.
  These coordinate parameters choose presentations supplied by the recorded
  shriek/calculus statements; they do not posit representability or gluing.
- `c₀ : Compactification h.left` chooses one coefficient-independent
  compactification. The ambient functor is exactly `SpTowerShriek.F l E b o c₀`.
  `support c₀ D₀` is its open normalization `j_D! ⋙ F_h`. It is canonically the
  compact-support functor for `c₀.precomp D₀.ι`, by the published
  `SpTowerCalculus.sequenceOpenComposition`; no independently chosen comparison
  map occurs. The node permits precisely this open-composition normalization.
- `U V` and `hcover : U ⊔ V = ⊤` are the binary cover; `U ⊓ V` is W.
  `_hF` states preservation by F_Z, and `_hFD` by every F_D for an open D.
  These are exactly the compact-support preservation assumptions in the node.
- `K`, `_hK`, `P`, `_hP`, `Q`, `_hQ` put the objects in C_Y,C_U,C_V.
  `eU,eV` are their local counits. `hU,hV : Represents ...` expand to
  `∀ N, good ... N → Function.Bijective (fun a : N ⟶ P ↦ F_D.map a ≫ eU)`
  and the analogous expression for Q. Fullness retains every ambient derived map.
- The first two conclusion conjuncts quantify over every `D₀ ≤ U` or `D₀ ≤ V`.
  They assert membership of the restriction and `Represents` with
  `restrictedCounit`, whose term is `F_h.map (nested i P) ≫ eU`.
  `nested` is the actual transpose under the published open adjunction of the
  restriction of its unit, followed by the inverse restriction-composition iso.
  This equals the canonical nested-open counit after open composition. No
  existence/choice of arbitrary derived arrows is substituted.
- The existential `c` is an isomorphism between the two restrictions to W.
  Its first equation is counit preservation and the following universal equality
  `c' = c` is uniqueness among all counit-preserving isomorphisms.
- The universal G,aU,aV clause admits every good G and every pair of restriction
  isomorphisms satisfying the displayed overlap equation, using exactly
  `SpTowerBinaryCtfFibre.restrictionComp` and `restrictionBetween`. This is the
  stated binary gluing compatibility. No assumption about constructibility of
  right direct images, a selected cone, or a shift of G is added.
- `∃ e, LiftEquations ... e` is existence of a counit lift. `LiftEquations`
  expands to the two exact equations obtained by applying F_Z to the actual
  open adjunction counits and composing with e, equal to F_D(aD) followed by eD.
- `∀ e, LiftEquations ... e → ...` applies all remaining assertions to EVERY
  lift. `Represents ... G K e` asserts bijectivity for every M in C_Z.
  There is no assertion that arbitrary morphisms with specified restrictions
  are unique.
- `OpenThetaEquation` for U,V,W states equality with the local representing map
  under `derivedAdjunction.homEquiv`, followed by the chosen restriction iso.
  On W its counit is the restricted U counit and its restriction iso is the
  composite of the recorded restriction-composition iso with restriction of aU.
  These equations hold for every good N, hence also for the shifted tests.
- `coverA`, `coverB`, `coverS`, `coverT` are respectively
  j_W!(M|W), j_U!(M|U) biproduct j_V!(M|V), the signed (1,-1) nested-open map,
  and the (1,1) pair of actual open counits. `beta` is the pair of local counits
  via the images of the biproduct projections. The two equations with `beta`
  state that its overlap composite is zero and that e factors it through
  F_Z(coverT). Both equations are explicit and retain the minus sign.
- The universal equation on M,M',v,a is naturality of the specified theta,
  written in Lean's diagrammatic order. It quantifies over every ambient arrow,
  so in particular supplies all four squares on the five-term rows: coverS,
  coverT, delta, and negative shifted coverS. This includes the connecting square,
  not just the local restriction squares.
- For every good M the last clause gives delta with the canonical cover triangle
  distinguished. Its A,B,A[1],B[1] are explicitly asserted good. `HomFiveExact`
  asserts `Function.Exact` for the three consecutive pairs of the row
  Hom(B[1],G) -> Hom(A[1],G) -> Hom(M,G) -> Hom(B,G) -> Hom(A,G).
  The first arrow is precomposition with `-shiftFunctor.map coverS`, as in
  signed rotation. `ImageHomFiveExact` is the corresponding row after F_Z,
  retaining the actual images of all four arrows. Writing F_Z(A[1]) instead
  of conjugating by the canonical exact-functor shift iso keeps the same row
  without introducing an extra comparison choice. Both rows are rows of
  homomorphisms since the recorded F_Z is additive and composition is bilinear.
  `OuterBijective` asserts exactly the four outer bijections. The central
  bijection is the earlier `Represents` conjunct specialized to M.

Dependency declarations read and used:

- sk-def-sfb-dc-setting: the setting and `compactificationOverField` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`;
  `Over` binders render its setting, and arbitrary c₀ renders its compactification
  convention. This module is also reexported by the binary-fibre dependency.
- def-weil-l-adic-coefficient-extension: `Padic.coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, `coefficientExtensionRing` in
  `Sheaf.NumberTheory.Padics.CoefficientExtension`, and
  `Padic.finite_coefficientExtensionRing` in `CoefficientExtensionFinite`.
- sk-def-sp-coefficient-towers: `spEllIdeal`, `spCoefficientRing`,
  `spCoefficientReduction`, `spCoefficientTowers` in
  `Sheaf.Paper.SmoothPurityCoefficientTowers`.
- det-sp-coefficient-towers-abelian: `SpCoefficientTowersAbelian` and
  `sp_coefficient_towers_abelian` in
  `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`; exact evaluations and
  the section-normalized ordinary system presentation are reused transitively.
- sk-def-sp-normalized-towers: `spConstructibleTorTowers`,
  `spDerivedCoefficientTowers`, `spDerivedCoefficientEvaluation` in
  `Sheaf.Paper.SmoothPurityNormalizedTowers`; only the unnormalized predicate is used.
- def-weil-proetale-constructible-sheaf: `Scheme.IsConstructibleProEtaleModuleSheaf`
  in `Sheaf.Paper.ProEtaleConstructibleSheaf`, used inside that predicate.
- def-weil-proetale-tor-amplitude: `Scheme.HasProEtaleTorAmplitude` and
  `HasFiniteProEtaleTorAmplitude` in
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`, used inside that predicate.
- det-sp-tower-shriek-levels: `SpTowerShriek.D`, `Base`, `Operations`, `Open`,
  `openD`, `F`, and their normalized derived adjunctions, in
  `Sheaf.Paper.SmoothPurityTowerShriekLevels`.
- lem-sp-coefficient-tower-shriek-calculus:
  `SpTowerCalculus.realization`, `Coordinates`, `sequenceOpenComposition`,
  `openComposition` in `Sheaf.Paper.CoefficientTowerShriekInterfaces`, publicly
  reexported by `Sheaf.Paper.CoefficientTowerShriekCalculus`;
  `coefficient_tower_shriek_calculus` is the proof dependency.
- lem-sp-tower-binary-ctf-fibre: `SpTowerBinaryCtfFibre.restriction`,
  `restrictionBetween`, `restrictionComp`, `binary_ctf_fibre` in
  `Sheaf.Paper.SmoothPurityTowerBinaryCtfFibre`. The statement accepts any gluing
  with its specified restriction isomorphisms; it does not re-prove fibre existence.
- Proof-only imports: `SemilinearSections.sequenceSiteOpenExtension` in
  `Sheaf.Paper.SequenceSiteOpenExtension`; `CategoryTheory.ringedTopos_binary_descent`
  in `Sheaf.CategoryTheory.RingedToposBinaryDescent`;
  `Pretriangulated.Triangle.yoneda_exact₂` and `yoneda_exact₃` in Mathlib's
  `CategoryTheory.Triangulated.Pretriangulated`; and
  `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono` in Mathlib's
  `CategoryTheory.Abelian.DiagramLemmas.Four`.

Edge cases checked against the definitions: U empty, V empty, W empty,
U=V=Z, Z empty, zero K/P/Q/G, arbitrary common intervals (not fixed to zero),
and first positive coefficient level. The signed maps remain meaningful and the
local pairs on the empty open are tested on the zero category. No Nonempty open,
nonzero coefficient, normalized reduction, faithfulness of evaluation, or
constructibility of Rj_* is assumed. The good predicate existentially quantifies
independent uniform cohomological and Tor intervals exactly as the recorded node.
Universes of generic Hom-row helpers are explicitly bound, as are all variables;
no auto-bound implicit variable or file-local notation/instance is introduced.

Searches actually run:

- msearch.py leanfinder: "Compatible local representing pairs for compact support
  on coefficient towers yield a representing counit by an open-cover triangle".
  Eight results, all about `CompHausLike.LocallyConstant` counits, no match.
- msearch.py loogle: "CategoryTheory.Adjunction,
  CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂". Zero hits.
- msearch.py grep: `counit.*represent|represent.*counit` in Mathlib/CategoryTheory.
  Zero hits.
- rg on lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `counit.*represent|represent.*counit|binary_counit|binary.*represent`.
  Generic adjunction/representative normalization hits, but no geometric binary
  coefficient-tower representability statement. Search for the exact item id in
  lean/WeilConjectures returned no hit. Existing binary-fibre and calculus modules
  were read and used instead of duplicating their constructions.

No STATEMENT-DISPUTED finding and no node fault. Validation uses only the prescribed
scompile.py and deliver2.py wrappers; the shared repository was read only.

## Second reading by Q106

Author's separate clause-by-clause check; the maintainer performs the independent
review, as specified in the dispatch brief. The source Gluing paragraph, the
current node and the full Lean file were reopened together. The first draft's
nested adjunction word put the composition comparison in the wrong direction;
server elaboration detected it, and it now restricts the unit first and then
uses `restrictionComp.inv`. The check also made U,V,W transpose equations explicit
and retained goodness of the four outer objects. The signed rotation starts with
negative shifted coverS; the lower row keeps F of this signed arrow. Naturality
quantifies over every arrow and therefore includes delta and this signed shift.
The universal quantifier on G follows the unique overlap iso and its compatibility
equation, so an arbitrary compatible binary gluing is admitted. The universal
quantifier on e follows existence and repeats only the two local equations, so
representability holds for every lift and no uniqueness of glued maps is claimed.
All helper data are explicit compositions, adjunction transposes, biproduct maps
or aliases of existing predicates. Only the main theorem is postponed.
