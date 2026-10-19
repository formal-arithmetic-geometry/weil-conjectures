## Worker report

The delivery states Stacks Tag 0EYM, `lemma-relative-colimit-general`, in
`Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity`, declaration
`AlgebraicGeometry.Etale.higherDirectImage_relative_continuity`. The theorem has only
`sorry` as its proof. The helper `AlgebraicGeometry.Etale.relativeHigherDirectImageExchange`
is an actual composite of existing functors, comparison isomorphisms, and morphisms;
it contains no postponed data or proof. The complete eight-step DAG proof is in the
theorem docstring. No statement correction or dispute is needed.

The prior attempt was stage-1 work: Q29's reviewed split did not provide a Lean
statement. This delivery keeps that split unchanged and adds the stage-2 `lean`
records. It does not resplit or re-review the stage-1 item.

I read the source at Tag 0EYM in `etale-cohomology.tex`, including the two paragraphs
constructing the comparison and the full second proof. Its coefficients are arbitrary
abelian sheaves. It assumes affine transitions on sources and bases, and qcqs vertical
maps; it assumes neither torsion nor cartesian transition squares. I read the full
signatures and docstrings of the dependency APIs, including the general-square mate.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Small nonempty directed poset | `I : Type u`, `[PartialOrder I]`, `[IsDirected I (· ≤ ·)]`, `[Nonempty I]`; the index and schemes use the same size universe. |
| Inverse systems of sources and bases | `DV DB : Iᵒᵖ ⥤ Scheme.{u}`. Their `map_id` and `map_comp` fields encode both stated identity and composition laws. An arrow `a : i ⟶ j` in `I` induces the transition `DV.map a.op` or `DB.map a.op` from stage j to stage i. |
| Compatible stage morphisms | `η : DV ⟶ DB`, with `η.app (op i)` the stage morphism; `η.naturality a.op` is the stated commutative square. |
| Both sets of transition maps affine | The two `∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (...)` instance binders, separately for `DV` and `DB`. |
| Every stage morphism qcqs | Separate `∀ i, QuasiCompact (η.app i)` and `∀ i, QuasiSeparated (η.app i)` binders. No compactness or separatedness of the bases or total spaces is assumed. |
| Limit schemes and compatible projections, universal among cones | `cV : Cone DV`, `hcV : IsLimit cV`, `cB : Cone DB`, `hcB : IsLimit cB`. The projections are the components of `cV.π` and `cB.π`; their compatibility is in the cone data. |
| The limit morphism | `v : cV.pt ⟶ cB.pt`, with `hu i : cV.π.app i ≫ η.app i = v ≫ cB.π.app i`. The two cone universal properties imply this is the limit of the stage arrows. |
| Abelian sheaves A_i on V_i | `F i : Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}`. |
| Coefficient transitions φ_ji | `φ a` has source `(upperStar ... (DV.map a.op)).obj (F i)` and target `F j`. |
| Coefficient identity law | `hφid`, including transport along `DV.map_id` and `upperStarId`. |
| Coefficient composition law under canonical identifications | `hφcomp`, using the specified `upperStarComp ... (DV.map_comp b.op a.op)`, followed by the pulled-back `φ a` and `φ b`. |
| A = colim a_i^{-1} A_i | `A`, `eA`, and `hA` present precisely the inverse-image diagram; `cA : Cocone A`, `hcA : IsColimit cA` identify its coefficient colimit as `cA.pt`. The `eA` only identify object presentations, and `hA` prescribes the maps without freedom. |
| Every integer q ≥ 0 | `q : ℕ`, explicitly cast to `ℤ` for the homology functor. This parametrizes exactly the nonnegative integers, including zero. |
| Higher direct image R^q | `DerivedCategory.Plus.homologyFunctor ... (q : ℤ)` after `rightDerivedLowerStarPlus` applied to `DerivedCategory.Plus.singleFunctor ... 0`. This is the dependency's bounded-below derived-direct-image definition. |
| Pulled-back higher-image system | `H : I ⥤ Sheaf cB.pt.smallEtaleTopology ...`, with `eH i` identifying `H.obj i` with `b_i^{-1}R^q u_{i,*}F_i`. |
| Specified transition i → j | `hH` first composes the two base inverse images using `upperStarComp` and the cone equation; then it pulls back `relativeHigherDirectImageExchange ⟨η.naturality a.op⟩ (F i) (F j) (φ a) q` along `b_j`; finally it undoes `eH j`. |
| Exchange is the mate of the inverse-image square isomorphism | The helper takes degree-q cohomology of the existing `Etale.derivedBaseChangeMapPlus ... sq`, characterized by the derived-mate computation. The underived square comparison uses only `upperStarComp` and `sq.w`. |
| Apply higher direct image to the coefficient transition | In the helper, `rightDerivedLowerStarPlus ... f'` maps the exact-pullback single-functor comparison followed by `singleFunctor.map φ`. Taking homology yields exactly `R^q f'_* φ`. |
| Source colimit in abelian sheaves | `cH : Cocone H` and `hcH : IsColimit cH`, whose point is the displayed left-hand colimit. |
| Specified leg to R^q u_* A | `legs` is a natural transformation to the constant target diagram; `hlegs i` fixes its component as `eH i` followed by exchange for `⟨hu (op i)⟩` and the coprojection `(eA i).inv ≫ cA.ι.app i`. |
| Canonical comparison C_u | `hcH.desc { pt := R^q u_* cA.pt, ι := λ }`, using the supplied colimit universal property. It is a specified descent map, not an arbitrary morphism. |
| C_u is an isomorphism | The conclusion is `IsIso (hcH.desc ...)`. |
| No torsion and no cartesianness hypotheses | No torsion predicate or `IsPullback` occurs anywhere. The only squares are `CommSq` from naturality or `hu`. |

The presentation variables `A`, `H`, `eA`, `eH`, `legs`, and their equations do not add
geometric or coefficient restrictions. They allow arbitrary isomorphic presentations
of the exact diagrams and cone described in the node, while prescribing all arrows.
`IsColimit` uses a supplied universal property instead of the library's chosen `colimit`;
the resulting assertion is the same for every colimit by its universal property.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`, the
  recorded `mathlib_match` of `pqf-def-affine-morphism`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and `.QuasiSeparated`:
  `AlgebraicGeometry.QuasiCompact` and `AlgebraicGeometry.QuasiSeparated`, as prescribed
  by the scheme-conventions node (which declares no additional notion).
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`;
  `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `Etale.lowerStar`, and `Etale.upperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`:
  `Etale.upperStarComp` and `Etale.upperStarId` for the identity/composition identifications.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `Etale.rightDerivedLowerStarPlus`, the recorded derived-direct-image component.
- `Mathlib.CategoryTheory.Limits.HasLimits` and `.IsLimit`:
  `Cone`, `IsLimit`, `Cocone`, `IsColimit`, and `IsColimit.desc`. The maps are constructed
  using these universal properties rather than a duplicate colimit definition.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, supplied as the record of the unstated
  `def-kun-commutative-derived-exchange` prerequisite; details below.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryPlusHomologyFunctorIso` and
  `Functor.mapDerivedCategoryPlusSingleFunctor` for the canonical cohomology/single
  identifications used in the exchange helper.

The modules of every already-stated proof dependency are imported without `public`.
The proof dependency `lem-kun-commutative-exchange-chart` has no recorded Lean statement,
so there is no module of it to import. It is not needed to type the continuity statement.
The general-square exchange prerequisite is supplied by an existing declaration rather
than a second construction. All mathematical definitions remain the recorded definitions.

Edge cases checked before writing:

- A singleton poset and constant diagram give the ordinary identity comparison after
  the canonical pullback and colimit identifications. No nontrivial transition is required.
- Degree zero uses the same construction, whose factors are the ordinary direct-image
  exchange and coefficient map on degree-zero homology; zero is not excluded.
- Empty schemes and empty bases are allowed; none of the schemes is assumed nonempty.
  Only the index is nonempty, as in the node. Zero coefficients give zero higher images.
- Constant integer coefficients are allowed, showing that no torsion condition is hidden.
- A noncartesian commutative square, including an empty top-left corner with nonempty
  pullback, still defines the helper: `CommSq` alone is its only square hypothesis.
- Distinct but isomorphic choices of limit cones, coefficient colimits, and higher-image
  colimits are admitted. All identifications are explicit; no arbitrary comparison is
  assumed invertible as a hypothesis.
- The index lives in the scheme universe `u`; small-etale coefficients live in `u+1`,
  following the recorded abelian-sheaf convention. There is no smaller independent
  test-object/index universe and every universe and variable is explicitly bound.

Searches for an existing statement or helper:

- `msearch.py leanfinder`, query: "Higher direct images of abelian etale sheaves commute
  with inverse limits of schemes with affine transitions and varying base". Eight hits:
  affine-transition structure-sheaf section/equality descent and morphism descent,
  including `exists_app_map_eq_map_of_isLimit` and `exists_appTop_π_eq_of_isLimit`.
  No higher-direct-image continuity statement.
- `msearch.py loogle`, query: `"rightDerived"`. Twelve generic right-derived-functor
  declarations (`HasRightDerivedFunctor`, `totalRightDerived`, and their structural
  lemmas), none with the geometric relative-continuity statement.
- `msearch.py grep`, query: `higherDirectImage.*limit|relative.*colimit|baseChange.*mate`,
  subdirectory `CategoryTheory`. Four unrelated small-object, Grothendieck-category,
  and comma-presheaf-colimit hits; no exact statement.
- `msearch.py leansearch`, query: "Higher direct images of abelian etale sheaves commute
  with inverse limits of schemes with affine transition maps and varying bases".
  Eight affine-limit geometry/structure-sheaf or existence-of-limits hits; no exact match.
- `rg` in the upstream `WeilConjectures` source found
  `Etale.higherDirectImage_limit` in `SmoothBaseChange/HigherDirectImage/Transition.lean`.
  I read its signature: it fixes one base and coefficients from one fixed sheaf and
  treats stalk continuity; it is not this varying-base/varying-coefficient statement.
- The exact item id has no upstream Lean occurrence. Searching both upstream and
  `lean/Sheaf` for `relativeHigherDirectImageExchange` and
  `higherDirectImage_relative_continuity` returned no existing declaration.
- Searches of project higher-image modules found fixed-base, fixed-pullback, or module
  coefficient arrows; none implements the arbitrary-square, variable-coefficient helper.
  The helper therefore only packages the actual composite specified by this node.

## Dependency modules

`def-kun-commutative-derived-exchange` is a genuine existing DAG definition with no
`lean` record, currently unsplit. The human's 2026-10-16 instruction requires supplying
such prerequisites in this delivery. The stage-1 attachment candidate
`AlgebraicGeometry.Etale.baseChange` in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs` has an unusable
interface for the node's abelian coefficients: its derived adjunction goes through
unbounded monoidal machinery, requiring a monoidal closed coefficient category and
functorial flat resolutions. The compile confirmed that these structures are not
available on `AddCommGrpCat`. Imposing them on the statement would change its objects.

The existing `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` in
`WeilConjectures.SixFunctors.BaseChange.Derived` is the coefficient-general interface
for the same canonical morphism. It needs only the abelian Grothendieck structures
already provided for abelian groups. This delivery repairs the prerequisite by recording
that existing declaration with `existing: true`, branch `slopmaster2`, and a `lean.note`
explaining the interface problem and the exact canonical replacement. No new dependency
module or duplicate construction is written; only this dependency's `lean` changes.

I read both constructions and the generic derived-mate computation in full.
`Etale.baseChangeMap` in `WeilConjectures.SixFunctors.BaseChange.Square` is explicitly
`mateEquiv` applied to `Etale.squareUpperStarIso`, formed from `upperStarComp` and the
commutativity equality. `derivedBaseChangeMapPlus` is the right-derived descent of
that underived mate, with its computation on complexes given by
`derivedBaseChangeMapPlus_fac_app` and its uniqueness by
`derivedBaseChangeMapPlus_ext`. The fully generic
`CategoryTheory.Adjunction.derivedPlus_mateEquiv_app_fac` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`
states that the mate under the canonical bounded-below derived adjunctions is computed
by exactly this underived mate on complexes, with exactly these comparison factors.
It has no monoidal assumptions. The square isomorphism on derived categories is
obtained by `Functor.mapDerivedCategoryPlusNatIso` and the composition comparison from
the underived square isomorphism, so its computation on complexes is the defining
exact-functor comparison. The derived universal property therefore identifies the
existing `derivedBaseChangeMapPlus` with the node's unit–square–counit mate for abelian
coefficients too. This does not assume a continuity or exchange invertibility theorem.

I also read `pullbackSquareComparison`, the unit/square/counit steps of `baseChange`,
and `baseChange_app_eq_mateEquiv` in the existing comparison module to confirm the
orientations. The current server sources were checked using `scompile.py --source`.
The helper uses the coefficient-general declaration directly. All transition and leg
maps remain the node's prescribed canonical maps; no stronger hypotheses or arbitrary
maps have replaced them, and no dependency cycle is added.


## Second reading by NW

I reread the item node, Tag 0EYM, the dependency signatures, and the complete Lean
signature. The item statement is rendered as follows (each verdict is **matches**).

| Node object, hypothesis, or conclusion clause | Lean rendering and verdict |
| --- | --- |
| Small nonempty directed poset | `{I : Type u}`, `[PartialOrder I]`, `[IsDirected I (· ≤ ·)]`, and `[Nonempty I]`; matches. |
| Inverse systems of sources and bases | `DV DB : Iᵒᵖ ⥤ Scheme.{u}`; functor laws give identities and composition; matches. |
| Stage transitions | `DV.map a.op` and `DB.map a.op` for `a : i ⟶ j` in `I`; these have source stage `j` and target stage `i`; matches. |
| Compatible stage morphisms | `η : DV ⟶ DB`, with naturality used at every `a.op`; matches. |
| Affine source and base transitions | The two separate instance binders `IsAffineHom (DV.map a)` and `IsAffineHom (DB.map a)`; matches. |
| Quasi-compact and quasi-separated stage maps | The separate binders `QuasiCompact (η.app i)` and `QuasiSeparated (η.app i)`; no extra geometric assumptions; matches. |
| Limit schemes and universal projections | `cV : Cone DV`, `hcV : IsLimit cV`, `cB : Cone DB`, and `hcB : IsLimit cB`; matches. |
| Limit morphism and compatibility | `v : cV.pt ⟶ cB.pt` and `hu : ∀ i, cV.π.app i ≫ η.app i = v ≫ cB.π.app i`; matches. |
| Abelian coefficient sheaves | `F i : Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u+1}`; matches. |
| Coefficient transition maps | `φ a : upperStar (DV.map a.op) (F i) ⟶ F j`; matches. |
| Coefficient identity and composition laws | `hφid` uses `DV.map_id` and `upperStarId`; `hφcomp` uses `upperStarComp`, `DV.map_comp`, and the two coefficient maps; matches. |
| Coefficient colimit on the limit source | `A`, `eA`, `hA`, `cA : Cocone A`, and `hcA : IsColimit cA` give exactly the prescribed inverse-image diagram and its colimit; matches. |
| Nonnegative degree | `q : ℕ`, cast to `ℤ` for the homology functor; includes `q = 0`; matches. |
| Higher direct images | `homologyFunctor (q : ℤ)` after `rightDerivedLowerStarPlus` of `singleFunctor ... 0`; matches the recorded direct-image definition. |
| Pulled-back higher-image diagram | `H`, `eH`, and `hH` identify each object and prescribe each transition by base inverse-image coherence and `relativeHigherDirectImageExchange`; matches. |
| General-square exchange | The helper takes `CommSq ⟨...⟩`, uses `derivedBaseChangeMapPlus`, and makes no cartesian or torsion assumption; matches the repaired dependency interface. |
| Source colimit of higher images | `cH : Cocone H` and `hcH : IsColimit cH`; matches. |
| Canonical legs to the limit higher image | `legs : H ⟶ (Functor.const I).obj (...)` and `hlegs` specify each leg using the projection square and the coefficient coprojection; matches. |
| Canonical comparison | `hcH.desc { pt := ..., ι := legs }`; this is the specified universal-property map, not an arbitrary map; matches. |
| Isomorphism conclusion | `IsIso (hcH.desc ...)`; matches. |
| No torsion or cartesian-square hypotheses | Neither appears in the binders; only commuting `CommSq`s are used; matches. |

Edge cases checked: a singleton or constant index diagram; `q = 0`; zero coefficient
sheaves; empty schemes and bases; noncartesian commuting squares; and distinct choices
of limit and colimit cones. All remain admitted. The index universe is exactly the
scheme universe `u`, while coefficient sheaves are in `u+1`; there is no smaller
independent index or test-object universe.

Searches were rerun with `msearch.py` using LeanFinder, Loogle, LeanSearch, and grep
queries for higher direct images, relative colimits, and base-change mates. I also
searched Mathlib, `WeilConjectures/`, and `lean/Sheaf` for both declaration names and
for the exact item id. The only related upstream declaration is fixed-base
`Etale.higherDirectImage_limit`, which does not state this varying-base,
varying-coefficient result. The exact helper and theorem are absent elsewhere.

The only interface issue found was the recorded dependency
`def-kun-commutative-derived-exchange`: its attached `baseChange` construction requires
coefficient structures unavailable for `AddCommGrpCat`. I repaired that dependency
record to the existing coefficient-general
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, with a note documenting the
underived mate characterization and why the old interface was unusable. No item
statement, hypothesis, conclusion, or source construction needed correction. The
module compiled cleanly with `scompile.py`; the node's `lean.statement` is byte-for-byte
equal to the theorem signature.
