## Worker report

The module `lean/Sheaf/Paper/CompletionMap.lean` defines
`AlgebraicGeometry.Scheme.adicCompletionMap` as
`M.realization.inv ≫ (adicLocalization X Λ).map (adicCompletionChainMap X d M)`.
It uses the explicit shifted mapping cone, with zero homotopy component, rather
than choosing a lift into a previously selected distinguished triangle. The
item's statement and dependency list are unchanged. No new or dependency nodes
are needed; auxiliary declarations belong to the construction already described
by this definition node. Every postponed property is a named theorem with a
source and natural-language proof in its docstring. Every definition contains
actual data; the two choices select objects uniquely characterized by formulas.

Source read: the item's complete DAG statement and the imported blueprint
`literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/def-weil-pbc-completion-map.md`,
order 1258. The imported blueprint says to use the compatible quotient arrows;
the audited DAG specifies the strict model needed to make that phrase precise.
Mathlib's `MappingCone.lean`, `MappingCocone.lean`, `HomotopyCofiber.lean`, and
`HomotopyCategory/Shift.lean` were read to check coordinates and signs.

Hypotheses and clauses, matched individually:

- The scheme is `X : Scheme.{t}`, and the commutative coefficient ring is
  `{Λ : Type t} [CommRing Λ]`, following the recorded pro-etale category's size
  convention. The site still has object universe t+1 and morphism universe t.
- `d : CompleteCoefficientDatum Λ` retains all coefficient assumptions:
  `d.ideal`, `d.noetherian`, `d.finitelyGenerated`, `d.quotientTorsion`, and
  `d.quotientPerfect`. Thus neither completeness of Λ nor flatness of its
  quotients has been imposed. The quotient is `Λ ⧸ d.ideal ^ (n+1)`.
- `K : proEtaleDerivedCategory X Λ` is an arbitrary unbounded derived object.
  `M : AdicKFlatModel X Λ K` is the fixed model from the dependency, with its
  K-flatness, flat terms, and isomorphism `M.realization : Q(M.complex) ≅ K`.
  The dependency's `adicKFlatModel_exists` supplies such a model for every K;
  its construction represents K and takes the stated K-flat resolution. The
  representative and augmentation to it are subsumed in this realization, which
  is exactly the resulting e used by the item.
- `adicReductionComplex X d M n` is the same fixed `M.complex` extended to
  the quotient coefficient ring and restricted to Λ. The indexing n : ℕ means
  the paper's positive level n+1, covering all n≥1 without a level-zero quotient.
  This uses the dependency's ordinary scalar-extension complex, which computes
  derived tensor on this K-flat model. Its `adicReductionUnderlying_tensor`
  identifies it with the recorded derived tensor construction. The local scalar
  extension uses 1 tensor m, the canonical commuted version of m tensor 1.
- `adicReductionComplexStep` is the already recorded `adicTransitionComplex`
  for levels n+2 and n+1. It acts by the quotient homomorphism on coefficients.
- `adicReductionAugmentation_exists` specifies the unique chain map on every
  degree, every site object, and every local section by `adicTensorSection ... 1 m`.
  `adicReductionAugmentation` selects that uniquely specified map, not an
  arbitrary map obtained from a mere existence assertion.
- `adicReductionAugmentation_step` states strict compatibility as an equality
  of chain maps before localization, not merely a derived equality.
- `adicReductionProduct` is the categorical product of these complexes; the
  imported homological-complex limits construct it termwise.
  `adicReductionProductShift` uses the existing `towerProductShift`, so its
  n-th component is the (n+1)-st projection followed by the strict transition.
- `adicReductionProductAugmentation` is `Pi.lift` of all a_n.
  `adicCompletionLift_relation` states the zero-homotopy cocycle equation,
  equivalently a followed by (1-s) equals zero strictly.
- `adicCompletionComplex` is Mathlib's `mappingCocone (𝟙 _ - s)`, definitionally
  `(mappingCone (𝟙 _ - s))⟦(-1 : ℤ)⟧`. Mathlib orders the raw cone summands
  as source-shifted then target. Exchanging them after shifting gives exactly
  the item's `C^j = B^(j-1) ⊕ B^j` and
  `d(y,x) = (-d y - (1-s)x, d x)`. There is no change of cone sign.
- `adicCompletionChainMap` uses `mappingCocone.lift` with a as its first
  coordinate and zero as its degree-minus-one coordinate. In the item's
  (y,x) order this is exactly (0,a), not an unspecified triangle lift.
  Mathlib's `lift_fst` and `lift_f_snd_v` specify these two coordinates.
- `adicCompletionObject` is Q(C). `adicCompletionMap` is e⁻¹ followed by Q(j),
  in Lean's left-to-right composition order.
- `adicCompletionProjection` is the canonical projection onto B, `(y,x) ↦ x`.
  `adicCompletionMap_projection` states the asserted quotient-arrow formula
  for every positive level after localization and precomposition by e⁻¹.
- `adicReductionSequence_hasProduct` states existence of the derived product.
  `adicCompletionProductComparison` is the canonical comparison defined by
  the localized product projections. Its `isIso` theorem states precisely the
  exact-products comparison, using the two recorded product dependencies.
  `adicCompletionProductIso` packages that particular comparison as an iso.
- `adicCompletionBoundary` uses the actual localized mapping-cocone triangle's
  boundary and the inverse of that canonical product comparison.
  `adicCompletion_distinguished` states the required Roos triangle property.
  `adicCompletionLimit` packages this specific object, projection, and boundary
  using the recorded `AdicDerivedInverseLimit` structure. The product instance
  in these packaging declarations is available by `adicReductionSequence_hasProduct`;
  it is not an additional mathematical hypothesis on the completion map.
- For a second fixed model N, `adicCompletionTowerMap_exists` quantifies over
  every family τ of strict tower maps and its strict transition compatibility.
  Its equations specify the product map in both cone coordinates, in every
  degree, uniquely. `adicCompletionTowerMap` selects this uniquely specified
  chain map. This implements the last sentence of the node. The zero map is
  included, and compatibility is required before localization.

Dependency declarations used, with their source modules read:

- `Sheaf.Paper.CompleteCoefficientDatum` (via the public import of
  `Sheaf.Paper.AdicDerivedInverseLimit`): `CompleteCoefficientDatum`,
  `AdicKFlatModel`, `adicKFlatModel_exists`, `adicLocalization`,
  `adicRestrict`, `adicChange`, `adicTensorSection`, `adicTransitionComplex`,
  `adicModuleRing`, and the `adicReductionUnderlying_tensor` comparison.
- `Sheaf.Paper.AdicDerivedInverseLimit`: `adicReductionSequence`,
  `adicReductionStep`, `AdicDerivedInverseLimit`. Its upstream import provides
  `CategoryTheory.towerProductShift` and `IsDerivedLimitTriangle`; no private
  tower or derived-limit notion is redefined.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`.
  The named `adicLocalization` is definitionally this Q; the module exposes
  its inherited `CommShift` instance for its use in `mapTriangle`.
- `Sheaf.Algebra.Homology.KFlatResolutionGeneral`:
  `CochainComplex.exists_isKFlatResolutionGeneral`, used by the existing model
  availability construction; the import retains this statement dependency.
- `Sheaf.Algebra.Homology.DerivedTensor`: `Scheme.derivedTensor` and
  `Scheme.derivedTensorRing`, through the recorded coefficient-model interface.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`:
  `Scheme.ProEt.countableProducts_exact`, for product existence and exactness.
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts`:
  `CategoryTheory.derivedCategory_countableProducts_core`, for the localized
  product cone and the derived-product comparison.

Existing-definition searches actually run:

- msearch LeanFinder: "canonical completion map from a complex to shifted
  mapping cone of one minus shift on quotient tower products". Eight hits,
  including `CochainComplex.mappingCone`, its `inl`, `inr`, `desc_f`, and
  `MappingConeCompHomotopyEquiv.hom`. These are general cone infrastructure,
  not the adic completion map. Their source was inspected and reused.
- msearch Loogle: `"mappingCone"`. Twelve cone-API hits; no completion map.
- msearch LeanSearch: "canonical completion map from a complex to homotopy
  inverse limit of reductions". Service unavailable: Internal Server Error;
  no mathematical no-match conclusion is drawn from that failure.
- msearch grep in Mathlib `Algebra/Homology`:
  `completionMap|adicCompletion|mappingFiber`. Zero hits.
- Direct rg of `lean/Sheaf` and slopmaster2 `WeilConjectures` for
  `completionMap|adicCompletion|mappingFiber|mappingCone.*lift|def-weil-pbc-completion-map`
  found ordinary ring/module completions and generic cone lifts, not this map.
  A separately requested nonexistent `Algebra/Homology/MappingCone.lean` path
  was corrected to `HomotopyCategory/MappingCone.lean`, which was read in full
  at the relevant constructors.
- Direct rg in slopmaster2 `WeilConjectures`, `dag/lean_names_upstream.json`,
  and `lean/Sheaf` for `def-weil-pbc-completion-map|adicCompletionMap|adicCompletionChainMap|adicCompletionObject`
  returned no matches. The dependency and Mathlib declarations listed above
  were read, including full signatures and docstrings, before being used.

Edge cases checked: I=0, I=Λ, the zero coefficient ring, K=0, the empty scheme,
unbounded K, and coefficients whose quotients are perfect but not Λ-flat.
The same construction applies in each case permitted by the coefficient datum.
Positive indexing avoids imposing an extra n=0 perfectness condition. No
boundedness, nonemptiness, characteristic, or quotient-flatness assumption is
introduced. Strict tower maps need not be invertible. Site universes remain
independent, as required by the small pro-etale site.

Validation: every theorem has `sorry` as its proof; no mathematical theorem was
proved in stage 2. The data-bearing definitions are explicit constructions or
uniquely specified maps. The final module passed scompile.py with no errors or
warnings. The only elaboration repair was exposing the existing localization's
CommShift instance, without changing a mathematical statement. All lines are
at most 100 characters. There are no statement corrections, disputed statements,
new nodes, dependency-record repairs, or unbound implicit variables.

## Second reading by ND

I read the complete node and CompletionMap.lean independently, then opened the
recorded dependency signatures and implementations in CompleteCoefficientDatum,
AdicDerivedInverseLimit, DerivedTensor, KFlatResolutionGeneral,
ProEtaleCountableProductsExact, DerivedLimitProducts, and Mathlib's
DerivedCategory.Basic. I read coord/pefw-upstream-framework.md. The generic
DerivedLimit and TowerTransitionEndomorphism modules were obtained with
`scompile.py --source`, since the older source checkout lacks those files.

Source check: the source pointer names blueprint order 1258, whose markdown
says to use the compatible quotient arrows. I also read the adjacent coefficient
datum (1255) and explicit inverse-limit model (1256): these specify the coefficient
conditions and Cone(1-s)[-1], with componentwise action of strict tower maps.
Stacks derived.tex, Definition 08TC and Remark 0H9J, explicitly warn that a lift
into an arbitrary derived-limit triangle is not unique. Stacks
sites-cohomology.tex, Lemma 06YS, supplies an unbounded K-flat resolution on any
ringed site, with flat terms and termwise surjective augmentation. No additional
scheme finiteness, characteristic, or completeness hypothesis is assumed there.
The archived wholeblueprint-final.tex does not have the completion construction at
the old line numbers cited in the node's historical split_report; the actual
source-pointer markdown and its adjacent definitions were used instead.

My object/hypothesis/conclusion checklist, with verdicts:

1. X is an arbitrary scheme; Lambda is a commutative Noetherian ring; I is
   finitely generated; Lambda/I is additively torsion; all positive-power
   quotients are perfect. Rendered by `X : Scheme.{t}`, `[CommRing Λ]`, and
   `d : CompleteCoefficientDatum Λ`. I opened all five datum fields, including
   `quotientPerfect : ∀ n, 1 ≤ n → ...`. Exact match; no quotient flatness or
   adic completeness assumed.
2. Complexes are Lambda_X-module sheaves on the small pro-etale site; Q is their
   derived localization. `adicModuleRing`, `SheafOfModules.{t+1}`, and
   `adicLocalization` are precisely the dependency's constructions, not copies.
   The site has object universe t+1 and morphism universe t. Exact match.
3. K is arbitrary and unbounded. A single fixed K-flat flat-term model and
   realization e are `K : proEtaleDerivedCategory X Λ` and
   `M : AdicKFlatModel X Λ K`, with `M.realization`. The representative and its
   resolution augmentation are used only through F and e in the node; this
   model records exactly those needed data. `adicKFlatModel_exists` ensures this
   is a choice of presentation, not an extra restriction on K. Exact match.
4. T_n uses the same F for all positive n, tensoring with Lambda/I^n and
   retaining Lambda scalars. `adicReductionComplex X d M n` unfolds to
   `adicRestrict ... (adicChange ... M.complex)` at exponent n+1. The dependency's
   `adicReductionUnderlying_tensor` compares it to the recorded derived tensor.
   Exact match, using the canonical commuted tensor order.
5. Quotient transitions are `adicReductionComplexStep`, using the recorded
   `adicTransitionComplex`, whose local formula applies the quotient ring map
   to the coefficient factor. Augmentations are `adicReductionAugmentation`,
   uniquely specified on every local section by `adicTensorSection ... 1 m`.
   `adicReductionAugmentation_step` asserts strict equality of chain maps.
   Exact match, with no derived-only compatibility substituted.
6. B is the termwise product; s has the stated successor projection formula.
   `adicReductionProduct` is the categorical complex product, computed termwise
   by HomologicalComplexLimits; `adicReductionProductShift` uses the existing
   `towerProductShift`. Its actual source is `Pi.lift (fun n ↦ pr (n+1) ≫ t n)`.
   Exact match.
7. Q(B) represents the product of the reductions. `adicReductionSequence_hasProduct`
   supplies existence, `adicCompletionProductComparison` is the specific comparison
   built from localized projections, and `adicCompletionProductComparison_isIso`
   supplies invertibility. Both exact-products dependencies have the required
   generality. The product instance in later packaging is not a new hypothesis
   on `adicCompletionMap`. Exact match.
8. C is Cone(1-s)[-1] with differential (-dy-(1-s)x,dx).
   `adicCompletionComplex` uses Mathlib `mappingCocone`. I checked the raw cone's
   differential in HomotopyCofiber and the shifted differential in Shift.
   Swapping the raw shifted summands gives exactly the node's (y,x) order.
   In particular, the minus in `mappingCocone.fst` cancels the sign in
   `Cochain.leftShift` at degree zero, so this projection is x, not -x.
   Exact match, including signs.
9. a has components a_n and j=(0,a). `adicReductionProductAugmentation` is
   `Pi.lift`; `adicCompletionLift_relation` is the zero-homotopy cocycle equation;
   `adicCompletionChainMap` is `mappingCocone.lift ... a 0 ...`. I checked
   `mappingCocone.lift_fst` and `lift_f_snd_v`: the coordinates are precisely a
   and zero. Exact match; no arbitrary triangle lift is selected.
10. comp_K is Q(j) after e inverse, and projects to every quotient arrow.
    `adicCompletionMap` is `M.realization.inv ≫ Q.map j` with target
    `adicCompletionObject = Q.obj C`; `adicCompletionMap_projection` gives the
    full projection equation for every n. Exact match, including composition order.
11. This particular C is an adic derived-limit triple.
    `adicCompletionBoundary` uses the actual mapping-cocone triangle and the
    inverse of the canonical product comparison; `adicCompletion_distinguished`
    and `adicCompletionLimit` use the dependency's `IsDerivedLimitTriangle` and
    `AdicDerivedInverseLimit`. The generic predicate's middle arrow is exactly
    `towerTransitionEndomorphism = 1 - towerProductShift`. Exact match.
12. Every strictly compatible map of the reduction towers acts by its product
    map on both coordinates. `adicCompletionTowerMap_exists` quantifies over
    arbitrary τ and strict compatibility hτ and uniquely specifies the two
    coordinate equations; `adicCompletionTowerMap` chooses that unique map.
    Exact match. No invertibility or compatibility with augmentations is added.

Edge cases: there is no variable index set here: the tower is the nonempty
positive integers, reindexed by all of Nat. Lean n=0 is exactly paper level 1,
not the quotient by I^0. Zero K, the empty scheme, the zero ring, I=Lambda,
and I=0 whenever the coefficient hypotheses hold all remain admitted. In
particular I=0 still requires Lambda torsion, as the node does. No boundedness,
nonemptiness of X, characteristic, or field hypothesis is present. Scheme and
coefficient sizes follow the existing pro-etale size convention; the construction
never identifies the site's object and morphism universes.

Independent one-definition searches:

- LeanFinder query `morphism to derived completion as homotopy limit of quotient
  complexes`: eight generic localization/homotopy-cofiber hits, no matching map.
- Loogle query `"mappingCocone"`: twelve generic cocone hits. I read and reused
  the actual cocone, lift, projection, and triangle declarations.
- LeanSearch query `canonical map into derived completion of a quotient tower`:
  Internal Server Error, recorded as unavailable, not a negative result.
- msearch grep `completionMap|derivedCompletion|mappingFiber`: five ordinary
  number-field completion-map hits, no match.
- Direct rg with `derived.?completion|completion.?morphism|completion.?map` and
  the item id across the project, current framework, older upstream, and
  Mathlib's Algebra/Homology found upstream `DerivedCategory.derivedCompletionCone`.
  I opened Complete/Defs.lean, including derivedCompletionDiagram and
  derivedCompletionCone: this is a cone with point K in the derived category of
  ModuleCat-valued sheaves, not a morphism to the specified strict shifted-cone
  target in our recorded module-sheaf category. It does not replace this node.
  The project's ExtendedCechCompletionModel is instead an internal-Hom completion
  reflection with its own augmentation, not this explicit reduction-tower map.

No mathematical mismatch found; no Lean declaration or node statement changed.
The only delivery change is this independent review report. There are no new
nodes or dependency modules to audit, and no statement_change or citer audit is
needed. Every postponed theorem belongs to a construction/property explicitly
present in this node and has its source, blueprint id, and natural-language proof.
All theorem proofs are sorry; the definitions contain actual data. The two
Classical.choose constructions use uniqueness by local-section or coordinate
formulas, not an unconstrained existence choice. All variables/universes are
bound, all lines are at most 100 characters, and lean.statement equals the main
signature verbatim. The complete delivered file passed scompile.py with no
errors or warnings (sandbox and library checks).
