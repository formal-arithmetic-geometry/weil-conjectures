## Worker report

The module `Sheaf.Paper.CompletedExtensionZeroComparison` states completed
extension-by-zero base change on the fixed small pro-etale sites. It now uses
`A : Type (t + 1)` with `Scheme.{t}`, the recorded coefficient limit and strict
reduction tower, the published transported intrinsic Koszul completion, and the
published completed tower pullback. The theorem remains unbounded and requires
only quasi-compactness of j in addition to the Cartesian open-immersion square.
The DAG statement, statement dependencies, and proof are unchanged.

This report supersedes the reports and second readings for the returned smaller
coefficient interface. A new independent second reading is required after this repair.

| Hypothesis or clause of the node | Lean rendering |
| --- | --- |
| Commutative ring A and Noetherian adic datum (A,I) | `{A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)`. `CompleteCoefficientDatum` supplies Noetherianity, finite generation, torsion first quotient and perfect positive quotients; `d.quotientFinite` supplies their finiteness. |
| Four schemes, four arrows, Cartesian square and open vertical arrows | `{U' U X' X : Scheme.{t}}`, the four named arrow binders, and `sq : OpenImmersionSquare gU j' j g`. Its inherited chosen Cartesian datum includes both projection identities; `sq.isOpenImmersion` and `sq.isOpenImmersion'` give the open conditions. |
| Quasi-compact j and unrestricted g | `[QuasiCompact j]`; no horizontal compactness or finiteness hypothesis. |
| Actual completed coefficients A_T and D(Mod(A_T)) | `completedReductionCoefficient T d`, the recorded limit of `reductionCoefficientSystem T d`; `pbcAdicCompletion T d` unfolds to this very same limit, and `pbcModules T (pbcAdicCompletion T d)` unfolds to `reductionModules T (completedReductionCoefficient T d)`. These are definitional aliases, with no unidentified ambient categories. |
| Slice-site identifications of coefficients | `cbcSliceFunctor`, `cbcFiniteSliceMap` and `cbcCompletedSliceMap`. The finite map is uniquely normalized on the actual `AdicCoefficients.functionPresheaf` sheafification units; the completed map is uniquely fixed by every `completedReductionProjection`. Commutative ring structure is forgotten only at the module pushforward. |
| The prescribed j! | `cbcOpenShriek` is slice module pushforward, `SheafOfModules.extensionByZeroPresheaf`, then `PresheafOfModules.sheafification`. `cbcDerivedOpenShriek` descends that exact functor termwise with `mapDerivedCategory`. |
| Arbitrary intrinsically complete input K | `K : (cbcCompleteProperty d U r a ha).FullSubcategory`. The object property applies recorded `IsDerivedCompleteIntrinsic` to `DerivedCategory.Q.objPreimage K` and its `objObjPreimageIso`. The published Koszul construction descends through quasi-isomorphisms, so this is precisely intrinsic completeness, independent of this representative. |
| Finite generators of I, with no additional condition | `(r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)`. Such a tuple exists from the datum; every tuple is allowed. |
| Completed pullback | `cbcCompletedPullback d g` is exactly `completedReductionTower Y d ⋙ completedTowerPullback g d ⋙ completedTowerRlim d X`. Its object action is the recorded `completedPullbackObject g d`. The tower counit is computed on objectwise K-flat strict replacements and preserves the actual transitions. |
| Canonical ordinary comparison | `cbcOrdinaryExchange` inverts the derived adjoint mate. The right exchange is fixed on sections by `MorphismProperty.Over.pullbackMapComparison`. `cbcModulePullbackAdjunction` fixes the pullback transpose by the small-model module inverse-image unit followed by the recorded `pbcTensorSection` at `1 tensor x`; `cbcOpenAdjunction` fixes the extension transpose by its direct-sum generator. The derived mate is fixed on K-flat representatives by recorded `completedOrdinaryPullbackComplexCounit`. |
| Canonical completed comparison in the required direction | `cbcCompletedExchange` is the unique natural map from `j!` followed by completed g-pullback to completed gU-pullback followed by `j'!`. Its normalization uses `cbcOrdinaryExchange` and the exact recorded `completedPullbackComparison`, assembled as a natural transformation. The latter is the strict quotient unit followed by the specified constant-tower/Rlim map. The proof docstring identifies this normalization with the finite-exchange/Rlim construction, including strict quotient transitions. |
| Isomorphism and naturality in K | `IsIso (cbcCompletedExchange d sq r a ha)`. The comparison is a natural transformation on the full subcategory, hence includes naturality for every ambient derived morphism between complete objects. |
| j!K remains complete | First conjunct inside `∀ K` of `completedExtensionZeroComparison`, using `cbcCompleteProperty d X r a ha`. |
| Both displayed sides are complete | The last two conjuncts apply the same predicate on X' to exactly the two displayed composites. |

Dependency declarations read and used:

- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum` (publicly reused
  from `CompletedAdicCoefficientDatum`), `AdicCoefficients.functionPresheaf`,
  `reductionCoefficient`, `completedReductionCoefficient`,
  `completedReductionProjection`, `reductionModuleRing`, `reductionModules`,
  and `completedReductionTower`.
- `Sheaf.Paper.IntrinsicCompletion`: `IsDerivedCompleteIntrinsic`,
  `intrinsicCompletionUnit`, `intrinsicPresentationDatum`,
  `intrinsicPresentationModules`, `intrinsicPresentationModulesBack`, and the
  identity-on-sections `intrinsicPresentationRoundTrip`. This public-imports
  `IntrinsicCompletionCompleted`, whose exterior Koszul complex, transitions,
  signed fibre, (u,0) unit, and `completedIntrinsicCompletion_descends` were read.
- `Sheaf.Paper.CompletedTowerPullback`: `completedCoefficientMap`,
  `completedModulePullback`, `completedOrdinaryPullback`,
  `completedOrdinaryPullbackComplexCounit`, `completedTowerPullback`,
  `completedPullbackObject`, `completedPullbackComparison`, and its
  finite-evaluation and completion-unit characterization statements.
- `Sheaf.Paper.CompletedTowerDerivedLimitFunctor`: `completedTowerRlim`,
  `completedConstantRlimUnit`. These are used through the recorded pullback module.
- `Sheaf.AlgebraicGeometry.OpenImmersionSquare`:
  `AlgebraicGeometry.OpenImmersionSquare` and its inherited chosen square.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `Scheme.ProEt.weaklyEtale_localization`, including cancellation, concrete
  site equivalence, coverings and constant-section normalization.
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf` and its direct-sum restriction formula.
- Mathlib `Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, `sheafificationHomEquiv`.
- Mathlib `AlgebraicGeometry.Morphisms.FiniteType` / `QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`.

The original blueprint excerpt in `scratchpad/blueprint-source.md` and the
node's eight-step corrected proof were reread. The archived source
`second-proetale.tex` was read at naive completion (099M), completed pullback
(099N, clauses 2 and 5), extension by zero, and quasi-compact j! limit
preservation (09BP). The source distinguishes constant and completed coefficients;
its completion comparisons preserve quotient projections and units. No node
statement correction or STATEMENT-DISPUTED flag is needed.

Edge cases checked: empty open and scheme, zero ring and complex, identity
vertical or horizontal arrows, empty tuple r=0 with I=0, I=top with an arbitrary
large coefficient ring, and the empty product. Positive index n=0 always means
exponent n+1. All rings A in Type (t+1) are allowed on the fixed Scheme.{t} site;
no shrinkability or universe equality is required. Site object and morphism
universes remain t+1 and t. The published AsSmall transport enlarges only Hom
sizes in its auxiliary model and returns modules to the original fixed site.

Searches repeated for this repair (also logged in `searches.jsonl`):

- LeanFinder: “Completed inverse image commutes with extension by zero for
  adically derived complete sheaves”; eight ordinary algebraic adic-completion
  hits, no sheaf extension-by-zero theorem.
- Loogle: `"extensionByZero"`; zero hits.
- LeanSearch: “completed pullback commutes with extension by zero on derived
  complete pro etale module sheaves”; eight ordinary module pullback and
  hypercover hits, no completed comparison.
- `rg` in Mathlib, upstream WeilConjectures, and project lean/Sheaf for
  `completed.*[Ee]xtension|completed.*[Ss]hriek|extensionByZero.*[Cc]omplet`;
  only coefficient scalar extensions, the older completion construction and
  a compact-support proof reference, no exact theorem.
- Read the exact side-project framework file
  `WeilConjectures/SixFunctors/ProEtale/LowerShriek/OpenImmersion/BaseChange.lean`
  and `derivedOpenImmersionLowerShriekBaseChangeIso`. This is the fixed abelian
  coefficient result, not this completed module-sheaf result.
- Read current server sources through `scompile.py --source` for both
  `Sheaf.Paper.IntrinsicCompletion` and `Sheaf.Paper.CompletedTowerPullback`;
  both now provide the required generalized published interfaces. The current
  shared DAG records name those exact declarations. No duplicate dependency
  construction or replacement node is delivered.

## Repair of return e161ccb796d2

1. H3/H13: the restricted Type t coefficient constructions were removed from the
   delivery. The theorem and all its helper interfaces now use Type (t+1)
   coefficients on the fixed Scheme.{t} site. Concurrently landed Q31
   `IntrinsicCompletion` and `CompletedTowerPullback` already supply exactly the
   requested generalized completion/pullback and canonical transport. Their
   current server sources were checked, and their now-usable DAG records are
   used directly. Consequently the former dependency-record overrides and both
   smaller-universe dependency modules are retired from this delivery rather
   than replacing those good published records. The intrinsic transport carries
   finite projections, generator actions, transitions and (u,0) completion units;
   the pullback comparison is the recorded strict quotient completion unit.
   The new tensor-unit adjunction and K-flat counit normalization carry the
   exchange map to these same recorded categories.
2. H6: retiring both superseded modules removes every arithmetic `change`/`omega`
   block and the proved quotient naturality block identified in the return.
   The needed new comparison naturality and open weak-etaleness obligations are
   named, documented helper theorems with `sorry`, recorded in lean.declarations.
   All remaining delivered theorem bodies are `sorry`; definitions have actual
   data. No local tactic proof is left inside a definition or a signature.

Validation: the final prescribed `scompile.py` invocation, including the three
new proof imports below, exited 0 with no errors or warnings. Both the sandbox
and module checks passed through the private local side overlay. All compilation
used the wrapper's unchanged per-file controls; no global build or live edit
was performed. The earlier dry run also returned OK (commit 1c77df2a95), except
for the independent second reading, which the next reader supplies.

The proof-import audit added the three newly recorded compatible proof-dependency
modules absent from the prior import closure: LocalizedModuleExactIndependent,
ExactFunctorDerivedLimit and RoosComplex. The upstream fixed-coefficient
`LowerShriek.OpenImmersion.BaseChange` was also tested, but importing it fails:
`UpperLowerStar.Defs` and `FiniteCoefficient.UpperLowerStar.Defs` both declare
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»`. Its import is therefore omitted;
the exact source was read, its canonical whole-adjunction conjugation is retained
in the construction here, and this compatibility exception is explicit.
The exact-item-id search in upstream and project Lean sources and the name
index returned no hits; an additional Mathlib grep for completed extension-by-zero
and shriek terms also returned no hits.

## Second reading by Q03

I independently reread the node statement, its blueprint source (order 1587), the
completed coefficient datum, intrinsic-completion, open-immersion-square, weakly
etale localization, extension-by-zero, sheafification, and completed-pullback
records, and the complete Lean module.

The node's objects and hypotheses are rendered as follows. The coefficient datum is
`{A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)`; its inherited
fields provide the Noetherian adic ring, finitely generated ideal, torsion residue,
and perfect quotients, while `d.quotientFinite` supplies finite positive quotients.
The square is `{U' U X' X : Scheme.{t}}` with arrows `gU`, `j'`, `j`, `g` and
`sq : OpenImmersionSquare gU j' j g`; the square carries the chosen Cartesian
comparison and both open-immersion instances. The sole additional geometric
hypothesis is `[QuasiCompact j]`; there is no hypothesis on `g` or `gU`.

The completed coefficient sheaf and module derived categories are rendered by
`completedReductionCoefficient T d`, `pbcAdicCompletion T d`, and
`pbcModules T (pbcAdicCompletion T d)`. `cbcSliceFunctor`, `cbcFiniteSliceMap`,
and `cbcCompletedSliceMap` provide the slice-site coefficient identifications,
with finite function-section and completed projection normalizations. The two
extension-by-zero functors are `cbcOpenShriek` and its termwise derived version
`cbcDerivedOpenShriek`; these use the recorded direct-sum presheaf followed by
module sheafification. Intrinsic completeness is the recorded
`IsDerivedCompleteIntrinsic`, transported through `cbcCompleteProperty`; the
explicit `(r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)`
are universally quantified witnesses for the datum's finitely generated ideal,
so every allowed generating tuple is covered and no extra assumption is imposed.
The completed pullback is the recorded composite `cbcCompletedPullback`, with
object action `completedPullbackObject`. `cbcOrdinaryExchange` is the ordinary
comparison and `cbcCompletedExchange` is the canonical completed comparison,
normalized by `cbcCompletedPullbackComparison`; its `IsIso` clause and natural
transformation domain encode the node's isomorphism and naturality in every
complete `K`. The final three conjuncts assert completeness of `j!K`, the pulled
left side, and the displayed right side in exactly `X` or `X'` as required.

Edge cases were checked in the module and source notes: empty schemes and opens,
the zero ring and zero complexes, identity arrows, `r = 0` with zero ideal,
`I = ⊤`, empty products, and the positive-index convention `n + 1`. The fixed
site has scheme universe `t` and coefficient universe `t + 1`; no universe
identification or shrinkability assumption was introduced.

Searches were repeated with LeanFinder, Loogle, LeanSearch, and `rg` over Mathlib,
the upstream WeilConjectures sources, and project `lean/Sheaf`; no exact completed
extension-by-zero comparison exists. The fixed-coefficient
`derivedOpenImmersionLowerShriekBaseChangeIso` was inspected and is a different
abelian six-functor result. The recorded dependency declarations were opened and
match the notions used here. No mathematical mismatch was found. The node `lean.statement` had been
whitespace-flattened rather than copied verbatim; I replaced it with the exact
multiline signature from the module. The mathematical statement and Lean code
are unchanged. Independent searches returned eight unrelated LeanFinder hits,
zero Loogle hits, and eight unrelated LeanSearch hits; the broader `rg` search
returned no completed-extension or completed-shriek statement.

Second-reader validation: `scompile.py` was invoked on the sole delivered module.
The prescribed `deliver2.py --no-push` then compiled both sandbox and library
forms and returned `OK (dry run)` at f4c95bbcc1. The exact multiline recorded
signature is a verbatim substring of the file; every declared helper is listed,
all lines satisfy 100 columns, only `lean` differs from the base node, and there
are no sibling modules, new definition nodes, or dependency overrides to compile.
