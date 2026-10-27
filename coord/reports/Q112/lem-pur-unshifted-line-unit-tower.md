## Worker report

The module `Sheaf.Paper.UnshiftedLineUnitTower` states the coefficient-unit and unshifted
Tate-line calculation. Its main declaration is
`WeilConjectures.PurityFiniteSetting.unshifted_line_unit_tower`. The transparent predicate
`unshiftedLineUnitTowerAssertions` spells out the equations. All five theorem proofs are
`sorry`; all definitions have actual data. The two choices of sheaf isomorphisms are
from uniqueness theorems with complete section formulas. The derived unit is built from
the specified resolving counit, not from an unspecified isomorphism.

Hypothesis and clause correspondence:

- The finite-field datum, prime ell distinct from p, and coefficient conventions are
  `P : PurityFiniteSetting`; use `P.field`, `P.coefficients.l` and
  `P.coefficients.different`. Its fixed finite coefficient extension and level are unused
  ambient convention data; no assertion depends on them. All choices of these data are
  allowed.
- The separated finite-type k-scheme is `S`, `[S.Over (Spec (.of P.field.k))]`, with
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structure morphism in
  the main theorem. The predicate constructs each residue-field inverse from
  `P.coefficientPrime_isUnit_stalk`, mapped to the residue field. No invertibility
  assumption has been added.
- The three finite extensions are `E`, `F`, `G`, each with `Field`,
  `Algebra (Padic P.coefficients.l)` and `FiniteDimensional`. The inclusions `ι` and `κ`
  are algebra homomorphisms; between fields they are injective. `κ.comp ι` is the direct
  inclusion. No strictness or nonidentity condition appears.
- The completed rings are `completedIntegralCommRingSheafUnrestricted`, with the recorded
  underlying ring sheaf `completedIntegralCoefficientSheafUnrestricted`; `regular` is
  just its existing regular module. `integralConstantCoefficientObject` is U=R[0],
  and `constantWeilIntegralComplex` is its actual degree-zero representative.
- The site is literally `S.ProEt` with `Scheme.ProEt.topology S`, object universe u+1,
  morphism universe u, and module universe u+1. Unbounded derived objects and morphisms
  are in the existing `DerivedCategory (integralTowerModules ... S)`.
- `m : ℕ` renders precisely m≥0, including zero. `integralTwistLine ... (m : ℤ)` is J;
  `lineUnit` is V=U(m); `lineModel` is the sheaf R tensor J. `lineCoordinate` is the
  existing scalar tensor left unitor identifying R tensor J with J, so displayed line
  values have exactly the target J from the node.
- C is `completedDerivedScalarExtension`, which despite its historical name is the
  ordinary derived extension in FiniteFreeCompletedScalarComparison. Its underlying
  sheaf and complex functors are `completedOrdinaryScalarExtension` and
  `completedOrdinaryScalarComplex`; its canonical resolving arrow is
  `completedScalarCounit`. The inclusion is `completedCoefficientMap`.
- Alpha is the **existing** `CompletedLineTensor.associatorData ... .derived`;
  `.sheaf` is its actual ordinary representative. `IsAssociatorNormalized` specifies
  its tensor formula and universal-counit equation. Thus neither an arbitrary
  associator nor a different completed associator is substituted.
- `multiplication_existsUnique` specifies x tensor b ↦ iota(x)b and the inverse
  b ↦ 1 tensor b over every site object, through `completedScalarTensorSection`.
  `multiplicationComplex` uses the standard exact single-complex comparisons.
  `unitMap` is exactly the resolving counit followed by the localization of that chain
  multiplication. `unitMap_isIso` supplies only the invertibility proof; `unitIso` is u.
- `lineIso` is **definitionally** the specified `integralTwistOrdinaryBeta` at U followed
  by the target twist of `unitIso`. U is bundled with its recorded constructibility
  proof by `constantWeilIntegralObject`, so beta is applied on its actual domain.
- `lineMultiplication_existsUnique` gives the exact displayed formula
  iota(x)b • theta(z) after the standard target unitor. Here
  `theta = twistScalarMaps`, the semilinear map z ↦ b_ji(z tensor 1), whose equation
  with `twistLineScalarIso` is `integral_twist_base_change`. The `@id` coercions merely
  expose the target line module action rather than its restricted source action.
- `lineMultiplicationComplex` is its genuine degree-zero chain map.
  `lineIso_model` equates the specified beta-composite with its localization through
  the two exact-tensor localization comparisons and the K-flat scalar counit.
- The first four conjuncts of `unshiftedLineUnitTowerAssertions` are equality of
  **sheaf morphisms** for unit and line, then equality of **derived morphisms** for
  unit and line, with Lean's left-to-right composition orientation. They render
  u20 alpha = u21 C21(u10) and w20 alpha = w21 C21(w10).
- The next sectionwise unit conjunct gives the value iota20(x)iota21(b)c on **each**
  of the direct and successive paths. The next line conjunct gives the direct value
  with theta20(z) and the successive value with theta21(theta10(z)), respectively.
  These are asserted in addition to the sheaf and derived morphism equalities;
  nothing assumes that arbitrary global sections are pure tensors.
- The identity derived comparisons are equated to
  `CompletedLineTensor.ordinaryUnit` at U and V. The identity chain comparisons are
  equated to `completedScalarIdentityMultiplication` at their actual models. These
  state the multiplication unitors rather than strict functor identities.
- The last conjunct gives the specified chi identity normalization on each of the
  two models: after `integralScalarExtensionComparisonOfUniverses`, chi is the
  scalar counit, multiplication, then the independently constructed
  `completedScalarIdentityUnit`. This is the natural derived-completeness map.
  The preceding good-model conjunct supplies K-flatness and flat terms for the line
  representative; the unit's good-model witness is already `constantWeilIntegralGood`.

Dependency declarations read and used (module names have their usual `Sheaf.` prefix
unless stated otherwise):

- `Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `coefficientPrime_isUnit_stalk`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, topology.
- `NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`,
  reexporting the recorded integer ring, uniformizer, and positive finite quotients.
- `Paper.CompletedIntegralConstantMapOfUniverses`: the recorded completed ring framework,
  reexporting `completedIntegralCoefficientSheafUnrestricted` and its commutative version.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`.
- `CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the same
  `SheafOfModules` category used by `integralTowerModules`.
- `Paper.IntrinsicCoefficientTwistsUnrestricted`: the published signed integral lines
  and exact `integralSheafTwist`, reexported without a new twist construction.
- `Algebra.Homology.OrdinaryDerivedChangeOfRings`: reexports the generic ringed-site
  derived-change-of-rings and cochain model; ordinary-module specialization is unused.
- `Paper.FiniteFreeCompletedScalarComparison`: `completedScalarChangeData`,
  `completedCoefficientMap`, ordinary sheaf/complex/derived functors,
  `completedScalarTensorSection`, `completedScalarCounit`, `completedScalarComparison`,
  `completedScalarIdentityMultiplication`, `completedScalarIdentityUnit`.
- `Paper.IntegralTwistDerivedScalarCanonical`: `integralTwistOrdinaryBeta`; its entire
  defining K-flat descent and completion-conjugation characterization was read in
  `IntegralTwistDerivedScalar` and retained.
- `Paper.IntegralTwistBaseChange`: `integral_twist_base_change`, `twistScalarMaps`, and
  `twistLineScalarIso`, including its formula and tower clause.
- `Paper.CompletedLineTensorCoherence`: `associatorData`, its `.sheaf` and `.derived`
  projections, `IsAssociatorNormalized`, and `ordinaryUnit` with its counit normalization.
- `Paper.ConstantCoefficientScalarNormalization`: reexports
  `integralConstantCoefficientObject`, `constantWeilIntegralComplex`,
  `constantWeilIntegralGood`, and `constantWeilIntegralObject` with their actual
  constructibility proof. The completed scalar-unit map is not used to define u.
- Proof imports: `Algebra.Homology.ChangeOfRingsKFlat` and
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
  The proof-only node `lem-pur-tate-unit-flat-model-domains` has no recorded Lean module,
  so there is no module to import for it; its mathematical statement is read and the
  exact required good-model assertion is included here.

Two already-landed nodes were added to stmt_deps, as the standing brief permits:
`lem-pur-completed-line-tensor-coherence` for its specified associator/unit, and
`lem-weil-constant-coefficient-objects-constructible` for the existing U and its
constructible-category lift. No new node, dependency repair, or statement correction.

Edge cases checked before writing and against the final statement: m=0 uses the recorded
zero-power coefficient unit; identity inclusions are allowed by `AlgHom.id` and the explicit
unit clauses; ι or κ can be identity independently or together; the empty scheme is allowed
(no Nonempty or nonzero-stalk assumption, and all formulas are local); any coefficient
extension size and any scheme size can be placed in the common ambient universe. The
small site's unequal object and morphism universes are retained. The equations involve
actual morphisms and chain maps, not only their effects on cohomology. No mathematical
fault or STATEMENT-DISPUTED issue was found.

Sources read: the entire item and all statement-dependency records; the local Stacks
`sites-modules.tex` section-tensor-product (03EK) and sheafification-tensor (0GMW),
`sites-cohomology.tex` lemma-derived-base-change (06YY) and lemma-pullback-K-flat (0G7E).
The current blueprint has renamed the older source file: read
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/`
`sk-thm-purity-transport-coefficient-change.proof.md`, clause (3), on coefficient
extension compatibility; the item remains the explicit auxiliary multiplication lemma.

Searches actually run using msearch.py (Q112, this item):

- leanfinder: “Derived coefficient multiplication on units and Tate lines is compatible
  with towers and identity scalar extensions”. Eight unrelated cotangent/base-change
  hits; no derived sheaf unit/Tate-line result.
- loogle: `ModuleCat.extendScalarsComp, ModuleCat.extendScalarsId`. Four ordinary-module
  composition/unit equations, no completed-ring sheaf or specified beta.
- grep in Mathlib Algebra/Category/ModuleCat: `extendScalarsComp|extendScalarsId`.
  Seven hits in ChangeOfRings and Pseudofunctor; ordinary module infrastructure only.
- leansearch: “Base change of coefficient ring units and Tate line module sheaves is
  associative in a tower in the derived category”. Eight hits, including
  `ModuleCat.extendScalars_assoc'`, ordinary tensor base-change and pushforward
  associativity; no exact match.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for the
  item id, unshifted unit/tower names, and coefficient-unit notions. No exact statement.
  Read the related shifted-unit module, which proves only its own shifted/base-field
  case and is a downstream consumer; it is not imported. Its helper unit comparison
  uses completion coordinates, whereas this item specifies the ordinary resolving
  multiplication directly. Reused the independently published CompletedLineTensor
  associator and scalar left unitor instead of defining those notions again.

Validation: scompile.py compiled both the sandbox and actual module paths cleanly,
with the default 60-second per-file limit. The final dry run and delivery results are
reported by the prescribed delivery wrapper.

## Second reading by Q112

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
