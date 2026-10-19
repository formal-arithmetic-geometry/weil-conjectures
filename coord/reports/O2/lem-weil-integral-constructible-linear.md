## Worker report

Owning-node repair for `lem-weil-integral-constructible-linear`, group N2,
2026-10-16. The node's `lean_invalidation` (L maintenance Q22) requires the
currently recorded intrinsic integral constructible category. No separate
`coord/repair-notes/lem-weil-integral-constructible-linear.json` is present.

The delivery adds `Sheaf.Paper.SfIntegralConstructibleLinear`, publicly importing
the published legacy `Sheaf.Paper.IntegralConstructibleLinear` unchanged.
The latter's canonical ambient action is retained. Its old constructible
subcategory is not identified with the new predicate. Instead, the new module
restricts that ambient action directly to the recorded `sfIntegralConstructible`
full subcategory, with its recorded repaired triangulation. Only this item's
`lean` record is changed; no other DAG node or existing source file is changed.

The new declarations are:

- `WeilConjectures.sfIntegralCoefficientLinear`: an instance adapter, whose data
  is exactly `integralCoefficientLinear l E Y`, for the ambient category written
  as `DerivedCategory (scalarReductionSource l E Y)`.
- `WeilConjectures.sfIntegralConstructibleLinear`: Mathlib's
  `Linear.fullSubcategory (sfIntegralConstructible l E Y)`, with that ambient action.
- `WeilConjectures.sfIntegralConstructible_linear`: the single new postponed theorem,
  with the five-step DAG proof in its docstring. It states the canonical scalar
  formula, ambient shift linearity, inclusion linearity, and all intrinsic shifts'
  linearity.
- `WeilConjectures.sfIntegralConstructibleShift_linear`: an instance obtained from
  the final conjunct of that theorem. No arbitrary linear structure is selected.

Hypotheses and clauses of the natural statement are rendered as follows:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- A finite extension E/Q_ell: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The valuation ring and uniformizer are the recorded
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`.
- Scheme Y: `(Y : AlgebraicGeometry.Scheme.{u})`, with no finiteness or base-field
  restriction. As in the repaired statement dependencies, the construction is
  intrinsic: the ambient constant-section action works for every Y and hence in
  the blueprint's context ell ≠ p. No extra finite-field datum is required by
  these same recorded categories.
- The actual completed integral sheaf, rather than a discrete constant sheaf:
  `scalarReductionSource` is modules over the underlying ring sheaf of
  `completedIntegralCommRingSheafUnrestricted`. Forgetting commutativity recovers
  `completedIntegralCoefficientSheafUnrestricted` definitionally. Consequently
  this category and `integralTowerModules` are definitionally identical, as are
  their standard derived localizations. The alias instance typechecks with the
  published action directly; no isomorphism or transport theorem is postulated.
- Scalar multiplication through constant sections: the first conjunct is
  `a • f = (integralScalarDerivedAction l E Y a).app K ≫ f` for every scalar,
  pair of ambient objects and derived morphism. The imported scalar transformation
  is the localization of the natural chain endomorphism multiplying in every
  degree by `integralScalarConstant`. That constant is uniquely specified by all
  its positive finite quotient residues, the sheafification unit applied to the
  quotient class of a. These are the same residues as the actual limit cone in
  the recorded `integralConstantToCompletion`. Naturality restricts the section
  at the terminal object to every site object; this is exactly the stated global
  constant-section map, not an arbitrary central action. The old
  `integralCoefficientLinear_existsUnique` fixes this very linear structure.
- Every Hom is an O_E-module and composition is bilinear:
  `CategoryTheory.Linear (Padic.coefficientExtensionIntegers l E) ...` in the
  imported ambient instance and the new full-subcategory instance. Its fields
  `homModule`, `smul_comp`, and `comp_smul`, with the existing `Preadditive`, give
  exactly the additive and homogeneous identities in both variables.
- All ambient integer shifts are linear: the second conjunct quantifies `n : ℤ`
  and asserts `Functor.Linear` for `shiftFunctor` of the ambient derived category.
- The full integral bounded constructible category is the recorded one:
  `sfIntegralConstructibleCategory l E Y`, definitionally the full subcategory
  of `sfIntegralConstructible`. Its Hom module data is inherited via the exact
  Mathlib `Linear.fullSubcategory` construction. Its inclusion is linear, the
  third conjunct, so there is no independently chosen subcategory action.
- The triangulated structure is precisely the recorded dependency's:
  `sfIntegralConstructible_isTriangulated` and
  `sfIntegralConstructible_isClosedUnderIsomorphisms` are imported instances.
  Mathlib supplies the inherited zero, shifts, distinguished triangles,
  triangulation and exact full-subcategory inclusion.
- All constructible shifts are O_E-linear: the fourth conjunct quantifies every
  `n : ℤ`; the final instance exposes that same assertion to consumers.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, importing the original coefficient
  extension constructions in `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `Sheaf.Paper.CompletedIntegralCoefficientGerm`:
  `WeilConjectures.integralConstantToCompletion`, importing the actual completion,
  coefficient tower and projections from `CompletedIntegralCoefficients`.
- `Sheaf.Paper.SfIntegralConstructible`:
  `WeilConjectures.sfIntegralConstructible` and
  `WeilConjectures.sfIntegralConstructibleCategory`, publicly through the
  triangulation module.
- `Sheaf.Paper.SfIntegralConstructibleTriangulated`:
  `WeilConjectures.sfIntegralConstructible_isClosedUnderIsomorphisms` and
  `WeilConjectures.sfIntegralConstructible_isTriangulated`.
- `Mathlib.CategoryTheory.Linear.Basic`: `CategoryTheory.Linear` and
  `CategoryTheory.Linear.fullSubcategory`.
- Proof dependencies imported: `Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`
  (`Padic.finite_module_adic_complete_and_hom`, clause (2));
  `Mathlib.CategoryTheory.Limits.HasLimits` (`CategoryTheory.Limits.limit`);
  `Sheaf.CategoryTheory.RingedSiteModules` (`CategoryTheory.ringedSiteModules`);
  `Mathlib.Algebra.Homology.DerivedCategory.Linear` (`DerivedCategory.instLinear`,
  `DerivedCategory.instLinearCochainComplexIntQ`, and
  `DerivedCategory.instLinearShiftFunctorInt`);
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` (`DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`).
- Existing ambient construction reused from
  `Sheaf.Paper.IntegralConstructibleLinear`:
  `WeilConjectures.integralCoefficientLinear_existsUnique`,
  `WeilConjectures.integralCoefficientLinear`, and the old ambient shift theorem.
  Its scalar transformation is in `IntegralScalarExtensionWellDefined`.

Edge cases checked: the empty scheme is allowed (constant maps land in its
possibly trivial section ring); zero objects and zero morphisms are allowed;
all positive finite levels start at n+1, including the first exponent 1; the
shift ranges over all integers, including 0 and negative shifts. No rank,
finite-Tor-dimension, nonemptiness, boundedness beyond the recorded predicate,
or characteristic condition on Y is introduced. The small pro-etale site has
object universe u+1 and morphism universe u, and module universe u+1; the adapter
uses these same universes without identifying site object and morphism sizes.
The source is the blueprint rationalization definition, order 1460, which
requires this exact O_E-linear triangulated input. No statement correction or
STATEMENT-DISPUTED flag is needed.

Searches (2026-10-16):

- `msearch.py ... leanfinder "The derived category of sheaves of completed integral
  coefficients and its constructible full subcategory are linear with linear shift"`:
  8 hits, including the general `DerivedCategory.instLinear`, linear localization,
  and shift results. They require the input category's linear structure and do
  not state the canonical completed-coefficient or intrinsic-subcategory clauses.
- `msearch.py ... loogle "CategoryTheory.Linear, DerivedCategory"`: 10 hits,
  including the same generic derived linearity declarations, read at their full
  signatures in `DerivedCategory/Linear.lean`.
- `msearch.py ... grep "Linear|Shift" CategoryTheory/Linear`: 20 hits, including
  the existing notion of linear category and linear functor. Directly read
  `Linear.fullSubcategory` and `fullSubcategoryInclusionLinear`; reuse them.
- `rg` in upstream `WeilConjectures` for
  `sfIntegralConstructible.*[Ll]inear|integralCoefficientLinear|integralConstructibleShift_linear`:
  no match. `grep -rn "lem-weil-integral-constructible-linear"` there: no match.
- The same `rg` in `lean/Sheaf` finds the legacy ambient and old constructible
  interface only, plus an old rationalization caller. No intrinsic linearity
  interface is already present. A further exact-name search of all four new
  declaration names across Mathlib, upstream, and the side source has no match.

## Validation (2026-10-16, resumed worker)

Re-read the current node and all five statement-dependency records, their source
signatures and docstrings, the Q22 invalidation, the archived ambient action,
the stage rules, and the blueprint rationalization unit. No separate repair note
exists. The Lean module requires no further source change. The sandbox node
continues to differ from the shared node only in `lean`; its signature is verbatim
from the file, with explicit variables and universes and no line over 100 columns.

Fresh prescribed searches again returned eight generic derived-linearity hits
(LeanFinder), ten generic derived-linearity hits (Loogle), and twenty hits on
linear categories and functors (Mathlib grep). The upstream and side-source search
again found only the legacy action and old subcategory interface, so the intrinsic
subcategory interface is not an existing declaration.

`scompile.py N2 lem-weil-integral-constructible-linear
lean/Sheaf/Paper/SfIntegralConstructibleLinear.lean` now succeeds: the sandbox
and library forms compile in 2.7 and 2.6 seconds, respectively. The prior
publication inconsistency does not recur against the current sources/artifacts.
Transcript: `scratchpad/attempt5-scompile.log`.

Consumer validation through the same wrapper compiled the delivered module and
`scratchpad/ConsumerChecks.lean` separately in dependency order. All checks succeed:
ambient and intrinsic `Linear` instances, intrinsic `IsTriangulated`, every
intrinsic shift's `Functor.Linear`, linear inclusion and exact triangulated
inclusion. The consumer also reads the canonical ambient characterization and
legacy declarations unchanged. No errors or warnings occur. Transcript:
`scratchpad/attempt5-consumer.log`. This validates the Q22 required interface on
the currently recorded `sfIntegralConstructibleCategory`, with its actual
triangulation, and preserves legacy callers.

The required `deliver2.py N2 lem-weil-integral-constructible-linear --no-push`
printed `OK (dry run)`: compilation and preflight pass except the second reading,
which is reserved for the independent reader. Nothing was pushed. Transcript:
`scratchpad/attempt5-dry-run.log`. A final dry run includes this updated report.

## Second reading by N2

Independent second reader, 2026-10-16. I opened the sandbox Lean and node, the
shared node including its Q22 invalidation, all five statement-dependency records
and their actual declarations, and the source paragraph in blueprint order 1460.
There is no separate repair-note file. This is the owning-node repair explicitly
requested by Q22, not a restoration of the withdrawn attachment. There are no new
nodes, dependency modules, or statement corrections in this delivery.

Clause-by-clause inventory and verdicts:

1. Prime ell: `(l : ℕ) [Fact l.Prime]` supplies exactly primality. The blueprint
   paragraph starts in the global finite-field context with ell different from p.
   Neither p nor the finite-field datum occurs in the construction or conclusion.
   I checked the recorded unrestricted completion, intrinsic predicate and repaired
   triangulation: they deliberately omit that auxiliary datum. The present action
   is the same intrinsic construction, applicable in particular in the source's
   ell-not-p context; it adds no invertibility or characteristic restriction on Y.
   This is consistent with Q22's instruction not to narrow consumers' base fields.
2. Finite extension E/Q_ell and its valuation ring: `(E : Type u) [Field E]
   [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` and
   `Padic.coefficientExtensionIntegers l E`. I read the coefficient dependency's
   record, `CoefficientExtensionFinite`, and the imported coefficient construction.
   These are the recorded spectral-absolute-value integer ring, chosen uniformizer
   and quotient rings, not an arbitrary ring or an additional valuation hypothesis.
   Verdict: match.
3. Scheme Y, its small pro-etale site and completed ring: `(Y : Scheme.{u})`, with
   no extra scheme instance. I read `scalarReductionSource` in
   `DerivedScalarExtensionRestrictionAdjunction`, `integralTowerModules` in
   `IntegralReductionTowerUnrestricted`, and the two unrestricted completed-sheaf
   definitions in `CompletedIntegralCoefficients`. The first uses
   `derivedChangeRingIndependentCoefficients` to forget the commutativity of the
   actual completed ring; the second uses its underlying ring sheaf directly.
   They are definitionally the same module category. The completion is the actual
   inverse limit of constant finite quotient ring sheaves, not the discrete
   constant integral ring sheaf. Verdict: match.
4. Ambient derived category: `DerivedCategory (scalarReductionSource l E Y)` uses
   that module category and its standard localization. The instance adapter is
   literally `integralCoefficientLinear l E Y`; no new ambient action, localization
   equivalence, or arbitrary identification of categories is postulated. Verdict:
   match, also confirmed by the compiler accepting this adapter.
5. Scalars act through compatible constant global sections: the first conjunct of
   `sfIntegralConstructible_linear` states, for every a, K, L and f,
   `a • f = (integralScalarDerivedAction l E Y a).app K ≫ f`.
   I followed this action in `IntegralScalarExtensionWellDefined`: finite constants
   are the sheafification-unit images of quotient classes; the completed constant
   is uniquely fixed by all limit projections; the chain map multiplies sections
   by that constant in every degree; the derived transformation is its preimage
   under fully faithful whiskering with Q. Thus the formula controls all derived
   morphisms, including those created by localization. I also read
   `integralConstantCoefficientCone` and `integralConstantToCompletion` in the
   recorded completion dependency: its projection formulas give those same
   quotient classes. Naturality restricts the terminal section to each U. No
   arbitrary central action replaces the node's map. Verdict: match.
6. Hom groups are O_E-modules and composition is bilinear: the ambient adapter and
   `sfIntegralConstructibleLinear` have type `CategoryTheory.Linear O_E ...`.
   I read `Linear.homModule`, `smul_comp`, `comp_smul` and `Linear.fullSubcategory`.
   Along with the categories' existing preadditivity these supply precisely both
   additive and scalar composition identities. The subcategory instance is
   exactly `Linear.fullSubcategory (sfIntegralConstructible l E Y)`; its module
   data comes from the same ambient action. Verdict: match, no hollow data.
7. Every ambient shift is linear: the second conjunct quantifies every `n : ℤ`
   and asserts `Functor.Linear O_E (shiftFunctor ... n)`. I read the generic
   derived-category linearity instances in Mathlib, including their abelian,
   linear and localization hypotheses, rather than inferring their meaning from
   their names. Verdict: match.
8. Full bounded constructible integral category: I opened the currently recorded
   `sfIntegralConstructible` definition. It requires `IsSfDerivedComplete`, every
   positive derived reduction to be intrinsically finite-torsion constructible,
   and one common finite interval containing all their cohomological supports.
   `sfIntegralConstructibleCategory` is its full subcategory. This is the current
   dependency, not the archived `boundedConstructibleDerivedCompleteIntegral`
   predicate. The inclusion-linearity conjunct fixes its action as the inherited
   one. Verdict: match and Q22 defect repaired.
9. The triangulated structure is the recorded inherited one: the public import
   `SfIntegralConstructibleTriangulated` supplies isomorphism and triangulated
   closure for this very predicate. I read both full signatures and docstrings.
   Mathlib then supplies the inherited shifts, distinguished triangles,
   triangulation and exact inclusion. Verdict: match, no freely selected structure.
10. All subcategory shifts are O_E-linear: the final conjunct again quantifies
    all `n : ℤ` for `sfIntegralConstructibleCategory`. The final instance projects
    exactly this conjunct. It does not infer a claim for the legacy predicate or
    select another linear action. Verdict: match.

Edge cases: no nonemptiness, finite type, Noetherian, connectedness, rank or
finite-Tor-dimension hypotheses are present. Empty Y and the zero object/morphism
are allowed; the zero section ring on an empty site causes no scalar-map problem.
There is no arbitrary finite index set to exclude an empty case. Tower indices n
mean exponent n+1, so n=0 is the first required positive level, not an omitted
case. All integer shifts, including zero and negative shifts, are quantified.
E=Q_ell is allowed. No condition on the characteristic of Y is added. The site
keeps object universe u+1 and morphism universe u; sheaf modules have universe
u+1. The file uses exactly the current intrinsic predicate's universe convention,
not an equality between site object and morphism universes. Every variable and
universe is explicitly bound (`autoImplicit false`).

Independent searches, with queries different from the worker's:

- LeanFinder: `intrinsic integral constructible linear category O_E shift` returned
  eight generic results, including derived, homotopy and complex shift linearity,
  and linear localization. None states the completed-section characterization and
  intrinsic-subcategory assertion together.
- Loogle: `CategoryTheory.Functor.Linear,
  CategoryTheory.ObjectProperty.FullSubcategory` returned the generic
  `Functor.fullSubcategoryInclusionLinear` and an FGModuleCat specialization.
  I opened the former's full signature and its implementation.
- Mathlib grep: `fullSubcategoryInclusionLinear|class Linear|homModule` in
  `CategoryTheory/Linear` returned six hits. I directly opened `Linear.Basic`,
  `Linear.LinearFunctor` and `DerivedCategory.Linear` and reused their notions.
- LeanSearch: `Modules over the completed integral coefficient sheaf form a
  linear derived category whose constructible subcategory has linear integer
  shifts` returned eight hits: the general sheaf/module/derived definitions,
  abelian instances, and derived-category/shift linearity. These require the input
  linear structure and do not supply this specific statement.
- Direct rg over upstream WeilConjectures, Mathlib and shared lean/Sheaf for the
  intrinsic linearity names and the concepts `integralCoefficientLinear`,
  `sfIntegralConstructible` and integral constructible shifts found only the
  published legacy ambient/subcategory interface and callers in the shared
  project. There is no existing intrinsic linearity interface to attach instead.
  I read the legacy signatures: their ambient part is reusable, but their old
  subcategory clause cannot certify the current dependency, exactly as Q22 says.

I also read the local Stacks text for 09MJ (linear categories), 03CW (module
sheaves), 03DA (their abelian category), and 05RU (unbounded derived categories).
Their assumptions introduce no extra scheme or coefficient hypothesis beyond
those encoded here. The module's theorem docstring carries all five DAG proof
steps, including rank-one completeness, constant sections, sectionwise linearity,
derived localization, and full-subcategory inheritance. Every new declaration has
its source and blueprint identifier. The sole new theorem has proof `sorry`;
the three instances reuse specified data or a named theorem's component. There
are no hollow definitions, extra proved statements, private copies, local
notations or local instances. No line exceeds 100 characters.

Mismatches and changes: none found in the delivered Lean or node record. I left
them unchanged and appended this independent reading. The sandbox node differs
from the shared node only in `lean`; its `lean.statement` is byte-for-byte the
main signature from `theorem` up to `:= by`. There is no `statement_change`, so
no correction-citer audit is applicable.

Fresh validation: `scompile.py N2 lem-weil-integral-constructible-linear
lean/Sheaf/Paper/SfIntegralConstructibleLinear.lean scratchpad/ConsumerChecks.lean`
compiled each file separately and cleanly in sandbox and library forms. The
consumer synthesizes the actual ambient and intrinsic Linear instances, the
intrinsic triangulation, all intrinsic shifts' linearity, linear inclusion and
exact triangulated inclusion, and checks both canonical and legacy declarations.
Times were 2.2--2.7 seconds per compile. There were no warnings or errors.
Transcript: `scratchpad/second-reader-compile.log`.
