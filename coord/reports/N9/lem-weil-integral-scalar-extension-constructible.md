## Worker report

The module `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic` adds the owning
node's intrinsic preservation interface:

- `WeilConjectures.sfIntegralScalarExtension_constructible`;
- `WeilConjectures.sfConstructibleIntegralScalarExtension`;
- `WeilConjectures.sfConstructibleIntegralScalarExtension_smul`.

Only the item's `lean` record changes. Its informal statement, statement dependencies,
proof plan, and all other fields are unchanged. No other DAG node is stated or edited.
The archived `IntegralScalarExtensionConstructible` module and its declarations are
preserved unchanged. Distinct new names avoid collisions when both interfaces are imported.

The source read is the last paragraph of
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-rationalization-karoubi.md`:
the rational scalar transition is defined on integral representatives by completed
integral tensor, at the finite quotient levels, followed by rationalization. The owning
node's five-step proof is included in the main theorem's docstring, with all its DAG
citations; the corresponding recorded proof-dependency modules are imported non-publicly.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The ambient integer `p` and coefficient prime `l` are explicit `(p l : ℕ)` binders;
  `[Fact l.Prime]` expresses primality of the coefficient index and `_hl : l ≠ p`
  retains exactly the node's prime inequality. No relation between `Y` and a chosen
  finite field is assumed or required. No finite-field datum is introduced.
- `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`, and the same binders for `L`, are the two finite
  extensions of Q_l, with the actual recorded coefficient valuation rings.
- `(ι : E →ₐ[Padic l] L)` specifies the Q_l-algebra inclusion. Every field algebra
  map is injective, so this covers the stated inclusion without adding a separate
  hypothesis. `integralScalarIntegerInclusion l E L ι` is its published restriction
  to the valuation rings; it is not supplied as an arbitrary map.
- `(Y : AlgebraicGeometry.Scheme.{u})` is an arbitrary scheme.
- `(K : DerivedCategory (scalarReductionSource.{u, u} l E Y))` is an object of the
  actual completed-coefficient derived category. `scalarReductionSource` and
  `integralTowerModules` reduce to the same module category over the same completed
  coefficient sheaf; the two standard derived-category instances are definitionally
  compatible, as checked by compilation. No equivalence of different mathematical
  coefficient categories is postulated.
- `(hK : sfIntegralConstructible l E Y K)` is exactly membership in the currently
  recorded integral bounded constructible category. Its definition includes
  `IsSfDerivedComplete`, every positive finite constructible reduction, and one
  common interval `[a,b]` with `a ≤ b` for the support of every reduction. None of
  those clauses is replaced by the old finite-field-indexed predicate.
- The conclusion
  `sfIntegralConstructible l L Y ((integralScalarExtension l E L ι Y).obj K)` uses
  the recorded completed scalar functor itself and asserts all the same target
  completeness, constructibility, and uniform amplitude clauses.
- The restricted functor has type
  `sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l L Y`.
  It is constructed by Mathlib's `(sfIntegralConstructible l L Y).lift` on
  `(sfIntegralConstructible l E Y).ι ⋙ integralScalarExtension l E L ι Y`, with the
  preservation theorem applied to each input's `obj` and `property`. Objects and
  morphisms therefore are precisely those of the ambient functor, with no arbitrary
  functor or map chosen.
- The last theorem states O_E-linearity for every `a` and every full-subcategory
  morphism `f`. Its left side is `T.map (μ_E(a).app K.obj ≫ f.hom)`, and its right
  side is `μ_L(ι(a)).app (T K).obj ≫ (T.map f).hom`, where `μ` is the already
  published `integralScalarDerivedAction`. This is exactly `T(af) = ι(a) T(f)`
  expressed through the canonical action on ambient morphisms. Using the action
  directly avoids assuming a currently unregistered `Linear` or `SMul` instance on
  the intrinsic full subcategory. That subcategory's Hom groups are full, and this
  canonical natural endomorphism action is inherited on those Hom groups.

Recorded dependency declarations read and reused:

- `Sheaf.Paper.SfIntegralConstructible`:
  `WeilConjectures.sfIntegralConstructible` and
  `WeilConjectures.sfIntegralConstructibleCategory`, including their complete
  signatures and docstrings. This is the active record of
  `def-weil-derived-complete-integral-detailed`.
- `Sheaf.Paper.IntegralScalarExtension`:
  `WeilConjectures.integralScalarExtension`, defined by the specified localization
  of the strict K-flat/Roos construction, with its representative comparison.
  This is the active record of `def-weil-integral-scalar-extension`.
- For the linearity clause the same import exposes
  `WeilConjectures.integralScalarIntegerInclusion` and
  `WeilConjectures.integralScalarDerivedAction` from
  `Sheaf.Paper.IntegralScalarExtensionWellDefined`. Its final theorem clause states
  exactly the ambient action equality restricted here.
- For the real restricted-functor data, reuse Mathlib's
  `CategoryTheory.ObjectProperty.lift` and the full subcategory inclusion `.ι`;
  no copy of the full subcategory construction is defined.

Edge cases checked: `Y` may be empty or non-Noetherian; no nonempty, finite-type,
Noetherian, or base-field hypothesis was introduced. Identity inclusions and `E = L`
are allowed. No positive lower bound is imposed on the cohomological interval:
zero complexes and intervals with equal endpoints are retained. The dependent
predicate uses index `n + 1` for every positive reduction, including exponent one.
No Tor bound or common choice of source and target uniformizer is assumed. Every
variable and universe is bound explicitly, and the module has `autoImplicit false`.

Searches actually run:

- `msearch.py ... leansearch "Completed integral scalar extension preserves bounded constructible derived complete sheaves"`
  returned eight generic results, including `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`,
  `Bornology.IsVonNBounded.extend_scalars`, and adic completion scalar declarations;
  none concerns the pro-etale intrinsic bounded constructible category.
- `msearch.py ... leanfinder "intrinsic bounded constructible derived complete predicate preserved by completed integral scalar extension"`
  returned eight generic results on complete integral closure and adic completion;
  no matching statement.
- `msearch.py ... loogle "sfIntegralConstructible, integralScalarExtension, FullSubcategory.lift"`
  returned zero hits, with `sfIntegralConstructible` unknown to that Mathlib index.
- `msearch.py ... grep "[Cc]onstructible.*[Ss]calar|[Ss]calar.*[Cc]onstructible" CategoryTheory`
  returned zero hits. The earlier grep of
  `"integralScalarExtension.*constructible|sfIntegralConstructible.*Scalar"` in `Sheaf`
  likewise returned zero hits.
- `rg` searched the three proposed names and the old
  `integralScalarExtension_constructible` in Mathlib, upstream `WeilConjectures/`,
  the project `lean/Sheaf`, and `dag/lean_names_upstream.json`. Only the legacy
  project-side theorem and its callers matched; its signature uses
  `boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y`, which is not
  the active recorded dependency. No declaration with a proposed new name exists.
- `grep -rn "lem-weil-integral-scalar-extension-constructible"` in upstream
  `WeilConjectures/` returned no attachment.

No `STATEMENT-DISPUTED` issue or informal statement correction is needed. The maintenance
invalidation identifies an interface migration, handled by the additive intrinsic
interface requested there, while preserving the legacy module. All theorem proofs
are `sorry`; the definition has real full-subcategory lift data.

Validation: `scompile.py N9 lem-weil-integral-scalar-extension-constructible` compiled
the delivered file as both sandbox and library module, with all final proof imports,
within the 60-second per-file limit and without errors or unexpected warnings.

## Earlier second reading (a previous round; superseded)

This section is reserved for the dispatcher-appointed second reader, who reads after
this worker and performs delivery. The worker has checked each signature against the
unchanged node and both active dependency records as detailed above; that self-check
is not an independent second reading. The second reader should verify especially the
canonical-action rendering of linearity and preservation of the legacy declaration
names. No independent review is claimed by this worker.

## Second reading by N9

I independently read the sandbox node and module, both active statement-dependency
records and their Lean sources, and the source paragraph in
`sec-smooth-purity/sk-def-sf-operations/def-weil-rationalization-karoubi.md`.
That paragraph defines rational scalar transition by completed integral tensor at
finite quotient levels before rationalization. The ambient finite-field convention
supplies the coefficient inequality; it imposes no map from the arbitrary scheme Y
to a finite field. I also read the integral-category definition at order 1459 and
Stacks `sites-cohomology.tex`, Tags 0G7E and 06YY (K-flat base change and its derived
functor). Those statements concern arbitrary ringed topoi and impose no geometric
Noetherian or finite-type hypothesis here. The item's source is the blueprint
paragraph, rather than a standalone Stacks preservation lemma.

Here is my object/hypothesis/conclusion list and its Lean correspondence. Every
verdict below is PASS.

1. A coefficient prime ell different from p: `(p l : ℕ) [Fact l.Prime]
   (_hl : l ≠ p)`. The node gives no further mathematical use for p or a base-field
   structure on Y. Retaining this explicit inequality introduces no such structure.
2. Two finite extensions of Q_l: `(E : Type u) [Field E]
   [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`, and the identical
   list for L. The inclusion is the specified `(ι : E →ₐ[Padic l] L)`;
   a unital map between these fields is injective. It respects the given Q_l maps,
   unlike an arbitrary ring map.
3. Their valuation rings and the induced inclusion: the reused
   `Padic.coefficientExtensionIntegers l E` and its L version, and
   `integralScalarIntegerInclusion l E L ι`. I opened the latter definition:
   it restricts `ι.toRingHom` using the absolute-value membership theorem. It is
   the actual integer inclusion, with no independently chosen scalar map.
4. An arbitrary scheme: `(Y : AlgebraicGeometry.Scheme.{u})`. There is no
   nonemptiness, Noetherian, finite-type, separatedness, or field-of-definition
   assumption.
5. An arbitrary input in the stated integral category: the binders
   `(K : DerivedCategory (scalarReductionSource.{u, u} l E Y))`
   and `(hK : sfIntegralConstructible l E Y K)`. I opened
   `SfIntegralConstructible`, `SfDerivedComplete`, `SfIntegralReductionTower`,
   `DerivedScalarExtensionRestrictionAdjunction`, and
   `IntegralReductionTowerUnrestricted`. The predicate requires the canonical
   derived-completeness Roos triangle, constructible cohomology at every positive
   derived reduction, and one interval `[a,b]`, with `a ≤ b`, bounding every
   reduction. `scalarReductionSource` and `integralTowerModules` use the same
   completed coefficient ring and module size; the standard derived-category
   structures are compatible, not related by an assumed arbitrary equivalence.
6. Preservation by the specified completed scalar extension: the conclusion is
   `sfIntegralConstructible l L Y
   ((integralScalarExtension l E L ι Y).obj K)`. I opened
   `IntegralScalarExtension` and `IntegralScalarExtensionWellDefined`:
   `integralScalarExtension` is the localization of the specified K-flat/Roos
   construction with its representative comparison and universal uniqueness.
   Thus the conclusion concerns exactly the functor in the dependency node.
   Target completeness, all positive constructible reductions, and uniform
   amplitude are all asserted, with no replacement by mere boundedness.
7. The resulting restricted functor: `sfConstructibleIntegralScalarExtension`
   has type `sfIntegralConstructibleCategory l E Y ⥤
   sfIntegralConstructibleCategory l L Y`. Its real data are
   `(sfIntegralConstructible l L Y).lift` of the source inclusion composed
   with `integralScalarExtension`. I opened Mathlib's
   `CategoryTheory.ObjectProperty.lift`: objects are `⟨F.obj X, hF X⟩` and
   maps are `homMk (F.map f)`. This is precisely restriction of the ambient
   functor; the preservation theorem supplies only the proposition needed for
   subtype membership.
8. O_E-linearity of that functor: `sfConstructibleIntegralScalarExtension_smul`
   quantifies over both full-subcategory objects, every morphism `f`, and every
   `a : Padic.coefficientExtensionIntegers l E`. It equates the ambient image
   of `(integralScalarDerivedAction l E Y a).app K.obj ≫ f.hom` with the
   target action of `integralScalarIntegerInclusion l E L ι a` composed with
   the restricted image of f. I read the action's construction: it is descended
   multiplication by the unique constant sections specified at every finite
   quotient. This equality is exactly linearity on the inherited Hom groups;
   it needs no extra hypothesized `Linear` instance. Together with the inherited
   additivity of the ambient functor, it supplies the full linearity clause.

Edge cases: the empty scheme and zero complexes are included; no nonzero-object
hypothesis occurs. Both the identity inclusion and E = L are allowed. The prime
ell can be any prime subject to ell != p, with no extra characteristic restriction
on Y. The n = 0 index in the dependency represents exponent one, and n+1 ranges
over every required positive exponent; exponent zero is not a condition of this
node. The common interval allows equal endpoints and arbitrary integer bounds.
There is no finite stratification or index type supplied as an extra hypothesis.
The theorem is polymorphic in u and uses the active category's size convention:
the small pro-etale site retains object universe u+1 and morphism universe u,
and coefficient modules live in u+1. No equality of those two site universes is
assumed. No new universe constraint is imposed beyond the recorded predicate's
existing common-size scheme/coefficient interface.

Independent searches, using words different from the author's queries:

- LeanFinder: `completed coefficient change preserves finite constructible
  cohomology with uniform amplitude` returned eight unrelated results, including
  `WeakFEPair.toStrongFEPair` and `ChevalleyThm.chevalley_polynomialC`;
  no match.
- LeanSearch: `Extension between valuation rings of finite p-adic fields
  preserves constructible derived complete sheaves` returned valuation extension
  and valued-field declarations; no preservation statement.
- Loogle: `ObjectProperty.lift` had no indexed identifier. Direct source inspection
  of Mathlib's `CategoryTheory/ObjectProperty/FullSubcategory.lean` nevertheless
  verified and reused the existing lift, rather than defining a new construction.
- The prescribed Mathlib grep for `adic.*constructible|constructible.*adic`
  returned zero hits. I separately used rg in Mathlib, upstream
  `WeilConjectures`, and project `lean/Sheaf` for scalar/constructible combinations,
  and for change-of-rings and preservation wording. The older
  `IntegralScalarExtensionConstructible` theorem uses the distinct legacy
  `boundedConstructibleDerivedCompleteIntegral` predicate. It is not a match
  for the active `sfIntegralConstructible` dependency. I opened that signature
  and its restricted functor. The pro-etale module-object search also found
  `boundedConstructible_derivedExtendScalarsSubfield_obj` in
  `ModuleObject/Colimit/TwoColimit`; opening it showed rational field ring objects,
  rather than completed integral sheaves and derived completeness. It is not a
  match. None of the three new names already occurs upstream or in Mathlib.

I read `coord/reports/maintenance/Q22-intrinsic-coefficient-interfaces.md` and
checked its precise repair request: preservation of the active intrinsic
predicate, the restricted intrinsic functor, and linearity are all present.
Legacy declarations are preserved. There is no item-specific file in
`coord/repair-notes` in the available repository. No new definition nodes or
dependency modules are delivered, so H12/H13 introduce no additional review items.
The item differs from the base only in `lean`; it has no statement correction.

No mismatch requiring a Lean or DAG repair was found. I left the working code and
node record unchanged and added this independent reading. The primary
`lean.statement` is verbatim equal to its file signature. All variables and the
universe are explicitly bound (`autoImplicit false`); there are no private notions,
local notations, hollow data, or proved theorems. Both theorem proofs are `sorry`.
Every declaration has the source/blueprint docstring. The main docstring carries
all five proof steps, and all recorded proof-dependency modules are imported.
Every Lean line has at most 100 characters.

Validation: my independent `scompile.py N9
lem-weil-integral-scalar-extension-constructible` invocation compiled the single
delivered file in sandbox and library contexts in 3.2 and 3.4 seconds respectively,
with no errors or warnings. The wrappers perform the final current-base compile
and preflight during dry run and delivery.
