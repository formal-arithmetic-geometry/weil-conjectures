## Worker report

States `AlgebraicGeometry.Scheme.isIso_classicalProEtaleExchange_of_isProper` in
`Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange`. Its only theorem proof is
`sorry`. Two real helper definitions form the constant-coefficient square comparison and
its normalized adjunction mate; they choose no arbitrary map or coefficient identification.
No source statement was corrected and no definition node was created.

Source read: main-20261015 `sec-proper-base-change/sk-thm-properbasechange/_section.md`
and its four-paragraph proof, together with the current node's nine proof steps. The
upstream `Etale.isIso_baseChange_of_isProper` was read in full: it concerns the etale
site, so it does not state this pro-etale theorem. The current module-object proper
base change theorem was also read: it concerns constructible condensed E/Qbar
coefficients, and does not state this arbitrary discrete-ring torsion theorem.

Hypothesis and clause correspondence:

- A commutative discrete ring Lambda: `(Λ : Type u) [CommRing Λ]`. There is no
  topological structure in this ordinary constant-sheaf construction. The coefficient
  sheaf is exactly `proEtaleConstantRing T Λ`, the sheafification of the constant
  presheaf with value `ULift.{u+1,u} Λ`. This is the existing size convention; the
  site retains object universe u+1 and morphism universe u, and modules live in u+1.
- Schemes and proper f: `{X' X Y' Y : Scheme.{u}}`, four explicitly bound arrows,
  and `[IsProper f]`. Properness is Mathlib's separated, universally closed,
  locally finite type predicate, as recorded in sk-def-conv.
- Arbitrary g: `{g : Y' ⟶ Y}` has no instance or other restriction. No qcqs
  hypothesis is imposed on a corner scheme, on g, or on g'.
- The pullback and projections: `sq : ChosenCartesianSquare g' f' f g` supplies
  an isomorphism `X' ≅ pullback f g` and both projection equations. Quantifying
  over such a chosen realization includes the literal chosen fibre product and
  is exactly the coordinate-independent rendering of the stated square.
- K in the bounded-below category: `K : proEtaleDerivedCategory X Λ` and
  `hbounded : ∃ n : ℤ, DerivedCategory.IsGE K n`. This is the strictly full
  subcategory `DerivedCategory.Plus` expressed by its object property, with
  all integer lower bounds retained.
- K classical: `hclassical : ProEtale.IsClassicalModuleComplex K` uses the
  dependency's recorded predicate, on every integer cohomology sheaf, and its
  existing affine-presentation continuity maps on the underlying set sheaf.
- Torsion underlying abelian cohomology: for every `q : ℤ`, `htorsion` applies
  `CategoryTheory.Sheaf.IsTorsion` to `SheafOfModules.toSheaf` of the q-th
  derived homology. The existing predicate means locally finite additive order
  on a covering sieve. It permits different orders on different cover members;
  it does not assert that every group of sections is torsion or choose a bound.
- The canonical exchange: `classicalProEtaleExchange Λ sq` is `mateEquiv`
  applied to `classicalProEtalePullbackSquare Λ sq`. The square comparison is
  `proEtaleConstantRingPullbackComposition f' g Λ`, then transport along
  `sq.toCommSq.w.symm`, then the inverse comparison for `g',f`. Thus it has
  direction f'^* g^* -> g'^* f^*. The edge adjunctions are precisely the published
  `proEtaleRingDerivedAdjunction` with `proEtaleConstantRingComparison`.
  The mate inserts the f'-unit and then the square and f-counit. Its endpoints
  are the existing ordinary uncompleted, unbounded derived operations, with
  exact inverse image and K-injective direct image, restricted here by bounds.
- Isomorphism *in* the bounded-below classical category: the conclusion gives
  a lower bound and `IsClassicalModuleComplex` for each actual endpoint,
  followed by `IsIso ((classicalProEtaleExchange Λ sq).app K)`. Since the
  subcategory is full, this is precisely invertibility there, including endpoint
  membership. Omitting endpoint membership would lose a clause of the node.
- No constructibility, finite-ring, invertible-order, finite-Tor-amplitude,
  completeness, uniform-torsion-order or nonemptiness assumption was added.

Dependency declarations used (their sources/signatures/docstrings were inspected):

- sk-def-exchange: the existing `Etale.derivedBaseChangeMapPlus` in
  `WeilConjectures.SixFunctors.BaseChange.Derived`, reexported by
  `WeilConjectures.SixFunctors.BaseChange.DerivedComparison`; the latter's
  `Etale.baseChange_eq_derivedBaseChangeMapPlus` identifies the adjunction mate
  with the resolution formula. The new helper uses the same formula for the
  existing pro-etale ringed operations, rather than an etale arrow on wrong objects.
- sk-def-conv: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `IsProper`.
- sk-def-pbc: `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty`,
  `Etale.HasTorsionBaseChange`; its imported `Scheme.IsTorsionSheaf`,
  `Etale.DerivedCategory.Plus.torsionHomology` and `Sheaf.IsTorsion` fix the
  local additive torsion convention. On the pro-etale site the last predicate
  applies directly to the underlying abelian sheaf.
- sk-def-pe-classical-definition: `Sheaf.SixFunctors.ClassicalDefinition`,
  `ProEtale.IsClassicalModuleComplex` and `IsClassicalModuleSheaf`.
- def-weil-pbc-constant-sheaf: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`, through `proEtaleConstantRing`.
- def-weil-sheaf-of-modules-category: `Sheaf.CategoryTheory.RingedSiteModules`,
  `ringedSiteModules`, transparently Mathlib's `SheafOfModules`; the operations'
  `proEtaleRingModules` is this exact intrinsic category after forgetting commutativity.
- def-weil-abstract-derived-category: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, with the existing `HasDerivedCategory.standard` instance.
- def-weil-pbc-bounded-derived-subcategories: Mathlib's DerivedCategory/TStructure,
  `DerivedCategory.Plus`, `IsGE`; no separate bounded category is constructed.
- def-weil-pbc-proetale-site: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `Scheme.ProEt` and `ProEt.topology`; the existing `proEtaleDerivedCategory`
  is used, not a second module or derived category.
- def-weil-pbc-proetale-operations: `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
  `proEtaleConstantRingDerivedPullback` and `proEtaleConstantRingComparison`;
  `ProEtaleOperations` supplies `proEtaleRingDerivedDirectImage` and the
  normalized `proEtaleRingDerivedAdjunction`.
- def-weil-pbc-ambient-ringed-exchange: the recorded PbcActualRingedExchange
  publicly imports `Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange`.
  Its generic `proEtaleAmbientRingedExchange` and pullback comparison were read
  in full. We import that smaller authoritative module; the recorded primary
  completed-adic specialization is not used for arbitrary discrete rings.
- Added landed statement dependency pur713-def-pullback-comparison: the existing
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`, especially
  `proEtaleConstantRingPullbackComposition`, is the arbitrary-ring composition
  comparison used by the helper. Its l-adic final square specialization is not
  applied. The general helper retains the constant-section and K-flat normalization.

Edge cases checked before finalizing the signature: empty schemes and the zero ring
are allowed; zero K is allowed with any lower bound; identity f and/or g use exactly
the ordinary square comparison and unit/counit mate; negative cohomological degrees
are included; Lambda=Z and locally Q/Z torsion permit arbitrarily large orders;
characteristic-p torsion is included without invertibility; a non-quasi-compact
object with a section having unbounded orders still meets the local torsion
condition; nonconstructible classical complexes are not excluded. Choosing the
ambient universe u is the published common-size convention for the ring and
schemes, with the module universe increased to u+1, not an equality between the
site's distinct object and morphism universes.

Searches actually run with msearch.py (N3, this item):

- LeanFinder: `Proper base change on classical pro-etale bounded below complexes
  with torsion cohomology` returned eight algebraic etale/base-change stability
  declarations, no derived classical pro-etale exchange theorem.
- Loogle: `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` returned unknown
  identifier (the service searches Mathlib; the upstream source declaration was
  separately read and found to concern the etale site).
- Mathlib grep: `proper.?base.?change|isIso_baseChange_of_isProper`, subdirectory
  AlgebraicGeometry, returned zero hits.
- LeanSearch: `Proper base change for classical pro etale sheaves with torsion
  cohomology` returned eight hits, headed by IsProper.isStableUnderBaseChange
  and etale algebra/Kaehler differential base-change declarations; no match.
- Local rg over WeilConjectures for proper/base-change, the exact node id and
  classical/base-change found the etale proper theorem and comparison/smooth
  exchange lemmas, not this theorem. The provided module-object framework proper
  theorem concerns constructible condensed E/Qbar coefficients. Local rg over
  lean/Sheaf found the finite-level specializations and generic ringed mate,
  which are reused. The new three full names had no existing match. The upstream
  names index had no additional exact match for the current pro-etale statement.

Validation: scompile.py compiled the statement both as a sandbox source and under
its actual library module name, with no errors or warnings. All variables and
universes are explicitly bound (`set_option autoImplicit false`). All lines are
at most 100 characters. The docstring carries all nine proof steps.

Proof-import fault reported for maintenance: importing the recorded
`Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence` alongside the current
coefficient operations fails with duplicate
`AlgebraicGeometry.ProEtale.derivedComparisonAdjunctionPlus`: that module and
ClassicalDerivedDefinitions import retired `ProEtale.Derived.Comparison`, while
current operations import `ProEtale.FiniteCoefficient.Derived.Comparison`.
The published source was confirmed with `scompile.py --source`. I removed only
that proof-only import; all usable stated proof dependencies remain imported.
The statement itself uses ClassicalDefinition, whose import closure is compatible.
No unrelated source module was changed. The maintainer must repair that proof-only
import closure before adding its import during stage 3.

## Dependency modules

`sk-def-exchange` and `sk-def-pbc` had no lean record in the base. Their copied
node files gain only existing-declaration records with `lean.note`, as permitted
by the human's bottom-up/missing-dependency update. No new module duplicates
these source notions. The first points to the existing bounded-below exchange
and its mate-identification theorem; the second points to the existing all
bounded-below torsion-cohomology PBC predicate and the local/stalkwise torsion
interfaces. See the signatures, source lines, and clause explanation above.
The ambient-ringed-exchange record itself was not changed: its public generic
ringed mate remains usable through the smaller public import.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (cc reviewer, 2026-10-18)

H4: the delivered helpers `classicalProEtalePullbackSquare` and `classicalProEtaleExchange`
re-built the mate of def-weil-pbc-ambient-ringed-exchange from a second selected comparison
(`proEtaleCanonicalPullbackComposition` instead of the recorded
`proEtaleCanonicalDerivedPullbackComparison`), a private copy of the recorded
`proEtaleAmbientRingedExchange`. The square helper is removed and
`classicalProEtaleExchange` is now an abbreviation of `proEtaleAmbientRingedExchange` on the
four constant ring sheaves and `proEtaleConstantRingComparison`, its coefficient coherence
given by `proEtaleConstantRingCompositeCoefficients_eq` (pur713-def-pullback-comparison) and the
square equation, exactly as the landed `ProEtale.directImageConstantExchange`. The theorem's
signature text is unchanged; the file compiles clean with nt_compile.py.
