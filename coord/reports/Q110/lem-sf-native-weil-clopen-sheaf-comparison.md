## Worker report

Recorded existing upstream declarations; no new Lean module, definition, theorem, or sorry.
Only the item's `lean` field changes. The entry module is
`WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion` and the primary declaration is
`AlgebraicGeometry.ProEtaleWeilSheaf.isIso_extensionByZeroToLowerStar` (lines 54–66).
The other six names in `lean.declarations` supply the remaining clauses. They are publicly
imported by the entry module. The primary `lean.statement` is copied verbatim from its
source signature, beginning at `instance` and ending before `:=`.

Hypothesis and clause correspondence:

- Finite field: `{k₀ : Type u} [Field k₀] [Finite k₀]`; prime coefficient parameter:
  `{l : ℕ} [Fact l.Prime]`. The node's unequal-characteristic assumption is
  `[Fact (ringChar k₀ ≠ l)]`. The existing all-sheaf operations and isomorphism instance
  work without that assumption, so apply in particular under it.
- Algebraic closure and coefficients: the framework dependency uses `AlgebraicClosure k₀`
  through `(X ↘ Spec (CommRingCat.of k₀)).geometricFiber` and `PadicAlgCl l` through
  `ProEtale.AdicSheaf`. `PadicAlgCl.locallyFiniteFunctions` in
  `SixFunctors/ProEtale/Adic/ConstantSheaf.lean`, lines 74–80, is exactly the subalgebra of
  continuous functions whose values locally span a finite-dimensional `ℚ_[l]`-space.
  `ProEtale.adicConstantSheaf`, lines 317–333, gives this sheaf on the small pro-etale
  site, with the recorded universe lift of sections. These are the dependency's fixed
  algebraic-closure and coefficient realizations, rather than new parameters or notions.
- Schemes over the field: `{U X : Scheme.{u}}` and the two
  `[U.Over (Spec (CommRingCat.of k₀))]`, `[X.Over ...]` instances. Locally finite type in
  the node is `LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))` and the analogous
  condition for `X`. The existing assertions hold for all such schemes without needing
  these restrictions; no global finite type, quasi-compactness or separatedness is added.
- All sheaves: `ProEtaleWeilSheaf k₀ l U`, defined in `WeilSheaf/Category.lean`, is
  `IsoAlgebra (WeilSheaf.frobeniusPullback k₀ l U)`, with carrier in `ProEtale.AdicSheaf`.
  It is the category of modules over the function sheaf with invertible Frobenius structure.
  It does not use the constructible full subcategory `WeilSheaf` or `WeilComplex`.
- Open immersion of field-schemes: `(j : U ⟶ X) [IsOpenImmersion j]` and
  `[j.IsOver (Spec (CommRingCat.of k₀))]`. The Mathlib open-immersion definition is the
  dependency's `AlgebraicGeometry.IsOpenImmersion`, read with its docstring in
  `Mathlib/AlgebraicGeometry/OpenImmersion.lean`, lines 35–39.
- Native extension: `ProEtaleWeilSheaf.extensionByZero k₀ l j` in
  `WeilSheaf/OpenImmersion.lean`, lines 45–55, is `IsoAlgebra.mapOfNatIso` of the actual
  geometric-fibre adic extension functor with its Frobenius commutation isomorphism.
  The carrier is `ProEtale.adicOpenImmersionLowerShriek l (Scheme.Hom.geometricFiberMap j ...)`.
- Additivity: `AlgebraicGeometry.WeilSheaf.instAdditiveProEtaleWeilSheafExtensionByZero`.
  Exactness: the two corresponding `instPreservesFiniteLimits...` and
  `instPreservesFiniteColimits...` declarations. They are the three instances at
  `WeilSheaf/OpenImmersion.lean`, lines 140–150. Each explicitly omits the section's
  `[QuasiCompact j]`. Finite-limit and finite-colimit preservation is exactness between
  these abelian categories. The server successfully synthesized all three with no
  quasi-compactness or constructibility hypothesis.
- Native ordinary direct image: `ProEtaleWeilSheaf.lowerStar k₀ l j`, from
  `WeilSheaf/LowerStar.lean`, lines 74–85. This is `IsoAlgebra.mapOfNatIso` of the adic
  direct image, with the specified Frobenius comparison.
- Canonical natural transformation: `ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l j`,
  `WeilSheaf/OpenImmersion.lean`, lines 57–69. Its type is the natural-transformation
  type from the native extension to the native ordinary direct image. Its body is
  `IsoAlgebra.mapOfNatIsoHom` applied to
  `ProEtale.adicOpenImmersionLowerShriekToLowerStar l (Scheme.Hom.geometricFiberMap j ...)`.
  Thus its underlying component after forgetting Frobenius is definitionally that very
  canonical adic comparison at the carrier. The definition of `mapOfNatIsoHom` in
  `Mathlib/CategoryTheory/Endofunctor/Algebra.lean` under the `WeilConjectures` root,
  lines 300–327, stores the input component as the underlying map and its supplied
  Frobenius compatibility as the commuting-morphism proof. The input adic comparison
  is the canonical adjoint-triple comparison in `Adic/OpenImmersion.lean`, lines 230–251,
  normalized by the inverse restriction counit. This is a specified map, not an
  existential or arbitrary natural transformation.
- Universally closed case: `[UniversallyClosed i]` in the primary instance, giving
  `IsIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l i)`. This is invertibility in
  the functor category, hence a natural isomorphism of precisely the preceding comparison.
  `UniversallyClosed` is the dependency's universally closed property, read in
  `Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean`, lines 39–44; it is not
  replaced by a stronger properness hypothesis. The source first proves the geometric
  fibre map has closed range (lines 40–51), then reflects invertibility through the
  fixed-pair forgetful functor (lines 54–66).

Dependency declarations used:

- `def-sf-native-weil-derived-framework`: entry module
  `WeilConjectures.WeilSheaf.LowerShriek`, primary declaration
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek` (signature and docstring read), with
  recorded `ProEtaleWeilSheaf`, `ProEtale.AdicSheaf`, `WeilSheaf.frobeniusPullback`,
  `ProEtaleWeilSheaf.extensionByZero`, and `ProEtaleWeilSheaf.lowerStar` used here.
  The derived compact-support operation is not needed for this sheaf-level assertion.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, recorded
  `AlgebraicGeometry.UniversallyClosed` (and `IsProper`/`IsSeparated` read to distinguish
  the universally closed clause from full properness).

Edge cases checked against the actual interfaces: the zero sheaf is allowed because the
category has no nonzero or constructible restriction; the empty open and identity open
satisfy the same universally closed open-immersion hypotheses; a clopen union need not be
connected or quasi-compact over the field; arbitrary nonconstructible module sheaves are
included. General opens require no quasi-compactness, including before the universally
closed hypothesis is supplied. The upstream statement is uniform in `u`, with the same
small-site and coefficient universes as the recorded framework; no universe equality or
smallness condition was introduced. No correction or STATEMENT-DISPUTED flag is needed.

Searches made (2026-10-24):

- `msearch.py ... leanfinder` with query "extension by zero on all pro etale Weil sheaves
  is additive exact and canonical comparison to direct image is invertible for a universally
  closed open immersion": eight hits, primarily ordinary scheme-module restriction and
  unrelated condensed results; none gives the native Weil assertion.
- `msearch.py ... loogle '"extensionByZero"'`: zero hits.
- `msearch.py ... grep 'extensionByZero|[Cc]lopen.*[Ss]heaf|[Ss]heaf.*[Cc]lopen'`:
  zero Mathlib hits.
- `rg -n 'extensionByZeroToLowerStar|ProEtaleWeilSheaf.extensionByZero|instAdditive.*ExtensionByZero'`
  in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: found the
  exact native definitions, exactness instances, and clopen instance named above.
  Sheaf consumers use the same upstream operations. The native basic-comparisons node
  has additional derived assertions, so it is not substituted for this node.
- `grep -rn 'lem-sf-native-weil-clopen-sheaf-comparison' lean/WeilConjectures`:
  no blueprint-id annotation; the exact declaration is found by the conceptual/name search.

Validation: the scratch module-mode probe `scratchpad/Check.lean` was compiled by the
prescribed `scompile.py` on the server against the live library, cleanly. It synthesized
additivity, finite-limit preservation, finite-colimit preservation and, with only the added
universally closed hypothesis, invertibility of the native natural transformation. It also
printed the comparison's body, confirming the canonical underlying map. No scratch module
is delivered. The delivery wrapper additionally checks all seven recorded names.

## Second reading by Q110

A second source-and-signature pass by the assigned worker checked every clause above.
No other agent was launched, as required by the dispatch brief; the maintainer supplies
independent review. This pass distinguished the unrestricted `ProEtaleWeilSheaf` operations
from the constructible `WeilSheaf` operations immediately below them, and checked that all
three exactness/additivity instances omit `[QuasiCompact j]`. It also checked that the
clopen conclusion uses `UniversallyClosed`, that `IsIso` concerns the natural transformation
itself, and that its carrier is the canonical geometric comparison rather than a chosen
map. The only adjustment was to list all three compiler-resolved instance names in the
existing-declaration attachment, so the exactness and additivity clauses are individually
reviewable alongside the primary invertibility clause. No mathematical statement changed.
