## Worker report

The module states `WeilConjectures.zlFiniteCompletedImageComparison` with its whole
proof postponed by `sorry`. Its record `ZlFiniteCompletedImageComparison` packages
exactly the clauses, and the two helper definitions have real data. No new DAG node,
dependency repair, or statement correction is needed. There is no STATEMENT-DISPUTED
finding. The source was read in Stacks proetale.tex `lemma-finite` (09A8), in the
current `literature/blueprint/latest` finite-pushforward statement and proof, and in
Bhatt–Scholze Proposition 3.5.1, Lemmas 3.5.6 and 6.7.2.

Hypotheses and clauses:

- `D : FiniteFieldDatum` binds the specified prime, positive exponent, finite field
  and fixed algebraic closure. `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` gives the
  coefficient prime and coprimality. `E`, `Field`, `Algebra ℚ_[l] E`, and
  `FiniteDimensional ℚ_[l] E` give the finite coefficient extension; all integers,
  uniformizers and quotient rings are the dependency's `Padic` constructions.
- `X Y : Over (Spec (.of D.k))` gives the two k-schemes. Their
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` structure-map instances
  are exactly separated finite type. `f : X ⟶ Y` is a k-morphism and
  `[IsFinite f.left]` is finiteness. No finite-presentation or exactness assumption
  is added to the theorem.
- `scalarReductionSource l E W` is all modules over the inverse-limit completed
  coefficient sheaf on the actual small pro-etale site. The site keeps object
  universe u+1 and morphism universe u; modules and finite coefficients have size
  u+1. Nothing equates the site's object and morphism universes.
- `exactLimits` and `exactColimits` assert exactness on the whole completed-module
  category. `products` uses `IsIso (piComparison ... M)` for every countable family,
  thus specifies the canonical product comparison, not mere existence of an iso.
- `derived`, `factors`, `commShift`, and `triangulated` give the induced termwise
  triangulated functor on ordinary derived categories. `comparison` and
  `resolutionNormalization` identify it with the existing completed right-derived
  image by the canonical resolution unit on every complex.
- `noetherian_source`, `noetherian_target`, `dimension_source`, `dimension_target`,
  and `finitePresentation` assert the geometric conclusions. Dimension is bounded
  above by a natural number in `WithBot ℕ∞`, retaining the empty scheme. Finite
  presentation is locally finite presentation, quasi-compact and quasi-separated.
- `finiteExact` gives exactness of every finite-coefficient pushforward on all
  modules. `finiteResolution` asserts invertibility of its actual right-derived
  resolution unit on every complex, expressing that it is its own derived functor.
- `scalarComparison` records the identity-on-sections normalization of the existing
  underived scalar square. The tower uses `sfDirectImageTransition`, whose formula
  conjugates the actual quotient transitions by the existing normalized derived
  restriction square, retaining quotient compatibility rather than independent
  finite-level objects.
- `zlFiniteCompletedImageProjection` is the actual `Pi.lift` of completed derived
  image of `sfDerivedReductionUnit`, followed by `sfDerivedRestrictionComparison`.
  Both maps come from the recorded dependencies. `roos` says that this precise map
  is the first arrow of an `IsDerivedLimitTriangle` for `sfDirectImageTransition`.
  Consequently the existing completed derived image is a model of the node's
  tower-defined image. Its boundary is asserted, never a new unmarked object.
- `ZlFiniteCompletedImageComparison.theta` is `isoWhiskerLeft` of the normalized
  resolution comparison, a natural iso on the integral constructible category.
  `normalization` is its equation with every actual Roos projection and reduction
  unit. The comparison after `derived.map q_n` is just the recorded termwise
  identification of the two target coefficient presentations.
- `constructible` and `complete` assert both properties of the tower image.
  `reduction` uses `sfDirectImageReductionComparison` on this very Roos record,
  so invertibility concerns the scalar-adjoint projection map specified by the node.
- `etaleOrigin` quantifies an actual bounded constructible etale complex `L` at
  every n+1 and an isomorphism from the reduction, after the canonical exact
  constant-scalar encoding, to `ProEtale.comparisonUpperStar.mapDerivedCategory L`.
  Its predicate is exactly the dependency's
  `Etale.DerivedCategory.isBoundedConstructible`. The finite instance is supplied
  explicitly by `Padic.finite_coefficientExtensionRing` and `Finite.of_equiv` for
  `ULift`; no extra finiteness hypothesis or local instance is introduced.
- `restricts` asserts preservation of the integral constructible category.
  `standard` preserves `sfIntegralStandardClass ... nonpositive 0` for both Bool
  values, so both standard halves are retained.
- The theorem's second conjunct quantifies every k-point as an Over morphism from
  `Spec k` with identity structure map. It asserts finiteness and the entire same
  comparison record for `pullback.snd f.left s.left`, the base-changed finite map h.

Dependency declarations used (all recorded signatures and docstrings were read):

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber` / `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` / `Padic.finite_coefficientExtensionRing`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite` / `AlgebraicGeometry.IsFinite`.
- `def-weil-scheme-morphism-properties`: `None` / `None`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` / `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale` / `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible` / `WeilConjectures.sfIntegralConstructible`.
- `def-pur-integral-derived-operations`: `Sheaf.Paper.IntegralDerivedOperationsOnSlices` / `WeilConjectures.IntegralOnSlice.completedTensor`.
- `def-weil-derived-direct-image`: `Sheaf.Paper.SfDerivedDirectImage` / `WeilConjectures.SfIntegralDirectImage`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules` / `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic` / `DerivedCategory`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` / `AlgebraicGeometry.Scheme.Modules.moduleBaseChange`.
- `def-weil-pbc-site-comparison-morphism`: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` / `AlgebraicGeometry.Scheme.proEtaleSiteComparison`.
- `def-weil-pbc-constructible-complexes`: `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes` / `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `def-weil-constructible-standard-tstructure`: `Sheaf.Paper.SfConstructibleHeart` / `WeilConjectures.sfIntegralStandardClass`.

The scheme-properties collection explicitly fixes no separate notion; its finite-type,
separatedness and finite-presentation constituents are the Mathlib declarations used
above. Abstract derived categories use Mathlib `DerivedCategory`; ringedSiteModules
is the transparent general-site abbreviation for Mathlib `SheafOfModules`.
The origin clause uses the existing `Scheme.proEtaleModuleRestriction` exact encoding
and `ProEtale.comparisonUpperStar`, both canonical functors, rather than constructing
a second comparison. Proof dependencies with records are imported; general Mathlib
leaves use their existing imports. The seven-step natural-language proof is in the
theorem docstring, including the K-injective transition check from step 5.

Edge cases checked: f=id (including n+1=1), empty source, an empty geometric fibre,
two disjoint points, the nonreduced finite scheme Spec(k[ε]/ε²), zero complexes,
shifted complexes, and torsion integral objects. There is no reducedness, surjectivity,
flatness, torsion-free hypothesis, or cohomological positivity restriction. Empty
schemes have dimension bottom, bounded by zero. The two standard halves are both
quantified, including zero. All positive exponents are covered by n+1. Universes
may be enlarged jointly for the finite-field and scheme data; the underlying site
is never replaced by a large etale site or a skeleton with a different morphism size.

Searches for existing statements and notions:

- msearch LeanFinder: “Exact finite proetale pushforward commutes with derived
  completed reduction inverse limit”: 8 hits (BDeRhamPlus/BDeRham, solid modules,
  AdicCompletion.map_exact and generic etale algebra). No match.
- msearch Loogle: `"mapDerivedCategory", "PreservesLimitsOfShape"`: 0 hits.
- msearch grep: `finite.*completed|completed.*image|finite.*proEtale` in
  Mathlib/AlgebraicGeometry: 0 hits.
- msearch LeanSearch: “Finite morphism exact proetale module direct image and
  normalized derived completion reduction tower comparison”: 8 hits, finite
  morphism constructors/recursors, finite implies proper, AdicCompletion and
  AdicCompletion.map_exact. No normalized geometric comparison.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: searched finite/completed image
  patterns, `sfCompletedModuleDirectImage`, and the exact blueprint id. The
  existing ZlFiniteAdicDirectImage theorem packages rational hearts, counits and
  stalk formulas, not this completed-module assertion. The completed-coefficient
  pushforward comparison is a general right-derived reconstruction result and
  does not state finite exactness or the constructible standard-pair conclusions.
- rg in Mathlib, both project roots, and `dag/lean_names_upstream.json` for
  `zlFiniteCompletedImageComparison|ZlFiniteCompletedImageComparison`: no collision.

Validation: scompile.py in module mode, sandbox and library module names. Initial
probes located the exact interfaces; corrected an explicit finite-ULift instance,
qualified `ProEtale.comparisonUpperStar`, and fixed method-application syntax. Final
line-length checks and the prescribed delivery dry run are recorded below.

## Second reading by Q43

A separate clause-by-clause rereading of the node and the module found that an early
draft merely provided a free image functor with projection data. It was replaced
before delivery: the image object is now the existing completed derived direct image,
and its projection is explicitly constructed from its actual reduction units and
the normalized scalar square. The Roos field proves that this exact object and exact
projection realize the tower, and theta is a real definition from the normalized
resolution comparison. The rereading also checked that the etale witness uses the
recorded bounded constructible predicate and the exact scalar encoding, that n=0
represents the first positive exponent, and that every base-changed map receives all
clauses. No independent agent was started, in accordance with the dispatch brief;
the maintainer's independent delivery review remains separate.

Final validation: `deliver2.py Q43 lem-zl-finite-completed-image-comparison --no-push`
printed `OK (dry run): commit fa9b18b2f21 passes the preflight and compiles; nothing
pushed`. Both sandbox and library module compilations were clean. All Lean lines are
at most 100 characters. The single remaining `sorry` is the assigned theorem's proof.

## Returned-delivery repair

The independent review of immutable head `bf5c10f25bf5` returned H2: the
`etaleOrigin` field uses scalar restriction and its derived encoding, but the
owning nodes were absent from `stmt_deps`. Added exactly the two requested
existing dependency nodes:

- `def-pur-proetale-module-scalar-restriction`, whose recorded module is
  `Sheaf.Paper.ProEtaleConstantModuleEncoding` and whose declaration is
  `AlgebraicGeometry.Scheme.proEtaleModuleRestriction`. This is the intrinsic
  module to constant-scalar module restriction used by `etaleOrigin`.
- `lem-pe-constant-derived-encoding`, whose recorded module is
  `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedEncoding`. Its
  `AlgebraicGeometry.Scheme.proEtaleModuleRestriction_additive` and
  `AlgebraicGeometry.Scheme.proEtaleModuleRestriction_equivalence` instances
  supply the additive equivalence used by `mapDerivedCategory`; the module also
  records the resulting derived restriction and its cohomology comparisons.

Read both nodes' statements and Lean records and the full signatures and
docstrings of these declarations. Compared the retained returned node with the
current shared main node: before this repair only the `lean` record differed.
The current main has no module for this item. The repair changes `stmt_deps` by
these two entries and retains every other non-`lean` field from main. No
mathematical statement, hypothesis, clause, or proof sketch changes. No new node
or dependency module is needed. The Lean source remains byte-identical to the
returned version (SHA-256
`6318ef017f19747c6d9bea9b098d9dfbe527395b4e5065b96ee1d930612a7f7d`).

Repair validation: the prescribed `scompile.py` compiled this file successfully
under both the sandbox and library module names, with no errors or warnings.
`deliver2.py Q43 lem-zl-finite-completed-image-comparison --no-push` printed
`OK (dry run): commit 514a6fe3871 passes the preflight and compiles; nothing pushed`.
The final report update is rechecked by the delivery wrapper before pushing.
