## Worker report

The module `Sheaf.SixFunctors.CompositionProjectionMate` states
`AlgebraicGeometry.ProEtale.CompactCompositionProjection.compositionProjectionMate`.
Its only postponed theorem is this declaration, with the eleven-step DAG proof in its
docstring. The node's natural statement, dependencies, and proof are unchanged. There are
no new nodes or dependency repairs.

The component helpers package existing operations. They do not assert the desired identity
as an assumption. In particular `TensorData` is instantiated explicitly in both coefficient
settings, rather than quantified over in the theorem. `projection` spells out the component
of the supplied-domain compactification projection: the existing counit projection, the
existing open tensor comparison, and inverse pullback composition, in that order. `alpha`
is the actual proper/open Gamma, whiskered by the inner open and outer proper functor,
followed by the specified direct-image and open compositors. Its functor associators are
inserted in the definition, rather than left unspecified.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Fixed algebraic closure of a finite field, of characteristic p | `F : WeilConjectures.FiniteFieldDatum.{u}`; its `k₀`, `k`, cardinality, field and algebraic-closure fields are the dependency's existing encoding. |
| Prime ell different from p | `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ F.p`. |
| Finite extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. |
| Integers, uniformizer, A_(E,n), n at least 1 | The actual `Padic.coefficientExtensionRing l E (n + 1)` is the quotient by the power of the recorded uniformizer ideal. `n : ℕ` with level `n+1` covers exactly the positive levels. `ULift.{u+1}` is the dependency's coefficient universe transport, preserving the ring operations. |
| All schemes finite type over k, with no separated structure-map assumption | The dependency's `Spaces F`: the full subcategory of `Over (Spec (.of F.k))` with locally finite type and quasi-compact structure morphisms. `geometry F` forgets to schemes. There is no `IsSeparated` condition on objects. |
| Separated finite-type f and g | In a supplied triangle these are `j ≫ q` and `i ≫ s`, respectively; an open immersion followed by a proper map is separated and locally finite type, and is quasi-compact here. Thus they already have exactly the required morphism properties, without needing an unrelated f or g parameter. |
| Compactification (i,s) of g | `IsOpenImmersion (geo.map i)` and `IsProper (geo.map s)` in `TriangleLaws`, and g is represented by `i ≫ s`. |
| Supplied compatible triangle j,b,q,p; f=qj and pb=iq | The `j b q p i s` binders and the open/proper instances in `TriangleLaws`; f is represented by `j ≫ q`, and `hb : b ≫ p = q ≫ i` is the square equation. No Cartesian condition appears. |
| Composite bj compactifies gf | The result functor is `compact c (j ≫ b) (p ≫ s)`. The equality of its morphism with fg is the explicit associativity/`hb` equality inside `trianglePull`. |
| Normalized comparison alpha | `alpha c j b q p i s hb`, made from `c.gamma`, `c.sComp`, and `c.jComp`, with their functor whiskerings and associators. `TriangleLaws` also asserts `IsIso` of this particular natural transformation, not existence of some comparison. |
| Arbitrary ambient K and L | `∀ (K : c.D X) (L : c.D Z)` in `TriangleLaws`; the finite categories are `ProperOpenDerived`, the ordinary unbounded derived categories of pro-etale constant-module sheaves. No predicates on K,L occur. |
| PF_g, followed by g_!(PF_f) | The first two factors of `leftMap`, using `projection c t i s ...` and `(compact c i s).map (projection c t j q ...)`. |
| Input of alpha retains both pullbacks | The third factor of `leftMap` is alpha at `tensor X (K, (P (j≫q)).obj ((P (i≫s)).obj L))`. Neither of these pullbacks is discarded. |
| Canonical pullback and tensor identifications | The last factor of `leftMap` is H applied to tensor identity with `trianglePull.hom.app L`. `trianglePull` is inverse `pComp` followed by equality transport along the triangle equation. |
| Right side PF_(gf)(alpha_K tensor 1) | `rightMap` first applies `tensor.map (Prod.mkHom (alpha.app K) (𝟙 L))`, then `projection c t (j≫b) (p≫s) K L`. |
| Displayed equality | Second conjunct of `TriangleLaws`: `leftMap ... K L = rightMap ... K L`. Lean's `≫` writes the displayed composition in execution order. |
| Natural in both inputs | Third conjunct of `TriangleLaws`, quantified over arbitrary `a : K ⟶ K'` and `d : L ⟶ L'`, is the full naturality square for the common map. Alpha itself is constructed as a natural transformation. |
| Compatible with the associative compositor for three morphisms | `Associativity c` states the actual 0F7K three-cell equation. The left path composes A, then B+C; the right path composes C, then A+B. Final `jCongr` and `sCongr` give the explicit open/proper associativity transports. The outer rectangle equalities hAB,hBC are consequences of hA,hB,hC; quantifying over their proof terms excludes no grid. Together with TriangleLaws this equates both successive applications of the projection identity. |
| Same identity for strict semilinear systems before evaluation/limit | The final conjunct universally quantifies `o : Operations l E` and `z : Realizations l E F o`, and asserts both `TriangleLaws (realizedSystems ...) (realizedTensor ...)` and `Associativity (realizedSystems ...)`. Its categories are exactly `System l E X = coefficientSequenceDerived l E X`. |
| Specified simultaneous system maps and quotient transitions | `realizedSystems` uses `pull l E`, `Operations.push`, `Operations.shriek`, their existing adjunctions, and `z.compositors.pullComp`. Its alpha is the inverse adjunction mate of `z.properOpen.gamma`; the forward mate in `Calculus.gamma` recovers that very specified Gamma by the equivalence inverse law. `realizedTensor` uses the actual `systemClosed.tensor`, `properProjection`, and `z.openComparisons.projection`. Thus quotient transitions remain in every map; none are chosen from finite evaluations. |
| No Tor/constructibility, separatedness of X,Y,Z over k, or faithfulness assumption | None of these hypotheses occurs. Realizations presents the canonical operations globally; its good-object subdomains do not restrict the K,L binders used here. No evaluation, scalar restriction, or total-limit functor appears in either equation. |

Quasi-compactness in the generic component notation is the inherited requirement of
`Calculus.gamma`. It excludes no triangle or grid over these `Spaces F`:
`spaceNoetherian` applies the existing finite-type-over-Noetherian theorem to the two
subtype properties, and Mathlib's `IsNoetherian.noetherianSpace` and
`quasiCompact_of_noetherianSpace_source` give quasi-compactness for every map from such
an object. In particular the open maps in the statement require no extra assumption.
The auxiliary generic notation can be used with other calculi, but the actual theorem
only asserts the two prescribed geometric realizations.

Dependencies read and used:

- `def-weil-l-adic-coefficient-extension`: module
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, theorem
  `Padic.finite_coefficientExtensionRing`, and its imported actual
  `Padic.coefficientExtensionRing`, `coefficientExtensionUniformizer`, and transition maps.
  `positiveCoefficientFinite` of the ambient dependency installs the positive-level lift.
- `def-weil-scheme-morphism-properties`: convention record, not a separate declaration.
  Its Mathlib `IsOpenImmersion`, `IsProper`, `LocallyOfFiniteType`, and `QuasiCompact`
  are used directly, through the existing full subcategory of over-schemes.
- `def-weil-compactifications-refinements`:
  `WeilConjectures.Compactification.Refinement`, declaration
  `AlgebraicGeometry.Compactification.Refinement`, imported unchanged. The indicated
  compactifications are represented by their open/proper factors and equations, so
  their functors compute exactly the same `S_p J_j` without choosing different data.
- `def-exchange-projection`: module `Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
  `CategoryTheory.SuppliedExchangeProjection.compactificationProjectionFromData` and
  `ExchangeProjectionStage.projection`; the component formula is spelled out using the
  existing realized proper projections and open comparisons, not arbitrary maps.
- `lem-sf-integral-compactification-system-realization`: module
  `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`,
  `WeilConjectures.IntegralSystemRealization.Operations`, `Realizations`,
  `properProjection`, `compactificationProjection`, and the intrinsic `properOpen.gamma`.
  Its theorem supplies these presentations for the stated coefficients.
- `lem-sf-ambient-proper-open-pasting`: module
  `Sheaf.SixFunctors.AmbientProperOpenPasting`, declarations
  `AlgebraicGeometry.ProEtale.AmbientProperOpen.Spaces`, `geometry`, `Calculus`,
  `ordinary`, `Calculus.gamma`, `sComp`, `jComp`, `pCongr`, `sCongr`, `jCongr`,
  and `ambientProperOpenPasting`. These fix the actual maps and their associators.
- `lem-coef-semilinear-derived-sections`: module `Sheaf.Paper.SemilinearDerivedSections`,
  `WeilConjectures.SemilinearSections.SemilinearDerivedSectionsData` and
  `semilinearDerivedSections`; their actual ringed-system categories and derived adjunctions
  are retained through the recorded system realization, not copied.

The stated proof dependencies are imported, directly or through the public ambient and
system modules. The direct proof imports include `ProperOpenProjectionMate`,
`OpenTensorNormalization`, `SemilinearDerivedSections`, `CompactifiableCompatibleTower`,
`NagataSketchClosure`, and upstream `Compactification.CategoryBaseChange`. Mathlib's
Noetherian, proper-composition, closed-immersion and adjunction interfaces are inherited.
No import is omitted to change the coefficient domain or evade an import cycle.

Edge cases checked before writing:

- Positive level 1 is n=0 in the theorem's indexing. There is no level-zero coefficient
  quotient substituted for it. Arbitrary positive levels occur exactly once.
- Empty schemes are objects of the same full subcategory. No point, inhabitedness,
  connectedness or nonempty-open assumption is used.
- Zero K or L remains an allowed derived object; no projection map is inverted.
- Identity/open/proper factors are allowed. Alpha still uses their canonical adjunction
  compositors; the grid includes identity cells.
- Non-Cartesian triangles are allowed; Gamma uses the intrinsic clopen projection mate.
- Systems can be noncartesian, nonnormalized, unbounded, or of infinite Tor amplitude;
  they are unrestricted objects of System. Evaluation is never used to detect equality.
- Independent object/morphism and category universes are explicit in the generic helpers;
  both geometric realizations retain the dependency's original site/coefficient sizes.

Searches made with the prescribed msearch.py, with the actual returned results:

1. LeanFinder: `compact support composition projection formula counit mate compatibility
   for unbounded derived coefficient systems`. Eight hits, including
   `CategoryTheory.Adjunction.derivedε_fac_app` and unrelated condensed/Dold--Kan maps;
   none states the normalized compactification equation or its system analogue.
2. Loogle: `CategoryTheory.mateEquiv, CategoryTheory.Adjunction.rightAdjointProjectionMap`.
   Zero hits: the hosted Mathlib search does not know the latter upstream declaration.
   The project source supplies the projection map, but not this compatibility statement.
3. Mathlib grep, CategoryTheory: `projection.*[Cc]omp|[Cc]omp.*[Pp]rojection`.
   Twenty-four hits concern graded-object projections, categorical products, and limit
   projections; none concerns this compact-support formula.
4. LeanSearch: `compact support derived direct image composition projection compatibility
   mate`. Eight hits on ordinary function support, with no derived-functor identity.
5. Direct project/source grep: `lem-sf-composition-projection-mate` has no upstream
   declaration. Searches for `compositionProjectionMate`, `CompactCompositionProjection`,
   and composition/projection phrases in upstream names, SixFunctors/ProEtale, and
   `lean/Sheaf` found the existing projection and proper/open normalization APIs,
   not the item's statement. These were read and reused rather than restated as the theorem.

Sources opened: the node and all seven statement-dependency records and their declaration
sources; the coefficient-ring definitions; Stacks more-etale.tex at the full statements
and formulas for 0F7B, 0F7C, 0F7D, 0F7J, 0F7K; and the existing compatible-tower and
cofiltered-compactification interfaces. No statement correction or dispute is needed.

Validation: per-file compilation through scompile.py; only the main theorem uses sorry.
The dry-run preflight and final delivery are recorded by the prescribed delivery wrapper.

## Second reading by Q118

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
