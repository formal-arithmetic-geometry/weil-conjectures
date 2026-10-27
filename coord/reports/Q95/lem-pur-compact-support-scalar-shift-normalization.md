## Worker report

Q95, 2026-10-24. The module `Sheaf.Paper.CompactSupportScalarShiftNormalization`
states `WeilConjectures.PurStrictScalar.compactSupportScalarShiftNormalization`.
Its only postponed proof is this named theorem, with all nine natural-language
proof steps in its docstring. The helper `OriginalMateShift` is a conjunction of
shift equations for the already specified original-site maps. The named shift
instances contain real data inherited from existing exact-functor localizations,
right-derived functors, the reduction adjunction, and composite shift structures.
No new scalar map or independently chosen support functor is introduced.

### Hypotheses and objects

- The finite-field datum is `(D : FiniteFieldDatum.{u})`, `[Fact l.Prime]`, and
  `(hl : l ≠ D.p)`. All are retained by the section's `include` command.
- Finite coefficient extensions are `E`, `F`, their `Field`, `Algebra ℚ_[l]`, and
  `FiniteDimensional ℚ_[l]` instances, with `(i : E →ₐ[ℚ_[l]] F)`. An algebra
  homomorphism between these fields is the specified inclusion, not an extra
  assumption that the extension splits. The existing coefficient constructions
  supply the valuation rings, chosen uniformizers, and their quotient maps.
- `X`, `Y` are `Scheme.{u}`, with their `Over (Spec (.of D.k))` instances;
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on both structure maps
  express separated finite type. The named `f.IsOver` and the three corresponding
  instances on `f` give the stated separated finite-type morphism over the base.
- `(c : Compactification f)` is the existing factorization with `c.i` open and
  `c.g` proper. Its intermediate scheme is `c.Z`.
- The ramification data are `(e : ℕ)`,
  `(he : PurCompactSupport.Ramification l E F i e)`, `(hepos : 1 ≤ e)`;
  these are exactly the valuation-ideal equation and positivity in the node.
- Completed rings and their canonical map are the existing
  `completedCoefficientMap l E F i W`; `pbcDerivedExtend` is the recorded
  total derived scalar extension. Finite rings are those in `finiteChange`,
  with exponent `n + 1`, so the quantified `n : ℕ` ranges over every positive
  exponent, and the F quotient exponent is `e * (n + 1)`.
- `M : finiteTorConstructibleIntegralCategory l E X` is precisely the full
  subcategory of completed integral objects that are bounded constructible with
  one uniform Tor interval for all reductions. Its ambient object is `M.obj`.
  No flatness or stronger boundedness assumption is imposed on M itself.
- `S`, `S' : CoefficientDerivedSystemCalculus.{u, u} ... X` specify the native
  derived reduction adjunctions, as in both recorded strict-mate and scalar-limit
  declarations. Quantifying over these choices expresses the node for the
  specified reduction lifts, and adds no existence or exactness hypothesis.
- `support` is the native separately derived open/proper tower followed by
  restriction to constant integral modules. `subsequence ... e` selects index
  `e*(n+1)-1`, preserving composite transitions. `T` is the existing degreewise
  ordinary tensor on strict towers, localized in its ordinary derived category.
  `scalarSupport` is the existing completed integral support functor. Sites stay
  `Scheme.ProEt` (object universe u+1, morphism universe u), and their module
  coefficients have universe u+1; no site-universe identification is added.

### Every conclusion clause

1. `OriginalMateShift (completedChange ...) c` and its `∀ n : ℕ` finiteChange
   counterpart state shift compatibility on the original ringed sites. The
   predicate uses the actual `properComparison`, `openComparison`, inverse
   `scalarPull`, and proper adjunction counit, not arbitrary isomorphic arrows.
   The last two are exactly the balanced comparison and epsilon in the defining
   geometric transpose: `proper_geometric_transpose` in the recorded scalar
   comparison module identifies their composite with that transpose. Thus their
   shift squares say its value at N[r] is the shifted C(epsilon_N), with the
   canonical balanced identification inserted.
2. `NatTrans.CommShift (proper ...) ℤ`, `openTensor`, `strictScalarPull.inv`,
   and `(adj ... c.g).counit` give the same four squares on the strict ringed
   diagram site, before evaluation at any level. The actual strict proper
   transpose is specified by `strictProper_geometric_transpose` upstream.
3. `∀ W, ∃! s, IsScalarShiftNormalized ... s` for completed maps and for every
   positive finite quotient is universal-derived-counit normalization and
   uniqueness. `CommShift ℤ` includes the zero and addition coherence laws.
   The canonical completed instance is the already specified `scalarCommShift`,
   which selects this unique structure. The corresponding finite instance is
   the same existing canonical construction. The extra tower clause
   `∃! s : (tensor ...).mapDerivedCategory.CommShift ℤ, letI := s; ...`
   uses the exact localization counit `mapDerivedCategoryFactors.hom`, giving
   the same normalization for degree-zero constant diagram coefficient tensor.
4. `NatTrans.CommShift (scalarCompletion ...).hom ℤ` states the square for the
   actual normalized ordinary/completed transport. Its target shift instance
   is passed explicitly so elaboration does not select a different structure.
   `scalarLimitTensor.hom` and `scalarLimitRestriction` state the squares for
   tau's finite-free limit/tensor factor and the canonical cofinal map.
5. `γ` is a natural transformation on the exact finite-Tor integral full
   subcategory between the stated composites `C_Y P_E^c` and `P_F^c C_X`.
   The first equation for each M is copied from the recorded scalar-limit
   factorization, using the fixed `scalarSupportLimit` and `scalarCompletion`.
   Its other side uses `scalarLimitArrow`, defined upstream as the ordered
   tensor/limit comparison, total derived limit of the actual strict arrow, and
   inverse cofinal restriction. Consequently this γ is tied to precisely
   `r_e⁻¹ R(q) τ`; it is not merely an arbitrary natural transformation.
6. For every `r : ℤ`, the first displayed equation is
   `arrow.app (M.obj⟦r⟧) ≫ s_target = s_source ≫ (arrow.app M.obj)⟦r⟧'`.
   This is the required actual strict-tower equation. The second is the same
   equation for `scalarLimitArrow`, with the canonical total-derived-limit
   comparisons. Neither is inferred only from evaluated/cohomology maps.
7. The final equation is
   `γ.app ⟨M.obj⟦r⟧, hMr⟩ ≫ s_target = s_source ≫ (γ.app M)⟦r⟧'`.
   At r=1 it is exactly the node's displayed gamma equation. Quantification over
   every integer supplies the coherent iterates using the actual `CommShift`
   structures. `hMr` is concluded, expressing shift stability of the stated
   full subcategory; it is not an added hypothesis. Proof irrelevance makes
   the subtype object independent of that proof.

### Recorded dependencies and declarations used

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: the scheme-property convention; Mathlib `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`.
- `def-weil-compactifications-refinements`: `WeilConjectures.Compactification.RefinementCategory`, `AlgebraicGeometry.Compactification.Refinement`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `def-weil-integral-rational-qbar-compact-support`: `Sheaf.Paper.QcqsCompactSupportRealization`, `WeilConjectures.sfQcqsCompactSupportRealization`.
- `lem-weil-compact-support-reduction-tower-functor`: `Sheaf.Paper.CompactSupportReductionTower`, `WeilConjectures.exists_compactSupportReductionTower`.
- `def-weil-inverse-system`: `Mathlib.CategoryTheory.Functor.OfSequence`, `CategoryTheory.Functor.ofOpSequence`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`.
- `def-pc-sheaf-restrict-scalars`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, `SheafOfModules.restrictScalars`.
- `lem-pur-compact-support-strict-scalar-mate`: `Sheaf.Paper.CompactSupportStrictScalarMate`, `WeilConjectures.PurStrictScalar.compactSupportStrictScalarMate`.
- `def-weil-triangulated-category`: Mathlib `CategoryTheory.Pretriangulated` and `Functor.CommShift`.
- `lem-weil-finite-free-completed-scalar-comparison`: `Sheaf.Paper.FiniteFreeCompletedScalarComparison`, `WeilConjectures.finiteFreeCompletedScalarComparison`.
- `lem-pur-compact-support-scalar-limit-reduction`: `Sheaf.Paper.CompactSupportScalarLimitReduction`, `WeilConjectures.PurStrictScalar.compactSupportScalarLimitReduction`.

The more specific declarations exported by those public imports are
`PurCompactSupport.Coefficients`, `Change`, `completedChange`, `finiteChange`,
`properComparison`, `openComparison`, `scalarPull`, `IsScalarShiftNormalized`,
`scalarCommShift`, `Ramification`; `CoefficientDerivedSystemCalculus`,
`coefficientSequenceLimit`, `compactSupportSystemLevel`,
`compactSupportSystemQuotient`; `PurStrictScalar.T`, `G`, `R`, `J`, `tensor`,
`towerPullback`, `towerDirectImage`, `towerJ`, `systemRestriction`, `systemU`,
`support`, `subsequence`, `arrow`, `baseTensor`, `constantMap`,
`scalarConstantRestriction`, `scalarCompletion`, `scalarSupportNative`,
`scalarSupport`, `scalarSupportLimit`, `scalarLimit`, `scalarLimitTensor`,
`scalarLimitRestriction`, and `scalarLimitArrow`.
`finiteTorConstructibleIntegral` and `finiteTorConstructibleIntegralCategory`
are the integral specialization exported by `FiniteTorAmplitudeSites`, rather
than a private duplicate of its etale or general-site predicate.
`DerivedCategory`, its canonical shifts, `Functor.CommShift` and
`NatTrans.CommShift` are Mathlib's definitions. Canonical inverse image, proper
right-derived image, and exact extension-by-zero shifts are obtained from these
existing functors, rather than adding separate arbitrary shift parameters.

The item's original 19 statement dependencies are retained verbatim. The signed
Roos calculation belongs to proof step 8 and its existing proof dependencies;
the conclusion states shift compatibility of the actual `scalarCompletion` map.
No separate representative-property theorem is added to the statement dependencies.
The exact module imports and helper names are listed in the node's lean record.

### Source and edge cases

Read the item's complete source/proof record (all nine steps), and the local
Stacks sources: derived.tex Tag 05SU, sites-cohomology.tex definition-derived-tor,
projection-formula-map and derived-limit-is-ok (06YU, 0B56, 0941), and
sites-modules.tex extension-by-zero-exact (03DJ). The auxiliary has no claim of
being one numbered Stacks theorem. The proof docstring retains its right-Kan
uniqueness, balanced tensor, adjunction, generator, strict-diagram, K-injective,
cofinal block, signed cone and final factorization arguments.

Checked zero M, empty X or Y when a compactification is supplied, identity
coefficient inclusion E=F with e=1, the first finite quotient (n=0 means exponent
1), and r=0, 1, -1. The zero coordinate stays zero for either cone sign; ordinary
scalar tensor uses a degree-zero coefficient and introduces no extra tensor
sign. Arbitrary e≥1, nontrivial ramification, negative shifts and nonuniform
individual resolutions are retained. No smoothness, properness of f, globally
chosen representative, or Tor-concentrated-in-degree-zero condition is added.
No STATEMENT-DISPUTED issue or correction was found.

### Searches and verification

- msearch.py leanfinder, query `derived scalar extension proper open mate strict
  tower compact support comparison commutes integer shift`: eight results,
  including LightCondensed internal-Hom and ordinary extendScalars associativity
  or sheaf pushforward/pullback comparison declarations; none states this node.
- msearch.py loogle, query `CategoryTheory.NatTrans.CommShift,
  CategoryTheory.Functor.rightKanExtension`: zero hits.
- msearch.py grep, query `CommShift|rightKanExtension`, directory
  `CategoryTheory/Shift`: 25 results, the foundational shift, adjunction,
  localization and natural-transformation API, not this statement.
- rg in lean/WeilConjectures and lean/Sheaf for scalar/shift, CommShift,
  properComparison, scalarPull, strict scalar mates and scalar limit maps:
  found the recorded actual maps, existing universal scalar normalization in
  IntegralCompactSupportCoefficientComparison, and the landed signed χ predicate
  in CompletedScalarShift. The actual maps and scalar normalization are reused;
  the separate signed representative predicate is not used in the repaired
  statement. No declaration states the combined
  original-site/strict-tower/total-limit/gamma proposition.
- grep -rn of the exact item id in lean/WeilConjectures found no occurrence;
  the exact-id/project searches likewise found no earlier owning module.
- Every delivered file was compiled using scompile.py against the live published
  server library, both in its sandbox import path and its final library path.
  The retained packet passed its initial dry run. The repaired module then
  compiled without errors or warnings in both paths (12.6 s and 10.6 s).
  Only the main theorem uses sorry.

## Second reading by Q95

No second reading by a worker: since 2026-10-17 the worker delivers directly and
the maintainer's independent review is the only review.

## Repair of returned delivery

The independent review at immutable head `29ab4b1fedd1` found H2: the packet
added `lem-weil-point-completed-scalar-shift` to `stmt_deps` even though only its
plain representative predicate was used. Its existential conjunct reproduced a
separate theorem conclusion for `completedDerivedScalarExtension`, without tying
those choices to this item's `scalarCompletion` or γ.

Applied the reviewer's correction (a): removed that existential conjunct, removed
the added theorem dependency and its now-unused public import, and regenerated
the verbatim Lean signature. The original 19 `stmt_deps` now agree with the
current base. The natural-language statement, proof, proof dependencies, universes,
canonical shift instances, original/diagram-site mate clauses, actual χ square,
strict-arrow and scalarLimitArrow equations, and factored γ equations are retained.
The nine proof steps still include the signed Roos representative calculation.
No statement correction or new node is needed.

The normalization uniqueness clauses restate the existing
`PurCompactSupport.scalarCommShift_existsUnique`; the canonical completed shift
is its uniquely normalized `scalarCommShift`. The existential γ is fixed by the
recorded scalar-limit factorization, as the review noted. These advisory points
require no added statement dependency or altered map.

Repair self-check: all node fields other than `lean` equal the current base,
including the original 19 statement dependencies. The recorded signature is
verbatim, `autoImplicit` is false, every Lean line is at most 100 characters,
and the only postponed proof remains the main theorem. The scalarCompletion
shift clause uses the same explicit canonical target shift instance as before.
