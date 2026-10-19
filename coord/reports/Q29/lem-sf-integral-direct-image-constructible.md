## Worker report

The main module `Sheaf.Paper.SfIntegralDirectImageConstructible` states
`WeilConjectures.sfIntegralDirectImage_constructible`, with proof `sorry`.
It asserts preservation of the precise integral category in the node, including the
specified projection-adjoint comparisons and all finite-level and uniform bounds.
There is no statement correction and no disputed mathematical claim.

Hypotheses and clauses, in the order of the node:

- The base field is `(K₀ : Type u) [Field K₀]`. The schemes are `Scheme.{u}`, with
  `X.Over (Spec (.of K₀))` and `Y.Over (Spec (.of K₀))`. Each structure morphism is
  locally of finite type and quasi-compact. The map is `f : X ⟶ Y`, with
  `f.IsOver (Spec (.of K₀))`. A morphism between these finite-type schemes over
  the field is itself finite type. No separation hypothesis occurs.
- The prime is `(l : ℕ) [Fact l.Prime]`, and invertibility is `_hl : IsUnit (l : K₀)`.
  The coefficient extension is `(E : Type u) [Field E] [Algebra ℚ_[l] E]`
  `[FiniteDimensional ℚ_[l] E]`. All integer rings, uniformizers and quotients are
  the existing `Padic.coefficientExtension*` constructions; none is replaced.
- `K : DerivedCategory (scalarReductionSource.{u, u} l E X)` is a complex over
  the actual completed coefficient sheaf. `_hK : sfIntegralConstructible l E X K`
  means derived completeness, intrinsic constructibility of each positive derived
  reduction, and one common finite interval containing their cohomological supports.
- At index `n : ℕ`, the coefficient exponent is `n + 1`, so level one is included
  and level zero is never substituted. `scalarReductionDerivedExtension` is the
  published universal derived change of rings along the completed-ring projection.
  `sfFiniteDerivedDirectImage l E f K n` is precisely the right derived ordinary
  constant-coefficient module direct image applied to that reduction.
- `sfDirectImageTerm` is its exact derived restriction to completed coefficients.
  `sfDirectImageTransition` is induced by the canonical quotient map on the source
  reduction, transported through the canonically normalized direct-image/restriction
  comparison. This produces the specified inverse system, rather than an arbitrary
  tower with objects having the right names.
- `SfIntegralDirectImage` records an object, its map to the product, its boundary,
  and the distinguished `IsDerivedLimitTriangle` for that tower. The first conclusion
  asserts existence of the product and such a presentation. The next conclusion
  quantifies over every product witness and every such Roos presentation. This
  explicitly accommodates the node's definition of derived limit as a triangle
  property, without choosing an object from an existence theorem lacking uniqueness.
- The main conclusion is `sfIntegralConstructible l E Y L.obj`. Completeness is
  also listed explicitly as `IsSfDerivedComplete l E Y L.obj`, as in the node's
  more precise clauses.
- For every `n`, `IsIso (sfDirectImageReductionComparison l E f L n)` asserts that
  the SPECIFIED comparison is invertible. Its definition applies the inverse of
  the published derived scalar-extension/restriction Hom bijection to
  `L.projection ≫ Pi.π ... n`. It is therefore exactly the adjunct required by
  the node, not an arbitrary isomorphism between the endpoints.
- For every `n`, `intrinsicFiniteTorsionConstructible ... Y
  (sfFiniteDerivedDirectImage l E f K n)` is finite-level bounded constructibility.
- The theorem asserts existence of an integer `N` bounding all residue-coefficient
  higher direct images. It then quantifies over EVERY integer `N` satisfying that
  bound and every integer interval `[a,b]` containing all source-reduction supports.
  Its conclusion is the support inclusion in `Set.Icc a (b + N)` for every level.
  Thus neither the coefficient exponent nor an arbitrarily chosen bound is fixed.
- The bound uses all sheaves in
  `Sheaf X.smallEtaleTopology (ModuleCat.{u+1} (ULift.{u+1} A₁))` and the ordinary
  higher right derived functor of `Etale.lowerStar`. This is the same higher
  direct image as `Etale.higherDirectImage`, expressed through its smaller owning
  functor import. `ULift` transports the SAME residue coefficient ring into the
  size required by this published étale module-sheaf API. It adds no algebraic
  restriction. Degree `q : ℕ` is sufficient: higher direct images of sheaves
  vanish in negative degrees. Even negative integer bounds are retained, in
  which case degree zero is tested as well.
- `IsAlgClosed K₀ → ∀ d : ℕ, Nonempty X → topologicalKrullDim X = d → ...`
  supplies the bound `2*d` for each dimension value of the nonempty source.
  Finite-type schemes over a field have finite dimension, so the equality binder
  names their dimension rather than imposing a new finiteness assumption.
  `IsAlgClosed K₀ → IsEmpty X → ...` supplies the bound zero separately under
  that same base-field condition. This agrees with the node's parenthetical and
  avoids assigning a natural dimension to the empty space, whose dimension is ⊥.

The main declaration's docstring contains the complete eight-step DAG proof plan.
A paragraph also explains the negative-bound case: vanishing in degree zero
annihilates all residue-coefficient sheaves; the coefficient filtration and finite
truncation devissage then annihilate every relevant bounded finite-level complex.
Every theorem in this packet has proof `sorry`; definitions have real data or use
an existence-and-uniqueness/universal characterization that fixes their data.

The eight postponed theorems are `sfReductionTransition_existsUnique`,
`sfDerivedReductionTransition_existsUnique`, `sfIntegralReductionUnit_naturality`
(owner: `def-weil-integral-reduction-tower`),
`sfCompletedCoefficientMap_existsUnique`, `sfCompletedModuleDirectImage_additive`,
`sfDirectImageRestrictionComparison_existsUnique`,
`sfDerivedRestrictionComparison_existsUnique` (owner:
`def-weil-derived-direct-image`), and the main
`sfIntegralDirectImage_constructible`. They are recorded in their owning nodes'
`lean.declarations`, and each docstring gives the construction or proof plan for
the corresponding part of that node's canonical notion.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, and its imported `CoefficientExtension`
  module, with the chosen integer ring, maximal ideal, uniformizer and quotient maps.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`,
  `scalarReductionSource`, `scalarReductionTarget`, `scalarReductionDerivedExtension`,
  `scalarReductionCounit`, `scalarReductionDerivedRestriction`, and
  `derivedScalarExtensionRestrictionAdjunction`, all in `WeilConjectures`.
  The current server source was checked with `scompile.py --source`.
- `Sheaf.Paper.CompletedIntegralCoefficients`,
  `completedIntegralCommRingSheafUnrestricted` and its finite projections and
  `integralCoefficientSheafTransition`, reached through the scalar interface.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`,
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`,
  `AlgebraicGeometry.Scheme.proEtaleCohomologicalSupport`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
  `CategoryTheory.IsDerivedLimitTriangle`, with its actual distinguished-triangle
  definition and the transition endomorphism `1-s`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`,
  `AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage` and the underlying
  `proEtaleConstantModuleDirectImage`, constructed with the constant-section map.
- Mathlib `LocallyOfFiniteType`, `QuasiCompact`, the `Over`/`IsOver` structures,
  and `topologicalKrullDim`; the convention node defines no independent notion.
- The smaller upstream étale functor interface `Etale.lowerStar`, together with
  Mathlib's ordinary `Functor.rightDerived`, expresses the cohomological bound.

Edge cases checked before finalization: empty source (separate zero bound), empty
cohomological support and zero complex, intervals including negative degrees,
all positive exponents including one, negative qualifying cohomological bounds,
base fields of characteristic zero and positive characteristic coprime to l,
arbitrary base fields of infinite absolute cohomological dimension, and
nonseparated finite-type morphisms. No perfectness over the finite quotient rings
or finite Tor-amplitude assumption on K was added. The site keeps object universe
u+1 and morphism universe u; its module coefficients are in u+1. The common ambient
u contains both the base and coefficient fields; there is no equation imposed on
small-site object and morphism universes.

Searches:

- `msearch.py`, LeanSearch: "derived direct image preserves bounded constructible
  integral adic complexes"; service unavailable (Internal Server Error), recorded
  as unavailable, not as an absence result.
- `msearch.py`, LeanFinder: the same query; eight hits on local cohomology, adic
  completion, condensed modules and constructible SUBSETS, no matching sheaf theorem.
  The earlier attempt also searched the full finite-type/integral-complete wording
  and found only constructible-subset declarations.
- `msearch.py`, Loogle: `"DerivedCategory", "constructible"` and the earlier
  `"IsConstructible", "rightDerivedFunctor"`; no hits.
- `msearch.py`, grep: `integralDerivedDirectImage|sfIntegralDirectImage|
  boundedConstructibleDerivedCompleteIntegral`; no Mathlib hits. The earlier
  `IsDerivedComplete|integralDerivedDirectImage|boundedConstructibleDerivedCompleteIntegral`
  search likewise had no Mathlib hit.
- `rg` on the upstream project, the side project and their DAG records found the
  published reduction/complete/category interfaces described above but no theorem
  stating this item; searching the upstream source for the item id had no hit.
  `scompile.py --source Sheaf.Paper.DerivedDirectImage` confirmed the missing
  direct-image module. The earlier read-only delivery-branch audit found no
  delivered direct-image definition. No independent missing notion needs a new node.

Source read: [Bhatt--Scholze, The pro-étale topology for schemes](https://arxiv.org/pdf/1309.1198),
Definition 3.5.2, Lemmas 6.5.9, 6.5.11, 6.7.2 and Theorem 6.7.1, as well as the
complete node statements and proof plans. In particular 6.5.9 distinguishes
pro-object comparison from finite-level comparison, and the coefficient-perfectness
or cohomological-dimension input is retained in the mathematical proof plan.

## Dependency modules

`def-weil-integral-reduction-tower`: the recorded `IntegralReductionTower` requires
an auxiliary `FiniteFieldDatum`, absent from this arbitrary-field lemma. The new
`Sheaf.Paper.SfIntegralReductionTower` supplies the same quotient tower and canonical
maps from K without that datum. Underived transitions are uniquely characterized
on sheafified pure tensors; derived transitions are uniquely characterized by their
K-flat representative equations. Units come from the published normalized derived
adjunction. `sfIntegralReductionUnit_naturality` and `sfIntegralReductionCone`
record compatibility with ALL inverse-system arrows. The node is already present
and recorded in the DAG; it is added to the item's dependencies and only its Lean
record is repaired. Every helper is listed in that record's `declarations`.

`def-weil-derived-complete`: the new `Sheaf.Paper.SfDerivedComplete` replaces its
unusable finite-field-parameter interface with exactly the original Roos-triangle
condition whose first map consists of the actual reduction units. The product is
existentially supplied inside the predicate; no product-existence hypothesis is
added to a statement. The node changes only in `lean`, with a note.

`def-weil-derived-complete-integral-detailed`: the new
`Sheaf.Paper.SfIntegralConstructible` removes the same unused datum, using the
repaired completeness predicate, the already published intrinsic constructibility
predicate, and the existing support definition. It defines both the object property
and its full subcategory. The node changes only in `lean`, with a note.

`def-weil-integral-derived-reduction`: Lean-only existing-declaration repair to
`WeilConjectures.scalarReductionDerivedExtension` in the already published
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`. This is precisely the
unrestricted universal derived change of rings along the SAME completed-ring
projection, with its K-flat counit. No module is copied or redefined for this repair.

`def-weil-derived-direct-image`: there is genuinely no recorded declaration.
`Sheaf.Paper.SfDerivedDirectImage` supplies it in this delivery. The completed
coefficient structure map is fixed uniquely by all finite coordinates; its module
pushforward is real `SheafOfModules.pushforward` data. The restriction comparisons
are fixed uniquely on sections and on K-injective representatives, without assuming
that coefficient restriction preserves K-injectives. The finite-image tower is
transported through these comparisons. A Roos presentation specifies the integral
object and its projections, and the reduction comparison is the actual derived
adjunct of each projection. The node changes only in `lean`, with a note; its
finite-coefficient and rational/coefficient-closure conventions remain the published
ones. No unspecified map or bare chosen isomorphism replaces a canonical map.

Proof-only imports: the stated proof dependencies with usable import closures are
included as ordinary imports. `ProfiniteCoefficientInverseImage` and
`ComparisonDirectImage` are omitted because each imports the legacy
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`, which duplicates notation
already exported by the finite-coefficient framework. The same conflict in the
broad `Etale.SmoothBaseChange.Defs` import was repaired by using its smaller owning
étale derived-functor module and Mathlib `Functor.rightDerived`. This preserves
the exact coefficient category and higher-direct-image assertion. Their proof
steps remain explicit in the theorem's docstring. Proof dependencies without a
recorded module are not invented or imported.

## Validation

The earlier ENOSPC infrastructure failure no longer reproduces. All five final
modules passed `scompile.py Q29 lem-sf-integral-direct-image-constructible` together
in dependency order, each compiled separately as a sandbox module and under its
library name. There were no errors or warnings. The final main declaration compiled
in 6.9 seconds as a sandbox and 4.7 seconds under its library name; all invocations
retained the wrapper's 60-second limit. The reported earlier line-length warning,
legacy import collision, and missing concrete-coefficient instance imports were
repaired. Local read-only `stage2_delivery.check_lean_text` checks passed for every
new module; all their declarations are listed in their owning node records and
have the appropriate blueprint/source docstrings. The first required delivery dry run printed OK, including compilation and server
preflight (the independent second reading remains for the next worker). A final
wording audit then aligned the empty-source bound with the algebraically closed
base-field antecedent of the node's parenthetical. The complete dry run is repeated
for that final packet; nothing has been pushed.

## Second reading by Q29

I read the node statement in order and matched each item to
`WeilConjectures.sfIntegralDirectImage_constructible`:

- `K₀`, `[Field K₀]`, `l`, `[Fact l.Prime]`, and `_hl : IsUnit (l : K₀)` render the
  base field, prime, and invertibility hypothesis exactly.
- `X`, `Y`, their `Over (Spec (.of K₀))` instances, locally-finite-type and
  quasi-compact structure morphism instances, `f`, and `[f.IsOver ...]` render
  finite-type schemes and a `K₀`-morphism without a separation assumption. The
  finite-type property of `f` is the standard consequence for morphisms between
  finite-type schemes over a field, as used by the proof plan.
- `E`, `[Field E]`, `[Algebra ℚ_[l] E]`, and `[FiniteDimensional ℚ_[l] E]` render
  a finite extension of `ℚ_[l]`; the `Padic.coefficientExtensionRing` terms in
  the theorem render the valuation-ring quotients and uniformizer tower.
- `K : DerivedCategory (scalarReductionSource l E X)` and
  `_hK : sfIntegralConstructible l E X K` render the derived-complete integral
  object with finite-level intrinsic constructibility and one common support
  interval.
- `sfFiniteDerivedDirectImage ... n`, `sfDirectImageTerm`, and
  `sfDirectImageTransition` use the recorded canonical derived reduction,
  restriction, and transition constructions at exponent `n + 1`, so every
  `n : ℕ` is exactly node level `n+1` and level one is included.
- `∃ hprod, Nonempty (SfIntegralDirectImage ...)` supplies the product and the
  Roos-triangle presentation required by the definition of the integral derived
  direct image. The following universal clause ranges over every product
  witness and every such presentation, rather than selecting an arbitrary
  object.
- `sfIntegralConstructible ... L.obj` and `IsSfDerivedComplete ... L.obj` give
  the codomain, completeness, and uniform bounded constructibility clauses.
  `IsIso (sfDirectImageReductionComparison ... L n)` is the specified adjunct
  comparison from the Roos projection, for every finite level.
- `intrinsicFiniteTorsionConstructible ... (sfFiniteDerivedDirectImage ... n)`
  gives finite-level constructibility for every `n`.
- The two `N` clauses quantify over exactly the node's integer bound and all
  residue-coefficient sheaves; the right-derived `Etale.lowerStar` object is the
  ordinary higher direct image. The support implication uses arbitrary integer
  `a,b` and every reduction, with the required interval `[a,b+N]`.
- The algebraically closed cases give `N = 2*d` for nonempty `X` with
  `topologicalKrullDim X = d`, and `N = 0` for empty `X`, under the same
  `IsAlgClosed K₀` antecedent.

Edge cases checked: empty source (separate zero bound), zero complex and empty
supports, `n = 0` indexing (which denotes coefficient exponent one), negative
integer support bounds, characteristic zero and positive characteristic coprime
to `l`, and nonseparated morphisms. The common universe `u` contains the base
and coefficient fields; no equality is imposed between the small-site object
and morphism universes.

Independent searches used `msearch.py` (LeanFinder, Loogle, and the unavailable
LeanSearch service), `rg` over Mathlib, the upstream `WeilConjectures` tree, and
all DAG records. They found no existing theorem or declaration for integral
constructible derived direct image; the recorded dependency declarations are
the canonical coefficient, reduction, completeness, finite-constructibility,
support, and derived-limit interfaces. The new dependency module
`Sheaf.Paper.SfDerivedDirectImage` is the missing direct-image notion and fixes
the coefficient map and restriction comparisons by their canonical
characterizations.

No statement mismatch was found, so no node or Lean statement was changed.
The source and dependency docstrings carry the required blueprint identifier
and proof plans. Compilation was rerun with the prescribed `scompile.py`; the
wrapper compiled the first three sibling modules, then failed while creating
temporary symlinks to the shared live library with `OSError: [Errno 28] No
space left on device`. This is an infrastructure failure, not a Lean error.
