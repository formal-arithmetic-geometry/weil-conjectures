## Worker report

The module `Sheaf.Paper.WeilPbcUniformCompleteTriangulated` states
`WeilConjectures.pbcBoundedConstructibleComplete_isTriangulated` with proof
`sorry`. Its docstring includes every one of the node's eight proof steps,
including the cone/shift signs, the uniform bound, arbitrary-morphism witness
lifting, quotient cocycles, local effectivity, and inherited triangulation.
The item's natural statement, statement dependencies, and proof are unchanged.

I read the item, all three statement dependencies, their current records and
source declarations, and the Mathlib subcategory classes and inherited instances.
I checked the current server source of `Sheaf.Paper.BoundedConstructibleComplete`
using `scompile.py --source`. It agrees with the shared checkout. In particular,
the category is now published; this packet uses that definition directly.
The earlier attempt's alternative category, tower, origin and completion repairs
are excluded. Only the item and the three comparison-interface rebuilds described
below are delivered. There are no new nodes or definitions.

Hypothesis and object checklist:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E/Q_ell: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. No base finite field is imposed.
- The valuation ring and chosen uniformizer are the existing
  `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`, transported by `ULift` into
  the site coefficient universe by `Scheme.PbcIntegralRing l E` and
  `Scheme.pbcUniformizer l E`. `Scheme.pbcIntegralDatum l E` has the actual
  principal ideal and its powers; its other fields are proofs of properties
  of that fixed datum. The positive level n is indexed in Lean by n-1.
- Scheme T: `(T : Scheme.{u})`; noetherianity: `[IsNoetherian T]`.
- Finite dimension:
  `∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞)`.
  This is a finite upper bound, including the empty scheme's dimension.
- Ell invertible: `IsUnit (l : Γ(T, ⊤))`. This is equivalent to unitness in
  all stalks as used by the dependency's `PbcIntegralCategory`: inverses
  restrict, and locally defined inverses glue uniquely. It does not exclude
  the empty scheme. These two hypotheses are explicit theorem binders;
  the underlying membership predicate makes sense more generally.
- The ambient category is `Scheme.PbcCompletedDerived T
  (Scheme.pbcIntegralDatum l E)`, the actual derived category of modules over
  `pbcAdicCompletion`, the limit of `AdicCoefficients.ringSystem`. These are
  the completed continuous-function coefficient sheaves, not constant O_E.
  The original small site retains object universe u+1 and morphism universe u.

Clause checklist:

- The full category is the dependency's `PbcIntegralCategory`, whose
  underlying property is precisely
  `PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)`.
  Fullness includes every ambient morphism between the selected objects.
- Its first conjunct, `PbcIsIntrinsicallyComplete`, transports along the
  canonical coefficient comparison and tests the specified intrinsic Koszul
  completion unit on a representative. The tuple is required to generate
  the ideal; the representative and tuple are proof witnesses only.
  It does not replace the unit by an arbitrary completion isomorphism.
- Its second conjunct, `PbcHasUniformConstructibleReductions`, identifies
  the canonical reductions with an actual `AdicTower`, including all
  transition equations, and requires
  `IsUniformlyBoundedConstructibleAdicTower`. I read its `AdicTowerLocalModel`:
  one finite locally closed stratification and one interval work for every
  level. Covering members carry a common bounded complex with adic-lisse
  finite-type terms, finite-lisse cohomology at every reduction and degree,
  and quotient-linear identifications satisfying the normalization equation.
  This is stronger data than separate bounded constructibility at each level.
- Its third conjunct, `PbcHasCompatibleEtaleOrigins`, existentially supplies
  a `PbcWitnessedTower` and level isomorphisms with the canonical reductions.
  Its equation uses the specified derived scalar-restriction mate and the
  canonical reduction normalization. The origins are bounded below and the
  iterated-composite convention includes the quotient cocycle.
- Isomorphism closure is the first conclusion,
  `ObjectProperty.IsClosedUnderIsomorphisms
  (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))`.
- Zero and every integer shift are contained in the second conclusion,
  `ObjectProperty.IsTriangulated` of the same property: its inherited fields are
  `ContainsZero`, `IsStableUnderShift ℤ` and `IsTriangulatedClosed₂`.
  Together with the first conclusion, `ContainsZero` gives actual zero
  membership, not just membership up to an isomorphism.
- Cones of every morphism: Mathlib's
  `ObjectProperty.instIsTriangulatedClosed₃OfIsTriangulated` and
  `ext_of_isTriangulatedClosed₃` give membership of the third vertex of every
  ambient distinguished triangle with its first two vertices selected.
  Conversely, cone closure and integer shift closure imply the middle-vertex
  field by inverse rotation. Thus this is the exact node criterion.
- Inherited shift, distinguished triangles, triangulated category and exact
  inclusion: Mathlib's `Pretriangulated P.FullSubcategory` takes triangles
  to be `P.ι.mapTriangle.obj ⁻¹' distTriang C`; the shift is inherited.
  Its `IsTriangulated P.FullSubcategory` and `P.ι.IsTriangulated` instances
  supply precisely the remaining assertions. No unrelated triangulation is
  postulated, and no additional conjunct or structure needs to be chosen.

Statement-dependency declarations used:

| Node | Module | Declaration |
| --- | --- | --- |
| def-weil-pbc-adic-coefficient-datum | Sheaf.Paper.AdicCoefficientDatum | AlgebraicGeometry.Scheme.AdicCoefficients.coefficientRing, ringSystem, completedRing |
| def-weil-pbc-bounded-constructible-complete | Sheaf.Paper.BoundedConstructibleComplete | AlgebraicGeometry.Scheme.PbcIntegralCategory, PbcIsBoundedConstructibleComplete, pbcIntegralDatum |
| def-weil-triangulated-subcategory | Mathlib.CategoryTheory.Triangulated.Subcategory | CategoryTheory.ObjectProperty.IsTriangulated |

All recorded proof-dependency modules are imported without `public`, including
`BoundedConstructibleTower`, `IntrinsicCompletionCompleted`, the current
`ProEtaleConstructibleCoefficientSheaf`, and the derived-change-of-rings, exactness,
comparison, stalk, finite-level triangulation and tensor-pullback interfaces.
The local-effectivity node already has the published declaration
`AlgebraicGeometry.Scheme.normalizedConstructibleTower_local_effectivity` in
`Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity`, imported for step 7.
The earlier absence claim was stale.

Edge cases checked before editing: the empty scheme satisfies the allowed
finite dimension and invertibility conditions; zero strata are permitted in
`LocallyClosedStratification`. Zero local complexes and zero origins are
allowed. The prime coefficient field is not restricted in characteristic beyond
the stated invertibility. The finite coefficient levels start at exponent one;
identity normalizations and repeated indices remain included. The shift index
is all integers, including negative ones. Every ambient morphism is allowed;
no functorial cone or witness-preserving map assumption is introduced.

Searches rerun for this completion:

- `msearch.py leanfinder`: "derived complete complexes of adic sheaves with
  compatible uniform constructible reduction towers form a triangulated
  subcategory" returned eight generic derived-category/t-structure results,
  none this theorem.
- `msearch.py loogle`: `CategoryTheory.ObjectProperty.IsTriangulated` returned
  the class and its projections/instances; the existing class is used directly.
- `msearch.py grep`: `complete.*triangulat|triangulat.*complete|uniform.*constructible`
  in CategoryTheory returned three generic triangle-completion hits, no match.
- `msearch.py leansearch`: "uniform constructible adic reduction towers and
  derived completeness are closed under shifts and mapping cones" was
  unavailable (Internal Server Error); this is not counted as a no-match.
- Direct `rg` on upstream WeilConjectures and shared Sheaf for
  `complete.*istriangulated|istriangulated.*complete|uniform.*(triangulat|cone)`
  found the generic derived-completeness closure and the nearby
  `boundedConstructibleDerivedCompleteIntegral_isTriangulated`. I read the
  latter: its base finite field and levelwise constructibility/uniform
  cohomological support property differ from this compatible local-model
  category, so it is not reused as an exact statement. Searching upstream
  for the exact node id returned no result. The proposed declaration name also
  has no match in upstream, shared Sheaf, Mathlib, or the upstream-name index.

I read the actual source corollary and order-1300 definition from the server
literature, and Stacks derived.tex's triangulated-subcategory definition.
The node explicitly identifies its uniform tower closure argument as an agent
supplement; the contextual Stacks definition is not silently substituted for
this category. There is no statement correction or disputed statement.

## Dependency modules

The initial local compile and its server confirmation exposed a published compiled-import
conflict: retired `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`
and modern `FiniteCoefficient.UpperLowerStar.Defs` export the same declarations.
This repeats the earlier attempt's diagnosed comparison-interface problem.
Under §1(B), the packet rebuilds the three current-source comparison modules.
Their mathematical declarations and docstrings are unchanged; a trailing rebuild
comment makes their recompilation explicit. Their node copies change only `lean`
and include the required reason in `lean.note`. The published category definition
itself is reused without any repair or duplicate module.

- `prop-weil-pbc-site-comparison-finite-level`, module
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`:
  retains `AlgebraicGeometry.ProEtale.siteComparison_finiteLevel` with exact
  inverse image, the actual sheaf unit, and positive higher direct-image
  vanishing on pulled-back injectives over every finite ring. Its current
  source has modern affine-comparison imports; rebuilding removes its stale
  compiled dependency on the retired functor framework.
- `lem-weil-pbc-comparison-pullback`, module
  `Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`:
  retains `AlgebraicGeometry.ProEtale.comparison_pullback_coherent`, including
  sets, abelian groups, all finite rings, identity, composition and the specified
  Cartesian-square equation for the actual canonical adjoint-mate comparison.
  Its current source already imports the modern finite-coefficient framework.
- `thm-weil-pbc-site-comparison`, module
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`:
  retains `AlgebraicGeometry.ProEtale.siteComparison_boundedBelow`, its actual
  derived adjunction, full faithfulness and invertible unit on all bounded-below
  objects, without any constructibility restriction. It is rebuilt against
  the preceding finite-level module so its import closure is consistent.

## Verification

The server confirmation compiled the three rebuilt comparison modules cleanly,
and rebuilt the current published category and its dependencies. Its only theorem
errors were field-notation elaboration: the published property is written as an
ordinary function to Prop, so Lean does not resolve object-property classes by dot
notation. Both class names are now explicit `ObjectProperty` applications, without
changing the mathematical assertion. All delivered lines are at most 100 characters,
all four signatures agree verbatim with their node records, and comparison with the
read-only base finds only `lean` changes.

The final `deliver2.py Q05 lem-weil-pbc-uniform-complete-triangulated --no-push`
exited 0 and printed: `OK (dry run): commit 7a2bede91d compiles and passes the
preflight except for the second reading, which the second reader writes; nothing
pushed.` All four delivered files compiled separately through the required local
wrapper, including its sandbox and library checks, with no errors or warnings.
The per-file limits were unchanged. The independent second reader will add their
reading; no earlier second-reading claim applies to this revised statement file.

## Second reading by Q05

I am the independent second reader of this revised packet. I opened the shared
item, its sandbox copy and statement module together; the three statement-dependency
nodes and their actual source declarations; the local-model and witness definitions;
and all three dependency modules in the delivery. I read the source corollary and
order-1300 definition from the server literature, the three comparison source nodes,
and Stacks `derived.tex`, `definition-triangulated-subcategory`, and `proetale.tex`,
`lemma-local-structure-constructible-complex` (09C3). The corollary's restriction is the
source of the implicit triangulation assertion. The DAG expressly records the uniform
closure proof as an agent supplement. The contextual 09C3 assumes a weakly contractible
affine scheme and a Noetherian coefficient ring and discusses constant-coefficient
constructible complexes; those hypotheses do not replace this node's scheme hypotheses
or its completed-coefficient category. There is no statement correction in this packet.

My object, hypothesis and conclusion list, with the exact Lean rendering and verdict:

| Node item | Lean rendering and second-reader verdict |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]`: exact. The primality fact also rules out ell = 0 and ell = 1, as the node does. |
| Finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`: exact; no extra field on the scheme or finite base field appears. |
| A = O_E, uniformizer and I | `pbcIntegralDatum l E` uses `PbcIntegralRing l E`, `pbcUniformizer l E`, and the actual ideal `Ideal.span {pbcUniformizer l E}`. I opened their definitions and the integer-ring source: these are the valuation ring and its recorded uniformizer, lifted by ULift. A different uniformizer generates the same maximal ideal and all its powers; fixing the recorded one does not restrict this category. |
| P_n = A/I^n, n positive | `AdicCoefficientDatum` and `PbcQuotient d n` use `n + 1`. Lean level zero is mathematical level one; no positive level is omitted. |
| Scheme T | `(T : Scheme.{u})`: exact, with no nonemptiness, affineness, separatedness, or base field assumption. |
| Noetherian | `[IsNoetherian T]`: exact. |
| Finite dimension | `_hFiniteDimension : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞)`: exactly a finite upper bound, including dimension minus infinity. |
| Ell invertible on T | `_hInvertible : IsUnit (l : Γ(T, ⊤))`: exact. A global inverse restricts to every stalk; conversely the unique local inverses glue to a global inverse. Thus this is equivalent to the stalk form on `PbcIntegralCategory`, including the empty scheme. |
| Completed coefficient A_T | `PbcCompletedDerived T (pbcIntegralDatum l E)` expands to the derived category of `pbcModules T (pbcAdicCompletion T d)`. I followed the aliases to the actual inverse limit of `AdicCoefficients.ringSystem`, whose levels are sheafified continuous functions to the finite quotients. This is A_T, not the discrete constant integer-ring sheaf. |
| Full compatible uniform category | `PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)` is the object property of the published `PbcIntegralCategory`. Its `ObjectProperty.FullSubcategory` contains every ambient morphism, with no witness-preservation requirement. Exact. |
| Derived completeness in that category | `PbcIsIntrinsicallyComplete` transports through the normalized completed-ring comparison and requires `IsCompletedIntrinsicallyDerivedComplete`: invertibility of the specified Koszul completion unit on a representative. The tuple must generate the ideal. No arbitrary isomorphism to a completion object is substituted. Exact. |
| Common uniformly bounded constructible local models | `PbcHasUniformConstructibleReductions` identifies one `AdicTower` with the canonical reductions and equates all transitions. `IsUniformlyBoundedConstructibleAdicTower` chooses one interval and one finite locally closed stratification before quantifying over all levels. `AdicTowerLocalModel` has one bounded complex over restricted completed coefficients, adic-lisse finite-type terms, finite-lisse reduction cohomology, quotient-linear level identifications and their normalization equation. Exact; mere separate boundedness at each level would not suffice. |
| Compatible etale origins | `PbcHasCompatibleEtaleOrigins` existentially supplies `PbcWitnessedTower` and identifies its levels with the canonical reductions. I read `boundedBelow`, `origin`, `theta`, `beta`, `compatibility`, and the iterated-composite convention. The tensor comparison is the canonical adjoint mate; the outer equation identifies theta with canonical reduction normalization. Thus the required alpha/beta equation, identities and quotient cocycles are retained. Witnesses are existence conditions rather than category-object data. Exact. |
| Closed under all ambient isomorphisms | First conjunct `ObjectProperty.IsClosedUnderIsomorphisms` of precisely the preceding property: exact. |
| Contains zero | Second conjunct `ObjectProperty.IsTriangulated` extends `ContainsZero`. Combined with isomorphism closure it gives membership of every ambient zero object. Exact. |
| All integer shifts | The same class extends `IsStableUnderShift ℤ`: all integers, with no sign or magnitude restriction. Exact. |
| Cones of every morphism | The same class extends `IsTriangulatedClosed₂`; Mathlib derives `IsTriangulatedClosed₃` by rotation. Its `ext_of_isTriangulatedClosed₃` uses isomorphism closure to give actual third-vertex membership for every ambient distinguished triangle with its first two vertices selected. Conversely cone closure and integer shifts imply the class's middle-vertex condition. Exact, with no extra condition on the morphism or cone choice. |
| Inherited shift and triangles | I read Mathlib's full-subcategory shift and `Pretriangulated` instance: its distinguished triangles are exactly `P.ι.mapTriangle.obj ⁻¹' distTriang C`. This is the node's inherited structure. Exact. |
| Triangulated category and exact inclusion | Mathlib's `IsTriangulated P.FullSubcategory` instance inherits the ambient derived triangulation; `P.ι.IsTriangulated` sends those same triangles to ambient triangles with its inherited shift comparison. Thus the conclusion provides both clauses without an arbitrary choice of triangulation. Exact. |

Edge cases: the empty scheme is included, because its dimension is minus infinity
and its section ring is the zero ring, where the relevant element is a unit. Empty
stratifications are allowed. Zero complexes, zero origins and the zero object are
included; the conclusion does not assume a nonzero coefficient-module object.
Finite quotient exponents start at one, whereas every identity/repeated quotient
index is allowed. The empty tuple in the generic intrinsic-completeness definition
is allowed only when it actually generates the ideal. All integer shifts, including
zero and negative shifts, and every ambient morphism are covered. Ell invertibility
is exactly the stated characteristic restriction; no finite-field datum is added.
The one universe `u` is the published dependency's common scheme/finite-extension
size convention: either object can be lifted to a common universe. Coefficients
are lifted to `u+1`; the small pro-etale site still has objects in `u+1` and morphisms
in `u`, rather than an imposed equality of these universes. No implicit instance or
unbound universe appears in the theorem's signature.

Independent duplicate searches, using words different from the first reading:

- `msearch.py leanfinder`: "The full subcategory of adically complete complexes
  with compatible constructible local models is stable under cones and all integer
  shifts" returned eight generic complex and derived-cohomological-bound results;
  none states the compatible uniform completed-category theorem.
- `msearch.py loogle`: the initial unqualified `ObjectProperty.IsTriangulated,
  ObjectProperty.FullSubcategory` query reported an unknown identifier, so I repeated
  it with `CategoryTheory.ObjectProperty.IsTriangulated`. This returned the Mathlib
  class, its zero/shift projections and generic closure instances. I opened
  `Mathlib/CategoryTheory/Triangulated/Subcategory.lean`, in particular its class,
  rotation lemmas, full-subcategory triangulation and exact inclusion.
- `msearch.py grep`: `adic.*[Tt]riangulat|[Tt]riangulat.*adic|[Cc]omplete.*[Cc]one`
  in Mathlib CategoryTheory returned no hit.
- Direct `rg` of upstream WeilConjectures and shared Sheaf for
  `complete.*(triangulated|cone)|uniform.*(shift|cone)` found generic constant-ring
  derived-completeness closure, the levelwise-isomorphism cone criterion, and
  `boundedConstructibleDerivedCompleteIntegral_isTriangulated`. I opened the latter
  two. The first cone criterion is conservativity, not this subcategory assertion.
  The integral triangulation theorem uses a `FiniteFieldDatum` and explicitly
  requires only one common cohomological support bound, not common local models or
  compatible etale witnesses. It is not an exact match. No exact existing theorem
  was found, and the packet reuses every existing notion rather than defining it.

Dependency-module review under H13: these are recompilations of the current
published mathematical interfaces, with only a trailing rebuild comment relative
to the shared source. Each dependency node changes only `lean` and explains the
retired/modern framework compiled-import collision in `lean.note`. I verified each
against its own source and node, not only against this item's use of it:

- `prop-weil-pbc-site-comparison-finite-level`: `(T : Scheme.{u})`, arbitrary
  finite `[Ring Λ]` coefficients in the prescribed `u+1` size; finite-limit and
  finite-colimit preservation give exactness; the unit is the actual
  `proEtaleSiteComparisonModules` unit on every etale module sheaf; for every
  injective and every `q > 0`, the displayed right-derived direct-image object
  is zero. No commutativity or finite-generation hypothesis is added.
- `lem-weil-pbc-comparison-pullback`: the constructed inverse images and their
  canonical conjugate comparison use the base-change square on restrictions.
  `ComparisonPullbackCoherent` explicitly records identity, arbitrary composite
  and specified chosen-Cartesian-square equations. The theorem covers sets,
  abelian groups and every finite-ring module coefficient category. The helper
  definitions have real Kan-extension, sheafification and adjunction-mate data;
  they do not choose an unspecified natural isomorphism. All node clauses remain.
- `thm-weil-pbc-site-comparison`: the left functor is the canonical finite
  coefficient comparison on all bounded-below objects. Its right adjoint is
  the bounded-below derived direct image transported through the specified
  coefficient realization. `Nonempty ...FullyFaithful` asserts exactly full
  faithfulness, and `IsIso ...unit` uses the actual derived adjunction unit.
  The coefficient ring is finite and discrete, with no constructibility,
  cohomological upper bound or finiteness requirement on module sheaves.

No new definition nodes are present. I found no mathematical mismatch to repair
in the revised main statement or the three dependency modules, so I left their
Lean and node copies unchanged. Every delivered theorem still has proof `sorry`;
there are no newly hollow definitions or new proved facts. The main docstring
contains the source/blueprint attribution and all eight node proof steps,
including cone signs, the uniform bound, arbitrary-morphism lifting, quotient
cocycles and exact inclusion. The four `lean.statement` strings occur verbatim
as their source signatures; all delivered Lean lines are at most 100 characters.
This second reading changes the report only, adding the independent source,
interface, clause, universe and search audit above.

Second-reader verification: `scompile.py Q05
lem-weil-pbc-uniform-complete-triangulated` compiled all four delivered modules
separately, including their sandbox and library checks, with exit status zero
and no errors or warnings. The wrapper's per-invocation 60-second limit and
normal compiler settings were unchanged. Preliminary and aggregate timings
include dependency work and slot acquisition; no file timeout was raised.


## Maintainer immutable-delivery review correction, 2026-10-16

H9: supply the recorded proof-dependency imports. The complete replacement main
module imports NormalizedConstructibleTowerLocalEffectivity for proof step 7 and
uses ProEtaleConstructibleCoefficientSheaf for the recorded intrinsic coefficient
constructibility predicate. The local-effectivity declaration is present already
at immutable delivery commit 4deda7e4bc3da7eae07ae88dfb303b2cc6dade11. No signature,
mathematical statement, definition, theorem proof or proof docstring is changed.
The original worker and second-reading sections are retained as delivery history;
the independent maintainer review and reproducibility evidence are in review.md.
