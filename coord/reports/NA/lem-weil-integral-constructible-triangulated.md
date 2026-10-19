## Worker report

The new module `Sheaf.Paper.SfIntegralConstructibleTriangulated` states the
isomorphism closure and triangulation of the **current** predicate
`WeilConjectures.sfIntegralConstructible`. Both named theorems have only `sorry`
proofs and are public instances. No notion is redefined. The legacy module
`Sheaf.Paper.IntegralConstructibleTriangulated` remains untouched for its callers.
The node copy changes only `lean`, preserving its invalidation history.

The main declaration is `WeilConjectures.sfIntegralConstructible_isTriangulated`;
its companion is `WeilConjectures.sfIntegralConstructible_isClosedUnderIsomorphisms`.
These are two clauses of this owning DAG node, not statements of another node.
The full eight-step natural-language proof is in the main docstring; the companion
has the isomorphism argument, including transport of the product/Roos witness.

Hypothesis and clause correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]` in both signatures.
- Finite extension of Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The valuation ring, uniformizer and quotient rings
  are the existing coefficient constructions used by `sfIntegralConstructible`.
- Arbitrary scheme: `(Y : AlgebraicGeometry.Scheme.{u})`, with no quasi-compact,
  Noetherian, finite-dimensional, characteristic or base-field assumption.
- The contextual `ell ≠ p` does not enter this intrinsic category at all: neither
  its coefficients nor its predicate depend on p. The recorded dependency now
  deliberately omits the artificial `FiniteFieldDatum`. The two statements apply
  for every prime l, hence in every stipulated context l ≠ p, without selecting
  a base field or changing the object property. The source's closure argument is
  independent of characteristic. No uniformizer is selected anew.
- The ambient category is exactly `DerivedCategory
  (scalarReductionSource.{u, u} l E Y)`, as in the recorded definition. Its site
  objects have size u+1, morphisms size u, coefficients size u+1. There is no
  identification of the site's object and morphism universes.
- The full subcategory is exactly `(sfIntegralConstructible l E Y).FullSubcategory`,
  already named `sfIntegralConstructibleCategory l E Y`. Its predicate uses
  `IsSfDerivedComplete`, the canonical scalar reductions at exponent n+1, the
  recorded intrinsic finite-torsion constructibility, and one common integer
  interval for all reductions. No legacy predicate is substituted.
- Contains a zero object: `ObjectProperty.IsTriangulated` extends `ContainsZero`.
  Together with isomorphism closure this includes the ambient chosen zero too.
- Isomorphism closure: the separate public instance theorem concludes exactly
  `(sfIntegralConstructible l E Y).IsClosedUnderIsomorphisms`.
- All integer shifts: `ObjectProperty.IsTriangulated` extends
  `IsStableUnderShift ℤ`, allowing every positive, negative and zero shift.
- A distinguished triangle with its first and third vertices satisfying the
  predicate has its middle vertex satisfying it: `IsTriangulatedClosed₂` is a
  superclass. Its `isoClosure` conclusion becomes the actual predicate using
  the companion isomorphism instance; Mathlib's
  `ObjectProperty.ext_of_isTriangulatedClosed₂` states this precisely.
- Inherited triangulation and exact inclusion: the publicly imported Mathlib
  `CategoryTheory.Triangulated.Subcategory` constructs `Pretriangulated` on the
  same full subcategory, with distinguished triangles defined as the inverse
  image of ambient distinguished triangles under `P.ι.mapTriangle.obj`
  (lines 693–694). Lines 719–723 supply `P.ι.IsTriangulated` and the subcategory's
  `CategoryTheory.IsTriangulated`; its shift and `P.ι.CommShift ℤ` are the
  existing full-subcategory shift constructions. Thus these are canonical
  inherited structures available by inference, without a second construction.

Dependency declarations read and reused (publicly via the intrinsic definition
where needed, and otherwise retained as proof-plan imports):

- `Sheaf.Paper.SfIntegralConstructible`:
  `WeilConjectures.sfIntegralConstructible`,
  `WeilConjectures.sfIntegralConstructibleCategory`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated`,
  `.Functor`, `.Subcategory`: `CategoryTheory.Pretriangulated`,
  `CategoryTheory.IsTriangulated`, `CategoryTheory.Functor.IsTriangulated`,
  `CategoryTheory.ObjectProperty.IsTriangulated` and inherited instances.
- `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `WeilConjectures.scalarReductionSource`, `scalarReductionTarget`,
  `scalarReductionDerivedExtension`. This is the recorded derived reduction.
- `Sheaf.Paper.IntegralReductionTowerWellDefined`:
  `WeilConjectures.integralReductionTowerWellDefined` and its canonical comparison.
- `Sheaf.Paper.IntegralReductionTower`:
  `WeilConjectures.integralReductionTower`, `integralReductionTowerMap`,
  `integralReductionTowerCone`.
- `Sheaf.Paper.DerivedCompleteUnrestricted`:
  `WeilConjectures.IsDerivedCompleteUnrestricted`; the current definition's
  `WeilConjectures.IsSfDerivedComplete` in `Sheaf.Paper.SfDerivedComplete` spells out the same canonical
  Roos condition with its product witness and quotient-induced units. The theorem
  is stated directly on the recorded `sfIntegralConstructible`, so no equality
  between predicates is assumed or required as a hypothesis.

Every already recorded proof dependency's module is imported, including the
current `CompletedIntegralCoefficientGerm`, `ConstantCompletionEquivalence`,
`WeilCompletedTensorReflector`, and `ProEtaleConstructibleCoefficientSheaf`
interfaces. No dependency is restated or edited. The generic small-site
completeness proof passes through a small model, as specified by proof step 1;
its generic ringed-site imports are proof tools, not extra smallness hypotheses.

Sources read: the blueprint order-1459 definition at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-derived-complete-integral-detailed.md`
(the explicit uniform-amplitude final paragraph); Bhatt–Scholze §6.5,
Definition 6.5.1 and the next sentence (read using `pdftotext`); Stacks
`algebraization.tex`, Tag 0999, lines 905–928 (local completeness and its
triangulated-subcategory paragraph); Mathlib's full-subcategory construction
and its exact-inclusion instance at the lines above. Bhatt–Scholze formulate
§6.5 for qcqs schemes; this node explicitly uses the blueprint's uniform-reduction
variant on arbitrary schemes. Closure follows from the pointwise conditions
and explicit uniform bound in this variant and requires no qcqs hypothesis.

Edge cases checked: the empty scheme is admitted; zero has empty cohomological
support and interval [0,0]; shift by zero and negative shifts are included;
for arbitrary shift m, [r,s] becomes [r-m,s-m]; extensions use
[min(r',r''),max(s',s'')], including degenerate intervals and zero outside
vertices. The reduction index n : ℕ denotes the positive exponent n+1, including
exponent 1 and imposing no exponent-zero condition. Bounds are uniform in n;
no common stratification or rank bound is imposed. No geometric finiteness
condition is needed. There is no empty-index special case: the tower index is ℕ.

Searches actually run:

- `msearch.py ... leanfinder "Derived complete integral complexes with uniformly
  bounded constructible finite reductions form a triangulated subcategory"`:
  eight results, including derived-category triangulation, t-structures and the
  acyclic homotopy subcategory; none is this predicate's closure theorem.
- `msearch.py ... loogle "CategoryTheory.ObjectProperty.IsTriangulated"`:
  twelve results, including the class and its zero/shift/extension superclass
  projections, inverse-image and iso-closure results. This supplies the generic
  encoding and inherited structures, not the desired intrinsic instance.
- `msearch.py ... grep
  "sfIntegralConstructible|boundedConstructibleDerivedCompleteIntegral|[Ii]ntegral.*[Tt]riang"`:
  two unrelated Mathlib measure-theory integral triangle inequalities.
- Direct `rg` of `lean/Sheaf` and the upstream `WeilConjectures` tree for
  `sfIntegralConstructible.*[Tt]riang`, `sfIntegralConstructible.*[Ii]so` and
  `sfIntegralConstructibleCategory`: only the category definition and a consumer
  in `PointSectionsDerivedReduction`; no current intrinsic closure instance.
- Direct upstream grep for this node id: no hit. Searches of upstream
  `WeilConjectures`, `dag/lean_names_upstream.json`, and `lean/Sheaf/Paper/Sf*`
  for integral triangulation found the older derived-complete integral category
  API and functor exactness, not closure of `sfIntegralConstructible`.
- Read the legacy `IntegralConstructibleTriangulated` theorem: it is about
  `boundedConstructibleDerivedCompleteIntegral` and cannot attach this reopened
  node. Reused its complete eight-step mathematical proof documentation while
  changing the signature to the current owning predicate, as requested.

No new nodes, dependency modules, statement correction, or statement dispute.
Compilation and dry-run evidence is recorded below after verification.

Verification: `scompile.py NA lem-weil-integral-constructible-triangulated`
compiled the delivered module and the separate scratchpad probe in dependency
order with no errors or warnings (about 3 seconds per file). The probe synthesized
all ten requested interfaces: predicate isomorphism closure, zero containment,
integer-shift stability, extension closure, and on `sfIntegralConstructibleCategory`
the zero object, integer shift, pretriangulation, triangulation, plus inclusion
shift compatibility and exactness. The probe is outside `lean/` and is not a
delivered module. Only the two delivered theorem proofs contain `sorry`.


## Second reading by NA

I read the item's current node and sandbox module independently, then opened
`SfIntegralConstructible`, `SfDerivedComplete`, `SfIntegralReductionTower`,
`DerivedScalarExtensionRestrictionAdjunction`, `CompletedIntegralCoefficients`,
`IntrinsicFiniteTorsionConstructibility`, `ProEtaleCohomologicalSupport`, and the
coefficient-extension definitions. The recorded dependency is now the intrinsic
`sfIntegralConstructible`; the old theorem about
`boundedConstructibleDerivedCompleteIntegral` cannot serve as this node's Lean
attachment. The delivered module uses the current recorded predicate verbatim.

Sources actually read: blueprint order 1459,
`sec-smooth-purity/sk-def-sf-operations/def-weil-derived-complete-integral-detailed.md`;
Bhatt--Scholze, Section 6.5, its opening assumptions, Definition 6.5.1 and the
following triangulated-subcategory sentence (using `pdftotext -layout`); Stacks
`algebraization.tex`, `definition-derived-complete`, Tag 0999, and the immediately
following paragraph (lines 905--925). Bhatt--Scholze explicitly fixes a qcqs scheme
and a complete Noetherian coefficient ring. This node states the blueprint variant:
all positive reductions are constructible and have one uniform bounded interval.
Its zero/shift/extension argument uses these conditions directly, and does not
import a geometric qcqs hypothesis from the different definition in that paper.
The coefficient valuation ring is the finite-extension DVR, not a general ring
for which the Noetherian assumption would have been omitted. Stacks states the
completeness closure on any ringed site.

Here is my object/hypothesis/conclusion checklist, made against the node:

| Node item | Lean rendering and verdict |
| --- | --- |
| A prime ell | `(l : ℕ) [Fact l.Prime]` in both theorems. Exact. |
| Contextual ell different from p | Neither the category nor any defining condition refers to p or a scheme over a characteristic-p field. The recorded intrinsic dependency deliberately has no finite-field parameter. The instances quantify over every prime and therefore apply in each stipulated ell-different-from-p context. No change to coefficients or to Y is hidden here. |
| A finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. Exact; no embedding into a chosen algebraic closure is required. |
| Its valuation ring, uniformizer and positive finite quotients | The existing `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and `coefficientExtensionRing` are used through the dependency. The chosen uniformizer generates the maximal ideal; the quotient ideals are its powers. There is no new coefficient choice in this delivery. Exact. |
| An arbitrary scheme Y | `(Y : AlgebraicGeometry.Scheme.{u})`. No Noetherian, finite-dimensional, qcqs, invertibility, finite-type or nonempty hypothesis. Exact. |
| Ambient derived category of completed-coefficient modules | `DerivedCategory (scalarReductionSource.{u, u} l E Y)`. I opened `scalarReductionSource`: it is `SheafOfModules` over `completedIntegralCommRingSheafUnrestricted`, forgetting commutativity only, not replacing completion by a discrete constant ring. Exact. |
| The full subcategory D^b_c(Y,O_E) | The exact recorded `sfIntegralConstructible l E Y`, whose `.FullSubcategory` is `sfIntegralConstructibleCategory l E Y`. Exact. |
| Derived completeness of its objects | The predicate's first conjunct is `IsSfDerivedComplete l E Y K`: there is a product witness and a distinguished Roos triangle whose first arrow is `Pi.lift` of the actual `sfDerivedReductionUnit` components. I opened the unit and transition definitions: they use derived tensor/restriction adjunction and quotient maps characterized on K-flat representatives. It is not completeness for an arbitrary map or tower. Exact. |
| Every positive reduction is bounded constructible | The second conjunct uses `∀ n : ℕ`, `intrinsicFiniteTorsionConstructible l E (n+1) ... Y ((scalarReductionDerivedExtension ... n).obj K)`. The finite-torsion predicate asks finite cohomological support and constructibility of each cohomology sheaf. I opened its signature and body. Exact. |
| A single finite interval independent of the reduction level | `∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, ... ∧ proEtaleCohomologicalSupport ... ⊆ Set.Icc a b`. The existential bounds precede the universal level. Exact. |
| Contains a zero object | The main theorem gives `ObjectProperty.IsTriangulated`, which extends `ContainsZero`. I read the class at Mathlib `Triangulated/Subcategory.lean:182`. Exact. |
| Closed under isomorphisms | The separate `sfIntegralConstructible_isClosedUnderIsomorphisms` concludes `ObjectProperty.IsClosedUnderIsomorphisms (sfIntegralConstructible l E Y)`. It is a public instance, so the conclusion is available to the inherited API. Exact. |
| Closed under every integer shift | `ObjectProperty.IsTriangulated` extends `IsStableUnderShift ℤ`. This includes all positive, zero and negative shifts. Exact. |
| In each distinguished triangle, membership of the first and third vertices implies membership of the middle | `IsTriangulatedClosed₂` is the remaining superclass. Its raw field lands in iso-closure; with the companion instance, Mathlib `ObjectProperty.ext_of_isTriangulatedClosed₂` yields membership in the actual predicate. I read both declarations. Exact. |
| Inherited shift and ambient distinguished triangles | Mathlib's `Pretriangulated P.FullSubcategory` sets `distinguishedTriangles := P.ι.mapTriangle.obj ⁻¹' (distTriang C)` at lines 693--694; the inherited shift and inclusion shift comparison are the full-subcategory structures. Exact. |
| The subcategory is triangulated and its inclusion is exact | Mathlib `Subcategory.lean:719--723` supplies `P.ι.IsTriangulated` and `IsTriangulated P.FullSubcategory`; `P.ι.CommShift ℤ` is also inferred. Both required parts of exactness refer to this inclusion. Exact. |

Dependency-interface checks: in addition to the defining chain above, I opened
`KFlat`, `KFlatResolutionIndependentCoefficients`, and
`DerivedChangeOfRingsIndependentCoefficients`. The latter has separate site object,
morphism and coefficient universes, an actual ordinary change-of-rings functor,
a universal left derived pair with triangulatedness and counit isomorphisms on
K-flat complexes. Thus the node's derived reduction is neither ordinary tensor
with an unjustified flatness assumption nor a functor on a different category.
I also opened `integralReductionTowerWellDefined`, `integralReductionTower`,
`integralReductionTowerMap`, `integralReductionTowerCone`, and
`IsDerivedCompleteUnrestricted`. Their older finite-field-parameter presentations
are retained as proof-plan imports; they are not substituted for the intrinsic
predicate in either theorem. No unusable dependency is required as a new
hypothesis. There are no new nodes or dependency modules in this delivery, so
H12/H13 introduce no additional source reviews.

Edge cases checked against the definitions and the proof docstring:

- The empty scheme is permitted by the same binders and all predicates; no point,
  affine cover of positive size, or nonzero section is assumed.
- Zero has zero reductions and empty cohomological support, contained in [0,0].
  `ContainsZero` asserts existence of a zero object; isomorphism closure then
  includes every ambient zero object.
- The index n = 0 denotes exponent 1, not exponent 0. Every positive exponent is
  covered, with no accidental requirement at exponent 0. The tower index is ℕ,
  so there is no arbitrary possibly empty indexing family to exclude.
- The common bound permits a = b. For a shift m the bound is [a-m,b-m]; for an
  extension use [min(a',a''),max(b',b'')]. Zero outside vertices cause no exception.
- There is no characteristic assumption on Y. In particular the closure argument
  does not demand that ell be invertible on Y. The contextual p does not occur in
  any coefficient construction or closure property.
- `universe u` is bound, with E and Y in the dependency's common ambient size.
  Arbitrary smaller objects can be viewed in that common universe. Crucially the
  pro-etale site still has objects in u+1 and morphisms in u, with module values
  in u+1; these two site universes are not equated. No extra smallness instance
  appears in the theorem signature.

Independent searches actually run during this reading (recorded in
`searches.jsonl`), using different search terms from the worker:

- LeanFinder: "The full subcategory of adically complete constructible integral
  sheaf complexes is stable under extensions and suspension". Eight hits:
  light-condensed Grothendieck abelianness and generic derived t-structure bounds;
  none states this closure result.
- Loogle: `CategoryTheory.ObjectProperty.IsTriangulated,
  CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms`. Twelve hits, including
  intersection/inverse-image closure and finite-product instances. These are
  generic subcategory tools, not this coefficient predicate's instance.
- Mathlib grep: `constructible.*(extension|shift|[Tt]riang)|
  ([Aa]dic|[Rr]oos|[Cc]omplet).*([Tt]riang|[Ee]xtension)` returned 25 unrelated
  completion and p-adic norm hits. A targeted second grep in `Algebra/Homology`
  for `derived.?complete|[Cc]onstructible|[Rr]oos` returned zero hits.
- Direct `rg` of the project's `lean/Sheaf/Paper`, upstream `WeilConjectures`, and
  `dag/lean_names_upstream.json` for integral/complete/constructible triangulation
  and isomorphism closure. I opened the relevant candidates: upstream
  `DerivedCategory.isTriangulated_derivedCompleteIntegral` concerns constant
  coefficient sheaves and completeness alone; upstream pro-etale
  `DerivedCategory.isTriangulated_boundedConstructible` concerns finite constant
  coefficients and etale-origin complexes. The legacy
  `boundedConstructibleDerivedCompleteIntegral_isTriangulated` uses the old
  predicate and auxiliary finite-field datum. The PBC complete-constructible
  triangulation interface has additional Noetherian/dimension/invertibility
  hypotheses and a different property. None is this exact recorded predicate's
  unrestricted closure statement. Direct upstream search for the item id had no
  hit. The module should therefore be retained, not marked `existing: true`.

H5/H6/H8/H9: the delivered module defines no data and contains exactly two named
`by sorry` theorem proofs, both clauses of this owning node. Both docstrings
name the source and blueprint id. The main docstring follows all eight node
proof steps, including the canonical-unit Roos/local-completeness comparison,
exact reductions, the uniform interval, and inherited triangulation. The imports
retain the recorded statement/proof interfaces. No private copy, local notation,
local instance, hidden statement-level `let` or `show ... from` occurs. All Lean
lines are at most 100 characters; `autoImplicit false` and the explicit universe
bind every variable. The node's `lean.statement` equals the main theorem's
signature byte for byte, as independently checked by a script.

Findings and changes: no mismatch requiring a Lean or node repair was found.
I left the correct module and node record unchanged and added this independent
reading. There is no statement correction or new `statement_change`, and no
statement dispute.

Independent verification: the required `scompile.py NA
lem-weil-integral-constructible-triangulated` call compiled the delivered module
and the separate scratchpad inference probe in dependency order. Both completed
cleanly, with no warnings or errors (each Lean invocation approximately three
seconds). The probe independently inferred all ten interfaces listed in the
worker report, including inherited triangulation and exact inclusion. It is
outside `lean/` and is not delivered. The prescribed delivery dry run follows.
