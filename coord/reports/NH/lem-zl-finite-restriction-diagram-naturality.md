## Worker report

Item: `lem-zl-finite-restriction-diagram-naturality`, group NH, stage 2.
Module: `Sheaf.Paper.FiniteRestrictionDiagramNaturality`.

This module states semilinear naturality of the actual published finite exchange and
counit-germ restriction maps. It constructs the geometric transport, the three
natural transport comparisons and the two strict-system squares. It states the
commutativity of these squares as whole complexes and after coefficient evaluation,
strict Roos realization, derived total limit, raw rationalization, point sections
and common-stage inclusion. No proof is supplied: the seven named theorem bodies
are `sorry`, each with its source and natural-language proof in its docstring.
All definitions have real data. The choices used for the fibre isomorphism, point
permutation and sum transport come from theorems specifying them uniquely.

### Hypotheses and clauses

- The finite-field datum is `F : FiniteFieldDatum.{u}`; its recorded fields supply
  p, a, q, k₀ and its algebraic closure k. The prime and characteristic condition
  are `[Fact l.Prime]` and `hl : l ≠ F.p`.
- A finite extension E/ℚ_l is rendered by `E : Type u`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. The coefficient ring,
  uniformizer and positive quotient rings are those of the imported coefficient
  extension and completed coefficient modules. Natural index n means exponent n+1.
- `Diagram F.k` records the four schemes, their k-structure maps, f and f', and
  the two equations making f and f' morphisms over k. The theorem's instances
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on all four structure maps
  express separated finite type over the field. `[IsFinite G.f]` and
  `[IsFinite G.f']` are the finite morphism hypotheses.
- The point is exactly `G.y : Spec (.of F.k) ⟶ G.Y`. No equation requiring it to
  be a k-morphism is imposed. During review I removed such an extra equation;
  the stated geometric point is allowed to be any scheme morphism from Spec k.
- S, v and h are the Mathlib pullback and its projections. `FiniteCounitTowers.Points`
  is exactly `{x // x ≫ f = y}`, and `FiniteCounitTowers.lift` is the canonical
  lift i_x. The first two conclusions assert finiteness of both point sets.
  The imported `pointSum` is the finite product in the abelian category, hence the
  canonical finite direct sum, including its empty zero object.
- `Diagram.sigma` is an arbitrary ring equivalence k ≃+* k. The fields
  `semilinearX`, `semilinearY`, `commutes` assert the three diagram equations.
  There is no condition concerning k₀. `c` is the induced automorphism of Spec k,
  and `y'` is exactly c⁻¹ ≫ y ≫ w in Lean's order of composition.
- `geometry` and `fibreIso` specify the fibre isomorphism by both projections:
  t ≫ v' = v ≫ u and t ≫ h' = h ≫ c. `points_existsUnique`/`points` specify
  x' = c⁻¹ ≫ x ≫ u. `point_paths` includes t i_x = i_x' c as an equality of maps.
- Input is written on X', with the unprimed representative its pullback by u.
  This is equivalent to the node's input on X transported by the inverse
  equivalence: u is an isomorphism and every primed input is covered.
- `paths` uses the published finite-level composition isomorphism, including its
  adjunction normalization. `pushSquare` is the actual mate, not an arbitrary
  map. `source`, `middle` and `stalk` use these comparisons and the geometric
  equations. The theorem asserts that the source, middle and sum comparisons
  are isomorphisms.
- `sum_existsUnique` fixes every projection of the sum comparison: the x-component
  is first the projection at `points G x`, pulled back by c, and then exactly
  `(stalk l E G x).hom`. Thus the permutation and each stalk map are specified;
  the coefficient field is not acted on by sigma.
- `exchangeSquare` uses precisely `FiniteCounitTowers.b`; `restrictionSquare`
  uses precisely `FiniteCounitTowers.r`. Their sides are the termwise three
  transport maps. The first universal conclusion asserts `CommSq` of each
  entire strict-system complex square. The following universal level clause
  applies `level` for every positive quotient exponent.
- These are maps on the ringed sequence site, not a collection of independently
  chosen level maps. Consequently their components commute with every quotient
  transition. They are natural transformations of complexes, so they commute
  with the cochain differentials as well.
- `roos` applies restriction of scalars to the entire system, converts the
  complex of diagrams to the diagram of complexes and applies the published
  signed Roos functor. Its two conclusions are equalities on whole Roos
  complexes. `PodCompletionReindex.Laws`, asserted for c, u, w and t, explicitly
  retains the product projection comparison, 1-s, both cone coordinates,
  quotient transitions and total-limit normalization. This retains the actual
  countable product/cone construction rather than merely checking its levels.
- `completed` applies `DerivedCategory.Q` and the published
  `coefficientSequenceLimit` to the four actual arrows. Its two commuting-square
  conclusions are before point sections. These are the total-limit realizations
  of the finite exchange and germ maps; the finite-level composition in `paths`
  and the reindexing laws fix the completion normalization. The source's
  reconstruction and substitution arguments identify these presentations with
  Ly*Rf*, Rh*Lv* and the finite sum of Lx*; no arbitrary identification is added.
- The representative clause explicitly binds K in `sfIntegralConstructibleCategory`,
  a complex Q over the completed coefficient sheaf, its independent-coefficient
  K-flat condition, termwise site flatness, and the representative isomorphism.
  It binds T, its quotient isomorphisms κ and whole-system comparison eT, and uses
  exactly `CoefficientReductionPresentation` from the published calculus.
  Thus it concerns actual strict derived quotients on one representative.
- For these representatives the theorem supplies constructibility of all vertices
  of both completed squares. `Square.restrict` keeps the same arrows in the full
  constructible subcategory. `sfRationalConstructibleLocalization` is the raw
  Hom localization, with no Karoubi envelope, and the two resulting square
  equalities are explicitly stated. The next two clauses apply the prescribed
  `pointRationalFibre F l hl E`.
- `inputNaturality` states the chain-map naturality equations for b, r and every
  individual counit-germ component. On sections the third equation is exactly
  a(m restricted to i_x) = a(m) restricted to i_x. The transport comparisons are
  themselves natural transformations. The strict equations therefore pass to
  roofs and their scalar-linear extensions as explained in the proof docstring.
- `finiteRestrictionDiagramNaturality_commonStage` quantifies over every finite
  coefficient stage A in Ω, uses the actual stage coefficient model, and states
  the two square equations after the published common-stage inclusion and then
  `pointQbarFibre`. The disjunction selecting S ranges over exactly the exchange
  and restriction square, preserving their actual arrows. The inclusion uses
  the recorded common-stage equivalence relation, so these are equalities of
  common-stage classes, independent of the chosen finite representative.
- Taking sigma to be the identity is permitted by the same declarations. In that
  case c and the point formulas specialize to ordinary diagram naturality.

### Dependencies used

The original statement dependencies were read with their recorded declarations,
including Mathlib matches. The following are the principal interfaces actually used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its imported coefficient
  construction: `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer`, `Padic.coefficientExtensionRing`.
- Mathlib `AlgebraicGeometry.Morphisms.Finite` and the morphism property modules:
  `IsFinite`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`.
- Mathlib pro-etale site and pullback: `Scheme.ProEt`, `Scheme.ProEt.topology`,
  `Limits.pullback`, its projections and `pullback.lift`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `completedIntegralCommRingSheafUnrestricted` and canonical quotients.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` (and its public dependency
  `IntegralDerivedOperations`): `integralDerivedPullback`, the scalar reduction
  modules and the published strict Roos realization.
- `Sheaf.Paper.SfDerivedDirectImage`: the prescribed reduction-tower direct image;
  the maps here are its finite-system/total-limit presentation.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleLocalization`, the raw scalar localization.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`, `pointQbarFibre`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `AlgebraicallyClosedCoefficients.Index`, `.Coefficient`,
  `GeneralAlgebraicallyClosedCoefficients.inclusion`.
- `Sheaf.Paper.LocalFrobeniusTrace`: the prescribed point/stalk and pullback
  composition conventions; no additional Frobenius datum is assumed here.
- `Sheaf.Paper.FiniteCounitRestrictionTowers`:
  `FiniteCounitTowers.pull`, `push`, `adj`, `Points`, `lift`, `pointSum`,
  `component`, `b`, `r`, `B`, `C`, `D`, `level`, `restricted` and their additive
  instances. This node landed while I was working; the current source was read
  locally and checked through `scompile.py --source` before using it.
- `Sheaf.Paper.IntegralComparisonSequenceSystems`:
  `integralComparisonSequenceComposition`, normalized by the direct-image mate.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus`, `CoefficientReductionPresentation`,
  `coefficientSequenceLimit` and the recorded sequence module categories.
- `Sheaf.Paper.PodCompletionReindexModels`: `PodCompletionReindex`, its `Laws`,
  the whole product, Roos and normalization interfaces.
- Mathlib `CommSq` is used for commutativity. The local `Square` is only data of
  four arrows without any commutativity proof, to be realized under functors;
  Mathlib's `CategoryTheory.Square` already assumes the equality being stated.

The last four landed statement interfaces were added to `stmt_deps`. All other
fields of the node, apart from `lean`, are unchanged. No new independent notion
or dependency repair module is needed. The plain proof imports are the published
isomorphism inverse-image, isomorphism-field transport, completion reindexing,
completed-operation substitution and scalar-extension pullback identities modules.
The reconstruction and coefficient-descent nodes are used in the natural-language
proof, not as unstated hypotheses of the Lean theorem.

### Edge cases and size check

Empty X or an empty fibre is allowed: there is no `Nonempty Points` hypothesis,
and all transports are fixed by product projections even for the empty product.
A singleton fibre gives its one stalk map. Nonreduced fibres are retained as the
scheme pullback; the construction never replaces them by their set of points.
Zero and unbounded representatives are allowed in the strict-system clause;
bounded constructibility is used exactly for rationalization of their realizations.
The index zero is coefficient exponent one, never the zero coefficient ring.
Every field automorphism is covered, including one not fixing k₀ and the identity.
No equality between site object and morphism universes is imposed: the small
pro-etale site has objects in u+1 and morphisms in u, and modules in u+1. The named
canonical size witness uses `essentiallySmallSelf.{u}`. Coefficients and the finite
field datum use a common containing universe, as in the recorded finite-counit and
point-fibre interfaces; smaller fields can be placed in that universe.

### Searches and validation

- `msearch.py ... leanfinder`: “Finite morphism fibre restriction counits commute
  with semilinear diagram isomorphisms and permutation of geometric point summands”.
  Eight hits concerned Galois fibres, topological fibres and locally constant
  functions; none asserted this strict-system/completion diagram.
- `msearch.py ... loogle`:
  “CategoryTheory.Adjunction.counit_naturality, CategoryTheory.NatTrans.naturality”.
  No exact hit. Generic naturality does not specify these maps or their completion.
- `msearch.py ... grep`: “semilinear|counit_naturality” in CategoryTheory.
  The returned adjunction naturality lemmas are generic tools, not this statement.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for finite-restriction/semilinear
  counit transport and the node id found no exact declaration. The relevant newly
  published finite-counit module was reused instead of copied. A further Mathlib
  search for square structures found `CategoryTheory.Square` (already commuting)
  and `CommSq`; the latter is used directly as the conclusion predicate.
- `scompile.py NH lem-zl-finite-restriction-diagram-naturality <module>` compiled
  both the sandbox form and the final library namespace cleanly; only stage-2
  `sorry` is present. No local or global library build was run.

No statement correction, disputed statement or unresolved node fault is reported.

## Second reading by NH

Written by the maintainer's independent second reader (cc review service, 2026-10-25),
replacing the delivered section, which said that no independent reading had been made.
The node was read against module `Sheaf.Paper.FiniteRestrictionDiagramNaturality` at
27f83eaf. Each clause is followed by the Lean that renders it and a verdict.

1. Fixed data: p, q, k₀, k come from `F : FiniteFieldDatum.{u}`. The prime is `l` with
   `Fact l.Prime` and `hl : l ≠ F.p`. E/ℚ_ℓ is finite (`[Field E] [Algebra ℚ_[l] E]
   [FiniteDimensional ℚ_[l] E]`). A_n has exponent n+1. OK.
2. X, Y, X', Y' are separated and of finite type over k: `Diagram.aX…aY'` carry
   `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`. f and f' are finite
   (`IsFinite`) and lie over k (`over_eq`, `over_eq'`). OK.
3. σ is an arbitrary `k ≃+* k`, and u and w are scheme isos. `semilinearX/Y` render
   semilinearity over c = Spec σ, and `commutes` renders f'u = wf. No k₀ condition is
   imposed. OK.
4. y is any `Spec k ⟶ Y`. This is no stronger than the node's geometric point (the
   k-linearity was dropped). The geometric arguments do not use k-linearity. OK.
5. y' = w y σ_s⁻¹ is rendered by `y' := c.inv ≫ y ≫ w.hom`. This is consistent with
   the semilinearity direction: x' ≫ aX' = c⁻¹ ≫ x ≫ aX ≫ c. OK.
6. The transport S ≅ S' is `geometry`/`fibreIso`, an ∃! iso fixed by both projection
   equations (v't = uv, h't = ch). The bijection P_y ≃ P_{y'} is `points_existsUnique`,
   with x' = c⁻¹ x u. `point_paths` gives c x' = x u and t i_x = i_{x'} c. All three
   were checked by hand from the pullback universal property. OK.
7. The transport comparisons:
   - T_B (`source`) is the paths iso c*y'* ≅ y*w* followed by the counit mate of
     paths(f,w,u,f').
   - T_C (`middle`) is the mate of paths(h,h',t,c) followed by t*v'* ≅ v*u*.
   - T_x (`stalk`) is paths(c,x',x,u).
   - The sum map (`sum`) is ∃!, pinned by every projection: c*π_{x'} ≫ T_x. This is
     exactly the permutation together with the stalk transports, and there is no
     coefficient action of σ.
   All of these use the published `integralComparisonSequenceComposition` and
   `FiniteCounitTowers.adj`, with the same mate convention as `FiniteCounitTowers.exchange`.
   OK.
8. b_n ↦ b'_n and r_{n,x} ↦ r'_{n,x'}: `exchangeSquare` (top c*b', bottom b(u*T),
   sides T_B, T_C) and `restrictionSquare` (top c*r', bottom r, sides T_C and the sum
   map). Both are stated `.Commutes` (Mathlib `CommSq`) on whole complexes of strict
   sequence systems, for every T. The x-component of the second square is
   T_x c*(r'_{x'}) = r_x T_C. OK.
9. Compatibility with quotient transitions, levels, products, Roos differential and
   projections: maps on the sequence site retain the transitions. The `level n`
   clauses and the `roos` clauses state these as whole Roos complexes. OK.
10. Completed derived category over s: `completed` (Q, then
    `coefficientSequenceLimit`). The normalization holds by construction, because the
    sides are the finite-level composition maps. The four `∃ R, Laws` clauses repeat
    the reindexing lemma for c, u, w, t. They are redundant but true (advisory). OK.
11. Raw rationalization and point sections: there is a representative clause (K
    constructible, flat K-flat Q, a `CoefficientReductionPresentation` T). It gives
    ∃ constructibility of the completed vertices. It then gives commutativity after
    `sfRationalConstructibleLocalization` (raw, no Karoubi) and after
    `pointRationalFibre`. OK.
12. Common stage: `finiteRestrictionDiagramNaturality_commonStage` applies to every
    A in Ω, through `GeneralAlgebraicallyClosedCoefficients.inclusion` and then
    `pointQbarFibre`. OK.
13. Input naturality, a(m|_{i_x}) = a(m)|_{i_x}: `inputNaturality` (b, r and each
    `component`). OK.
14. σ = id is a special case of the same declarations. OK.

Edge cases:
- The empty P_y is covered: the empty product gives the zero object, and the sum map
  is unique.
- Singleton and nonreduced fibres are covered, since S is the scheme pullback.
- σ not fixing k₀ and the empty X are covered.
- Index n means exponent n+1, so the zero ring never occurs.
- Universes: the site has objects in u+1 and morphisms in u. `canonicalSiteSmall` is a
  Prop instance, so it cannot create a data diamond.

Dependencies:
- The four added stmt_deps had landed on the base.
- The theorem stmt_dep lem-zl-finite-counit-restriction-towers is genuine. B and C need
  its `push_additive` theorem (instance `pushAdditive`), D needs `pointSum_additive`,
  and finiteness of the points is its `finitePoints`.
- The theorem stmt_dep lem-coef-derived-system-evaluation-calculus is genuine. The
  statement uses `coefficientDerivedSystemEvaluationCalculus.choose`.

Searches: a grep of the live lean/Sheaf and dag found no other declaration of this
naturality. Nothing was changed in the Lean or the node record.
