## Worker report

The item is stated in `Sheaf.Paper.GeometricStalkPerfect`, with four theorem declarations and the canonical field-stalk helper:
`AlgebraicGeometry.Scheme.finiteTorConstructible_proEtale_stalk_finiteFree`,
`AlgebraicGeometry.Scheme.finiteTorConstructible_etale_stalk_finiteFree`,
`WeilConjectures.rationalConstructible_stalk_perfect`, and
`WeilConjectures.commonStageConstructible_stalk_perfect`.
Every theorem has proof `sorry`; every definition has actual data. There is no statement
correction and no statement dispute.

I read the entire item and its proof, every direct statement-dependency node, and the
recorded declarations and docstrings. The original blueprint Markdown is absent from
this checkout, but I located and read the identical source at the read-only blueprint
archive, `sec-smooth-purity/sk-prop-sf-trace-perfectness/fix-lem-finite-tor-perfect.md`,
including the finite-free resolution and field-coefficient paragraphs. I also read
Stacks `proetale.tex`, the points section including the neighbourhood definition and
Tag 0993, to check the strict-localization/product assertion used in the proof plan.

Each assertion is stated on an arbitrary cochain representative K, with the relevant
predicate applied to `DerivedCategory.Q.obj K`. This does not require a bounded complex
of finite terms as input. Every derived object has a cochain representative, and all
hypotheses are properties of its image in the derived category. The conclusion is an
isomorphism in the derived category, which is exactly the stated quasi-isomorphism
class assertion, rather than a demand for a single quasi-isomorphism in one direction.

Hypotheses and clauses of the finite-coefficient assertions:

- The fixed prime is `(l : ℕ) [Fact l.Prime]`.
- The finite coefficient extension is `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The actual quotient ring is
  `Padic.coefficientExtensionRing l E n`, lifted by `ULift.{u+1,u}` only to put modules
  in the site's coefficient universe. The positive exponent is `n` with `hn : 1 ≤ n`.
- The scheme and geometric point are `{Y : Scheme.{u}}`, `{Ω : Type u}`, `[Field Ω]`,
  `[IsAlgClosed Ω]`, and `y : Spec (.of Ω) ⟶ Y`.
- On the coefficient site K is a cochain complex of modules over the exact constant
  commutative-ring sheaf, with commutativity forgotten, of `proEtaleDerivedCategory`.
  The hypothesis `WeilConjectures.finiteTorConstructible l E n hn Y (Q.obj K)` is the
  recorded conjunction of intrinsic bounded constructibility and finite Tor amplitude.
  In particular the Tor condition tests every module sheaf, not just finite modules.
- The pro-etale stalk complex is the termwise image under
  `finiteCoefficientModuleStalkFunctor y ...`. This is the original pointed-neighbourhood
  module colimit, restricted along the existing `proEtaleConstantRingGerm`, so it is a
  module over the original coefficient ring. No unrelated linear action is supplied.
- The bounded finite-free model is the existential complex P with integer bounds a,b,
  `P.IsStrictlyGE a ∧ P.IsStrictlyLE b`, and, in every degree, both `Module.Free` and
  `Module.Finite` over that same lifted quotient ring.
- `Nonempty (Q.obj (stalkComplex K) ≅ Q.obj P)` renders the quasi-isomorphism assertion.
- On the small etale site K instead belongs to
  `CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat ...)) ℤ`.
  `Etale.DerivedCategory.boundedConstructibleFiniteTor` is the existing small-etale
  conjunction of bounded constructibility and the derived-tensor finite-Tor predicate.
  Its stalk is precisely `(pointSmallEtale y).ulift.sheafFiber`, applied termwise.
  The same finite-free, boundedness, and derived-isomorphism clauses follow, now for
  this etale stalk. Thus no pro-etale condition is substituted for the etale hypothesis.

Hypotheses and clauses of the field assertions:

- At stage E, K is an arbitrary integral cochain representative and
  `sfIntegralConstructible l E Y (Q.obj K)` is its only membership hypothesis. This is
  the actual derived-complete integral category, with every positive reduction
  constructible and a single ordered common cohomological interval. There is no
  additional finite-Tor hypothesis at the integral or field stage.
- The representative formulation uses exactly the objects in the source: raw
  rationalization has the same objects as the integral category. It is not replaced by
  the derived category of discrete E-sheaves. No rationalization morphism, triangle, or
  category structure is needed to express this objectwise assertion. The current node
  records for rationalization and algebraically closed coefficients have no Lean
  declarations, and the server source lookups for both natural module names were
  unavailable; no nonexistent declarations are imported. I checked delivered Q09
  branches as well; neither contained these two definitions. The unused category
  structures need not be rebuilt to quantify over their actual integral representatives.
- `fieldGeometricStalkComplex l E y E (RingHom.id E) K` is the geometric module stalk
  of this integral representative with its canonical O_E action, followed by termwise
  scalar extension along the actual inclusion O_E → E. Flatness of localization
  makes termwise extension equal to derived scalar extension. This is the source's
  rational stalk of the representative. Its definition chooses no perfect model.
- The rational conclusion exhibits a P over `ULift E`, strict integer bounds, finite
  dimensionality `FiniteDimensional (ULift E) (P.X i)` in every degree, and the derived
  isomorphism from the rational stalk complex to P. The final conjunction explicitly
  asserts `DerivedCategory.IsPerfect` of that stalk.
- For the common-stage assertion F is a fixed algebraic closure, expressed by
  `[Algebra ℚ_[l] F] [IsAlgClosure ℚ_[l] F]`.
  `E : Padic.FiniteCoefficientFields l F` is any finite field of definition, and K has
  the same integral membership predicate over E.val. These are exactly the pairs
  of objects in the raw common-stage category; no retract or idempotent completion
  is introduced. There is no restriction on which finite stage represents the object.
- The map into F is the actual subfield inclusion `E.val.subtype`.
  `fieldGeometricStalkComplex l E.val y F E.val.subtype K` is consequently the
  scalar-extended geometric stalk of that pair. The conclusion gives a bounded model
  with finite-dimensional F-terms and separately asserts its perfectness over F.
  Lifting F changes only its carrier universe and excludes no characteristic or degree.

The module and declaration dependencies used are:

- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`;
  it uses `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` /
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible` and
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude` /
  `AlgebraicGeometry.Scheme.HasFiniteProEtaleTorAmplitude`, whose tensor computations
  use the recorded `Sheaf.Algebra.Homology.DerivedTensor` / `Scheme.derivedTensor`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` / `Scheme.proEtaleDerivedCategory`:
  the same constant ring sheaf and standard localization used by the hypotheses.
- `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk` / `Scheme.proEtaleGeometricStalkRing`,
  `Scheme.proEtaleGeometricModuleStalk`, `Scheme.proEtaleGeometricNeighbourhoodForget`,
  `Scheme.proEtaleGeometricStalkRingDiagram`, with the functorial extension in this packet.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk` /
  `Scheme.proEtaleConstantRingGerm`: the fixed finite-coefficient scalar action.
- `Mathlib.CategoryTheory.Sites.Point.Basic` / `Point.sheafFiber` and
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint` / `Scheme.pointSmallEtale`: etale stalks.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` /
  `Etale.DerivedCategory.boundedConstructibleFiniteTor`: the corresponding etale hypothesis.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` imports the original
  `Padic.coefficientExtensionRing`, `coefficientExtensionIntegers`, and
  `coefficientExtensionIdeal`; no coefficient construction is copied.
- `Sheaf.Paper.SfIntegralConstructible` / `WeilConjectures.sfIntegralConstructible` and
  the existing `scalarReductionSource`: the actual completed integral coefficient
  category and the precise intrinsic constructibility condition.
- `Sheaf.Paper.CompletedIntegralCoefficients` /
  `completedIntegralCoefficientSheafUnrestricted`, `integralCoefficientSheafSystem`,
  `integralCoefficientSheafTransition`, `completedIntegralCommRingSheafUnrestricted`:
  the same completion, re-exported with its canonical constant-scalar map in this packet.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields` / `Padic.FiniteCoefficientFields`
  and its finite-dimensionality instance: the common-stage field of definition.
- `WeilConjectures.CategoryTheory.DerivedCategory.Perfect` / `DerivedCategory.IsPerfect`:
  bounded finite-projective models over the field, used without redefining perfectness.
- Mathlib `SheafOfModules.forget`, `PresheafOfModules.pushforward₀`,
  `PresheafOfModules.colimitFunctor`, `ModuleCat.restrictScalars`,
  `ModuleCat.extendScalars`, `Functor.mapHomologicalComplex`, and `limit.lift` supply
  the actual functors, complexes, scalar maps, and limit construction.

The existing stated proof dependencies are imported without `public` where they are
not already public statement dependencies: derived completeness/reduction,
classical pro-etale stalk, etale stalk tensor, K-flat change of rings, derived-limit
products, DVR structure, constant etale stalks, canonical derived tensor pullback,
and perfect reconstruction. Unstated proof-only nodes have no module to import;
their content remains in the supplied natural-language theorem proofs. No proof import
is deliberately omitted to change the proof route.

Edge cases checked: the zero complex and points outside the support give a rank-zero
model; no nonzero-rank or Nonempty hypothesis is imposed on a module. The empty scheme
has no geometric point, so every assertion is vacuous there. At n=1 the finite ring is
the residue field. At n>1 a finite-cohomology complex need not be perfect (e.g. the
residue field over O_E/(pi²)), which is why finite Tor amplitude is retained. n=0 is
excluded as in the source. No common stratification over all reductions or extra Tor
bound is assumed for the integral representative. Every finite field of definition is
allowed, including the base field; the algebraic closure is fixed but otherwise arbitrary.

Searches actually run:

- `msearch.py ... leanfinder "geometric stalk of bounded constructible complex of finite
  Tor amplitude is perfect"`: eight generic boundedness/derived-category hits, no exact
  geometric-stalk perfectness statement.
- `msearch.py ... loogle "DerivedCategory.IsPerfect, finiteTorAmplitude"`: zero hits,
  unknown identifier `DerivedCategory.IsPerfect` in Mathlib. The project-specific
  declaration was found and read in upstream `DerivedCategory/Perfect.lean`.
- `msearch.py ... grep "finiteTorAmplitude|stalk.*[Pp]erfect" Algebra`: zero Mathlib hits.
  A direct rg of the same concepts in Mathlib/Algebra likewise found no exact match.
- `msearch.py ... leansearch "geometric stalk bounded constructible finite Tor amplitude
  perfect"`: service unavailable, Internal Server Error; no successful LeanSearch
  result is claimed.
- `msearch.py ... loogle "PresheafOfModules.colimitFunctor"`: four hits including
  the module colimit functor and its adjunction. Those definitions were opened and
  reused, rather than reproducing their colimit-module operations.
- `msearch.py ... leanfinder "canonical map from constant ring sheaf to inverse limit of
  quotient ring sheaves"`: eight hits on Spec structure sheaves, tilde localization,
  and adic-completion evaluation maps; none constructs this constant-to-completed
  coefficient sheaf map.
- Direct rg in upstream WeilConjectures, Mathlib, the upstream name index and lean/Sheaf
  for the item id, stalk/perfectness terms, and every newly introduced declaration name:
  no exact whole-item theorem or competing new helper declaration. The existing
  `DerivedCategory.isPerfect_of_finiteTorAmplitude` was opened; it is an algebraic
  criterion, not either site's stalk theorem or the two field clauses.
- `scompile.py --source Sheaf.Paper.RationalizationKaroubi` and
  `--source Sheaf.Paper.AlgebraicallyClosedCoefficients`: module source unavailable.
  These missing category structures are not used as a stand-in or as an extra hypothesis:
  the objectwise field assertions quantify over the representatives specified by their
  source definitions, as explained above.

All three delivered modules compile cleanly through scompile.py, separately in dependency
order, under both the sandbox and final library module names. The scalar-extension
additivity instance is obtained from the explicit extension/restriction adjunction at
the recorded coefficient universe. The required final check is deliver2.py --no-push;
the independent second reader supplies the second-reading section and delivers.

## Dependency modules

`def-weil-proetale-geometric-stalk`: the old module defines the actual colimit objects,
including their module scalar action, but supplies no functor on module morphisms with
additivity available to form cochain complexes. The new module
`Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor` publicly imports that module and
reuses precisely its `PresheafOfModules.colimitFunctor` construction. It adds the
functor and its named additivity obligation, plus restriction along the already
recorded finite-coefficient constant germ. The additivity theorem is a construction
property of the node's module stalk, with its full proof in its docstring. No alternative
stalk, neighbourhood category, ring colimit, or scalar action is defined.

`def-weil-completed-integral-coefficients`: the old interface has the inverse-limit
coefficient sheaf and all quotient projections but lacks the constant integral-scalar
map needed to take its module stalk over O_E. The new module
`Sheaf.Paper.CompletedIntegralCoefficientGerm` publicly imports the exact old completion,
defines the actual quotient maps, states their compatibility as the named construction
obligation, forms the cone and its actual `limit.lift`, and applies the pointed-
neighbourhood colimit map to obtain the integral constant germ. Restriction along this
map provides the canonical integral module-stalk functor; no arbitrary ring map or
mere Nonempty choice is substituted. This existing node and the already landed
`def-weil-finite-subextension-directed-set` are added to the item's statement dependencies.

`def-weil-derived-complete-integral-detailed`: its record still points to the old
predicate requiring an auxiliary finite-field datum D and l ≠ D.p, which the item
never supplies and which do not occur in the intrinsic condition. The existing landed
`WeilConjectures.sfIntegralConstructible` in `Sheaf.Paper.SfIntegralConstructible` gives
exactly the same completion/reduction/constructibility/uniform-interval predicate
without those unused parameters, and is already used by the recorded finite-Tor module.
The node is repaired only in lean, as existing:true, with this explanation in lean.note;
no new module or second integral category is introduced.

## Second reading by Q19

I did not write the module. I read the node and the archived blueprint source
`/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-trace-perfectness/fix-lem-finite-tor-perfect.md`
with the three delivered modules open. The source statement agrees verbatim with the
node statement; there is no statement correction and no citer audit is required.
For the stalk construction I independently read Stacks `proetale.tex`,
`section-points`, `lemma-cofinal-etale` (0F6B), the following stalk definition,
and `lemma-classical-point` (0993). These explicitly use pointed weakly etale
neighbourhoods, assert exactness, and identify evaluation on strict localization.
The main source assumes no Noetherian, finite-type or nonempty condition on Y.
Its coefficient notation uses a prime, a finite extension, and positive exponent.

My object/hypothesis/conclusion inventory and its Lean match is as follows.

1. **Prime and finite field extension.** `(l : ℕ) [Fact l.Prime]`,
   `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`
   render exactly the coefficient stage. `Padic.coefficientExtensionRing l E n`
   is the recorded quotient of its actual valuation ring by the chosen uniformizer
   ideal power. The `ULift` is a ring equivalence and changes only size. Verdict: exact.
2. **Finite positive exponent.** `(n : ℕ) (hn : 1 ≤ n)` in the pro-etale theorem,
   and `_hn : 1 ≤ n` in the etale theorem. Every positive exponent is allowed,
   including the residue field at one. Verdict: exact.
3. **Scheme and geometric point.** The section binds `{Y : Scheme.{u}}`,
   `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`, and every assertion binds
   `y : Spec (.of Ω) ⟶ Y`. These are precisely a scheme and a geometric point
   within the recorded size bound. No geometric property of Y or its point is
   added. The implicit variables are explicitly declared, with autoImplicit false.
   Verdict: exact.
4. **The pro-etale coefficient category.** `K` is an arbitrary cochain complex of
   `SheafOfModules.{u+1}` on `ProEt.topology Y`, over the constant CommRingCat
   sheaf followed by forget₂ to RingCat. I opened `proEtaleDerivedCategory`,
   `ProEtaleGeometricStalk`, `IntrinsicFiniteTorsionConstructibility`, and
   `FiniteTorAmplitude`; this is the very same module category and localization,
   not a category of discrete integral modules. Verdict: exact.
5. **Bounded constructibility and finite Tor amplitude.**
   `hK : finiteTorConstructible l E n hn Y (DerivedCategory.Q.obj K)` unfolds
   into `intrinsicFiniteTorsionConstructible` and `HasFiniteProEtaleTorAmplitude`.
   I checked the latter in `ProEtaleTorAmplitude.lean`: one ordered interval
   works for every module sheaf in degree zero and every K-flat representative,
   with no finiteness restriction on test modules. The constructibility predicate
   imposes finitely many nonzero cohomology sheaves and the actual locally constant
   finite-stalk stratification condition. Verdict: exact, with neither condition dropped.
6. **The pro-etale stalk and its scalars.** The termwise functor is
   `finiteCoefficientModuleStalkFunctor y (Padic.coefficientExtensionRing l E n)`.
   Its underlying module is the dependency's pointed-neighbourhood colimit, and
   its scalar action is restricted along the existing `proEtaleConstantRingGerm`.
   I compared its formula with `proEtaleGeometricModuleStalk` and opened the germ
   construction in `ProEtaleConstantSheafStalk.lean`. The ring, point, diagram and
   common-refinement action agree. Verdict: exact, with no arbitrary action.
7. **Bounded finite-free model.** `∃ (P : CochainComplex (ModuleCat ...) ℤ)
   (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b` imposes actual termwise
   bounds; `∀ i, Module.Free ... (P.X i) ∧ Module.Finite ... (P.X i)` imposes
   finite freeness, with ranks permitted to vary and be zero. The final
   `Nonempty (Q.obj (stalkComplex K) ≅ Q.obj P)` is exactly representation of
   the stalk's quasi-isomorphism class in D(Λ). It does not assert finite free
   terms of the original representative. Bounds come after K and may depend on
   K and y, as in the node. Verdict: exact.
8. **Small-etale assertion.** The second theorem uses
   `Sheaf Y.smallEtaleTopology (ModuleCat ... )`, the recorded upstream
   `Etale.DerivedCategory.boundedConstructibleFiniteTor`, and precisely
   `(pointSmallEtale y).ulift.sheafFiber`, applied termwise. I opened upstream
   `Coefficients.lean`, `Constructible.lean` and `TorAmplitude.lean`, and Mathlib
   `Sites/EtalePoint.lean` and `Sites/Point/Basic.lean`. The predicate is bounded
   constructible homology plus the derived tensor test with every etale module
   sheaf. The fibre is the colimit over pointed etale neighbourhoods. The same
   bounds, finite freeness and derived-isomorphism conclusion appear. Verdict: exact;
   the pro-etale notion has not been substituted for the etale one.
9. **Rational-stage bounded constructible object.** The field theorem uses any
   complex K in the actual `scalarReductionSource` and precisely
   `sfIntegralConstructible l E Y (Q.obj K)`. I opened its definition and
   `SfDerivedComplete.lean`: completeness is the triangle with the canonical
   reduction units, every positive reduction is constructible, and one ordered
   cohomological interval works for all reductions. There is no integral Tor
   assumption. The rationalization node states that raw scalar localization has
   exactly these integral objects; no idempotent completion occurs. Quantifying
   over every cochain representative covers every such derived object, since
   the derived category is the localization of this cochain category. It adds
   no representative boundedness or termwise finiteness assumption. Verdict: exact.
10. **Actual rational geometric stalk.** `fieldGeometricStalkComplex ... E
    (RingHom.id E) K` first takes the integral module stalk with its canonical
    O_E action, then extends along the lifted actual inclusion O_E → E.
    The functor is constructed from the recorded module colimit and
    `ModuleCat.extendScalars`; it selects no model. Flatness of the fraction
    field makes termwise scalar extension compute derived scalar extension
    for every representative K. Verdict: the specified rational stalk.
11. **Field-model and perfectness conclusions.** The rational theorem exhibits
    a P over `ULift E`, two strict term bounds and finite dimensionality in each
    degree, together with an isomorphism of its derived image to the field stalk.
    It also asserts `DerivedCategory.IsPerfect` of that same stalk. I opened
    upstream `DerivedCategory/Perfect.lean`: this means a bounded finite-projective
    model, not a different notion of perfection. Over a field the exhibited
    finite-dimensional model is finite free, hence projective. Verdict: both clauses.
12. **Common-stage object and field.** The last theorem takes any algebraic
    closure `[IsAlgClosure ℚ_[l] F]`, any
    `E : Padic.FiniteCoefficientFields l F`, and any integral representative K
    with the same constructibility predicate at E.val. I opened
    `FiniteCoefficientFields.lean`; these are exactly all finite intermediate
    coefficient fields, including the base field. The common-stage node has
    pairs as objects and no additional retract objects. Thus these binders cover
    every object of that category, without requiring its morphism/triangle
    infrastructure for this objectwise assertion. Verdict: exact.
13. **Common-stage stalk and conclusion.** The helper uses the actual inclusion
    `E.val.subtype : E.val →+* F`. The conclusion exhibits a bounded complex
    with finite-dimensional F terms in the same derived isomorphism class and
    explicitly asserts perfectness. It imposes no extra Tor hypothesis at F.
    Verdict: exact; it includes all finite fields of definition.

Dependency repairs were independently checked too. There are no new definition nodes.
The pro-etale dependency module publicly imports the original colimit definitions;
its functor's object formula is that exact existing construction, with its induced
maps. Its additivity obligation is a named theorem with a natural-language proof,
not data selected by a sorry existence assertion. The finite-coefficient specialization
restricts scalars along the canonical germ already in the library. The completion
module publicly imports the exact inverse-limit coefficient sheaf. Its cone legs
are the genuine quotient maps at exponents n+1, with a named compatibility theorem;
`limit.lift` constructs the constant-to-completed map. `colim.map` then constructs
its germ, and restriction of scalars supplies the integral stalk action. No second
completion, ring identification by choice, or unrelated homomorphism is used.
For the existing:true integral predicate repair, I opened both the previous
`boundedConstructibleDerivedCompleteIntegral` record and the landed
`sfIntegralConstructible` declaration. The latter retains exactly completeness,
constructibility of every positive reduction and a common ordered interval,
while eliminating the unused auxiliary global finite-field parameters. This is
also the actual predicate used by the current finite-Tor dependency. Each repaired
record includes its reason; no dependency statement is altered.

Edge cases: the zero complex and zero ranks satisfy the conclusions; neither a
nonzero stalk nor a basis of positive rank is assumed. An empty scheme admits no
geometric point and the statements remain valid there. Exponent zero is outside
A_{E,n}'s source convention; one is included. Arbitrary residue characteristics
and primes, including two, are not silently restricted. Y need not be Noetherian
or of finite type. The choice of Ω and coefficient carriers in Type u follows the
site's fixed bound, with modules in Type (u+1); no site morphism/object universes
are collapsed. There is no index set or common-stage upper bound required to be
nonempty as an additional hypothesis. At field coefficients arbitrary complex
representatives, rather than just already bounded complexes, are admitted.

Independent searches, using different words from the worker:

- LeanFinder: `a geometric fibre of a torsion constructible sheaf complex with bounded
  Tor dimension admits a finite free resolution`. Eight hits, mainly finite
  presentation of module sheaves and `DerivedCategory.isGE_Q_obj_iff`; no match.
- Loogle: `"Module.Finite", "Module.Free"`. No result states this stalk-perfectness
  theorem or constructs the required canonical scalar maps.
- LeanSearch: `bounded finite dimensional geometric fibre of rationalized constructible
  complex`. The service returned Internal Server Error; recorded as unavailable.
- Independent rg over Mathlib, upstream WeilConjectures and the side library with
  `stalk.*perfect`, `perfect.*stalk`, `finite.*free.*stalk` and the reverse order,
  and with each of the new helper names. Hits about locally free O_X-modules and
  Zariski perfect stalks concern different objects. The upstream Exchange module
  mentions the finite-free fibre argument only in the projection-formula docstring;
  its theorem is a projection formula, not this statement. The existing algebraic
  `DerivedCategory.IsPerfect`/`isPerfect_of_finiteTorAmplitude` are correctly reused;
  they do not state either site's stalk theorem or the field assertions.
- I opened Mathlib `Presheaf/ColimitFunctor.lean`: its general colimit-module
  construction is the reused implementation, not an existing specialization of
  the delivered stalk functor or the constant-to-completed coefficient germ.

Mismatches and changes: no object, hypothesis or conclusion mismatch was found.
The worker report's opening inventory omitted the helper definition, although its
later analysis included it; I made the inventory explicit. The rational theorem's
proof docstring compressed away the residue-field splitting and the precise
completeness/product steps of the node's nine-step proof. I expanded that docstring
with the cycle lifts, Cauchy/residue argument and cited dependency IDs. All theorem
signatures and construction data are preserved. There are no hollow definitions,
no new proved theorem, and no local notation or unbound universe. Every postponed
construction property is named, documented and recorded in its owning node.
The item's lean.statement is verbatim its first theorem signature.
