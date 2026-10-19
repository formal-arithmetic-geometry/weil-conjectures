## Worker report

The module `Sheaf.Paper.RationalOpenDirectImageConstructible` states
`AlgebraicGeometry.ProEtale.constantModelBoundedConstructible_rational_open_direct_image`.
It has one theorem with proof `sorry`, no definitions, no new nodes, and no dependency repairs.
The natural statement and every DAG field except `lean` are unchanged.
The theorem docstring includes all eight supplied proof steps, including their source-node
citations. No proof has been attempted in this statement stage.

Clause-by-clause correspondence:

- A prime ℓ: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A field k of characteristic p > 0: `(k : Type u) [Field k]
  [Fact (ringChar k).Prime]`. A field's positive characteristic is prime, so this expresses
  precisely the source's positive characteristic assumption. The inequality is
  `[Fact (ringChar k ≠ ℓ)]`.
- The fixed algebraic closure is the existing `PadicAlgCl ℓ`, with its existing norm topology.
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)` is literally an intermediate field of that
  closure together with `FiniteDimensional ℚ_[ℓ] E.1`. Thus E has the induced topology, not
  an arbitrary topological field structure. Using a concrete fixed closure is the source's
  instruction to fix one, and imposes no restriction on schemes or on finite subextensions.
- `{U X : Scheme.{u}}` with the two `Over (Spec (.of k))` instances makes U and X k-schemes.
  Each structure morphism has `LocallyOfFiniteType` and `QuasiCompact` (finite type) and
  `IsSeparated`, exactly as in the setting dependency. There is no smoothness, regularity,
  equidimensionality, nonemptiness or extra Noetherian hypothesis.
- `j : U ⟶ X` with `[j.IsOver (Spec (.of k))]` is a k-morphism;
  `[IsOpenImmersion j] [QuasiCompact j]` states its two required properties.
- The first conjunct is the choice Λ = E: its coefficient is the published
  `Profinite.continuousMapRingObj E`, with sections C(S,E) and pointwise ring structure.
  The second is Λ = Qlbar: its coefficient is `Profinite.padicAlgClRingObj ℓ`, whose
  sections take values in some finite subextension. No all-continuous-functions Qlbar
  coefficient ring is substituted. Taking the conjunction of these two implications
  expresses exactly the source's two allowed choices of Λ.
- In each conjunct, `K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U)
  Ab.{u + 1}) (condensedRingObj Λ U))` and
  `constantModelBoundedConstructible Λ U K` express K ∈ Dbc(U,Λ).
  The conclusion is the same predicate on X, applied to the actual derived direct image
  `((CondensedRing.lowerStar Λ j).rightDerivedFunctor).obj K`.
  The predicate is the recorded finite-constant-model category, not the upstream weaker
  predicate based on arbitrary local finite presentations. It includes boundedness and
  constructibility in every integer cohomological degree.
- `condensedRingObj Λ U` and `condensedRingObj Λ X` are the recorded point-pullback
  coefficients; no alternate coefficient ring or module category is defined.
- `rightDerivedFunctor` derives the entire recorded `lowerStar` composite on module
  objects. This is the unbounded derived module direct image of the dependency, not
  termwise pushforward or the abelian-sheaf derived image.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: the setting and Nagata choice in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, especially
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`. The geometric
  hypotheses are written explicitly; no compactification is needed by this theorem's type.
- `sk-def-sfb-condensed-ring`: import its current recorded
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`. The underlying original
  `Profinite.continuousMapRingObj` from
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap` is also read and
  used (it is recorded in this dependency's upstream closed audit). It is the same
  continuous-function construction for the small coefficient carrier of a literal
  subfield of the fixed closure. The generalized `continuousCoefficientRingObj`
  interface is needed for arbitrary carriers in Type u; no such carrier is imposed here.
  The original interface allows arbitrary Scheme.{u} independently of this small E.
- `sk-def-sfb-qlbar-condensed`: no `lean` record is required, because its closed audit
  names `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj` in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`. Their actual sectionwise
  definitions and docstrings were read. `FiniteSubextension` publicly imports these and
  supplies the existing CoeSort on `PadicAlgCl.FiniteIntermediateField`.
- `sk-def-sfb-pulled-back-coefficients`: `AlgebraicGeometry.ProEtale.coefficientRing` and
  `condensedRingObj` in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
- `sk-def-sfb-constructible`: `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible`
  in `Sheaf.Paper.CondensedConstantConstructibility` (listed in its `lean.declarations`).
  Read its definition down through `IsConstantModelConstructible`, stratification, and
  `HasFiniteConstantLocalModel`; the same object property occurs at input and output.
- `sk-def-sfb-module-derived-pushpull`: `derivedUpperStarLowerStarAdjunction` and the
  comments describing `Functor.rightDerivedFunctor` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`; the underived
  `CondensedRing.lowerStar` in `UpperLowerStar.Defs` is mapMod followed by scalar restriction.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, in the recorded Mathlib morphism modules.

The stated proof-dependency modules are imported without `public`, including the
localization, right-derived triangulated structure, coefficient-change and finite-subfield
flatness interfaces, bounded continuity, ring-sheaf scalar restriction comparison,
derived Hom, completed coefficients and the relevant Mathlib geometric/colimit lemmas.
The currently unstated proof nodes (integral open image, integral models, scalar-six
pullback, finite-model triangulated closure) have no module to import; their exact
uses are retained in the theorem docstring and unchanged proof-dependency list.

Edge cases checked before writing:

- U empty: no Nonempty hypothesis is present; direct image of the zero category's object
  is zero, which has bounded constructible cohomology.
- U = X and j identity: the assertion is preservation by the identity derived functor;
  there is no density or nontrivial-complement hypothesis.
- K zero and arbitrary shifts: the input/output predicates allow any finite vanishing
  interval, not a fixed nonnegative interval.
- E the bottom finite subfield (Q_l): included by `FiniteIntermediateField`.
- Algebraic-closure objects requiring some different finite E': the Qlbar conjunct
  quantifies over every K in that category without a descent assumption to the fixed E.
- Characteristic p = ℓ and characteristic zero are excluded precisely as the source says;
  all other positive characteristics and all primes ℓ, including 2, are allowed.
- Schemes and their sites have the arbitrary universe u, sheaves take values in
  Ab.{u+1}; the small fixed algebraic closure does not impose u = 0.

Searches (all for this item through msearch.py unless otherwise specified):

- LeanFinder: `derived direct image along quasi compact open immersion preserves bounded
  constructible rational l-adic sheaves`: eight hits, including scheme constructible-image
  lemmas and ordinary module pushforward, none the required rational finite-model theorem.
- Loogle: `AlgebraicGeometry.IsOpenImmersion, DerivedCategory`: zero hits.
- Mathlib grep: `constructible|proetale|ellAdicSheaf` in `AlgebraicGeometry/Sites`:
  ten reported hits, in ElladicCohomology and Proetale; site and coefficient definitions,
  no direct-image finiteness statement.
- LeanSearch: `quasi compact open immersion derived direct image bounded constructible
  rational l-adic coefficients`: eight hits, quasi-compactness and open-immersion results,
  no required theorem.
- rg in the upstream WeilConjectures tree and the published lean/Sheaf tree:
  `rational.open|open.*[Cc]onstructible|[Cc]onstructible.*[Oo]pen`, then the exact node id,
  and searches of `constantModelBoundedConstructible`: ordinary/adic direct-image results
  concern other coefficient categories; the upstream generic boundedConstructible result
  uses the different general locally-finitely-presented notion. The only existing exact
  finite-model property is the definition in CondensedConstantConstructibility.
- Exact proposed declaration name and exact node id searched in upstream sources,
  lean/Sheaf and dag/lean_names_upstream.json: no existing declaration.

No statement dispute or source correction is needed. The prescribed single-file
scompile.py validation completed cleanly: the library file took 17.2 seconds,
with no errors or warnings. Compilation and dry-run/delivery are performed only by
those authorized wrappers; no global build or direct Git command is used.

## Second reading by Q101

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
