## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators` states
`AlgebraicGeometry.Etale.finiteRing_compactGenerators`.  It introduces an algebraically
closed field `k`, a prime natural number `ℓ` whose scalar in `k` is a unit, a scheme
structure morphism `f : T ⟶ Spec (CommRingCat.of k)` with `LocallyOfFiniteType` and
`QuasiCompact` instances, and a finite commutative coefficient ring `C` with
`∃ n, (ℓ : C)^n = 0`.  No separatedness instance is required.

The first conclusion existentially supplies
`hcoprod : HasCoproducts.{u + 2} (DerivedCategoryModule C T)` and states
`LocallySmall.{u + 1} (DerivedCategoryModule C T)`.  For each complex `E`, the three
conjuncts render the node's clauses as follows: boundedness is
`DerivedCategory.TStructure.t.bounded E`; bounded constructibility is the assertion for
every `i : ℤ` that the `i`th `DerivedCategory.homologyFunctor` value satisfies
`AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`; and finite Tor amplitude is
`∃ r s : ℤ, ∀ N i, (i < r ∨ s < i) → IsZero (H^i((derivedTensor ...).obj E).obj
(singleFunctor 0).obj N)`, with `N` an arbitrary degree-zero sheaf of `C`-modules.
The compactness conclusion is the recorded declaration `@IsCompactObject ... hcoprod E`.

The second conclusion provides an indexing type `S : Type (u + 2)` and family
`E : S → DerivedCategoryModule C T`.  Every member satisfies the same bounded,
constructible, and finite-Tor predicates just described.  For arbitrary `A`, `B` and
`h : A ⟶ B`, the hypothesis that every postcomposition map
`fun φ : (E s)⟦n⟧ ⟶ A => φ ≫ h` is bijective for every `s` and `n : ℤ` implies `IsIso h`.
The `S` universe is the indexing universe of the supplied coproducts; the local-smallness
universe is the corresponding `u + 1` Hom universe.

The dependency declarations used are:

* `Sheaf.CategoryTheory.CompactObject`, `CategoryTheory.IsCompactObject` (the compact
  object predicate).
* `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` (the finite-ring étale
  constructibility notion).
* `Sheaf.AlgebraicGeometry.DerivedCategories` and
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (the `D(T_et,C)` encoding and standard
  cohomology vocabulary).
* `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, including
  `AlgebraicGeometry.Etale.derivedTensor` and the degree-zero `singleFunctor`.
* The dependency `def-sbc-standard-tstructure-derived-category` is the Mathlib leaf
  `DerivedCategory.TStructure.t` (Mathlib `Algebra/Homology/DerivedCategory/TStructure.lean`,
  line 34; its cohomology characterizations are `isGE_iff` line 90 and `isLE_iff` line 107).
* `def-weil-scheme-morphism-properties` supplies the recorded meanings of finite type,
  but its statement is a collection node; the Lean binders use Mathlib's
  `LocallyOfFiniteType` and `QuasiCompact` directly.

Edge cases checked: the theorem does not assume separatedness; `S` is allowed to be empty;
`r ≤ s` is not added, matching the source's existential finite interval convention (if
`r > s`, the displayed vanishing condition is simply stronger); `n = 0` is allowed in the
annihilating-power hypothesis; zero sheaves and zero complexes are included; all integer
cohomological degrees, arbitrary sheaf test objects, and arbitrary morphisms `h` are
quantified.  The coefficient universe is `Type (u + 1)` and the scheme/indexing universes
are explicit.

Searches made before writing:

* `msearch.py ... leanfinder "Compact generators of the unbounded derived category of
  torsion etale sheaves and compactness of bounded constructible finite Tor complexes"`:
  semantic `DerivedCategory.IsGE`/localization hits only; no matching theorem.
* `msearch.py ... loogle "IsCompactObject, DerivedCategory"`: no matches for this
  étale compact-generation statement.
* `msearch.py ... grep "IsCompactObject|CompactlyGenerated" Mathlib/AlgebraicGeometry`:
  no matches.
* `msearch.py ... leansearch "Constructible torsion etale complexes of finite Tor
  dimension are compact in the unbounded derived category"`: only generic derived-category
  homology/localization hits.
* `msearch.py ... leanfinder "Extension by zero of the constant free rank one module on
  affine etale objects forms compact generators"`: only generic local-generator hits.
* `rg` over `WeilConjectures/` for `IsCompactObject`, étale compact generators, and the
  target id: no existing declaration.

No new definition or dependency module was needed; all notions are supplied by the
recorded project/Mathlib declarations above.  The module compiles cleanly with `scompile.py`.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading and delivery by the follow-up worker.

## Second reading by Q17

I independently read the current shared node, the sandbox statement, the recorded
statement-dependency declarations, and Bhatt--Scholze's PDF, printed pp. 45–49
(Definition 6.3.1, Lemmas 6.3.7 and 6.3.14, and all of Section 6.4). The source here
is the PDF, not a Stacks statement. Section 6.4 assumes a qcqs scheme and a uniform
finite coefficient-cohomological dimension on its affine étale objects; Example
6.4.1 supplies this for varieties over a separably closed field with torsion
coefficients. Finite type over the given field implies Noetherian and qcqs,
without separatedness. Lemma 6.4.2 expressly passes through the separated case to
the general qcqs case. Lemma 6.4.5 gives compact free étale extensions, and
Proposition 6.4.8 gives compact generation and compactness of perfect-value
constructible objects. The node's finite-Tor formulation agrees via Lemma 6.3.7
and the finite-Tor perfectness criterion, exactly as its source field explains.

The following is my object/hypothesis/conclusion checklist. Each entry gives the
final Lean rendering and verdict.

1. Algebraically closed field: `{k : Type u} [Field k] [IsAlgClosed k]`.
   Exact; the characteristic is unrestricted.
2. Prime invertible in the field: `(ℓ : ℕ) (hℓprime : Nat.Prime ℓ)
   (hℓunit : IsUnit (ℓ : k))`. Exact; this includes characteristic zero and
   excludes precisely the residue-characteristic prime in positive characteristic.
3. Finite-type scheme over that field: `{T : Scheme.{u}}`
   `(f : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [QuasiCompact f]`.
   Exact. The collection dependency def-weil-scheme-morphism-properties points
   to these Mathlib properties. No separatedness, connectedness, nonemptiness,
   Noetherian instance, or dimension bound is imposed as an extra hypothesis.
4. Finite commutative ring annihilated by an ell-power: `{C : Type (u + 1)}`
   `[CommRing C] [Finite C] (hC : ∃ n : ℕ, (ℓ : C) ^ n = 0)`.
   Exact; multiplying any module element by this scalar annihilates it.
5. Ordinary unbounded derived category and its cohomology/tensor:
   `DerivedCategoryModule C T`, read in
   `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, is exactly
   `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} C))`.
   The recorded `derivedTensor` is the unbounded K-flat-derived bifunctor
   (source `...Etale.Derived.Tensor`, lines 65–96), not bounded tensor or Tor.
   The recorded standard t-structure is Mathlib's
   `DerivedCategory.TStructure.t`; its `isGE_iff` and `isLE_iff` use the same
   homology functors. Exact categories and constructions, with their canonical
   global derived-category instance; no independent derived model is chosen.
6. Bounded constructibility: `DerivedCategory.isBoundedConstructible C T E`.
   I opened `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`: its body
   requires every integer cohomology sheaf to satisfy the recorded
   `Scheme.IsConstructibleEtaleModuleSheaf`, and ordered integer bounds outside
   which cohomology is zero. I opened that constructibility definition too:
   it uses a finite locally closed partition with constructible parts and étale
   trivializations with finite constant module values. Exact. The similarly
   named upstream `boundedConstructible` uses another recorded constructibility
   interface and was deliberately not substituted.
7. Finite Tor amplitude: `∃ r s : ℤ, r ≤ s ∧
   DerivedCategory.hasTorAmplitudeIn C T r s E`. I opened its definition in
   `...Etale.Derived.Coefficients`, lines 63–75. It universally quantifies over
   every module sheaf in degree zero and every integer degree, and requires
   `IsZero` of the homology of the specified derived tensor outside the interval.
   Exact. This is the bounded-interval declaration recorded by
   def-kun-tor-amplitude, publicly re-exported through EtaleTorAmplitude.
8. Compactness of every such object: the universally quantified implication
   concludes `@IsCompactObject (DerivedCategoryModule C T) _ _ hcoprod E`.
   I read CompactObject: this is bijectivity of the direct-sum Hom comparison,
   with the coprojections of the same `hcoprod`. Exact, for all complexes.
9. A set of such generators: `∃ (S : Type (u + 1))
   (E : S → DerivedCategoryModule C T)`, with the identical bounded-
   constructible and ordered finite-Tor conditions for every `s`.
   The subsequent `∀ A B h` concludes `IsIso h` from
   `∀ (s : S) (n : ℤ), Function.Bijective (fun φ ↦ φ ≫ h)`, where
   `φ : (E s)⟦n⟧ ⟶ A`. Exact order of quantifiers, shifts, map, and conclusion.
10. Coproducts and local smallness: existential
    `hcoprod : HasCoproducts.{u + 1} (DerivedCategoryModule C T)` and
    `LocallySmall.{u + 1} (DerivedCategoryModule C T)`. Exact relative to the
    fixed module-value/indexing universe, which contains the small presentation
    of the site. The category's object type is in `u + 2`; that object universe
    does not license larger coproducts. I read the upstream
    GrothendieckAbelian.HasDerivedCategory and ConcreteCoefficients modules:
    they place the relevant Hom types, small-site sheafification, and colimit
    sizes in `u + 1`. No additional equality of universes is assumed.

Edge cases: empty schemes are allowed, as is the zero coefficient ring and the
annihilating exponent zero (which forces that zero ring). All zero complexes
satisfy the interval conditions with `[0,0]`; adding ordered bounds does not
exclude them. The generator type need not be nonempty, so an empty generator
family is allowed in the zero category. Coproducts include the empty family.
The integer shift and homology degrees include zero and negative degrees.
There is no positivity/nonzero/field assumption on C. The coefficient and
index universes both use `u + 1`; the scheme and field use `u`; polymorphism in
u permits the expected enlargements. No case requires separatedness.

Independent searches on 2026-10-17:

- `msearch.py ... leanfinder "unbounded derived etale category compact generators
  finite cohomological dimension"`: eight generic derived-category localization
  and t-structure results; no matching compact-generation theorem.
- `msearch.py ... loogle '"IsCompactObject"'`: zero hits.
- `msearch.py ... leansearch "compact generation of derived categories of sheaves
  of torsion modules on schemes"`: generic HasDerivedCategory and sheaf module
  generator results; none states this theorem.
- `rg` for `compact.*(generat|constructib)`, `CompactlyGenerated`,
  `compactGenerators`, `hasTorAmplitudeIn`, and the proposed declaration in
  Mathlib's AlgebraicGeometry and CategoryTheory, the upstream WeilConjectures
  tree, and the shared project's lean/Sheaf tree. Existing compact-generation
  results concern module categories, quasi-coherent derived categories, or
  abstract compactly generated categories. They do not give this étale theorem.
  The search did find the exact Tor predicate above and the project's exact
  bounded-constructibility predicate; both are now reused.

Mismatches found and repaired:

- The original `HasCoproducts.{u + 2}` and generator index `Type (u + 2)` used
  the derived category's object universe for coproducts of sheaves with values
  only in `Type (u + 1)`. That is an excessive coproduct requirement (already
  too large for modules over a nonzero finite ring). Both indices are now
  `u + 1`, also the Hom/local-smallness universe. This implements the node's
  fixed indexing-universe convention; its mathematical statement is unchanged.
- The original inline Tor conditions omitted the node's ordered bounds. Although
  the existential unordered-interval property can be replaced by an ordered
  interval without changing the objects, the statement now renders `r ≤ s`
  explicitly and uses the existing `hasTorAmplitudeIn` declaration.
- The original inline bounded/constructible conjunction repeated a notion with
  an exact recorded declaration. It now uses `isBoundedConstructible`.
  The item's stmt_deps gains the already landed
  def-weil-pbc-constructible-complexes and def-kun-tor-amplitude, with their
  public module imports. No new definition or dependency module is introduced.
- The original docstring summarized an earlier, unsplit proof. The current node
  has six proof steps. The new docstring spells out each, including Noetherian
  qcqs reduction, K-injective/local-smallness and coproduct prerequisites,
  compact stratum objects, thick closure, affine free generators, the natural
  free-Yoneda/K-injective Hom calculation, and local cocycle/boundary detection.
  All currently recorded proof-dependency modules are imported without `public`
  unless already public statement dependencies. Not-yet-recorded proof nodes
  have no module to import and are named in the proof docstring.
- Refreshed the sandbox node's non-owned fields from the shared node, retaining
  its current reviewed stage-1 proof. The delivery changes only the owned Lean
  record and the two permitted landed statement dependencies. Its recorded
  signature is extracted verbatim from the file. No statement_change is needed;
  no natural-language node statement or target is changed.

There are no hollow definitions, private notions, local notation, unbound
variables or universes, or proved assertions in this delivery. The only proof
body is the named theorem's `by sorry`. The prescribed `scompile.py Q17
lem-pur-etale-finite-ring-compact-generators
lean/Sheaf/AlgebraicGeometry/FiniteRingEtaleCompactGenerators.lean` completed
successfully: the required FlatModel overlay, sandbox module, and library-path
module all compiled without errors or warnings.
