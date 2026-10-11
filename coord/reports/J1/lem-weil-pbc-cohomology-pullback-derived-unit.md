## Worker report

The item is stated by four sorry-only theorems in
`Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`. Its main declaration is
`AlgebraicGeometry.Etale.derivedCohomologyPullback_eq_derivedUnit`.
No node statement is corrected, no proof is supplied, and no new definition node is needed.
One dependency module supplies the missing derived clause of the already existing definition
node `def-weil-pbc-cohomology-pullback`.

The source read was Stacks Project Tags [01F8](https://stacks.math.columbia.edu/tag/01F8),
[01EZ](https://stacks.math.columbia.edu/tag/01EZ), and
[08J6](https://stacks.math.columbia.edu/tag/08J6), at their stated places in cohomology.tex
and sites-cohomology.tex. The literature checkout is not populated on this machine, so the
actual tag pages were opened. The original item has eight proof steps: functor conventions,
comparison of arbitrary K-injective representatives, preservation of K-injectivity, the
Leray identification and its independence, naturality, the representative of the derived
unit, the comparison of its Γ-image with the section map, and passage to H^q. All eight
steps are included in the theorem docstrings, with the dependency names used by the node.

Hypotheses and clauses:

- Schemes and the arbitrary morphism `u : Y → X` are `{X Y : Scheme.{v}} (f : Y ⟶ X)`.
  No properness, étaleness, finiteness, nonemptiness or coefficient restriction is imposed.
- Abelian étale sheaves are `Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}` and the
  analogous category for Y. This is the abelian-sheaf case of the recorded derived-category
  node, rather than a different ringed-space or module-sheaf encoding.
- Direct image is the recorded `Etale.lowerStar AddCommGrpCat f`. Its termwise action is
  `mapCochainComplexPlus` / `mapHomotopyCategoryPlus`, and its bounded below derived action
  is the recorded `Functor.rightDerivedFunctorPlus` (the expression used by
  `Etale.rightDerivedLowerStarPlus`).
- Inverse image on D⁺ is the dependency's `Functor.mapDerivedCategoryPlus` applied to the
  existing exact `Etale.upperStar`; it is induced termwise, without resolving inverse image.
- The adjunction and its derived unit are the recorded
  `Etale.upperStarLowerStarAdjunction` and `Adjunction.derivedPlus.unit.app K`.
- Bounded below complexes in clause 1 are `CochainComplex.Plus`, or their images in
  `HomotopyCategory.Plus`. K-injectivity is exactly `CochainComplex.IsKInjective`, the
  declaration recorded in `def-weil-pbc-kinjective-resolutions`; no private predicate occurs.
  The module for this resolution dependency was read, including its explicit explanation
  that the Hom-complex and homotopy-zero definitions agree. Its extra resolution abbreviation
  is for module-valued sheaves and is not needed for the abelian-valued statement here.
- The first theorem gives K-injectivity of the termwise pushforward; its output remains a
  `CochainComplex.Plus`, so it also retains the bounded below condition.
- Γ is `Sheaf.Γ`, derived Γ is its `rightDerivedFunctorPlus`, with values in
  `DerivedCategory.Plus AddCommGrpCat`. This uses the existing derived functor, not a new
  definition of Γ or cohomology. The recorded unbounded `Etale.rightDerivedGlobalSections`
  restricts to this functor under the canonical
  `Functor.rightDerivedFunctorPlusCompatibility`. The choice between the two canonically
  isomorphic presentations is the same resolution-identification convention as the node.
- The natural Leray isomorphism λ is the existing
  `Functor.rightDerivedFunctorPlusCompIso' lowerStar Γ_X
  (Etale.lowerStarCompGlobalSectionsIso AddCommGrpCat f)`.
  It has type `R⁺f_* ⋙ R⁺Γ_X ≅ R⁺Γ_Y`, so it includes existence, invertibility and naturality
  in every L. Its input isomorphism is the sectionwise terminal-object identification
  `(f_*F)(X) ≅ F(Y)` from the direct-image dependency, including its restriction maps.
  The preservation-of-injectives argument required by this constructor is supplied explicitly
  by the existing `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`;
  it is not an additional hypothesis or a file-local instance.
- `lerayPlus_on_kInjective` specifies precisely its value on every bounded below K-injective
  representative J: the composite unit followed by λ equals localization of the underived
  sections isomorphism followed by Γ_Y's unit. The three `IsIso` clauses express that all
  units used to identify these resolution complexes with derived values are invertible.
  The composite unit itself consists of Γ_X's unit at f_*J followed by Γ_X of the
  direct-image unit. Thus this is the displayed equality of complexes after the canonical
  identifications stipulated in clause 1, not an arbitrary existential isomorphism.
- Clause 2 for every K is exactly `derivedCohomologyPullback f |>.app K =
  R⁺Γ_X.map (derivedPlus.unit.app K) ≫ λ.hom.app (u⁻¹ K)` in the main theorem.
  The left hand side is defined independently of the derived unit by deriving the
  underived section map, so this is a comparison theorem, not equality by definition.
- Clause 2 for a sheaf in degree zero is `DerivedCategory.Plus.singleFunctor _ 0 |>.obj G`.
  The final theorem binds `(q : ℕ)`, applies `DerivedCategory.Plus.homologyFunctor
  AddCommGrpCat (q : ℤ)` to both displayed maps, and uses
  `Functor.mapDerivedCategoryPlusSingleFunctor` to identify the inverse image of G[0]
  with (u⁻¹G)[0]. Thus its source is H^q(X,G) and its target is H^q(Y,u⁻¹G), in the
  resolution-derived presentation stated by the node. The existing `cohomologyMap` is the
  Ext presentation; its bridge to this presentation was already left to stage 3 in the
  definition node's accepted record. This delivery does not silently equate two carriers.
- Derived Γ acts on maps by the existing right derived functor's `map`. The universal
  defining property of right derivation makes this the map induced by a lifted homotopy
  class of resolutions. The representative comparison equation of the second theorem
  explicitly fixes the identifications rather than allowing arbitrary isomorphisms.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`,
  `Etale.upperStar`, `Etale.upperStarLowerStarAdjunction`, and the terminal sections iso.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`: the recorded
  `CochainComplex.IsKInjective` and `QuasiIso` are Mathlib declarations; the resolution
  abbreviation's module and docstring were read, but no resolution predicate needs copying.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryPlus`, `mapDerivedCategoryPlusFactorsh`,
  `mapDerivedCategoryPlusSingleFunctor`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: its mixed record names the existing
  `DerivedCategory`, `DerivedCategory.Plus` and `DerivedCategory.homologyFunctor`.
  The module was read; its torsion predicate is not used because this node has no torsion
  hypothesis, and it is not imported merely to make an unused dependency import.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  `Adjunction.derivedPlus` and the unit/counit comparison signatures and docstrings.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedGlobalSections`, `Etale.cohomology`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`:
  `Etale.cohomologyMap`, with the full Ext-map signature and its docstring.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  the recorded shift and triangulated instances for `Functor.rightDerivedFunctorPlus`,
  and its equivalence with applying the functor to an injective representative.
- `lem-weil-pbc-cohomology-pullback-functorial` has no `lean` record or `mathlib_match` on
  the supplied base. Its whole statement was read. It is used by the item's natural-language
  proof for the independence theorem, not as a notion in a Lean signature: the new pullback
  is a single well-defined natural transformation built using the existing universal derived
  comparison, with no resolution-choice arguments. Therefore no replacement predicate or
  hypothesis for this dependency is introduced. Its separate stage-2 statement remains open.

Edge cases: X or Y may be empty, f may be the identity, G and K may be zero, and q may be
zero. All binders still type in these cases. Bounded below complexes may begin in any
integer degree, including negative degrees; neither a degree-zero nor a termwise-injective
restriction was substituted for K-injectivity. The single sheaf case is a specialization
of the all-K formula, not the only case. The same universe v is used for X and Y and their
sites, with AddCommGrpCat in v+1 as required by the existing small étale sheaf encoding.
Every universe is declared, and every object is bound explicitly. No local notation,
private abbreviation, local instance, `let`, `have` or `show ... from` occurs in a signature.

Searches actually run with msearch.py:

- LeanSearch, "derived global sections pullback induced by derived adjunction unit": HTTP
  Internal Server Error, recorded unavailable, not a negative search result.
- LeanFinder, "right adjoint exact functor preserves K injective complexes derived global
  sections pullback": eight results; the exact-adjoint preserves-injectives theorem is
  useful, but none is the derived-unit pullback statement.
- Loogle, "CategoryTheory.Adjunction, CochainComplex.IsKInjective": zero hits.
- Mathlib grep, "rightDerived.*(NatTrans|CompIso)|preservesKInjective", CategoryTheory:
  found `Functor.rightDerivedNatTrans` and its comparisons, not the étale statement.
- Source rg for `rightDerived.*(NatTrans|natTrans)`, `globalSectionsUpperStarMap`,
  `derivedPlus`, `rightDerivedLowerStarPlus`: found the generic PlusComp and PlusAdjunction
  constructions. Source rg for `cohomologyPullback`, `derived.*Unit`,
  `rightDerivedLowerStarComp`, `pullback.*GlobalSections`: found the unbounded Leray iso and
  the explicit TODO for general derived pullback in Derived/GlobalSections.lean.
- Source node-id search returned no hits. Project rg for `cohomologyPullback` and
  `derivedGlobalSectionsPullback` returned no existing definition. A final exact-name rg of
  Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json returned no collisions
  for the five declarations delivered here.

Both modules compiled together on the server in 4.8 seconds, without errors or warnings.
All four theorem proofs are `sorry`; the dependency definition has complete data and no sorry.

## Dependency modules

`def-weil-pbc-cohomology-pullback`: the old record's `Etale.cohomologyMap` implements the
Ext pullback for sheaves and is retained as the existing implementation. It does not provide
any arrow on RΓ of a general bounded below complex, as the old record itself explicitly
notes. `Sheaf.AlgebraicGeometry.DerivedCohomologyPullback` supplies that missing clause by
`AlgebraicGeometry.Etale.derivedCohomologyPullback`. It first builds the underived natural
section map from the existing adjunction unit and the terminal-section isomorphism, applies
`NatTrans.mapHomotopyCategoryPlus` and localization, then the Γ_Y derived-functor unit,
and transports across `mapDerivedCategoryPlusFactorsh`. `Functor.rightDerivedDesc` extends
this comparison uniquely to R⁺Γ_X. On I and u⁻¹I → J it therefore evaluates to Γ of the
underived unit followed by Γ(r), exactly the definition node's `a ↦ r(η(a))` recipe.
All the data is written out, with no theorem about the main derived-unit formula assumed.
No node other than this dependency and the item is changed; the dependency changes only
in `lean`, with the reason recorded in `lean.note`.

## Second reading by J1

I reread the item node, its Stacks source (cohomology.tex Tags 01F8, 01EZ, 01F9,
01FA and sites-cohomology.tex Tag 08J6), the dependency nodes, and both delivered
modules. The objects and hypotheses match as follows: `X Y : Scheme.{v}` and
`f : Y ⟶ X` are the arbitrary scheme morphism; the étale sheaf categories are
`Sheaf _ AddCommGrpCat.{v + 1}`; `lowerStar` is the recorded direct image,
`mapDerivedCategoryPlus` of `upperStar` is the recorded inverse image on D⁺,
and `derivedPlus.unit` is the unit of the recorded derived adjunction. No
properness, finiteness, étaleness, characteristic, nonemptiness, or torsion
hypothesis is introduced, and all universes are bound explicitly.

The eight source steps render in the declarations as follows. (1--3) The
conventions and K-injectivity claim are `lowerStar_isKInjective_boundedBelow`;
its conclusion is exactly preservation of `CochainComplex.IsKInjective` for a
bounded-below complex. (4--5) The Leray comparison and its naturality are the
conjunction and equality in `lerayPlus_on_kInjective`, including the three
resolution-unit `IsIso` clauses and the sectionwise comparison map. (6--7) The
derived-unit description is the equality in
`derivedCohomologyPullback_eq_derivedUnit`, with source
`derivedCohomologyPullback f` and target Γ of the derived unit followed by the
canonical `rightDerivedFunctorPlusCompIso'` Leray map. (8) The degree-q
specialization is `cohomologyPullback_eq_homology_derivedUnit`, applying the
recorded homology functor to the single sheaf and its inverse-image comparison.
Thus every object, quantifier, and conclusion clause in the node has a Lean
rendering; the four declarations are listed in the item's `lean.declarations`.

The empty schemes, identity morphism, zero sheaf/complex, complexes beginning
in negative degrees, and `q = 0` all type without extra assumptions. The same
universe is used for schemes and sites, and the coefficient category has the
required successor universe. No local notation, hidden `let`/`have`, private
definition, or unbound variable occurs in a signature.

I repeated the existing-definition searches with LeanSearch, Loogle/LeanFinder,
Mathlib/source/project `rg`, and exact declaration-name searches. They found
generic right-derived and homotopy-category infrastructure only; no declaration
states this étale derived pullback/unit comparison. The source's unbounded
Leray isomorphism is a different presentation, while its bounded-below derived
pullback clause is explicitly absent. The dependency module therefore supplies
the missing derived definition and does not duplicate `cohomologyMap`.

No mismatch was found in the item statement or hypotheses. The only repair
present in this delivery is the dependency module for
`def-weil-pbc-cohomology-pullback`, which now records the missing D⁺ derived
map; the existing Ext-based sheaf map remains untouched. Both modules compile
together with only the four intended `sorry` proofs.
