## Worker report

Item: `lem-trf-total-site-component-restriction`.
Module: `Sheaf.TraceFormula.TotalSiteComponentRestriction`.
Main declaration: `CategoryTheory.totalSiteComponentRestriction`.
This repairs returned immutable head `cb9974775b2f`. The saved packet was read
first and its prescribed initial `deliver2.py --no-push` passed at `a3628fdec6`.
That mechanical success did not repair the mathematical faults in the return.
The retained module has therefore been repaired, rather than repushed unchanged.
The current shared node has the same natural-language statement and dependencies;
this delivery changes only its `lean` record. There is no source-statement correction,
new independent notion, new node, or dependency-node replacement.

### Repair of every returned point

H3, arbitrary category counterexample: `TotalSiteCompatibleSystem` now defines
actual families `obj i` with transition maps, identity laws, and composition laws.
`TotalSiteCompatibleMorphism X Y` defines ALL families of component maps commuting
with those transitions. `TotalSiteSystemData.map_bijective` requires that the map
from EACH Hom set of `T` to that precise type of compatible morphisms be bijective.
`essentially_surjective` requires that EVERY compatible family be realized by
some object of `T`, with component isomorphisms commuting with its transitions.
These are the full-faithfulness and essential-surjectivity criterion for an
equivalence to the category of systems. Identities and composition are respected
because their components are the maps of the functors `component i`. Thus the
statement uses evaluation transported along that equivalence, the alternative
explicitly authorized in the return; it no longer assumes an arbitrary category
with arbitrary component functors.

The returned example with `T = A i = AddCommGrpCat`, identity pulls, and constant
zero components fails `map_bijective`: the distinct identity and zero endomorphisms
of the group of integers have the same component images. It also fails
`essentially_surjective`: the constant compatible system of integer groups cannot
be componentwise isomorphic to the zero system. Neither the conservativity
conclusion nor the left-adjoint assertion is assumed in the repaired interface.
In particular, merely adding conservativity as an assumption would not supply
all systems; the essential-surjectivity clause supplies exactly that missing data.

H3, coherence: `pull_id_left` compares `pullComp f (𝟙 j)` followed by the outer
`pullId` to the canonical transport along `𝟙 j ≫ f = f`. `pull_id_right` compares
`pullComp (𝟙 i) f` followed by the image of `pullId i` to transport along
`f ≫ 𝟙 i = f`. `pull_assoc` compares the two paths from the inverse image of a
triple composite to the threefold inverse image, inserting `eqToHom` for
`Category.assoc h g f`. The comparisons are natural isomorphisms, so their
naturality is already part of the types. These are both unit identities and the
cocycle identity, including non-strict identity/composition comparisons.

H3, extra coproduct assumption: `[∀ i, HasCoproducts (A i)]` is removed. The sums
are indexed by ordinary simplex-category Hom sets, which Mathlib knows are finite.
`Abelian.hasFiniteColimits`, together with `Limits.Shapes.FiniteProducts`, supplies
finite coproducts. No arbitrary-coproduct hypothesis is left, and no new finite-
coproduct assumption is needed. Reindexing from opposite Hom sets to ordinary
simplicial maps is via `φ.op`, with no mathematical change of summands.

H3, transitions of the left adjoint: the isomorphisms `e m` are quantified
simultaneously for every component. The additional equation precomposes a
transition with the image under `pull ψ` of the `φ`-summand inclusion and of
`(e m).inv`, then postcomposes with `(e k).hom`. The result is exactly
`(pullComp φ.op ψ).inv.app G` followed by the inclusion of the composite summand
`φ ≫ ψ.unop`. This specifies the transition maps induced by composition, rather
than merely giving unrelated objectwise isomorphisms to coproducts.

H11: the second reading below explicitly checks the corrected representation,
its two equivalence conditions, all coherence paths, finiteness, and the summand
transition equation against the source and the returned counterexample.

### Hypothesis and clause correspondence

- The simplicial index is Mathlib's `SimplexCategoryᵒᵖ`; degree `n` is
  `Opposite.op (SimplexCategory.mk n)`.
- `A i` is the abelian category of component abelian sheaves. `pull f : A i ⥤ A j`
  is the inverse image for an arrow `f : j ⟶ i` of the opposite simplex category.
  `pull_exact` records its preservation of finite limits and finite colimits,
  the exact inverse-image condition from the morphisms-of-sites hypothesis.
- The specified identity and composition isomorphisms are `pullId` and `pullComp`.
  `pull_id_left`, `pull_id_right`, and `pull_assoc` render their coherent unit and
  cocycle identities, with explicit transport for equality of index composites.
- The category of systems, including its morphisms, is rendered by
  `TotalSiteCompatibleSystem` and `TotalSiteCompatibleMorphism`. The total abelian
  category `T` presents precisely these systems by `map_bijective` and
  `essentially_surjective`, not just some collection of them. The evaluation
  functors are exactly `S.component i`; their maps are those in `map_bijective`.
  `transition_id`, `transition_comp`, and `transition_naturality` give their
  compatible-system structure. `component_additive` is ordinary additive
  evaluation on abelian systems, used to apply the functor termwise to complexes.
- Exactness of restriction is the first conjunct, giving both
  `PreservesFiniteLimits (S.component i)` and `PreservesFiniteColimits ...`.
- For each `n`, `∃ g` and `Nonempty (g ⊣ S.component (op (mk n)))` state the left
  adjoint. Its two preservation conjuncts state exactness.
- For each `G`, `∃ e` gives the direct-sum formula in every degree. The family is
  `fun φ : SimplexCategory.mk n ⟶ m.unop ↦ (pull φ.op).obj G`, precisely the source
  formula over `[n] → [m]`. `∐` is a finite coproduct, hence the abelian direct sum.
  The following summand equation states its induced transition maps as above.
- `Injective I → Injective ((S.component (op (mk n))).obj I)` states injective
  preservation for every total injective object.
- The cochain-complex implication uses Mathlib's `CochainComplex.IsKInjective`
  and `(S.component ...).mapHomologicalComplex (ComplexShape.up ℤ)`, so it gives
  termwise preservation for arbitrary unbounded integer cochain complexes.
  The predicate says every map from an acyclic complex is homotopic to zero,
  exactly the inline definition in the node.
- The final implication, for every morphism `f` of `T`, is joint conservativity:
  componentwise `IsIso ((S.component i).map f)` implies `IsIso f`.

The structures contain real family, morphism, functor, and isomorphism data and
explicit law fields; no definition chooses from a postponed existence theorem.
The sole postponed theorem is `totalSiteComponentRestriction`, with proof `sorry`
and the complete five-step proof plan in its docstring. Helper structures belong
to this node's total-system interface and are all recorded in `lean.declarations`.

### Dependencies and sources read

All four statement dependency nodes and their recorded declarations were read:

- `def-weil-pbc-sites-and-cohomology`: `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`; its docstring and full definition
  specify the covering-presieve site convention. The system theorem uses the
  induced abelian categories and the exactness of inverse images, rather than
  restating site axioms or changing any sheaf definition.
- `def-weil-size-convention`: a convention-only record, no declaration to import;
  the module uses explicit universes `u v w` and no imposed equality between
  object and morphism universes. `T` and `A i` can have different object universes.
- `def-weil-pbc-simplicial-object`: `Mathlib.AlgebraicTopology.SimplicialObject.Basic`,
  `CategoryTheory.SimplicialObject`, `δ`, and `σ`. The full simplex-category indexing
  is used, with no truncation or omission of identities or composite operators.
- `def-sp-injective-resolutions`: `Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
  `CategoryTheory.Injective` and `CategoryTheory.InjectiveResolution`; the former
  is the standard extension-along-monomorphisms predicate used in the conclusion.

The two proof interfaces were also read: Mathlib
`CategoryTheory.Adjunction.map_injective` (exact left adjoints preserve monos),
and `CategoryTheory.Adjunction.preservesKInjectiveComplexes` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
The latter is a proof-only import. Mathlib's full `CochainComplex.IsKInjective`
signature was checked in `Algebra.Homology.HomotopyCategory.KInjective`.

Source reread: `literature/stacks-project/spaces-simplicial.tex`, lines 540–895,
including Cases A/B, all system data before 09WF, the equivalence of 09WF, the
explicit direct-sum construction in 09WG, and injective/K-injective preservation
in 09WH. The corresponding three Stacks tag pages were also opened. The proof
of 09WG explicitly identifies the transition on the summand with the composite
inverse-image comparison, as in the repaired equation.

### Searches

The retained original searches found no existing total-site component theorem:
LeanFinder queries for exact conservative component restriction and compatible
systems of sheaves gave generic sheaf-adjunction/sheafification results; Loogle
for `CategoryTheory.Adjunction.map_injective,
CategoryTheory.Adjunction.preservesKInjectiveComplexes` gave no hits; grep for
`simplicial.*component|preservesKInjectiveComplexes` in Mathlib CategoryTheory
gave no hits. Project/source searches found only the specific `TotalEtaleSite`
construction, not a generic coherent compatible-system evaluation theorem.

Repair searches, run with `msearch.py NX lem-trf-total-site-component-restriction`:

- LeanFinder: `category of compatible systems with transition maps for a
  pseudofunctor and component evaluation`: eight hits, for pseudofunctor
  (co)Grothendieck constructions and descent data. Their actual source was read:
  Grothendieck objects are a SINGLE base object and a single object of its fibre,
  not families over every component; descent data is relative to a covering
  family and forces its compatibility maps to be isomorphisms. Neither is this
  category of systems with arbitrary, generally noninvertible transitions.
- Loogle: `CategoryTheory.Pseudofunctor, CategoryTheory.Grothendieck`: zero hits.
- grep in Mathlib CategoryTheory:
  `CompatibleSystem|TotalSiteSystem|simplicial.*component`: zero hits.
- `rg` over shared `lean/Sheaf`, upstream `WeilConjectures`, and `dag/nodes` for
  `TotalSiteSystem|compatible systems|CompatibleSystem`: unrelated Tate-module,
  thickening, and descent systems; no total simplicial-site system definition.
- Mathlib `Pseudofunctor` was read for comparison of the unit/associativity laws;
  the present componentwise equations state those laws on the given inverse-image
  functors. SimplexCategory's `Finite (a ⟶ b)` and Abelian's finite-colimit instance
  were read to remove the excess coproduct assumption.

### Edge cases

With identity pull functors and identity comparisons, systems are ordinary
covariant functors on the simplex category: all components and all compatible
morphisms are included. For `n = 0`, there are `m + 1` summands in degree `m`;
for target degree zero, there is exactly one summand for every `n`. The repaired
formula has these counts (the earlier report's generic empty-index discussion
was inappropriate: these simplicial Hom sets are nonempty). Identity transition
maps of the left adjoint reduce using the two unit laws; composition of two
transitions reduces using the full cocycle, including non-strict comparisons.
Zero objects, zero complexes, and the all-zero abelian category are allowed.
No boundedness, characteristic, field, arbitrary coproducts, or extra universe
identity is assumed. The returned zero-component presentation is excluded for
the concrete two independent reasons above. No `STATEMENT-DISPUTED` remains.

### Validation

The repaired module compiled cleanly through the prescribed `scompile.py NX
lem-trf-total-site-component-restriction <module path>` wrapper, both as its
sandbox file and at its library path. There were no errors or non-sorry warnings.
A direct packet check confirms that only `lean` changes in the node JSON, every
line of the Lean file is at most 100 characters, the recorded signature is
verbatim, all four declarations are recorded, and exactly one `sorry` remains.

## Second reading by NX

I reread the unchanged node statement and all of the repaired module, including
the data quantified by its theorem, rather than relying on the initial green dry
run. In Tag 09WF the category is ALL systems and ALL compatible component maps:
`map_bijective` supplies exactly the compatible Hom sets and `essentially_surjective`
supplies every compatible object up to compatible isomorphism. The maps to the
Hom sets come from the component functors themselves, so they preserve identities
and composition. This really identifies `T` with the system category; no left
adjoint, exactness of evaluation, or conservativity is presumed to obtain it.
The zero-component AddCommGrp counterexample cannot supply these fields.

For coherence I checked the actual endpoints: the first unit path starts at
`pull ((𝟙 j) ≫ f) X`, the second at `pull (f ≫ 𝟙 i) X`. Both end at `pull f X`.
The cocycle starts at `pull ((h ≫ g) ≫ f) X` and ends at
`pull h (pull g (pull f X))`; its other path first transports along associativity.
Thus both unit laws and the full associativity constraint are present, with the
right variance. The system object's own identity/composition laws are separate
fields, as required, and compatible morphisms have the naturality square.

I checked the full left-adjoint equation: `φ : [n] → [m]` labels the original
summand, `ψ.unop : [m] → [k]` labels the transition, and `φ ≫ ψ.unop` labels its
image summand. The comparison has source `pull ψ (pull φ.op G)` and target
`pull (ψ ≫ φ.op) G`, so it is `pullComp.inv`, not `.hom`. The components `e` occur
on both ends in the correct directions. Finite simplex Hom sets give finite
coproducts without any added hypothesis. I then checked each of exactness of
restriction, adjunction, exactness of the left adjoint, the sum formula WITH
transitions, injective preservation, unbounded K-injective preservation, and
joint conservativity against the conclusion. All are retained. The repaired
statement matches the given system description, with no change to the DAG's
natural-language statement and no hollow definition.
