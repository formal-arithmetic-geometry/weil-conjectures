## Worker report

The delivery states `CategoryTheory.simplicial_undercategory_model` in
`Sheaf.CategoryTheory.SimplicialUndercategoryModel`. It constructs the canonical
arrows needed to spell out the undercategory tensor and cotensor, and states the
existence of the full inherited simplicial model structure with those formulas.
The only postponed proof is this theorem; its docstring includes the node's proof:
limits, empty/disconnected colimits via a pushout, inherited classes, functorial
factorization, undercategory lifting and retract arguments, object characterizations,
fiber enrichment and its laws, enriched tensor/cotensor adjunctions, and SM7 via the
explicit pullback of the ambient corner map.

Hypothesis and clause correspondence:

- The model-category conventions of `lem-coef-simplicial-model-nerve-localization`
  are `[ModelCategory M]`, `[HasLimits M]`, `[HasColimits M]`, and both
  `[MorphismProperty.HasFunctorialFactorization ...]` binders. Mathlib's
  `ModelCategory` already includes retract closure, two-out-of-three, lifting and
  both weak factorization systems, but requires only finite limits and colimits;
  hence the explicit completeness and functoriality binders are necessary parts of
  the node's convention, not extra hypotheses.
- The ambient simplicial structure is `[SimplicialCategory M]`,
  `(T : SimplicialTensorCotensor M)` and `(_hSM7 : SatisfiesSM7 M)`.
- `(A : M)` is arbitrary. There is no cofibrancy, properness or combinatorial
  hypothesis. `M : Type u` and `[Category.{v} M]` retain independent object and
  morphism universes; `Under A : Type (max u v)` has morphisms in `Type v`, so its
  enrichment and tensor parameters remain `SSet.{v}`. No universe equality is added.
- Mathlib's ordinary `Under A` has objects `a.hom : A ⟶ a.right`; its morphism
  `f : a ⟶ b` has underlying map `f.right` and triangle `a.hom ≫ f.right = b.hom`.
  No substitute category or private definition is introduced.
- The existential witnesses are `m : ModelCategory (Under A)`,
  `S : SimplicialCategory (Under A)`, and
  `U : @SimplicialTensorCotensor (Under A) _ S`. The conclusion also includes
  `HasLimits (Under A)`, `HasColimits (Under A)`, both functorial factorizations
  of the inverse-image classes along `Under.forget A`, and
  `@SatisfiesSM7 (Under A) _ m S`. Thus the full simplicial model structure, not
  merely object assignments or an enrichment, is asserted.
- For every `f : a ⟶ b`, the three equivalences identify `m`'s cofibrations,
  fibrations and weak equivalences with `Cofibration f.right`, `Fibration f.right`
  and `WeakEquivalence f.right`, respectively.
- `Nonempty (IsInitial (Under.mk (𝟙 A)))` and
  `Nonempty (IsTerminal (Under.mk (terminal.from A)))` give exactly the two stated
  objects. `IsInitial`/`IsTerminal` are data types in Mathlib, so `Nonempty` is the
  propositional existence assertion.
- The next universal clause tests cofibrancy on the unique arrow from the identity
  object, explicitly `Under.homMk a.hom`. It tests fibrancy on the unique arrow to
  `Under.mk (terminal.from A)`, explicitly the underlying `terminal.from a.right`,
  and identifies this with `IsFibrant a.right`. Because the initial and terminal
  objects are established, these are precisely the stated object characterizations.
- `mappingFiber a b` is
  `pullback (eHomWhiskerRight SSet a.hom b.right) (eHomEquiv SSet b.hom)`.
  The second leg has source `𝟙_ SSet`, the degreewise singleton simplicial set
  (isomorphic to the standard zero simplex). Thus it is the constant simplex of
  the vertex `b`, including every degree. The theorem supplies a simplicial
  isomorphism `e a b` from the actual enriched Hom of `S` to this strict fiber.
  `mappingProjection` is its canonical first projection; `MappingCompatibility`
  identifies ordinary morphisms with their actual underlying maps and preserves
  enriched composition in every degree. Taking an ordinary identity also fixes
  the enriched unit. Composition implies naturality under pre/postcomposition,
  so the comparison specifies the actual undercategory enrichment.
- `tensorTranspose` inverts the existing `T.tensor_isIso` representing map.
  `tensorCollapse` applies this to the constant identity family; it is the canonical
  `X ⊗ K ⟶ X` induced by the unique `K ⟶ Δ⁰`. `tensorObject T K a` is
  `Under.mk (pushout.inl (tensorCollapse T K A) (T.tensorMap K a.hom))`, hence exactly
  `A ⟶ A ⨿_{A ⊗ K} (X ⊗ K)` with the two specified legs. `T.tensorMap` is reused
  from the dependency, not redefined. The penultimate clause makes the chosen
  enriched tensor object equal to this canonical undercategory object.
- `cotensorTranspose` inverts the existing `T.cotensor_isIso` representing map.
  `cotensorObject T K b` transposes the constant family with vertex `b.hom`, hence
  its arrow is exactly `A ⟶ Y ⟶ Y^K`. The final clause makes the chosen enriched
  cotensor equal to that undercategory object. These are definitions with real
  data obtained from universal isomorphisms; no arbitrary existence choice is used.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `CategoryTheory.SimplicialModelLocalization.SatisfiesSM7` and its `cornerMap`;
  the full signature and docstring of `CategoryTheory.simplicial_model_nerve_localization`
  were read to retain its model-category conventions.
- `Sheaf.CategoryTheory.SimplicialTensorCotensor`, publicly imported through the
  preceding module: `CategoryTheory.SimplicialTensorCotensor`, its universal
  element fields, both `*_isIso` fields, and `SimplicialTensorCotensor.tensorMap`.
- Proof imports: `Mathlib.CategoryTheory.Limits.HasLimits` supplies
  `CategoryTheory.Limits.colimit` (`def-weil-pbc-category-colimit`);
  `Sheaf.AlgebraicTopology.KanQuillenRightProper` supplies
  `SSet.KanQuillen.right_proper_kan_quillen` (`lem-coef-kan-quillen-right-proper`).
  Both records and source signatures/docstrings were read. These remain non-public
  imports as the stage rules require for proof dependencies.
- Mathlib `Under`, `Under.homMk`, `Under.forget`, enriched ordinary category,
  `eHomEquiv`, `eComp`, enriched whiskering, pullbacks and pushouts are reused.

Edge cases checked mathematically before the final formulation:

- `A` need not be cofibrant: a cofibrant object in `Under A` is a cofibration out
  of `A`, even when its target is not ambient cofibrant. None of the constructions
  tests ambient cofibrancy of `A` or `a.right`.
- `K` empty: the tensor pushout is the identity object `A ⟶ A`; the cotensor is
  `A ⟶ 1`. No nonemptiness or positive dimension condition is imposed.
- `K = Δ⁰`: the pushout tensor and constant cotensor recover the original object
  up to the usual unit isomorphisms, as their representing maps require.
- An initial `A` recovers the ambient formulas under the usual equivalence of
  categories. Identity under-arrows, the terminal map, and degree zero of the
  mapping fiber have the expected ordinary undercategory meanings.
- Empty diagrams yield initial object `1_A` and terminal object `A ⟶ 1`.
  Disconnected diagrams require `B = colim const A` in the colimit pushout; the
  proof docstring keeps this step and makes no connectedness assumption.

Searches for an existing statement or helper:

- `msearch.py`, LeanFinder:
  `simplicial model category undercategory strict fiber mapping simplicial set tensor pushout`:
  8 hits, including Kan fibration definitions and the ordinary `Over` structure;
  no full undercategory result.
- `msearch.py`, Loogle:
  `CategoryTheory.Under, HomotopicalAlgebra.ModelCategory`: zero hits.
- `msearch.py`, LeanSearch:
  `simplicial model structure undercategory tensor cotensor`: 8 hits, chiefly
  `HomotopicalAlgebra.ModelCategory.over` and basic simplicial declarations;
  no matching undercategory simplicial structure. The source of `ModelCategory.over`
  was read: it explicitly leaves the dual `Under` construction as TODO.
- `msearch.py`, grep in `AlgebraicTopology/ModelCategory` for
  `Under|undercategory|coslice`: only `Over` and unrelated model axioms.
- `msearch.py`, grep in `CategoryTheory` for
  `(Undercategory|Simplicial.*Under|Under.*Simplicial|tensorTranspose|cotensorTranspose|tensorCollapse)`:
  zero hits.
- Direct `rg` searches in `WeilConjectures`, `lean/Sheaf`, the Mathlib simplicial
  category sources, and `dag/lean_names_upstream.json` found no existing version
  of the full statement or the added tensor/cotensor transposes. Hits for algebraic
  tensor-Hom adjunctions concern modules and complexes, not simplicial tensors.
  The search for the item id in upstream `WeilConjectures` returned no declaration.

Source checked: the cited online HTT PDF, printed pp. 851–852 and 907 (PDF pp.
868–869 and 924), and the current main-20261015 ancestor proof, paragraph 2.
HTT uses the simplicial model category of objects under `A`; the node's displayed
formulas and expanded construction give its interface without the left properness
used elsewhere in HTT's local-equivalence argument.

No new nodes, dependency repair, statement change or disputed statement is needed.
All eight helpers are parts of the construction stated by this same node and are
listed in `lean.declarations`. The theorem remains entirely `sorry` as required.
Compilation through `scompile.py` is clean for the delivered module, including its
library module path, with no warnings.

## Second reading by Q80

I read the node and sandbox module independently, then opened the recorded dependency
declarations and the cited HTT PDF. This node has no Stacks source: HTT Lemma A.3.7.1,
printed p. 907 (PDF page index 924), uses the simplicial model category of objects
under A. Definition A.3.1.5 and Remark A.3.1.6, printed pp. 851–852, specify tensors,
cotensors and the corner-map axiom. The node explicitly expands the undercategory
construction. Left properness in the surrounding lemma is used for its preceding
weak-equivalence pushout argument; the undercategory construction below needs none.

My object/hypothesis/conclusion checklist, matched against the actual file:

1. **Ambient model category and size conventions.** `M : Type u` and
   `[Category.{v} M]` introduce the ordinary category with independent universes.
   `[ModelCategory M]`, `[HasLimits M]`, `[HasColimits M]` and the two
   `MorphismProperty.HasFunctorialFactorization` instances render exactly the
   convention imported from `lem-coef-simplicial-model-nerve-localization`.
   I opened `ModelCategory.Basic`: its CM1 fields give only finite limits/colimits,
   its CM5 fields give factorization, and its lifting/retract fields imply both
   weak factorization systems. Consequently the additional completeness and
   functoriality instances are required, rather than extra assumptions. Mathlib's
   `HasLimits M` means `HasLimitsOfSize.{v,v} M`, and the undercategory conclusion
   uses the same small-diagram universe. Verdict: exact.
2. **Ambient simplicial model structure.** `[SimplicialCategory M]`,
   `T : SimplicialTensorCotensor M` and `_hSM7 : SatisfiesSM7 M` supply enrichment,
   full enriched tensors/cotensors and SM7. I opened
   `Sheaf.CategoryTheory.SimplicialTensorCotensor`: the two isomorphism fields are
   the actual internal-Hom comparison maps induced by universal elements, not just
   bijections of ordinary Hom sets. I opened `cornerMap` and `SatisfiesSM7` in
   `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`: they use pre/postcomposition,
   horn lifting, and weak homotopy equivalence when either input is trivial.
   Verdict: the same notions and conventions as the dependency node.
3. **Arbitrary base and ordinary undercategory.** `(A : M)` has no cofibrancy
   instance. Mathlib `Under A` really is `StructuredArrow A (𝟭 M)`;
   `a.hom : A ⟶ a.right`, `f.right`, and `Under.w` give exactly the objects,
   morphisms and triangle equation in the node. There is no properness or
   combinatorial assumption. Verdict: exact, including noncofibrant A.
4. **Existence of the whole inherited simplicial model structure.** The witnesses
   `m : ModelCategory (Under A)`, `S : SimplicialCategory (Under A)` and
   `U : @SimplicialTensorCotensor (Under A) _ S` concern that same ordinary
   undercategory. The conjunction includes its completeness/cocompleteness,
   both functorial factorizations of the inverse-image classes, and
   `@SatisfiesSM7 (Under A) _ m S`. The universal clause in `a b f` identifies
   all three fields of m with `Cofibration f.right`, `Fibration f.right`, and
   `WeakEquivalence f.right`. These identifications also identify the displayed
   factorization classes with m's own classes. Verdict: full inherited structure,
   with no missing model axiom or extra condition.
5. **Initial and terminal objects.** `Nonempty (IsInitial (Under.mk (𝟙 A)))`
   and `Nonempty (IsTerminal (Under.mk (terminal.from A)))` express the two
   universal properties. `Nonempty` is appropriate since the universal-property
   witnesses are data, whereas the theorem's conclusion is a proposition.
   Verdict: exactly identity at A and the arrow from A to the ambient terminal.
6. **Cofibrant and fibrant objects.** The next clause tests m's cofibration
   field on `Under.homMk a.hom` from the stated initial object and m's fibration
   field on `Under.homMk (terminal.from a.right)` to the stated terminal object.
   It equates these with `Cofibration a.hom` and `IsFibrant a.right`.
   Because the preceding universal properties fix initial and terminal objects,
   these are exactly the object predicates, independently of any chosen initial
   or terminal object in later uses. In particular it never substitutes ambient
   cofibrancy of `a.right` for cofibrancy under A. Verdict: exact.
7. **Strict enriched mapping fiber.** `mappingFiber a b` is the pullback of
   `eHomWhiskerRight SSet a.hom b.right` and `eHomEquiv SSet b.hom`.
   I checked `Enriched.Ordinary.Basic`: the first arrow is precomposition with a;
   the second has source the monoidal unit of SSet, the singleton simplicial set,
   hence the simplicial point representing b. Presheaf pullbacks are degreewise.
   The existential `e` gives actual simplicial isomorphisms from S's Hom objects
   to these fibers. `MappingCompatibility` makes their first projections agree
   with the underlying ordinary maps and all degree-n enriched compositions.
   Identities follow by taking the ordinary identity, and naturality under
   whiskering follows from composition. The pullback's point coordinate is unique,
   so its projection is monic; these compatibilities determine the full fiber
   enrichment. Verdict: the specified enrichment, not unrelated Hom isomorphisms.
8. **Tensor for every a and K.** The penultimate clause fixes U's tensor object
   equal to `tensorObject T K a`. Its structure arrow is `pushout.inl` for
   `tensorCollapse T K A : T.tensor K A ⟶ A` and `T.tensorMap K a.hom`.
   I checked the latter dependency definition and both representing maps:
   `tensorTranspose` curries the family, inverts `T.tensor_isIso`, then applies
   `eHomEquiv.symm`. `tensorCollapse` uses the constant identity family, precisely
   the collapse induced by K to the point followed by the tensor unit isomorphism.
   Thus the pushout and its arrow are exactly the node's formula. Verdict: exact.
9. **Cotensor for every b and K.** The last clause fixes U's cotensor equal to
   `cotensorObject T K b`. `cotensorTranspose` inverts the cotensor representing
   isomorphism, with its required braiding; its input is the constant family at
   `b.hom`. Naturality of that adjunction identifies this transpose with b followed
   by the constant-K arrow into the ambient cotensor. Verdict: exact.
10. **Quantifiers and negative hypotheses.** M, its given structure, and arbitrary
    A precede the existence of one shared m, S and U. All mapping and object
    formulas concern those witnesses and hold for every under-object, morphism,
    simplicial degree and parameter K. No nonemptiness, small-object generation,
    properness, finite-dimensional parameter or extra instance appears. Verdict: exact.

Edge-case review: K empty makes the tensor the initial under-object, since tensors
preserve initial objects, and makes the cotensor the terminal under-object. K equal
to the simplicial point recovers a and b up to their representing unit isomorphisms.
Mapping fibers can be empty; there is no Kan-complex or nonemptiness assumption on
each fiber. `n : ℕ` includes degree zero and all higher degrees. Empty diagrams give
the two displayed universal objects, and disconnected colimits require the node's
pushout with `colim const A`, retained in the proof docstring. If M has a zero object,
A equal to it recovers the ambient construction; no nonzero hypothesis occurs.
Schemes, coefficient rings, characteristics and scheme emptiness are not parameters
of this categorical statement. `Under A` has object universe `max u v` and morphism
universe v, so both enriched structures and every K use `SSet.{v}` consistently;
there is no forced equality of u and v and no new unbound universe.

Independent H4 searches, performed in this reading with different wording:

- LeanFinder via `msearch.py`: `coslice category enriched model structure tensors
  pushouts mapping spaces` returned eight hits, principally enriched functor-category
  Hom constructions and `Enriched.HasConicalPullback`. I opened
  `Enriched/FunctorCategory.lean`: its appearances of `Under j` index restricted
  functors, not an enrichment or model structure on an undercategory. No match.
- Loogle via `msearch.py`: `CategoryTheory.Under, CategoryTheory.SimplicialCategory`
  returned zero hits.
- LeanSearch via `msearch.py`: `An under category of a simplicial model category has
  mapping spaces given by fibers and tensor objects given by pushouts` returned eight
  ordinary-under-category results: its category, `Under.mk`, `Under.pushout`,
  `Under.mapPushoutAdj`, and related formulas. None supplies this simplicial model
  structure. Mathlib `ModelCategory/Over.lean` explicitly leaves Under as a TODO.
- Direct `rg` over Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for coslice/undercategory, the combinations
  `simplicial` with `under` or `coslice`, and all added helper names found no existing
  statement or helper. Broad hits concern underlying simplicial sets, infinity-category
  slices and ordinary comma constructions. The canonical representing maps are
  based on the already recorded `SimplicialTensorCotensor`, not a private copy.

There are no new nodes, dependency modules, statement corrections or repair notes
for this item. I also opened the proof dependencies' recorded interfaces:
`Limits.colimit`/`colimit.desc` in Mathlib `Limits.HasLimits`, and
`SSet.KanQuillen.right_proper_kan_quillen` in
`Sheaf.AlgebraicTopology.KanQuillenRightProper`. The latter includes the horn and
boundary lifting characterizations needed here; right properness itself is not
assumed on M. Both proof imports are correctly non-public.

Mismatch found and repaired: H8's step-by-step proof documentation omitted the
node's explicit tensor/cotensor unit and associativity coherence argument at the
end of proof step 10. I added it after the enriched adjunction calculation, including
the common transpose on three parameters and deletion of point factors. I also added
the main-definition and main-statement index required for a module with several
declarations. The mathematical statement, all eight helper bodies and the node
record were already correct and are unchanged. Every helper has real data from
specified universal isomorphisms or pullbacks/pushouts; no arbitrary existence choice
or definition with sorry occurs. The only theorem remains entirely sorry, every
declaration has its source and blueprint docstring, all lines are at most 100
characters, and `lean.statement` is verbatim the theorem signature.
