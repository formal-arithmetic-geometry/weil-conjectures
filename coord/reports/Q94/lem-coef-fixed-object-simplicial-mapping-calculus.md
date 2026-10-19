## Worker report

Item: `lem-coef-fixed-object-simplicial-mapping-calculus`, group Q94.

The module `Sheaf.CategoryTheory.FixedObjectSimplicialMappingCalculus` states
`SSet.Bergner.fixed_object_simplicial_mapping_calculus`. It constructs the
cotensor with actual internal-hom mapping objects, constant identities and
diagonal composition. Its sole postponed construction-law theorem,
`mappingCotensor_laws`, is precisely the identity/associativity subclaim of
this node's cotensor construction (proof Step 2), not a separate assumed
notion. Its three equations have a source and full natural-language proof.
The main theorem's proof is also `sorry`, with all six DAG proof steps in
its docstring. No data are extracted from the main existence theorem.

Source checked: Dwyer--Kan, *Simplicial localizations of categories*,
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-1.pdf,
Section 7.1 and Proposition 7.2, printed pp. 276--277, PDF page 9.
The source asserts the closed simplicial structure on SO-Cat with precisely
local weak equivalences and local Kan fibrations. The formulas spell out
that structure as in the DAG; there is no statement correction.

Hypotheses and clauses, with their Lean counterparts:

| Node text | Lean rendering |
| --- | --- |
| Any small set O, including empty | `(O : Type u)` with no `Nonempty`, endpoint or category assumptions |
| The existing category sCat_O | `SSet.Bergner.Fixed O`, with its existing `fixedCategory O` |
| B in sCat_O and arbitrary small K | `mappingCotensor (K : SSet.{u}) (B : Fixed O)` |
| Cotensor objects are O | Result type `Fixed O` |
| Mapping objects Fun(K,B(a,b)) | `Hom a b := (ihom K).obj (B.Hom a b)` |
| Pointwise composition using the diagonal | `mappingCotensorEvaluation` evaluates both internal-hom factors at the same K coordinate; `mappingCotensorComp` curries that map followed by `B.comp` |
| Constant identities | `mappingCotensorId` is `curry (snd K (𝟙_ SSet) ≫ B.id a)` |
| These operations define a category | `mappingCotensor_laws`, used only in the three proof fields of `mappingCotensor` |
| Tensors adjoint to these cotensors | The main theorem gives `T : SimplicialTensorCotensor (Fixed O)` and `T.cotensor K B = mappingCotensor K B`; the existing tensor/cotensor structure has the enriched representing isomorphisms induced by its universal elements |
| Map(C,B)_n = Hom(C,B^(Delta^n)) | `FixedMappingFormulas` supplies `ε C B n`, a bijection for every `n : SimplexCategoryᵒᵖ`, with target `C ⟶ mappingCotensor (stdSimplex.obj n.unop) B` |
| Simplicial operators are restriction | First conjunct of `FixedMappingFormulas`: uncurrying after any operator theta equals precomposition by `SSet.stdSimplex.map theta.unop` on the parameter |
| Composition is pointwise | Second conjunct: uncurrying the image of `eComp` equals composing the two uncurried maps using the same simplex parameter |
| Identities are constant functors and vertices are actual arrows | Third conjunct normalizes `ε` on every ordinary `f : C ⟶ B` via `homEquiv'`; the existing `SimplicialCategory` laws identify the identity and composition of these ordinary arrows |
| Fixed-object model structure is simplicial | Exists `s : SimplicialCategory (Fixed O)`, the specified tensor/cotensor structure, and an actual `ModelCategory (Fixed O)` witness with all three classes equal to `fixedWeakEquivalences`, `fixedFibrations`, `fixedCofibrations` |
| Cofibration C to D, local Kan fibration B to B' | Existing `SimplicialModelLocalization.SatisfiesSM7`, instantiated with that same model witness and enrichment, quantifies over all such inputs |
| Actual corner map to the displayed pullback | The existing `SimplicialModelLocalization.cornerMap` is the pullback lift of precomposition and postcomposition; it is not an arbitrary arrow |
| Corner is Kan, trivial if either input is local weak | `SatisfiesSM7` asserts `modelCategoryQuillen.J.rlp` and realization-based weak equivalence when either input is weak; the model's weak classes have been fixed to the local ones |
| Free arrows are the recorded word construction, with loops allowed | `freeArrow`, `freeArrowFunctor`, `freeArrowMap`, `freeArrowGenerator` and `mappingSetEvaluation` are imported from `FixedObjectFreeArrowAdjunction`; no second free construction |
| Ordinary adjunction enriches | Last conjunct of `FixedMappingFormulas` gives the actual ordinary adjunction normalized by restriction to generators, and isomorphisms `sHom (freeArrow a b K) B ≅ (ihom K).obj (B.Hom a b)` |
| Natural simplicial mapping isomorphism | The isomorphisms are specified on every n-simplex: their uncurried Yoneda transpose equals the same generator restriction of `ε`, with the cartesian symmetry switching parameter order. Thus substitution in K and postcomposition in B give naturality, including higher parameters, rather than unrelated isomorphisms |
| Quillen adjunction | The last clause of the theorem says free arrows preserve every monomorphism as a fixed cofibration and every weak monomorphism as a local weak equivalence. These are exactly the cofibration/trivial-cofibration preservation conditions for the displayed left adjoint in the Kan model; the existing evaluation right adjoint detects the local fibrations and trivial fibrations |

The existential enrichment is fully characterized by the degreewise
bijections and their restriction, composition and ordinary-arrow formulas.
This is an assertion that the specified enrichment exists, not a new data
definition chosen from an unspecified existence proof. Likewise tensors
are asserted through the already defined enriched universal property;
no arbitrary map or unconstrained `Nonempty` replaces a canonical map.

Dependency interfaces read and used:

- `Sheaf.CategoryTheory.FixedObjectSimplicialFreeCalculus`:
  `SSet.Bergner.fixed_object_simplicial_free_calculus`; its existing category
  and local classes are used in the theorem. The supplied model has the
  precise three classes; we add no assumed Bergner model witness.
- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `CategoryTheory.simplicial_model_nerve_localization`, and the statement
  notions `SimplicialModelLocalization.SatisfiesSM7` and `.cornerMap`.
  Its `SimplicialTensorCotensor` is the existing definition from
  `Sheaf.CategoryTheory.SimplicialTensorCotensor`, with enriched universal
  elements, not just ordinary Hom bijections.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen`, the horn lifting definition of
  Kan fibrations, monomorphism cofibrations, and realization-based
  `SSet.Enhanced.IsWeakHomotopyEquivalence` convention.
- `Sheaf.AlgebraicTopology.FixedObjectFreeArrowAdjunction`:
  `SSet.Bergner.fixed_object_free_arrow_adjunction` and the explicit
  `freeArrow`, `freeArrowMap`, `freeArrowFunctor`, `freeArrowGenerator`,
  `mappingSetEvaluation` constructions and their full signatures/docstrings.
- The owning imported module `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`
  was also read for `Fixed`, `FixedHom`, `fixedCategory`, `fixedWeakEquivalences`
  and `fixedFibrations`.

Stated proof dependencies are imported without `public`:
`ConeSortedTheoryIdentification`, `SortedSimplicialAlgebraModel`, and
`SimplicialSM7GeneratorExtension`. The tensor/cotensor definition and the
other stated proof dependencies are already public statement imports.
The DAG proof dependencies `lem-coef-fixed-object-simplicial-sm7-free-cell`
and `lem-coef-sset-anodyne-pushout-product` have no recorded Lean module
on the read base, so their proof-only imports cannot yet be written.
Neither is needed to type this statement; the proof plan still names both.

Edge cases checked:

- Empty O: all mapping and operation quantifiers are empty, `Fixed O` is
  the unique empty enrichment, the free-arrow clauses have no endpoints,
  and no object/nonempty assumption was added.
- Equal endpoints a=b: uses exactly the dependency's finite word free-loop
  category, so generators are not silently identified with identities.
- Empty K: every cotensor mapping object is terminal, with its unique
  composition; the empty tensor is the identity-only object in `Fixed O`.
  The free-arrow on empty K has no generators, and its mapping complex is
  terminal as is `Fun(empty,B(a,b))`.
- K=Delta^0 and n=0: ordinary-arrow normalization uses all actual functors,
  and the corner includes the zero-dimensional trivial-fibration test via
  the imported Kan model convention.
- Non-Kan B, noncofibrant C: neither is excluded from cotensors, mapping
  formulas or the free-arrow isomorphism. Only SM7's input arrows carry
  the required cofibration and fibration conditions.
- Universes: O and the small mapping simplicial sets use arbitrary u;
  `Fixed O` naturally lives in the next universe with u-small Hom sets.
  No extra universe equality or smallness condition is imposed.

Searches before construction (msearch output is also in sandbox searches.jsonl):

1. LeanFinder query: “Fixed object simplicial categories form a simplicial
   model category with cotensors and a simplicial free arrow evaluation
   Quillen adjunction”. Eight hits: standard simplicial-set model classes,
   simplicial-object enrichments, `SSet.QCat`, and `SimplicialCategory`/`sHom`;
   no fixed-object mapping-calculus declaration.
2. Loogle query: `"SimplicialCategory", "EnrichedCategory"`. Zero hits.
3. Mathlib grep via msearch: `fixedObject|fixed_object|Bergner|sCat` under
   CategoryTheory. Twenty-five displayed hits concerned Galois-category
   names (`PreGaloisCat` contains sCat), not this construction.
4. `rg` over upstream `WeilConjectures` for `fixedObject|fixed_object|Bergner`
   and the item's exact id: no hits. `rg` over `dag/lean_names_upstream.json`
   for the proposed theorem name: no hit.
5. `rg` over `lean/Sheaf/CategoryTheory` and `lean/Sheaf/AlgebraicTopology`
   for cotensor/enrichment and fixed-object mapping names: found the existing
   fixed-object category/free-arrow/model declarations described above;
   no canonical mapping enrichment or this theorem. These are reused.
6. LeanSearch query: “The category of simplicial categories with a fixed set
   of objects is a simplicial model category with pointwise cotensors and
   free-arrow simplicial Quillen adjunctions”. Eight hits gave only the
   general simplicial-category and simplicial-object interfaces and the
   simplicial-set model classes. No exact theorem match.

Validation: prescribed `scompile.py Q94
lem-coef-fixed-object-simplicial-mapping-calculus
lean/Sheaf/CategoryTheory/FixedObjectSimplicialMappingCalculus.lean`
passed both sandbox and library-name file checks cleanly (3.3 seconds each).
The first attempt exposed only a namespace collision on stdSimplex.map
and the class-definition reducibility warning; both were fixed by fully
qualifying `SSet.stdSimplex.map` and marking the cotensor
`@[instance_reducible]`. No warnings remain. Every variable and universe
is bound explicitly (`set_option autoImplicit false`).

No disputed statement, missing statement dependency, new independent notion,
dependency interface repair, or node correction was needed. Only `lean` changes
in the copied node; its statement, dependencies and proof are unchanged.

## Second reading by Q94

Final author self-check against the node and module (the dispatcher forbids
starting other agents; the maintainer supplies the independent review).
I checked each row above against the actual declaration and the imported
signatures. In particular the SM7 predicate uses the same model witness,
the cotensor composes with the same K parameter, the epsilon formula covers
all simplex operators, and the generator formula fixes the entire enriched
comparison rather than just its vertices. The zero-object-set and loop cases
remain quantified. No mismatch required changing the DAG statement. All
helper declarations belong to the node's own explicit mapping/cotensor
construction and are included in `lean.declarations`.
