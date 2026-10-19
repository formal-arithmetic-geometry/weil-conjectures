# lem-coef-simplicial-derived-exponential — stage 2

## Worker report

The delivery states `CategoryTheory.SimplicialDerivedExponential.simplicial_derived_exponential`
in `Sheaf.CategoryTheory.SimplicialDerivedExponential`. Its only theorem has proof `by sorry`.
All auxiliary definitions have actual data; the structures describe the canonical data and
properties asserted by the theorem. No arbitrary map is supplied as a hypothesis, and no
object is selected from an undetermined existence theorem. No dependency module or new DAG
node is needed. The original natural-language statement, all seven proof steps, their
citations and proof dependencies are preserved. The only additional statement dependency is
the already recorded `lem-coef-simplicial-diagram-equivalence-classes`, for its large
Bergner localization and object-set lifts used directly in the statement.

I read AGENTS, SETUP, GOAL, STATE, the worker role, the whole stage-2 brief, the stage-2
stage document, delivery-errors H, tools/README, and CompactObject with its node record.
I read the item's two original dependency statements and their recorded modules, signatures
and docstrings, and the recorded diagram-classification interface. No repair note exists for
this item. I read the maintenance note and the already reviewed NU report. The route note's
normal `deliver.py --no-push` was run once and its result was awaited: server preflight
rejected only that the item's stage-1 node file is unchanged. It pushed nothing. That check
concerns an already present split, not the new stage-2 statement delivered here. I did not
change any preserved stage-1 sandbox proof, citations or report, or restore the withdrawn
nerve-localization decomposition.

### Hypotheses and objects

- The model category A is `C : Type (max u w)` with `[Category.{u} C]` and
  `[ModelCategory C]`. The separate object and mapping sizes allow a large locally small
  model category. Given any desired object size, `w` can be enlarged; no size is excluded.
- Simplicial enrichment is `[SimplicialCategory C]`; tensors and cotensors are the recorded
  `T : SimplicialTensorCotensor C`; the simplicial model axiom is the recorded
  `hSM7 : SimplicialModelLocalization.SatisfiesSM7 C`. Combinatoriality is exactly
  `hC : CombinatorialModelCategory.{max u w, u, u} C`.
- Each index `D I : CoherentNerve.SCat.{u}` is a small bundled enriched category, with
  `underlying` supplying the recorded ordinary/simplicial category. Neither index has
  a cofibrancy, fibrancy or local Kan binder.
- The diagram category is `E.Diagrams` for
  `E : SimplicialDiagramEnrichment (underlying D) C`. Its projective structure is the
  recorded `ProjectiveSimplicialModelStructure T E`. These structures are universally
  quantified presentations of the existing projective model, whose existence is already
  asserted by `simplicial_projective_model_calculus`; they are not assumptions replacing
  any part of the exponential conclusion.
- The two full bifibrant categories are exactly
  `SimplicialModelLocalization.Bif E.Diagrams` and `SimplicialModelLocalization.Bif C`.
  Their enrichment is inherited from the recorded enriched-end projections and C.
- The product index is the already defined `SSet.MarkedCone.productIndex I D`, whose
  objects are actual pairs, Hom objects are products of mapping simplicial sets, and
  composition is coordinatewise. `IndexProducts.object` and `.mapping` fix product maps
  on objects and entire Hom objects. This is uniquely specified canonical-map data,
  not a second product category or a free choice of maps.
- `index I` and `target C` use the existing `diagramULiftEnrichment`, lifting only object
  sets. `bergnerHom` and `diagramBergnerLocalization` are the existing large localization
  at the existing Dwyer--Kan predicate. The mapping simplicial sets stay in `u`, and
  the localization Hom sets live in the suitably enlarged universe. No shrinkability
  or calculus-of-fractions assumption is made.

### Every conclusion clause

- Enriched evaluation is rendered by `Uncurrying.functor`, `.object` and `.mapping`.
  On a strict `g : I → B`, the object at `(i,d)` is exactly `g(i)(d)`; its full
  mapping-simplex action is `(g.map ≫ E.projection at d) ⊗ targetDiagram.map d e`,
  followed by the actual enriched composition in C. This is precisely
  `e ∘ (g × 1_D)`. Specifying the evaluated functor on every small test category
  avoids introducing a second, size-restricted product B × D. Evaluation is fixed
  on every mapping simplex, not just on vertices or object classes. The endpoints
  are the full bifibrant objects themselves. `HEq` only transports endpoints fixed
  by the object equation, without weakening the action equation.
- `Statement.exponential` is an equivalence of precisely
  `bergnerHom (index I) (target E.Diagrams)` and
  `bergnerHom (index (productIndex I D)) (target C)`. Thus it includes both
  injectivity and surjectivity. `Statement.representative` fixes this bijection as
  actual evaluation on every strict enriched representative, using `functorClass`.
  The unrestricted diagram classification supplies strict representatives for
  every derived class, including noncofibrant I; this normalization fixes the
  entire derived map, not an unspecified bijection between sets of equal size.
- `Statement.naturality_index` is the square under any enriched `a : J → I`,
  expressed as precomposition by its actual localization class and by
  `products.map a (𝟙 D)` on the right. It quantifies over every derived class.
- `RestrictionPresentation` describes a representative of derived restriction
  along `b : D' → D`: its enriched functor goes from the original bifibrant
  D-diagrams to bifibrant D'-diagrams and has an objectwise weak-equivalence
  comparison to actual enriched restriction. The comparison is a Mathlib
  `GradedNatTrans` of unit degree, so its naturality is on whole simplicial Hom
  objects in D'; the separate `.naturality` equation imposes naturality on whole
  Hom objects in the diagram variable as well. The weak-equivalence components
  are actual C-morphisms obtained by `eHomEquiv`, not unrelated isomorphisms.
  `Statement.restriction_exists` asserts existence for every b and both projective
  presentations. `Statement.naturality_diagram` asserts the square for every such
  representative and every derived class, using precomposition along
  `products.map (𝟙 I) b` on the right. This expresses derived restriction without
  assuming that strict restriction preserves projective cofibrancy or selecting
  arbitrary comparison maps. Choice-independence on all these Hom sets follows
  directly by cancellation of the exponential bijection in that square. Identity
  and composite restrictions give the identity and composite squares as well.
- A set of vertex arrows S is a dependent family `S : ∀ x y, Set (x ⟶ y)` on the
  underlying index. `Inverts S g` means that an actual strict representative of
  this class carries those vertices to `IsPiZeroIso` arrows. This specializes the
  existing class inversion test to bifibrant targets in the large localization:
  the unrestricted classification provides representatives and identifies their
  component functors up to natural isomorphism. The predicate is an existential
  predicate of the class, so it does not require an arbitrary chosen strict lift.
  It uses the recorded `IsPiZeroIso` component test, not strict inverses.
- `productMarking` selects exactly the arrows `(s, 𝟙 d)` with `S s`, using the
  actual paired vertices and equal endpoints; it does not saturate the marking
  or replace the identity by any invertible arrow. `Statement.subsets` asserts,
  for every class, the iff between `Inverts S g` and inversion of that exact
  product marking by its exponential image. It therefore identifies precisely
  the two specified subsets.
- `Statement.pointwise` states the equivalent transformation criterion for every
  vertex arrow `f : F ⟶ G` in the full bifibrant diagram category. Its right side
  uses the recorded end component of the actual full-subcategory inclusion of f
  into E.Diagrams. Invertibility is `IsPiZeroIso` on each C-component; fullness
  identifies this with invertibility in C^cf, since all endpoints are bifibrant.
  No strictly natural pointwise inverses are chosen.

### Dependency declarations and imports

- `Sheaf.CategoryTheory.SimplicialInversionUniversalProperty`:
  `CategoryTheory.SimplicialInversion.simplicial_inversion_universal_property`,
  and the existing Bergner conventions; its full statement and proof docstring
  were read. No downstream product-inversion theorem is assumed.
- `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`:
  `SimplicialDiagramEnrichment`, `.Diagrams`, `.value`, `.component`,
  `ProjectiveSimplicialModelStructure`, and `simplicial_projective_model_calculus`.
  The full enrichment and model-structure records were read, including their
  representation, componentwise composition, and bifibrant evaluation fields.
- `Sheaf.CategoryTheory.SimplicialDiagramEquivalenceClasses`:
  `diagramULiftEnrichment`, `diagramULiftFunctor`, `diagramLargeSimplicialCategory`,
  `diagramBergnerLocalization`, `bergnerHom`, and
  `simplicial_diagram_equivalence_classes`. Its unrestricted representative and
  restriction clauses are exactly what the retained proof uses; its chunk clause
  and its index-cofibrancy hypothesis are not used.
- `Sheaf.AlgebraicTopology.MarkedConeExternalProduct`: only its existing
  `SSet.MarkedCone.productIndex` and `productEnrichment` definitions are used.
  The marked-cone external-product theorem is not a mathematical prerequisite;
  its theorem node has a dependency path back to this item. No such theorem
  dependency is added. This is the same distinction between definition-only
  imports and theorem prerequisites used by the recorded projective-calculus
  interface. No second product-category construction is introduced.
- Retained proof-only imports are
  `Sheaf.AlgebraicTopology.RealizationFiniteLimits` (`SSet.realization_finite_limits`),
  `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`
  (`CategoryTheory.simplicial_model_nerve_localization`),
  `Sheaf.CategoryTheory.LocalizationHomotopyCategory`
  (`SSet.Enhanced.localization_homotopy_category`), and
  `Sheaf.CategoryTheory.ModelLocalizationDetectsWeakEquivalences`
  (`HomotopicalAlgebra.modelLocalization_weakEquivalence_iff_isIso`).
  Their recorded statements and the maintenance warning were read. The pending
  nerve-localization theorem is a cited statement; its withdrawn split is unused.

### Sources, searches, edge cases and validation

I opened the Harvard HTT PDF and read A.3.4.12--A.3.4.13, printed pp. 889--890,
and the third bijection in A.3.5.14, printed p. 896. A.3.4.13 allows arbitrary
small test categories and identifies the two sides through weak-equivalence
classes of product-indexed enriched diagrams. The subset clause is precisely
the marking transition in A.3.5.14. The retained seven-step proof is reproduced
in the theorem docstring, including both restriction variables and the separate
model-localization detection argument. There is no source-based statement
correction and no STATEMENT-DISPUTED finding.

I ran the following required searches through msearch.py (all logged in this
stage-2 sandbox's searches.jsonl), read the hits, and searched the named local
source trees with rg/grep:

- LeanFinder: `derived exponential simplicial projective diagrams evaluation
  bijection homotopy classes`. Eight hits, including simplicial-set homotopy
  functor product comparisons, Dold--Kan and nerve adjunctions; none states
  this enriched projective-diagram exponential or the marked subset assertion.
- Loogle: `SimplicialCategory EnrichedFunctor` returned no hits and reported
  the unqualified identifier unknown. I did not treat that as an exhaustive
  successful search. The corrected query `"EnrichedFunctor"` returned twelve
  hits for Mathlib's functor, composition and category interfaces. I opened
  Mathlib CategoryTheory/Enriched/Basic.lean, read their signatures and the
  graded transformation presheaf, and used that interface rather than copying
  it. It supplies no derived projective exponential.
- msearch grep: `DerivedExponential|simplicial.*exponential|exponential.*simplicial`
  returned no matches. The further Mathlib grep `EnrichedFunctor|SimplicialCategory`
  under CategoryTheory/Enriched found the enriched basic, ordinary and bundled
  category interfaces; none is this theorem.
- rg over WeilConjectures and lean/Sheaf for exponential, simplicial model,
  projective and homotopy class terms found the exact projective calculus,
  diagram classification, bifibrant category and product index reused above.
  The exact item-id grep in WeilConjectures found no declaration. The shared
  item's own Lean record was absent. I confirmed the current server source of
  both the projective calculus and the diagram classification with scompile.py
  --source, so the interfaces used are the published ones.

The module introduces helper encodings belonging to this one statement, all
listed in lean.declarations, with source/blueprint docstrings; no independent
missing mathematical notion was found and no new definition node is needed.

Edge cases were checked before writing: I empty gives singleton Hom sets with
no marked arrows; D empty gives the terminal diagram category, empty product
index and vacuous component tests; D terminal recovers ordinary diagram
classification; S empty gives the full subsets and identity vertices are always
invertible. Noncofibrant indices and indices with non-Kan mapping sets remain
allowed throughout. The size choice keeps locally u-small targets of every
larger object size. Actual endpoint transport is explicit in the full-subcategory
component map and in the action equations.

Compilation uses only the authorized scompile.py wrapper. The completed compile
checks both the sandbox and library module paths separately under the 60-second
limit and reports no errors or warnings (4.3 seconds and 5.5 seconds respectively).
All universes and variables are explicit, autoImplicit is false, and every line
is at most 100 characters. The node's Lean signature is copied verbatim from the
file. Only the expected single named theorem remains sorry. Required deliver2
preflight/dry-run and push results are recorded by the delivery wrapper.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
