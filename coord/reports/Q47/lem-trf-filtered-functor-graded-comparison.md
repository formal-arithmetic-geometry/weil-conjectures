## Worker report

This is a stage-2 statement delivery. The retained sandbox contained only dispatcher
brief markers, not a Lean statement or node record. The shared node was already split
and reviewed at stage 1, but had no `lean` record. This delivery supplies that record,
two new modules, and one definition node; it does not try to redeliver an unchanged
stage-1 split. No existing node statement, proof, proof dependency, or review is changed.

The main declaration is
`CategoryTheory.FiniteFilteredDerived.filteredFunctorGradedComparison` in
`Sheaf.CategoryTheory.FilteredFunctorGradedComparison`. Its only proof is `sorry`.
All definitions and structure constructors contain real data. The helper module has
no postponed theorem, axiom, or `sorry`.

Clause correspondence:

- Abelian categories A and B: `C : I → Type u`, with explicitly bound category and
  Abelian instances for every `i : I`. A third index expresses functor composition.
  This is a family formulation of the same assertion, allowing every pair and triple
  in one common universe. `z`, `u`, `v`, `u'`, `v'`, and the derived morphism universe
  `w` are explicitly declared and independent. There is no enough-injectives hypothesis.
- D+ is Mathlib's `DerivedCategory.Plus (C i)`, under the recorded size convention
  `[HasDerivedCategory.{w} (C i)]`. DF+ is represented by `D i` and `P i : Presentation`.
  A presentation is certified by `Q.IsLocalization (gradedQuasiIso C)`, not an arbitrary
  category or arbitrary comparison map. Its distinguished triangles are characterized
  exactly as images, up to isomorphism, of filtered cone triangles. Thus the binder
  chooses a realization of the specified category, not a new geometric assumption.
- Complexes are the full subcategory `Complexes C` of the recorded `FilteredObject`
  category, with `filtration.IsFinite ∧ CochainComplex.plus C K.obj`. The first conjunct
  has two global filtration endpoints independent of cochain degree; the second is
  strict boundedness below. `gradedQuasiIso` tests `QuasiIso` of the recorded
  `FilteredObject.gradedMapSteps` for every integer grade. It is not an underlying
  quasi-isomorphism predicate.
- The forgetful and graded functors are the fields `Presentation.omega` and `.gr`.
  `omegaComplex`, `grComplex`, `omegaNaturality`, and `grNaturality` fix both their
  values and maps after localization. The codomain is D+, with its fully faithful
  inclusion into the recorded ordinary derived category used to write these equations.
  `.omegaShift`, `.grShift`, `.omegaExact`, `.grExact` specify their usual exactness.
- `DF^{+,[a,b]}` is the full-subcategory predicate `Supported P a b`: `IsZero` of
  every graded object in D+ outside the interval. This uses derived zero and includes
  nonzero acyclic graded complexes.
- Each supplied ordinary exact functor and its supplied filtered exact lift form a
  `Lift C D P i j`. `.ordinary` and `.filtered` are the two functors. Their CommShift
  and IsTriangulated fields express exactness; `.interval` is preservation of every
  interval. `.phi : filtered ⋙ omega ≅ omega ⋙ ordinary` is precisely the specified
  forgetful comparison, in Lean's left-to-right functor composition convention.
- The conclusion `∃ theta : ∀ ... F p, F.filtered ⋙ gr p ≅ gr p ⋙ F.ordinary`
  supplies the comparisons as natural isomorphisms, for every lift and every integer.
  The first conjunct normalizes their components on pure-degree-p objects: canonical
  `gr ≅ omega`, followed by the supplied phi, followed by G applied to the inverse
  source pure comparison. These pure comparisons are fixed naturally by the inclusion
  and quotient normalization in the presentation. This is the source's canonical
  comparison, rather than an unconstrained family of graded isomorphisms.
- A supplied transformation `h : F.ordinary ⟶ G.ordinary` and supplied filtered
  transformation `a : F.filtered ⟶ G.filtered` satisfy exactly `LiftsTransformation`:
  `omega.map (a.app M) ≫ G.phi.hom.app M = F.phi.hom.app M ≫ h.app (omega.obj M)`.
  The second conjunct states `gr.map a ≫ theta_G = theta_F ≫ h(gr M)`, and
  `IsIso h → IsIso a`. It does not assume either transformation commutes with a
  chosen shift isomorphism, and does not assert any transformation lift exists.
- `identityLift` has identity functors and `Iso.refl` forgetful comparison. The third
  conjunct says its theta components are identities. `composeLift` has composite
  functors and the prescribed whiskered composite of phi, including associators.
  The fourth conjunct is `theta_GF = theta_G ≫ G.map theta_F` componentwise.
- The last two conjuncts explicitly state compatibility with identity transformations
  and composition of already supplied lifted transformations, using the same theta
  family. The composition square uses `(a ≫ b)` and `(h ≫ k)` and assumes exactly
  the two original forgetful squares.

Recorded dependency declarations read and used:

- `def-sp-abelian`: Mathlib.CategoryTheory.Abelian.Basic, `CategoryTheory.Abelian`;
  finite products, kernels, cokernels, normal monos and epis give the usual abelian
  category, zero objects, and finite biproducts.
- `def-sp-filtration`: WeilConjectures.CategoryTheory.Abelian.Filtration,
  `CategoryTheory.DecreasingFiltration`, fields `F` and `F_succ_le`, plus the existing
  `FilteredObject`, finite-filtration and category interface through
  Sheaf.CategoryTheory.Filtration. The recorded upstream source was missing from the
  older checkout, so it was read using `scompile.py --source` as required.
- `def-sp-filtered-complex-subquotients`: Sheaf.Algebra.Homology.FilteredComplexSubquotients,
  `CategoryTheory.DecreasingFiltration.complexStep`, `.complexQuotient`,
  `.complexQuotientπ`, `.complexCycles`, `.complexBoundaries`; graded objects use the
  same `.gradedPiece`/upstream `.gr` cokernel, not a second quotient definition.
- `lem-sp-finite-filtration-induction`: Sheaf.CategoryTheory.FiniteFiltrationInduction,
  `FilteredObject.restrictionSteps`, `.exists_gradedMap_steps`, `.gradedMapSteps`,
  `.finite_filtration_induction_steps`; the helper node cites it for the canonical
  graded morphisms used to specify graded quasi-isomorphisms.
- `def-weil-abstract-derived-category`: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`; the Plus module supplies
  `DerivedCategory.Plus` and `.ι`.
- `def-weil-triangulated-category`: Mathlib.CategoryTheory.Triangulated.Pretriangulated,
  `CategoryTheory.Pretriangulated`; Mathlib.CategoryTheory.Triangulated.Triangulated,
  `IsTriangulated`; Mathlib.CategoryTheory.Triangulated.Functor,
  `Functor.CommShift`, `Functor.IsTriangulated`.
- The proof dependency `lem-kun-distinguished-cone-zero` is the Mathlib declaration
  `CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁`, read in
  Mathlib.CategoryTheory.Triangulated.Pretriangulated and imported for the proof.
  `lem-trf-filtered-truncation-triangle` currently has no Lean declaration: its exact
  natural-language truncation proof is retained in the main theorem docstring, and
  there is no nonexistent proof import. The statement does not take its conclusion
  as a hypothesis and does not require naming truncation functors in its signature.

Edge cases checked before finishing: zero categories and zero complexes; a complex
concentrated in an arbitrary filtration degree (including negative degrees); empty
filtration intervals (zero objects, preserved by exact functors); interval endpoints;
filtration truncation cutoffs beyond either uniform bound; complexes unbounded above
but bounded below; graded complexes acyclic without being literally zero; identity
functors and transformations; ordinary isomorphisms with supplied lifts; composites
through an arbitrary third category; and an empty indexing family (vacuous coherence,
no extra nonemptiness assumption). The pure normalization takes proofs of both pure
supports; the target support follows from `.interval`, so this introduces no additional
restriction on a lift.

Searches performed:

1. `msearch.py leanfinder`, query “exact functors on filtered derived categories
   preserving filtration intervals commute with associated graded functors”: 8 hits
   about ordinary exact-functor derived-category comparisons and Ext maps; no match.
2. `msearch.py loogle`, query `"Filtered", "DerivedCategory"`: 0 hits.
3. `msearch.py grep`, query `FilteredDerived|filteredDerived`: 0 Mathlib hits.
4. `msearch.py leansearch`, query “localization of finite filtered bounded below
   complexes associated graded and forgetful functors”: 8 hits about ordinary
   complexes, graded objects and ordinary derived localization; no match.
5. `rg` in upstream WeilConjectures for `FilteredDerived`, `filteredDerived`,
   `FilteredLift`, `filteredLift`, `DFPlus`, `DFplus`, and `DF⁺`: no general interface.
   Searching the exact item id also returned no declaration.
6. `rg` in lean/Sheaf found FilteredProjectiveComparison.filteredDerivedCategory and
   .boundedAboveFilteredDerivedCategory: read them and their source
   FiniteFilteredModuleHomotopy; they specialize to module categories and the latter
   has the opposite cochain bound. Neither states this item or supplies general DF+.
7. DAG search and `blueprint_refs.py search 'filtered derived'` found the specialized
   bounded constructible sheaf definition and ordinary comparison nodes, not this
   general presentation. The existing statement lem-trf-filtered-truncation-triangle
   has no Lean binding and supplies properties rather than a definition node.
8. Checked names and the item id in dag/lean_names_upstream.json; no match for the
   delivered namespace or theorem.

Source read: Varshavsky PDF pp.39--42, all of 5.1.1--5.1.4 and the proof, as well as
5.1.5 and 5.2.1--5.2.3 for the consumer context. No statement correction or disputed
statement is needed. The source's reversed adjoint terminology in 5.1.1(c) is not
used: the proof docstring follows the already reviewed node's correct universal maps.

Validation: both delivered files compiled separately in dependency order using
`scompile.py Q47 lem-trf-filtered-functor-graded-comparison`, under the default limits.
They compiled without errors or warnings. `set_option autoImplicit false` is in each
module. No global build and no direct source-repository or shared-repository mutation.

## New nodes

`def-trf-finite-filtered-derived-presentation` supplies the missing general DF+ notation
and its presentation, in Sheaf.CategoryTheory.FiniteFilteredDerivedPresentation. Its
source is Varshavsky 5.1.1--5.1.2. It uses the recorded filtration, graded quotient,
abelian and derived category notions. `Complexes`, `gradedQuasiIso`, `Localization`, `quotient`, `ShiftRepresentative`,
`IsConeTriangle`, `Presentation` and `Supported` are all recorded in its lean.declarations.
The concrete `Localization C := (gradedQuasiIso C).Localization` and its canonical
`quotient` functor are real Mathlib formal-inversion constructions. A presentation
allows any equivalent realization of that construction, using IsLocalization.
There is no arbitrary selection of functor data from a Nonempty theorem: presentation
maps carry the localization and factorization specifications themselves. The cone
predicate fixes the degreewise direct-sum cone filtration, ordinary inclusion and
connecting morphism. The normalized natural pure-degree comparison is part of the
canonical presentation data. The theorem is valid for any such realization of the
same localization. Three search kinds and the project/DAG searches are recorded in
mathlib_searches. The specialized def-trf-bounded-filtered-derived-category is not this
node: its coefficients, sheaf category and cochain boundedness differ. No dependency
module or existing-node repair was necessary. The item gains only this stmt_dep and
its Lean record.

## Second reading by Q47

I read the item node, Varshavsky §5.1.1--§5.1.4 (pp. 39--41), and every recorded
statement dependency. The item statement has the following objects, hypotheses, and
conclusion clauses; the Lean rendering is in
`Sheaf/CategoryTheory/FilteredFunctorGradedComparison.lean`.

1. The source's abelian categories are represented by the family `C : I → Type u`
   with `[Category (C i)]`, `[Abelian (C i)]`, and `[HasDerivedCategory (C i)]`.
   The family permits the third category needed by functor composition; an empty
   `I` is consequently vacuous, while every unary and compositional instance is
   included. `D : I → Type u'` with `HasShift`, `Preadditive`, `HasZeroObject`,
   additive shifts, `Pretriangulated`, and `IsTriangulated` is the supplied
   presentation realization of each `DF⁺(C i)`, via `P : ∀ i, Presentation`.
   These are the recorded triangulated-category and presentation interfaces, not
   extra mathematical hypotheses on the source categories.
2. A supplied filtered lift is `Lift i j`: `ordinary` is the exact functor between
   `DerivedCategory.Plus` objects, `filtered` is the exact functor between the
   presentation realizations, `interval` is precisely preservation of every
   `Supported (P i) a b` interval, and `phi` has source
   `filtered ⋙ (P j).omega` and target `(P i).omega ⋙ ordinary`, matching
   `ω G̃ ≅ G ω`.
3. A supplied lifted transformation is `LiftsTransformation`; its sole condition is
   the componentwise forgetful square
   `omega.map (a.app M) ≫ G.phi.hom.app M = F.phi.hom.app M ≫ h.app ...`.
   No arbitrary transformation lift is asserted to exist.
4. The first conclusion clause supplies, for every `Lift` and integer `p`, the
   natural isomorphism `F.filtered ⋙ (P j).gr p ≅ (P i).gr p ⋙ F.ordinary`.
   Its component formula uses `Presentation.pureComparison` on both source and
   target pure-degree objects and the supplied `phi`, which is the explicit
   normalization of “canonical” in the presentation dependency.
5. The second clause gives the graded naturality square for every supplied
   `LiftsTransformation`, followed by `IsIso h → IsIso a`, exactly Lemma 5.1.4(ii)
   and (iii). It neither asserts existence of `a` nor adds shift compatibility.
6. The remaining clauses state identity compatibility, the componentwise formula
   for `composeLift` through a third index `k`, compatibility with identity
   transformations, and compatibility with composition `(a ≫ b)` and `(h ≫ k)`.
   The `identityLift` and `composeLift` definitions use identity functors and the
   specified associator/whiskering composite for `phi`.

The dependency declarations match their nodes: Mathlib `CategoryTheory.Abelian`,
the upstream `CategoryTheory.DecreasingFiltration`, the project's filtered complex
subquotients and finite-filtration induction interfaces, Mathlib's
`DerivedCategory.Plus`, and Mathlib's pretriangulated/triangulated functor classes.
The new `def-trf-finite-filtered-derived-presentation` module was also read against
Varshavsky §5.1.1--§5.1.2: its finite bounded-below complexes, graded localization,
shift and cone representatives, exact `omega`/`gr` factorizations, interval support,
and pure normalization all match that definition node. No dependency module was
unusable and no second definition was introduced.

Edge cases checked are zero categories and zero complexes, a pure complex in any
(including negative) filtration degree, empty intervals, cutoffs beyond finite
support, acyclic but nonzero graded pieces, unbounded-above but bounded-below
cochain complexes, identity and invertible transformations, arbitrary third-category
composites, and an empty indexing family. Universes `z`, `u`, `v`, `u'`, `v'`, and
`w` remain independent, so none of these cases is excluded.

I repeated the three searches: LeanFinder for exact filtered-derived functor graded
comparisons, Loogle for `Filtered`/`DerivedCategory`, and grep in Mathlib and
`WeilConjectures`; I also searched the project's `lean/Sheaf`, DAG names, and the
item id. They found only ordinary derived functor APIs and specialized filtered
module constructions, not this general statement. The module compiles separately
with `scompile.py` under the default limit, with the theorem proof as the sole
`sorry` and no warnings. No mismatch was found, so no source-based correction or
code change was necessary; the delivery adds the second-reading record and the
stage-2 `lean` records for the item and its new presentation node.
