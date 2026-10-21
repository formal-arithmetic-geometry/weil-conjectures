## Worker report

The module `Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus` states
`CategoryTheory.exactOpenClosedUnboundedCalculus`, with its sole proof `sorry`.
There are no new definitions, helper theorems, new nodes, dependency repairs or
statement corrections. The item JSON changes only its `lean` field.

The source is the exact open/closed route extracted in the DAG from blueprint
`main-20261015`, `det-prop-scalar-six-pullback.proof.md`, (2). I read that source,
the whole item including its eight proof steps, both statement dependencies,
and every proof dependency's statement and recorded declaration. The blueprint
alternative uses the same-right-adjoint argument for open extension; this node
provides the underlying abstract unbounded support calculus.

Hypothesis correspondence:

- The three abelian categories are `AX`, `AU`, `AZ`, each with its own object
  universe, morphism universe, `Category` and `Abelian` instances.
- Their ordinary unbounded derived categories are `DerivedCategory AX`, etc.,
  with independent `HasDerivedCategory.{wX}`, `.{wU}`, `.{wZ}` choices. These
  are localizations of all integer-indexed complexes, with no boundedness.
- The four functors have precisely the directions in the node: `J : AU ⥤ AX`,
  `P : AX ⥤ AU`, `Q : AX ⥤ AZ`, `I : AZ ⥤ AX`.
- Each has `Additive`, `PreservesFiniteLimits`, `PreservesFiniteColimits`.
  This renders the node's explicitly stipulated meaning of additive exact.
- The specified adjunctions are `(a : J ⊣ P)` and `(b : Q ⊣ I)`.
- `hopen : IsIso a.unit` and `hclosed : IsIso b.counit` say the open unit
  and closed counit are invertible natural transformations.
- `hPI : ∀ M : AZ, IsZero (P.obj (I.obj M))` and the analogous `hQJ`
  say that both mixed restrictions are zero. Objectwise zero is equivalent
  to the functor being a zero functor, since maps between zero objects are
  unique; no arbitrary chosen zero comparison is assumed.
- `hseq` states for every `M : AX` that the actual maps `a.counit.app M` and
  `b.unit.app M` compose to zero and give a `ShortComplex.ShortExact`.
  The latter is exactness together with mono first map and epi second map.
  The existential proof `h` is only the proof of a composite being zero,
  not additional data or a replacement of the two specified maps.

Conclusion correspondence:

- Termwise descent is realized by the existing canonical `J.mapDerivedCategory`,
  `P.mapDerivedCategory`, `Q.mapDerivedCategory`, `I.mapDerivedCategory`;
  `mapDerivedCategoryFactors` is the published factorization through complex
  localization. No arbitrary replacement functors are quantified over.
- The existential `da` and `db` have exactly the required derived adjunction
  types. Each `Adjunction` contains both triangle identities. The first four
  conjunctions specify their units and counits on every localized complex,
  with exactly the factorization composites in item proof step 2.
  For a unit the factors are `Q.map unit`, the inverse right-adjoint
  factorization, and the image of the inverse left-adjoint factorization.
  For a counit they are the image of the right-adjoint factorization, the
  left-adjoint factorization, and `Q.map counit`. Localization extensionality
  ensures these equations determine the natural transformations on all objects.
  Thus these are the actual localized maps, with no free adjunction choice.
- `IsIso da.unit ∧ IsIso db.counit` gives the two invertibility conclusions.
- The next two universally quantified `IsZero` clauses give the two mixed
  zero restrictions on the derived categories.
- The clause for every `K L` and `f : K ⟶ L` says precisely that invertibility
  of both derived restriction maps implies invertibility of `f`.
- The clause for every `H` with `IsZero (P.mapDerivedCategory.obj H)` says
  `IsIso (db.unit.app H)`: it concerns the actual normalized closed unit.
- The final clause uses Mathlib's `I.mapDerivedCategory.essImage` on both
  objects and bijectivity of `Q.mapDerivedCategory.map` on the entire Hom set.
  This is exactly full faithfulness on the full essential-image subcategory,
  including objects merely isomorphic to closed-extension objects.
- No boundedness, enough-injectives, resolution, geometric or recollement
  hypothesis occurs. All nine universes are explicitly declared and independent.

Dependencies and declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`, imported via exact derived functors.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
  Its docstring specifies precisely the chosen localization and size convention.
- `lem-weil-pbc-exact-functor-derived-factorization`:
  `CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`
  in `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `def-weil-exact-derived-adjunction`:
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction` in
  `Sheaf.SixFunctors.OpenTensorNormalizationData`, imported for the proof plan.
  Its body localizes the actual cochain adjunction with the inverses of the
  exact factorization isomorphisms. The theorem spells out that same construction's
  universal characterization with independent universes, rather than applying
  its shared-universe signature or duplicating its definition. There is no
  need to impose equality of universes or repair that existing helper.
- The cochain adjunction is the existing
  `CategoryTheory.Adjunction.mapHomologicalComplex` in
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction` (read its full
  definition: the maps are degreewise the given unit/counit).
- `lem-weil-pbc-localization-universal-property`: `Localization.lift`,
  `fac`, `liftNatTrans`, `liftNatTrans_app`, `liftNatIso`, `natTrans_ext` in
  `Mathlib.CategoryTheory.Localization.Predicate`; the component formulas are
  also `Adjunction.localization_unit_app` and `localization_counit_app` in
  `Mathlib.CategoryTheory.Localization.Adjunction`. Their types and docstrings
  were read, including the actual construction and its two triangle proofs.
- `lem-weil-pbc-exact-functor-complex-cohomology`:
  `CategoryTheory.Functor.homologyFunctorIso`, with `preservesHomologyOfExact`,
  in `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
- `lem-weil-pbc-short-five-lemma`:
  `CategoryTheory.ShortComplex.isIso₂_of_shortExact_of_isIso₁₃` in
  `Mathlib.Algebra.Homology.ShortComplex.ShortExact`.
- `lem-weil-pbc-unbounded-derived-iso-cohomology`: `DerivedCategory.isIso_iff`
  and `homologyFunctorFactors` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Functor.essImage` in `Mathlib.CategoryTheory.EssentialImage` is the property
  `∃ X, Nonempty (F.obj X ≅ Y)`, not the strict object image.

All modules of stated proof dependencies are imported; those needed solely for
proof are ordinary imports. The proof docstring follows all eight DAG steps,
including both explicit inverse equations for the Hom map.

Edge cases checked mathematically before writing:

- Zero open category: the sequence forces the closed unit invertible on every
  object; joint reflection reduces to closed restriction. The stated hypotheses
  and conclusion allow this case.
- Zero closed category: the sequence forces the open counit invertible;
  an object with zero open restriction is zero. The closed support unit is
  then an isomorphism between zero objects; the essential image is the zero
  subcategory and the final Hom maps are bijective.
- All categories zero, zero complexes and zero morphisms cause no exclusions.
- In a product abelian category with complementary summand embeddings and
  projections, the hypotheses and conclusions hold term by term, even for
  complexes with nonzero terms in arbitrarily positive and negative degrees.
- No uniform object/hom/derived universe or strict equality with a chosen
  zero object is imposed. The essential-image clause includes all isomorphic
  copies of an extension object.

Searches performed (2026-10-21):

- `msearch.py ... leanfinder`: “Exact open closed adjunctions of abelian
  categories descend to unbounded derived categories with joint isomorphism
  reflection and invertible closed support unit”. Eight hits: standard derived
  categories, `Adjunction.derived`/`derived'`, exact functor factorizations,
  and bounded representative results. No complete abstract support-calculus match.
- `msearch.py ... loogle 'CategoryTheory.Adjunction, "localization"'`: twelve
  hits, including `Adjunction.localization`, its units/counits, and localization
  consequences of fully faithful adjoints. These provide descent ingredients,
  not the complete node.
- `msearch.py ... leansearch`: “exact open closed adjunctions of abelian
  categories yield unbounded derived support equivalence”. Eight hits:
  `abelianOfAdjunction`, derived adjunctions, `HasDerivedCategory.standard`,
  `Adjunction.toEquivalence`, `Functor.exact_tfae`; no complete match.
- `msearch.py ... grep 'mapDerivedCategory|localization_unit_app|localization_counit_app'
  Algebra/Homology/DerivedCategory`: ten hits including the exact factorization
  and derived Ext maps; no abstract open/closed theorem.
- `rg` in both project's `lean/WeilConjectures` and `lean/Sheaf` for
  `openClosed|exactOpenClosed|jointly.*[Ii]so|unbounded_calculus` found geometric
  detection/recollement specializations, including
  `WeilConjectures.SixFunctors.OpenClosed.*` and
  `Sheaf.AlgebraicGeometry.OpenClosedRecollement`; none has this general exact
  abelian-category statement with the specified localization maps and all clauses.
- Searches of `dag/lean_names_upstream.json`, `lean/WeilConjectures` and
  `lean/Sheaf` for the item id and proposed theorem name returned no match.

Validation: prescribed `scompile.py` compiled the sandbox module and final
`Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus` module cleanly, about
3.3 and 3.2 seconds respectively. The initial compile identified that the
cochain adjunction was visible only through a private import; its owning upstream
module is now an explicit public import. No warnings remain.
No statement dispute or node fault was found.

## Second reading by N8

I reread the node and the delivered file in a separate pass in this worker;
no second agent was started, as the dispatcher brief forbids that. The
maintainer supplies the independent review. I checked every hypothesis and
conclusion against the correspondence above, with particular attention to all
four component equations and their inverse orientations. The two triangle
identities belong to each existentially supplied `Adjunction`; they are not
assumed as separate hypotheses. Both essential-image arguments are explicit,
so the final clause is not limited to strict images. Every zero clause means
categorical `IsZero`, not strict object equality. All complex and derived
categories are unbounded. There was no semantic mismatch requiring a node
correction; the only compile repair was the explicit upstream public import.
