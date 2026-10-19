## Worker report

The module `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction` states
`ModuleCat.derivedCoinductionAdjunction_spec`. The sole postponed proof is that
named theorem. Seven helpers belonging to this node expose existing canonical
constructions, with real data and no new axioms, arbitrary maps, or existence choices.
The natural statement and dependency graph are unchanged; no new nodes or dependency
repairs are needed.

Clause-by-clause reading:

- The commutative rings and homomorphism are `{R B : Type u} [CommRing R]
  [CommRing B] (f : R →+* B)`. Both arbitrary rings live in a common ambient universe.
  `HasDerivedCategory.{wR}` and `HasDerivedCategory.{wB}` independently select the
  localization morphism sizes. These are the standard size parameters of
  `def-weil-abstract-derived-category`, not mathematical restrictions on the rings.
- The ordinary unbounded categories are `DerivedCategory (ModuleCat.{u} R)` and
  `DerivedCategory (ModuleCat.{u} B)`. All complex indices are `ℤ`, and restriction
  `U` is exactly `(ModuleCat.restrictScalars f).mapDerivedCategory`.
- The prescribed complex Hom_R(B[0],I), including its B-action, is
  `(coinductionComplexFunctor f).obj I`. This is precisely existing
  `ModuleCat.coextendScalars f` applied degreewise. Its carrier is the R-linear
  maps from B to Iⁿ. In Mathlib's `CoextendScalars.hasSMul` and `smul_apply`,
  `(b • h)(b') = h(b' * b)`. Its differential is postcomposition with d_I.
  Since B[0] has a single term, the Hom-complex product has just this one
  nonzero factor and there is no additional differential/sign term.
- `derivedCoinduction f` is the existing total right derived functor of this
  exact ordinary coinduction construction, using K-injective localization.
  `derivedCoinductionModel f I` is the existing canonical
  `Functor.rightDerivedFunctorObjQIso`, for EVERY K-injective I, not a selected
  isomorphism from a merely nonempty collection. The theorem's third conjunct
  gives its naturality for every map `t : I ⟶ J`; in particular it applies to
  each quasi-isomorphism comparing choices. Transport by `mapIso` handles any
  `K ≅ DerivedCategory.Q.obj I`. This states the choice-independence and
  functoriality clauses with the actual canonical comparisons.
- Right adjointness is carried by the actual data definition
  `derivedCoinductionAdjunction f : U ⊣ derivedCoinduction f`. It directly
  specializes `Adjunction.mapDerivedCategoryRightDerivedAdjunction` to the
  ordinary `restrictCoextendScalarsAdj`. No theorem is proved here to construct
  an adjoint: the existing derived-adjunction constructor supplies its data.
- `derivedCoinductionUnderlyingHom f` is ordinary `RHom_R(B[0],-)`: it is the
  total right derived functor of `coextendScalars f ⋙ restrictScalars f`.
  This composite is literally the R-module-valued Hom_R(B,-) functor, including
  postcomposition on morphisms and the R-action: precomposition by multiplication
  with f(r) equals multiplication by r by R-linearity and commutativity of B.
  It is not a new sheaf internal-Hom definition. It is the ordinary-module
  specialization of the K-injective prescription in def-pur-derived-internal-hom,
  implemented by existing ordinary-module derived-functor APIs. This is why no
  replacement of the general ringed-site dependency interface is required.
- The existential `e : derivedCoinduction f ⋙ U ≅
  derivedCoinductionUnderlyingHom f` gives the underlying-R-object identification,
  NATURALLY in K. Its first conjunct characterizes it on every K-injective I:
  composing with `derivedCoinductionUnderlyingModel` equals forgetting the
  canonical `derivedCoinductionModel` and then the exact-restriction factorization.
  Thus `e` is normalized to the identity of the actual underlying Hom complexes;
  this is stronger information than a bare existence of an arbitrary isomorphism,
  but is exactly the node's canonical comparison, not a new mathematical clause.
- `coinductionEvaluation f I` is the ordinary adjunction counit on complexes.
  The ordinary counit is `h ↦ h(1)` in every degree. The second conjunct says
  the derived counit equals this map after the canonical model/restriction
  comparisons. It has target `Q.obj I`, precisely the chosen representative K.
- The last conjunct, `U.ReflectsIsomorphisms`, says for every derived B-linear
  morphism that an isomorphism after restriction implies an isomorphism before
  restriction. The reverse implication holds for every functor.
- There is no flatness, finite generation, Noetherian, perfectness, injectivity
  of the ring map, or boundedness assumption. In particular none is hidden in
  the binder for the input complex: only its chosen representative is K-injective.

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, from Mathlib.Algebra.Homology.DerivedCategory.Basic.
- `def-pur-derived-internal-hom`:
  CategoryTheory.derivedInternalHomOfUniverses (and its comparison/object-iso
  signatures), in Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses.
  Read its full signature and docstrings. Its Hom-complex/K-injective recipe
  specializes to ordinary Hom_R(B[0],I) as explained above; its module is imported.
- Ordinary canonical constructions: ModuleCat.coextendScalars,
  ModuleCat.CoextendScalars.smul_apply, ModuleCat.restrictCoextendScalarsAdj
  (Mathlib.Algebra.Category.ModuleCat.ChangeOfRings);
  Adjunction.right_adjoint_additive (Mathlib.CategoryTheory.Adjunction.Additive);
  Functor.mapDerivedCategory and mapDerivedCategoryFactors
  (Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor);
  Functor.rightDerivedFunctor (WeilConjectures.CategoryTheory.DerivedCategory.
  RightDerivedFunctor.Defs), Functor.rightDerivedFunctorObjQIso
  (same tree, KInjective), and Adjunction.mapDerivedCategoryRightDerivedAdjunction
  (same tree, Adjunction). Read definitions, signatures and docstrings.
- The proof-only imports retain the recorded modules
  Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
  (`CategoryTheory.rhom_global_sectionsOfUniverses`),
  Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
  (`CategoryTheory.quasiIso_homComplex_map`), and
  Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
  (`SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`).
  Read their full signatures and proof docstrings.
- `lem-weil-pbc-unbounded-derived-iso-cohomology` has no Lean record, but its
  Mathlib match is exactly `DerivedCategory.isIso_iff`, from
  Mathlib.Algebra.Homology.DerivedCategory.HomologySequence; imported for the proof.
- The remaining proof dependency
  `lem-trf-algebraic-shriek-derived-hom-adjunction` has neither a usable Lean
  record nor Mathlib match. Its statement and proof were read; it supplies an
  optional route for Step 3, while the already published general derived-adjunction
  constructor directly supplies that data. No missing notion of it is needed to
  state this item, so there is no prerequisite reconstruction or extra import.

Edge cases checked mathematically against the source: identity map (coinduction
and evaluation reduce to the identity model), zero ring B (D(B) is zero and
coinduction is zero), zero input, zero source ring (forces zero target ring for a
unital map), noninjective/nonflat map such as Z → Z/2, and complexes unbounded
in both directions. All formulas and conservativity hold, and no case is
excluded. The two localization morphism universes are independent. Every
universe and variable is bound, with autoImplicit disabled. There are no lets
in the theorem signature (letI is confined to real definitions).

Searches made (the wrapper's raw records are in the sandbox searches.jsonl):

1. msearch.py leanfinder: "Derived coinduction Hom_R(B,I) right adjoint to
   restriction of scalars on unbounded module derived categories". Eight hits,
   including generic derived-adjunction constructors and ordinary coextension;
   none gives all model, underlying-RHom, counit and conservativity clauses.
2. msearch.py loogle: "ModuleCat.restrictCoextendScalarsAdj". One hit, the
   ordinary adjunction, whose source and full type were read and reused.
3. msearch.py grep: "coextend|Coinduction|coinduction", subdirectory Algebra.
   Seven hits in ordinary ChangeOfRings and EnoughInjectives. Read the
   ChangeOfRings definitions and evaluation formulas.
4. msearch.py leansearch: "Derived coinduction for a commutative ring
   homomorphism is right adjoint to unbounded derived restriction with
   evaluation at one counit". Eight hits: representation coinduction,
   ordinary evaluation counit, and generic derived counit. No exact match.
5. rg on upstream WeilConjectures, shared lean/Sheaf and upstream name inventory:
   coinduct/Coinduct/coextend/Coextend/moduleDerivedHom/derivedModuleHom and
   the proposed declaration names. Generic derived-functor infrastructure is
   reused. The sheaf coinduction and étale coextension results have different
   categories. AlgebraicShriekCalculus packages an assumed coinduction model
   inside a much larger data structure; it neither provides this theorem nor
   conservativity, and importing that downstream calculus would reverse the DAG.
6. Exact node-id search upstream found no matching declaration. Exact proposed
   name search across upstream, lean/Sheaf and dag/lean_names_upstream.json
   found no collisions.

Source checked directly: literature/stacks-project/dualizing.tex,
lemma-right-adjoint and lemma-RHom-ext, lines 2198–2248 (Tags 0A70 and 0A71).
No statement correction or STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiles the delivered module cleanly (2.1 s scratch and
2.3 s library-path verification in the latest successful run). Every definition
has actual data; exactly one named theorem has `sorry`. The prescribed deliver2.py --no-push dry run passed the server preflight
and per-file compilation (printed OK, dry-run commit ebc54f86cd).

## Second reading by Q131

Direct second pass in this session; the dispatcher explicitly forbids starting
other agents, and the maintainer supplies the independent delivery review.
Reopened the node and final file and checked each clause against the mapping
above. The K-injective comparisons quantify over every I, and their naturality
includes every quasi-isomorphism. The underlying comparison is normalized by
its first equality, not merely asserted nonempty. The counit equality uses the
same actual adjunction as the right-adjointness definition and the existing
degreewise evaluation counit. Conservativity quantifies through
ReflectsIsomorphisms over all derived B-module morphisms. No boundedness or
flatness binder appears. The only interface defect found in the first compile
was the absent coextension Additive instance in the counit expression; the final
helper coinductionEvaluation supplies that exact existing adjunction consequence
inside its real construction, without adding a global competing instance.
No mathematical statement mismatch was found; no node fields outside lean changed.
