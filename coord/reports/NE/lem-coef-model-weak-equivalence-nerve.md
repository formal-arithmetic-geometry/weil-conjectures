## Worker report

`Sheaf.CategoryTheory.ModelWeakEquivalenceNerve` states
`HomotopicalAlgebra.ModelNerve.model_weak_equivalence_nerve`, with exactly one
postponed theorem proof. Its supporting definitions have actual data. They specify
this node's weak-arrow category, localization comparison and naturality; no other
DAG node is stated and no new independent definition node is introduced.

The earlier sandbox draft covered only an unconstrained existential comparison.
It omitted the component formula, path formula, replacement inclusions, and the
entire Quillen clause. It also used the full-subcategory object type with a second
category instance. This worker replaced it with the complete statement and
Mathlib's `InducedWideCategory`, and removed the old second-reading claim. The
independent second reader must still read this delivery.

The natural-language statement is unchanged. Its hypotheses and clauses map to
Lean as follows (helper names are in `HomotopicalAlgebra.ModelNerve`).

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A model category with the completeness, cocompleteness and functorial factorizations specified by the frame dependency | `[ModelCategory C]`, `[HasLimits C]`, `[HasColimits C]`, and the two `HasFunctorialFactorization` binders; the second category `D` has the same binders |
| Universes enlarged for all nerves | Separate `u,v,u',v',t`; simplicial sets in `max u v u' v' t`; `FiniteReedy.largeNerve` and `frameLargeNerveMap` lift actual simplices degree by degree |
| A full subcategory S | `P : ObjectProperty C`, with objects `P.FullSubcategory` |
| Closed under weak equivalences in both directions | `hP : ∀ a, weakEquivalences C a → (P X ↔ P Y)`; `_hT` is the corresponding hypothesis for T |
| Same objects, only weak arrows | `WeakObjects P` is Mathlib's `InducedWideCategory C (fun X : P.FullSubcategory ↦ X.obj) (weakEquivalences C)`; `inclusion P` forgets just the arrow property |
| The specified homotopy coherent localization | `q` with `hq : FiniteReedy.IsLocalization (weakEquivalences C) q`; this includes the quasicategory condition, inversion and the universal property on full coherent functor categories |
| Full localization subcategory represented by S | `represented P q`: a vertex is equivalent to `FiniteReedy.object q X` for some X satisfying P; taking this replete full subcategory allows any equivalent localization representative |
| Core, with equivalences and all higher homotopies | `localizedCore P q`, using the recorded `SSet.Enhanced.core` of that full subcomplex |
| Localization induces the comparison | `Comparison` requires `f ≫ coreInclusion P q = localizationDiagram P q`, where the right side is the actual enlarged nerve of `inclusion P`, followed by q; thus every simplex is prescribed |
| Weak homotopy equivalence | `Comparison` includes the recorded realization-based `SSet.Enhanced.IsWeakHomotopyEquivalence f` and `KanComplex (localizedCore P q)` |
| pi_0 equals isomorphism classes in Ho(M) | `ComponentsFormula` gives a surjection from objects of wS to realization path components, normalized on the realization of every corresponding vertex. Its equality criterion is `Nonempty ((weakEquivalences C).Q.obj X.obj ≅ (weakEquivalences C).Q.obj Y.obj)`, in the ordinary localization Ho(M). Surjectivity plus precisely this equality criterion is the claimed quotient by isomorphism classes |
| Paths are equivalence components of derived maps | `PathFormula` factors the canonical `mappingSpaceMap (coreInclusion P q)` through `equivalenceMaps` and asserts it is a weak homotopy equivalence. `equivalenceMaps` is the full subcomplex of the existing right-pinched mapping space on equivalence arrows. Because the core is a Kan model weakly equivalent to N(wS), its right-pinched mapping spaces model the required path spaces, without treating the raw nerve as Kan |
| Cofibrant, fibrant and bifibrant inclusions | `ReplacementInclusions` asserts weak homotopy equivalence of the three enlarged nerve maps of `restriction P IsCofibrant`, `restriction P IsFibrant`, and `restriction P (fun X ↦ IsCofibrant X ∧ IsFibrant X)` |
| A Quillen adjunction L ⊣ R | `QuillenClause`: `L`, `R`, `adj : L ⊣ R`, preservation of cofibrations and of weak equivalences among cofibrations, which together say preservation of trivial cofibrations |
| Derived functors, computed with replacements | Arbitrary functorial Q with `e : Q ⟶ 𝟭 C`, cofibrant values and weak components, and arbitrary fibrant B with `b : 𝟭 D ⟶ B`, followed by the recorded `ModelInfinity.ReplacementAdjunction adj Q e B b qM qN`. These are computations of the derived functors, not additional existence assumptions: the already stated dependency supplies them |
| Chosen classes correspond under derived equivalences | The left represented-class condition in `QuillenClause` and the right represented-class condition in its final implication. With inverse derived unit/counit these are exactly mutual correspondence of the classes, including all equivalent representatives |
| Quillen equivalence, with the actual derived unit/counit | The final implication assumes `IsEquivalenceEdge` of `A.coherent.unitEdge` and `A.coherent.counitEdge`. These are precisely the specified inverse-equivalence transformations of the derived adjunction |
| Induced weak equivalence N(wS) to N(wT), after Q | The conclusion constructs the relative functor on Q followed by L and asserts weak homotopy equivalence of its actual `frameLargeNerveMap (weakFunctor P T (Q ⋙ L) hF hFT)`; the relative-functor and object-class proofs are conclusions, not extra hypotheses |
| On cofibrant objects use L itself when it carries the classes | `CofibrantClause` quantifies over `hLT` expressing precisely this condition, constructs the actual weak-arrow restriction of L, and asserts its nerve map is a weak equivalence under the same inverse-derived and mutual-class conditions |
| Natural for Quillen functors | The comparison edge from `f ≫ l` to `N(LQ) ≫ g` is normalized by an exact equality to the restriction of `A.leftComparison.edge`. This is an edge of the whole internal hom, hence retains higher naturality. The cofibrant clause specifies a 2-simplex whose first two edges are the same derived comparison and the localization of L(e), and whose long edge is the stated cofibrant comparison |
| Right derived comparison | `CoreAdjunction.right_relative` and `right_objects` define the actual RB weak-arrow functor, `right_weak` asserts its nerve is a weak equivalence, and `right_comparison` normalizes its entire coherent comparison edge to the restriction of `A.rightComparison.edge` |
| Natural for derived units and counits | `CoreAdjunction` supplies the restricted core functors and their unit/counit equivalence edges. `unit_normalization` and `counit_normalization` identify their entire images with restrictions of `A.coherent.unitEdge` and `A.coherent.counitEdge`, not merely their component functions or an arbitrary equivalence |

Dependencies read and used:

- `lem-coef-cosimplicial-frame-mapping`, module
  `Sheaf.CategoryTheory.CosimplicialFrameMapping`: read the signature and proof
  docstring of `CategoryTheory.cosimplicial_frame_mapping`, and the actual
  definitions of `frameLargeNerveMap` and `frameVertex`. Its imported
  `Sheaf.CategoryTheory.FiniteReedyLocalization` supplies `largeNerve`,
  `IsLocalization`, `object`, `EquivalentObjects`, and `transformation`; their
  full definitions were read.
- `def-cbc-enhanced-diagrams-cones`, module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`: read the full module, including
  `fullSubcomplex`, `core`, `IsEquivalenceEdge`, `mappingSpace`,
  `mappingSpaceMap`, `diagramVertex`, and `IsWeakHomotopyEquivalence`.
- `lem-coef-model-infinity-derived-adjunction`, module
  `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`: read the complete
  `CoherentAdjunction` and `ReplacementAdjunction` structures and the statement
  and proof docstring of `quillenAdjunctionInfinityLocalization`.
  This already landed proof dependency is additionally listed in `stmt_deps`,
  because the signature uses its specified coherent-adjunction data. It is used
  as published, with no dependency module or repair.
- The stated proof dependencies `EnhancedFunctorConeCalculus`,
  `SimplicialGroupoidLocalization`, and `KanQuillenRightProper` are imported
  without `public`. The two presheaf proof dependencies have no recorded Lean
  module yet, so their proof-only imports are omitted and identified by node id
  in the theorem's complete seven-step proof docstring. They are
  `lem-coef-locally-constant-presheaf-slice` and
  `lem-coef-weak-equivalence-representable-local-model`. Neither is needed to
  state the item or used as an unstated interface.
- Mathlib supplies `InducedWideCategory`, `wideInducedFunctor`, its morphism
  structure and category instance, `ObjectProperty.FullSubcategory`, nerves,
  the ordinary localization Q, geometric realization, and path components.
  There is no second definition of model categories, cores, weak homotopy
  equivalences, or derived adjunctions.

Source check: opened the original HAG II PDF at
https://perso.math.univ-toulouse.fr/btoen/files/2012/04/HAGII.pdf,
Appendix A, PDF pages 213--215 (printed pages 207--209). Proposition A.0.3 is the
presheaf/slice Quillen equivalence, the paragraph before A.0.4 identifies the
same equivalence mapping spaces with paths, A.0.4 gives classifying spaces, and
the left-arrow proof of A.0.6 uses bifibrant replacement. The node's expanded
coherent-localization and Quillen naturality clauses are rendered using its
already recorded derived-adjunction dependency. No change to the source's or
node's mathematical statement is required.

Searches performed in this attempt:

- `msearch.py ... leansearch`: “The nerve of the weak equivalences in a model
  category is equivalent to the core of its infinity localization and is invariant
  under Quillen equivalence”. Eight hits: model-category weak-equivalence data,
  ordinary-localization equivalence transport, the quasicategory condition for
  ordinary nerves, ordinary localization object equivalence, nerve edges,
  homological-complex localization, and nerve reflection. None is this theorem.
- `msearch.py ... leanfinder`: “The nerve of weak equivalences in a model category
  is weakly equivalent to the core of its infinity localization”. Eight hits,
  including `CofibrantObject.instIsLocalizedEquivalenceWeakEquivalencesLocalizerMorphism`,
  `CofibrantObject.instIsLocalizedEquivalenceHoCatWeakEquivalencesToHoCatLocalizerMorphism`,
  `nerveFunctorCompHoFunctorIso`, and nerve reflection/fully-faithfulness results.
  Read the relevant `CofibrantObjectHomotopy.lean` and `NerveAdjunction.lean`
  signatures/docstrings: these are ordinary categorical localizations and
  ordinary nerve adjunctions, not this moduli-space theorem.
- `msearch.py ... loogle '"nerve", "WeakEquivalence"'`: zero hits.
- `msearch.py ... grep 'hammock|weakEquivalence.*nerve|core.*localization'`:
  zero Mathlib hits.
- `rg` for `weakEquivalence.*[Nn]erve|[Nn]erve.*[Ww]eak|localizedCore|weakEquivalenceSubcategory`
  in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  only related filtered/zigzag nerve and hammock-localization modules, none
  stating this theorem; no previous helper of the named kind.
- `grep -rn 'lem-coef-model-weak-equivalence-nerve'` in `WeilConjectures`:
  no hits. Focused DAG searches for weak-equivalence categories locate this
  item and its presheaf proof dependencies, not an independent recorded
  definition of wS. Searches for `InducedWideCategory.*weakEquivalences`,
  `WideSubcategory.*weakEquivalences`, and the new declaration names in the
  project/upstream sources found no duplicate. The generic Mathlib construction
  was read and is reused as an abbreviation.

Edge cases checked before finalizing the statement:

- Empty P or T: empty nerves and cores are allowed; path statements are vacuous
  and the component surjection is between empty types. Correspondence cannot
  silently match an empty class with a nonempty one.
- The zero object, initial/terminal objects, and the empty selected class are
  unrestricted; no pointedness or nonemptiness assumption appears.
- A discrete category, isomorphisms-only weak arrows, and a contractible selected
  class retain the correct automorphism information. Components use Ho(C)
  isomorphism, rather than equality of representatives or raw isomorphism in C.
- A raw weak-arrow nerve need not be Kan; only the localization core is asserted
  Kan. The component and weak-equivalence predicates use realization, which
  applies to all simplicial sets.
- Cofibrant or fibrant subcategories are never assumed to be model categories.
- Q and B are arbitrary functorial replacements satisfying the specified
  conditions, and are not required to fix already cofibrant/fibrant objects.
  The cofibrant clause uses L(e) to account for that case.
- No properness, enrichment, simplicial model structure, combinatoriality,
  finiteness, connectedness, or universe equality is imposed.
- Both object and morphism universes of C and D stay independent; the shared
  maximum is only the universe of lifted simplicial data. The declarations use
  `autoImplicit false`, with explicit universe applications where inference
  would otherwise be ambiguous.

Validation: `scompile.py NE lem-coef-model-weak-equivalence-nerve` compiled both
its sandbox and its intended library module, cleanly with no warnings (about
3.8 and 4.7 seconds per file). The required `deliver2.py --no-push` is the final check.
No STATEMENT-DISPUTED flag, statement correction, dependency module, or new node.

First dry-run attempt: the prescribed `deliver2.py NE
lem-coef-model-weak-equivalence-nerve --no-push` completed its compile phase but
waited over ten minutes for its delivery lock, before producing any staged-file
or preflight result. The process status was `locks_lock_inode_wait` at elapsed
09:53 and it remained waiting afterwards. No lock files were inspected or
changed. This worker stopped only its own waiting invocation; nothing was pushed.
Separately, the final Lean file was recompiled through `scompile.py`
with clean sandbox/library results of 3.2 and 4.0 seconds. The worker retried the required dry run with unbuffered output. READY is issued
only if that invocation reports OK; the independent second reading is still required.

## Second reading by NE

I read the item node, its source place (HAG II Appendix A, Proposition A.0.3,
Corollaries A.0.4--A.0.5 and Proposition A.0.6, PDF pp. 213--215), and the
three recorded dependency interfaces. The source defines the classifying space
as the nerve of the subcategory of equivalences, identifies representable slice
mapping spaces with equivalence mapping spaces, and gives the cofibrant/fibrant
replacement nerve equivalences and their functoriality. The Lean statement
faithfully expands those clauses through the recorded coherent-localization and
derived-adjunction interfaces.

The item statement, object by object and clause by clause, matches as follows.

* The model category is `C` with `[Category.{v} C]`, `[ModelCategory C]`,
  `[HasLimits C]`, `[HasColimits C]`, and the two functorial factorization
  instances in `model_weak_equivalence_nerve`. `P : ObjectProperty C` is the
  full selected class, and `hP` is exactly closure in both directions under
  every `weakEquivalences C` arrow.
* The weak-arrow category on the same objects is `WeakObjects P`, the
  `InducedWideCategory` on `P.FullSubcategory`; `inclusion P` forgets only the
  induced arrow predicate. `localizationDiagram` is the actual enlarged nerve
  map followed by `q`.
* `q` and `hq` are the homotopy-coherent localization and its localization
  property. `represented P q` is the replete full localization subcomplex on
  vertices equivalent to a `q`-image of a `P` object. `localizedCore` and
  `coreInclusion` use the existing `SSet.Enhanced.core`, retaining equivalence
  edges and all higher simplices.
* The first conclusion is an `f` from the enlarged nerve of `WeakObjects P` to
  this core. `Comparison` requires the exact localization square, weak
  homotopy equivalence, Kan condition, `ComponentsFormula`, `PathFormula`, and
  all three `ReplacementInclusions`; no clause is dropped or strengthened.
* `ComponentsFormula` gives a surjection onto realization path components,
  normalizes every represented zero-simplex, and says equality exactly when
  the ordinary weak-equivalence localization objects are isomorphic. This is
  the stated `pi_0` formula in `Ho(M)`.
* `PathFormula` uses the existing right-pinched `mappingSpace`, restricts to
  the full equivalence-edge subcomplex through `equivalenceMaps`, factors the
  canonical `mappingSpaceMap` induced by `coreInclusion`, and asserts that
  factor is a weak homotopy equivalence. It therefore gives the claimed union
  of equivalence components of the derived mapping space without assuming the
  raw nerve is Kan.
* `ReplacementInclusions` states weak homotopy equivalence for the cofibrant,
  fibrant, and bifibrant restrictions, with no model structure imposed on
  those full subcategories.
* For every second model category `D`, `QuillenClause` supplies exactly the
  second model-category limits, colimits, and functorial factorizations; the
  selected `T` and `_hT` closure; a Quillen adjunction `L ⊣ R` via `adj`; and
  preservation of cofibrations plus weak equivalences between cofibrant
  objects. It then quantifies arbitrary functorial `Q,e` and `B,b` with
  cofibrant/fibrant values and weak components, and the recorded
  `ReplacementAdjunction` `A`.
* The Quillen conclusion contains the represented-class hypotheses, the
  actual relative functor on `Q ⋙ L`, its comparison edge normalized to
  `A.leftComparison.edge`, the cofibrant-object `CofibrantClause` (including
  its 2-simplex and `L(e)` edge), and the weak-equivalence nerve conclusion
  under equivalence unit/counit and mutual represented-class conditions. The
  `CoreAdjunction` witness supplies the right derived relative functor, its
  weak nerve map, the normalized right comparison, and normalized coherent
  unit/counit equivalence edges. Thus all naturality clauses in the node are
  retained in their stated order.

Edge cases checked: `P` or `T` empty; empty nerves and cores; zero, initial,
and terminal objects; discrete categories and isomorphisms-only weak arrows;
contractible selected classes and nontrivial automorphisms; arbitrary (also
non-Kan) raw nerves; empty and singleton simplicial degrees; `n = 0`; arbitrary
replacement functors that do not fix already cofibrant/fibrant objects; and
independent object/morphism universes. No nonemptiness, pointedness,
properness, enrichment, combinatoriality, finiteness, connectedness, or universe
equality is imposed.

I repeated the three required existence searches. LeanSearch/LeanFinder and
Loogle queries for the nerve of weak equivalences, localization cores, and
Quillen-equivalence classifying spaces returned only ordinary nerve/localization
or model-category helper results. `rg` over `WeilConjectures`, `lean/Sheaf`,
and `dag/lean_names_upstream.json` found no declaration of this theorem or of
these item-specific helpers; the nearby coherent-nerve and hammock modules are
different notions. The generic constructions in `Mathlib.CategoryTheory.Widesubcategory`
and the recorded enhanced-diagram and model-infinity modules were read and are
used directly.

The only delivery-level mismatch was that the worker's sandbox node correctly
added `lem-coef-model-infinity-derived-adjunction` to `stmt_deps`, because
`ReplacementAdjunction` occurs in the Lean signature; the shared node lacked
that dependency. I verified the dependency declaration and its source-based
interface, retained the addition, and made no other code or statement change.
The module compiles cleanly with the required `scompile.py` invocation.
