## Worker report

Q37, item `lem-coef-model-infinity-derived-adjunction`, 2026-10-16 UTC.
Module: `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`.
Main theorem: `HomotopicalAlgebra.ModelInfinity.quillenAdjunctionInfinityLocalization`.
Its proof and the added prerequisite theorem are the delivery's two `sorry`s. All definitions contain actual constructions
or explicitly written mathematical predicates, and every structure field specifies
concrete data or a particular equation/property of that data.

The previous prerequisite wait is resolved. During this retry,
`scompile.py --source Sheaf.CategoryTheory.EnhancedDiagramsCones` returned its
published source, and the shared DAG gained the corresponding Lean record.
The delivery imports that module and adds its already-landed node
`def-cbc-enhanced-diagrams-cones` to the item's `stmt_deps`, as authorized by
brief-stage2 §5, STMT_DEPS MAY GAIN LANDED NODES. It does not state that node,
copy its module, or modify its record. The item's mathematical statement is unchanged.

Hypotheses and conventions, clause by clause:

- The two categories are `C : Type u`, `D : Type u'`, with independent morphism
  universes `v`, `v'`. `ModelCategory C` and `ModelCategory D` use Mathlib's
  actual classes `cofibrations`, `fibrations`, `weakEquivalences`. They include
  two-out-of-three, retract closure and both lifting/factorization systems.
  Read `ModelCategory` and its two `IsWeakFactorizationSystem` instances in
  `Mathlib.AlgebraicTopology.ModelCategory.Basic`, and
  `MorphismProperty.IsWeakFactorizationSystem` in its owning module.
- The source requires completeness and cocompleteness, rather than only
  Mathlib's finite completeness: the four `HasLimits`/`HasColimits` binders
  supply these. The four `HasFunctorialFactorization` binders supply the
  two functorial weak factorization systems on each category. These hypotheses
  are the ones in the node, not an extra model-category convention.
- Trivial cofibrations/fibrations use Mathlib's intersection with weak equivalences.
  `IsCofibrant` is `Cofibration (initial.to X)` and `IsFibrant` is
  `Fibration (terminal.from X)`, from `ModelCategory.IsCofibrant`.
- `L`, `U`, `adj : L ⊣ U` give the ordinary adjunction. `hL` is preservation
  of cofibrations. `hLt` is preservation of trivial cofibrations, writing its
  two conjunctions explicitly. No preservation of arbitrary weak equivalences
  is assumed on either functor.
- `M` and `N` are the localized quasicategories, with Mathlib
  `SSet.Quasicategory` instances. The inner-horn condition is the actual
  Mathlib definition; no ordinary category substitutes for either localization.
- `FiniteReedy.largeNerve` is `nerve C` followed by the ordinary universe-lift
  functor. Its level is `max u v w`. `frameLargeNerveMap` applies the given
  functor to every composable string; `FiniteReedy.strictEvaluation` evaluates
  a string of functors on a string of objects; `FiniteReedy.transformation`
  curries that evaluation on the actual nerve edge of a natural transformation. These are real
  maps, not arbitrary comparison maps. Their simplicial naturality is checked
  by Lean as part of these definitions.
- Both localizations live in `max u v u' v' w`; object and morphism universes
  have not been identified. Every `ULift` is normalized to that ambient level.
  The independent `w` permits enlargement. No site-universe equality is imposed.
- `qM`, `qN`, `hM`, `hN` specify homotopy-coherent localization. `Inverts`
  sends every weak-equivalence edge to `IsEquivalenceEdge`. `FiniteReedy.localDiagrams`
  is the full subcomplex of the *entire* internal hom on the inverting objects.
  `IsLocalization` says restriction is a functor equivalence onto this full
  subcomplex, with the comparison map characterized by equality with actual
  precomposition. Thus the universal property retains arbitrary transformations,
  mapping spaces and all higher simplices. It is not ordinary localization.
- `Q`, `e`, `hQ` give an arbitrary functorial cofibrant replacement with
  weak-equivalence components; `T`, `t`, `hT` give an arbitrary functorial
  fibrant replacement. They need not be weak equivalence preserving as an
  additional hypothesis: naturality and two-out-of-three imply that. Neither
  `L(e)` nor `U(t)` is assumed an equivalence in general.

Conclusion, clause by clause:

- The first two conjuncts are preservation of fibrations and trivial fibrations
  by `U` for every morphism of `D`.
- The third conjunct restricts weak-equivalence preservation by `L` to maps
  whose two endpoints satisfy `IsCofibrant`. The fourth restricts preservation
  by `U` to maps with two fibrant endpoints. Neither is accidentally global.
- `Nonempty (ReplacementAdjunction adj Q e T t qM qN)` asserts existence of
  actual simplicial maps `left : M ⟶ N` and `right : N ⟶ M`, with the properties
  below. It is not used to choose any definition's data.
- The `coherent` field contains unit and counit edges in the full internal
  functor simplicial sets, with their four explicit endpoint equations.
  `left_triangle` and `right_triangle` are actual 2-simplices in those functor
  sets: their short edges are the appropriate two whiskerings of unit/counit,
  and their long edge is the degenerate identity. Thus the triangles are
  coherent natural homotopies, not pointwise equalities on homotopy categories.
- The displayed natural mapping-space equivalences are rendered by their
  equivalent universal-arrow formulation (Cisinski §6.1, Proposition 6.1.11
  and its dual). `universal_unit` says the unit at `x` is an initial object
  `(left x, unit_x)` of `(x ↓ right)`; `universal_counit` says the counit at
  `y` is terminal in `(left ↓ y)`. The exact comma vertex is specified both
  on its apex and on its arrow, by evaluating the coherent unit/counit.
  `SSet.Enhanced.IsInitial`/`IsTerminal` mean weak contractibility of the
  full right-pinched mapping spaces, not only uniqueness of components.
  These are precisely universal arrows representing respectively
  `Map_M(x,right(-))` and `Map_N(left(-),y)`. They produce the stated
  equivalences `Map_N(left x,y) ≃ Map_M(x,right y)`, coherently natural in
  both inputs because the representing arrows are entire internal-hom edges.
  The module uses this equivalent formulation directly rather than postulating
  a separate unconnected family of weak equivalences between mapping sets.
- `leftComparison` is an equivalence edge of coherent diagrams
  `qM ≫ left → nerve(Q ⋙ L) ≫ qN`; `rightComparison` is an equivalence edge
  `qN ≫ right → nerve(T ⋙ U) ≫ qM`. These are the two replacement formulas
  as coherent natural equivalences, stronger in presentation than objectwise
  equalities but mathematically the functorial formulas intended by the node.
- `unit_normalization` specifies the following equality of coherent
  transformations after using those comparisons:
  `q(e) ; (unit on qM) ; (leftComparison whiskered by right) ;
  (rightComparison restricted along LQ) = q(eta_Q ; U(t_LQ))`.
  Both sides go from `qQ` to `qUTLQ`. The inverse of `q(e)` is allowed because
  `e` is weak and `qM` inverts it. This is exactly the ordinary-unit zigzag.
- `counit_normalization` states
  `(rightComparison whiskered by left) ; (leftComparison restricted along UT) ;
  q(L(e_UT) ; epsilon_T) = (counit on qN) ; q(t)`.
  Both sides go from `left right qN` to `qT`. Inverting `q(t)` gives exactly
  the ordinary-counit zigzag. There is no assumption that `L(e_UT)` is weak.
- These pasting equations are equalities in the homotopy category of the full
  internal functor simplicial set. `Represents` relates each arrow to its
  specified actual edge, including the endpoint equations. Equality therefore
  means homotopy of coherent transformations; it is not an equality of their
  component homotopy classes. `edgeClass` uses Mathlib's actual homotopy-category
  quotient, not a newly supplied equivalence relation.
- `directlyLocalizedLeft` and `directlyLocalizedRight` are separately conditional
  on preservation of *all* weak equivalences by that side. Each asserts existence
  of a direct localization and a coherent natural equivalence with the derived
  functor, and agreement with every such direct localization. Neither side's
  additional preservation hypothesis is imposed globally on the theorem.
- No enrichment, properness, combinatoriality, presentability, pointedness,
  nonemptiness, fixed coefficient category, or finiteness binder appears.

Dependency declarations used:

- `def-weil-pbc-simplicial-set` is a Mathlib leaf: `SSet` from
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`; morphisms are its natural
  transformations. Its remaining matches `SSet.degenerate`, `SSet.nonDegenerate`,
  `SSet.Subcomplex`, `SSet.Finite` were read in their owning modules; the current
  theorem has no degeneracy-finiteness hypothesis.
- `def-cbc-enhanced-diagrams-cones`, module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `IsEquivalenceEdge`,
  `fullSubcomplex`, `IsFunctorEquivalence`, `diagramVertex`, `evaluation`,
  `comma`, `IsInitial`, `IsTerminal`, `AreNaturallyEquivalent`. Read the complete
  live source and their docstrings. In particular the comma equations hold in
  every simplicial degree, and initial/terminal use weakly contractible mapping
  spaces. No private duplicate of these definitions is present.
- Additional Mathlib interfaces: `CategoryTheory.Adjunction` for the ordinary
  adjunction; `nerve`, `ComposableArrows`, `uliftFunctor`; `ihom` and
  `MonoidalClosed.pre/curry` for coherent diagrams; `SSet.Edge` and
  `SSet.Truncated.HomotopyCategory.homMk` for actual coherent edges and their
  homotopy classes. `ModelCategory` supplies exactly the model axioms discussed above.
- The proof dependency `lem-coef-cosimplicial-frame-mapping` is now stated in
  `Sheaf.CategoryTheory.CosimplicialFrameMapping` and imported by the item.
  Its previously absent statement is the substantive repair requested for
  returned immutable head `b04b56508301`; see the dependency audit below.

## Dependency modules

`lem-coef-cosimplicial-frame-mapping` is included as
`lean/Sheaf/CategoryTheory/CosimplicialFrameMapping.lean`, with the main statement
`CategoryTheory.cosimplicial_frame_mapping`. The shared-base node has no `lean`
record and no Mathlib match. The explicit return for immutable head `b04b56508301`
authorizes stating this missing non-elementary prerequisite in this delivery.
The retained live-source interface is supplied as a module and a lean-only node
binding, rather than relying on its availability in a compiler overlay. The source
lookup was compared byte for byte with the retained `current` scratch file; they agree.
The only source addition is the ordinary proof-only import of
`Mathlib.AlgebraicTopology.ModelCategory.BrownLemma`, for its existing Mathlib
proof dependency `lem-coef-brown-split-factorizations`.

The prerequisite node is copied from the current shared base and changes only `lean`.
No new DAG node, statement correction, proof change, or dependency change is made.
The consumer retains its existing public import of the prerequisite. The old report's
claim that concurrent publication made delivery of the prerequisite unnecessary is
withdrawn. Both modules and both node bindings are now explicitly delivered.

Prerequisite hypotheses and conclusions, clause by clause:

- `C : Type u`, `[Category.{v} C]`, `[ModelCategory C]`, `[HasLimits C]`,
  `[HasColimits C]`, and both `HasFunctorialFactorization` instances express
  the node's model category and functorial factorization convention. The
  object and morphism universes remain independent. The target universe
  `max u v u' v' t` permits enlargement and a second differently sized category.
- `K`, `q`, `hq : FiniteReedy.IsLocalization (weakEquivalences C) q` specify
  the homotopy coherent localization, including quasicategory structure.
  `IsLocalization` is the published predicate on the entire internal hom,
  not an ordinary-category localization. It is imported, not redefined.
- `CosimplicialFrame C X` contains an actual `CosimplicialObject C`, equality
  of degree zero with `X`, an augmentation to the constant `X`, its objectwise
  weak-equivalence property, and `augmentation_zero` identifying degree zero
  with the equality transport of the identity.
- `FrameLatchingIndex n` is the full subcategory of `Over [n]` on monomorphisms
  from strictly smaller simplices. For simplex maps this is precisely the
  category of nonidentity injective faces and their factorization triangles.
  `frameLatchingDiagram` is restriction along the slice forgetful functor.
  `frameLatchingCocone` uses the actual face maps. Each frame has a
  `ColimitCocone` and `latching_cofibration` for its canonical desc map into
  degree `n`; these are not freely chosen arrows called latching maps.
- `CosimplicialFrameMappingData.frames_exist` supplies a frame for each
  cofibrant `X`. `object_representatives` supplies both a cofibrant and a
  fibrant representative for every localized vertex, using equivalence edges.
- `frameHom A Y = A.op ⋙ yoneda.obj Y` has degree `n` equal to `Hom(A^n,Y)`.
  Its operators are precomposition. `hom_kan` states the Kan condition for
  every frame and every fibrant target. `frameHomLarge` only applies `ULift`.
- `comparison` is an isomorphism in `FrameSpaceHo`, the localization of
  simplicial sets at the existing realization weak homotopy equivalences.
  Its other object is the published right-pinched
  `SSet.Enhanced.mappingSpace K (qX) (qY)`. Thus it compares homotopy types
  of full mapping spaces, rather than sets of homotopy classes.
- `actual_maps` normalizes the comparison on each actual `f : X ⟶ Y`:
  the framed vertex maps to the actual edge `q(f)`, with its two endpoint
  equalities. `component_representatives` says every point in the homotopy
  type of that mapping space has an actual map as representative.
- `target_naturality` and `frame_naturality` are both canonical naturality
  squares. `frameHomPost` postcomposes with the target map, while
  `frameHomPre` precomposes with the given frame transformation.
  `FrameMappingRelation` uses the two endpoint evaluation maps from the
  arrow quasicategory. It expresses their actions in the homotopy theory
  of spaces, without introducing arbitrary pre/postcomposition maps.
- `fibration_mapping` states that a fibration between fibrant targets gives
  a map with the right lifting property against all horn inclusions
  (`SSet.modelCategoryQuillen.J.rlp`). If the original map is also weak,
  the function-complex map is a weak homotopy equivalence as well, giving
  the trivial Kan fibration clause.
- `FrameKanPullbacksAndProducts` gives the strict-pullback assertion by
  replacing the right leg by a weakly equivalent Kan fibration and asserting
  that the actual `framePullbackComparison` is a weak homotopy equivalence.
  Its existence clause covers arbitrary right legs. The product assertion
  uses `Limits.Pi.map` for every finite family, including the empty family.
- For each other model category and localization, `FrameLeftQuillenClause`
  supplies compatible target comparison data. It quantifies over an ordinary
  adjunction whose left functor preserves cofibrations and trivial
  cofibrations. It asserts Brown preservation on cofibrant weak equivalences,
  preservation of cofibrant objects, and image frames with the actual
  cosimplicial functor and augmentation (`FrameIsImage`).
- The same clause supplies an actual localized simplicial functor and an
  equivalence edge of entire coherent diagrams on the cofibrant subcategory.
  Its mapping action is compared with `frameFunctorHomMap`, literally
  `f ↦ T(f) ≫ j` in each degree, where `j` is a fibrant replacement of
  the target. The target comparison uses the specified image frame, the
  induced mapping-space map, and canonical endpoint evaluation. Checking
  the action on bifibrant targets suffices by target naturality, fibrant
  representatives, and the fibration clause; proof step 12 explains this
  transport to an arbitrary fibrant target. Hence evaluation and restriction
  when left Quillen receive the compatibility used in the consumer's proof.
- `cosimplicial_frame_mapping` assembles this data, the pullback/product
  assertion, and compatibility for arbitrary second categories. Its twelve
  docstring paragraphs follow all twelve proof steps of the existing node,
  including Brown factorization, the bisimplicial comparison, special
  resolution zigzags, hammock localization, and the transported-diagram
  argument. Exactly this named theorem remains `sorry` in the module.

Dependency declarations read and reused:

- The Mathlib simplicial-set leaf `def-weil-pbc-simplicial-set`: `SSet`
  (`Basic`), `SSet.degenerate` and `SSet.nonDegenerate` (`Degenerate`),
  `SSet.Subcomplex` (`Subcomplex`), and `SSet.Finite` (`Finite`).
- `Sheaf.CategoryTheory.FiniteReedyLocalization`: `largeNerve`, `IsLocalization`,
  `object`, `Composes`, `EquivalentObjects`; the consumer additionally uses
  `strictEvaluation`, `diagram` and `transformation`. Their full signatures
  and docstrings were fetched through `scompile.py --source`. These concrete
  helpers are used; the downstream finite-Reedy theorem is not a prerequisite
  of the frame statement and no reverse import is added.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: the realization weak-equivalence
  predicate, mapping spaces and their induced maps, diagram vertices,
  evaluation, equivalence edges and natural equivalences. Its complete live
  source was fetched; the consumer also uses its comma/initial/terminal
  constructions. No duplicate of a published enhanced notion is introduced.
- Mathlib `CosimplicialObject`, `yoneda`, `Over`, `ObjectProperty.FullSubcategory`,
  `ColimitCocone`, `SSet.KanComplex`, the Quillen horn-lifting predicate,
  `CofibrantObject`, `ModelCategory` and the factorization classes.
  `BrownLemma` is imported for the existing Mathlib proof prerequisite;
  the other proof prerequisites have no recorded Lean module yet and remain
  cited in the node and the full proof docstring.

Prerequisite edge cases checked: at `n = 0` the latching indexing category is
empty and its colimit is initial, so the cofibrancy condition is retained.
The augmentation at degree zero is identity after the specified equality.
Empty mapping spaces are allowed. The finite-product clause includes an empty
index. The terminal simplicial set and trivial model category cause no failure.
Neither simplicial enrichment, properness nor combinatoriality occurs as a
hypothesis. Object/Hom universes and the universes of the two model categories
are independent; all mapping objects are lifted to their maximum.

## Repair of the return

C1, immutable head `b04b56508301`: the missing non-elementary prerequisite
`lem-coef-cosimplicial-frame-mapping` is now stated and delivered, with its own
module, lean-only node binding, complete proof-plan docstring, and report
inventory above. The consumer still cites and imports it. The consumer theorem
signature and definitions are unchanged. Both modules are compiled separately
in dependency order by the prescribed wrapper. The delivery wrapper rebases
the sandbox delta onto current `newtargets-dag`; no direct Git mutation is used.
The previous second-reading text is archived in the sandbox scratchpad because
it described omission of this prerequisite. A fresh second reader will review
this repair and deliver it.

## Searches and sources

Fresh searches made during this repair, through `msearch.py Q37
lem-coef-model-infinity-derived-adjunction` (actual output retained in
`searches.jsonl`):

- LeanFinder: “Cosimplicial frames of cofibrant objects compute mapping spaces
  in infinity localization of arbitrary model categories”. Eight hits were
  ordinary cofibrant-object localizer and homotopy-category declarations;
  none supplies the frame mapping-space statement.
- Loogle: `"CosimplicialObject", "ModelCategory"`. Zero hits.
- Grep: `cosimplicial.*frame|CosimplicialFrame|functionComplex`. Zero Mathlib hits.
- LeanSearch: “Cosimplicial frames compute infinity localization mapping spaces
  naturally in both inputs and under left Quillen functors”. Eight hits include
  cosimplicial (co)limits and ordinary localizations, not this theorem.
- Direct `rg` of upstream `WeilConjectures`, the shared `lean/Sheaf`, and the
  upstream-name index for the frame names, the main adjunction theorem, and
  `frameLargeNerveMap` found no competing statement. The live source lookup
  does supply the retained frame module, which this repair includes with its
  missing DAG binding as explicitly requested. Existing searches for the
  consumer and prerequisite remain unchanged in their node records.

Source places checked: Hovey Definition 5.2.7, Theorem 5.2.8, Corollary 5.4.4
and Proposition 5.4.7 (frames, Kan mapping complexes, invariance); Hinich
Theorem 1.3.3 (mapping-space comparison) and Proposition 1.5.1 (Quillen
adjunction); Cisinski Theorem 7.5.30 and paragraph 7.5.25 (derived adjunction
and replacements), Corollary 3.8.4 (strict Kan pullbacks). The URLs are exactly
those recorded in the nodes. No statement correction or dispute is introduced.

## Validation

Both modules passed the prescribed per-file compilation through `scompile.py`,
including the two-module compilation performed by `deliver2.py --no-push`,
without compiler errors or warnings. The required dry-run command is
`python3 /home/ubuntu/weil-launcher-nt/deliver2.py Q37
lem-coef-model-infinity-derived-adjunction --no-push`; its output is retained
in the sandbox at `scratchpad/current-repair-dry-run.log`. Every delivered
theorem has `sorry` as its proof; no definition contains `sorry`. Both recorded
signatures are extracted verbatim from their respective modules. The copied
prerequisite node differs from current shared base only in `lean`. The item
changes only its Lean binding and its already retained statement dependencies.
All Lean lines have at most 100 characters and all variables/universes are explicit.


## Second reading by Q37

Independent second reader, 2026-10-17. I read the current shared node and both
sandbox node records with both delivered Lean modules open, then read the owning
signatures in `EnhancedDiagramsCones`, `FiniteReedyLocalization`, and Mathlib's
model-category, nerve, simplicial-object and homotopy-category interfaces. I also
read the current source of `CosimplicialFrameMapping` through `scompile.py --source`:
it is byte-for-byte the delivered dependency module after removing the added
proof-only `BrownLemma` import. Its live availability is not being used to omit its
node binding or delivery: the prerequisite remains explicitly in this packet.

The source places are not Stacks tags. I opened the PDFs named by the nodes:
[Cisinski](https://cisinski.app.uni-regensburg.de/CatLR.pdf), Theorem 7.5.30,
paragraphs 7.5.23--25, and Proposition 6.1.11 with its dual;
[Hinich](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hinich.pdf),
Theorem 1.3.3 and Proposition 1.5.1; and
[Hovey](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf),
Definition 5.2.7, Theorem 5.2.8, Corollary 5.4.4 and Proposition 5.4.7.
The sources confirm the general model-category setting, the framed comparison,
and derived adjunction without a simplicial enrichment. Cisinski's universal-arrow
criterion supports the equivalent comma formulation used below. I checked its
strict-pullback source, Corollary 3.8.4, as well.

Here is my statement inventory, matched item by item; each verdict is PASS.

1. Two complete and cocomplete ordinary model categories, with two-out-of-three,
   retract closure, both mutually characterized lifting classes, and functorial
   factorizations: `C : Type u`, `D : Type u'`, independent
   `[Category.{v} C]`, `[Category.{v'} D]`, `[ModelCategory C/D]`, all four
   `HasLimits`/`HasColimits` instances, and the four displayed
   `HasFunctorialFactorization` instances. Mathlib's `ModelCategory` has only finite
   (co)limits by itself, so the full (co)limit assumptions are needed and correctly
   present. Its two `IsWeakFactorizationSystem` instances give the mutually
   characterized classes, not just one direction of lifting. The extra retract
   closure of (co)fibrations in the Mathlib class follows from those systems and
   introduces no mathematical restriction.
2. Trivial maps mean membership in both the appropriate class and weak equivalences.
   The intersection properties in the factorization binders and the explicit
   conjunctions in `hLt` and the second conclusion use precisely this convention.
   Cofibrant and fibrant are the imported `IsCofibrant` and `IsFibrant`, defined by
   `initial.to` and `terminal.from`. No private replacement notions are used.
3. Ordinary functors and adjunction: `L : C ⥤ D`, `U : D ⥤ C`, `adj : L ⊣ U`.
   The only preservation hypotheses are `hL` and `hLt`, on cofibrations and trivial
   cofibrations. Weak-equivalence preservation on arbitrary maps is not assumed.
4. Infinity localizations and all required size enlargements: `M N : SSet` at
   `max u v u' v' w`, with `SSet.Quasicategory`; `qM`, `qN` have the actual lifted
   ordinary nerves as domains. `hM`, `hN` are `FiniteReedy.IsLocalization` for the
   corresponding `weakEquivalences`. I read that predicate: it requires inversion
   of the specified edges, and equivalence of the entire internal functor object
   with `localDiagrams`, with its map equal to actual precomposition. The full
   subcomplex imposes inversion only on objects and retains every higher simplex.
   This is the coherent universal property, not a homotopy-category localization.
5. Functorial replacements: `Q`, `e : Q ⟶ 𝟭 C`, `hQ`, and `T`,
   `t : 𝟭 D ⟶ T`, `hT`. Components are weak equivalences and values are cofibrant
   or fibrant; no trivial-fibration/trivial-cofibration requirement has been added
   to these arbitrary replacements. Their order is before the whole conclusion,
   so the result holds for every such choice. Functorial factorizations ensure
   that these choices can be supplied.
6. Right-adjoint preservation of fibrations and trivial fibrations: the first and
   second conjuncts quantify over every `f : X ⟶ Y` in `D`, with exactly the
   indicated antecedents and both trivial-fibration conclusions.
7. Brown preservation: conjunct three asks for `IsCofibrant X` and
   `IsCofibrant Y` in `C`; conjunct four asks for `IsFibrant X` and `IsFibrant Y`
   in `D`. Each then takes `WeakEquivalence f` and concludes the mapped weak
   equivalence. The clauses neither omit the endpoints nor assert global
   preservation.
8. Derived functors and adjunction: `Nonempty (ReplacementAdjunction adj Q e T t
   qM qN)` asserts actual simplicial maps `left` and `right` with `coherent`.
   `CoherentAdjunction` has unit/counit edges of full internal homs with all four
   endpoints fixed and triangle 2-simplices whose long edge is the respective
   degenerate identity and whose short edges are the correct whiskerings.
9. Natural equivalences of full mapping spaces: `universal_unit` specifies the
   exact vertex `(left x, unit_x)` in `comma N M right x false` and its
   `IsInitial` property; `universal_counit` specifies `(right y, counit_y)` in
   `comma M N left y true` and its `IsTerminal` property. I checked both comma
   endpoint conditions and the direction of initial/terminal. Their definitions
   require weak contractibility of full right-pinched mapping spaces. These are
   universal arrows for `Map_M(x,right(-))` and `Map_N(left(-),y)`, respectively,
   yielding the displayed mapping-space equivalences with the specified arrows.
   The arrows vary as full coherent transformations, rather than an unrelated
   family of component bijections. This equivalent adjunction formulation retains
   the node's full mapping-space conclusion.
10. Replacement formulas: `leftComparison` and `rightComparison`, each an
    equivalence edge of an entire functor simplicial set, compare `qM ≫ left`
    with the actual localized `Q ⋙ L` diagram, and `qN ≫ right` with `T ⋙ U`.
    The domain functors and replacement order match the node exactly.
11. Ordinary unit normalization: `unit_normalization` pastes `q(e)`, the derived
    unit, the left comparison whiskered by `right`, and the right comparison
    restricted along `Q ⋙ L`; it equals the localization of
    `eta_Q ; U(t_LQ)`. Its source is `qQ` and target is `qUTLQ`. Since `q(e)` is
    invertible, this is precisely the unit zigzag stated in the node.
12. Ordinary counit normalization: `counit_normalization` pastes the right
    comparison whiskered by `left`, the left comparison restricted along
    `T ⋙ U`, and `q(L(e_UT) ; epsilon_T)`, and equates that with the derived
    counit followed by `q(t)`. Both go to `qT`; inverting `q(t)` gives the node's
    counit zigzag. Neither `L(e_UT)` nor `U(t_LQ)` is incorrectly assumed weak.
    `Represents` fixes every edge's endpoints and actual `homMk` class. These
    equations live in homotopy categories of full internal homs, and hence mean
    homotopies of coherent transformations, not mere componentwise equations.
13. Agreement with direct localization: `directlyLocalizedLeft` and
    `directlyLocalizedRight` each start with that side's separate conditional
    preservation of all weak equivalences. Each supplies a direct localization
    comparison, its coherent equivalence with the derived functor, and agreement
    with every such direct localization. The conditions are not theorem hypotheses.
14. No enrichment, properness or combinatoriality: no such binder or structure
    field occurs. No coefficient field, characteristic, pointedness, finiteness,
    or nonemptiness constraint was introduced.

The additional dependency `lem-coef-cosimplicial-frame-mapping` was read as a
stage-2 statement in its own right. Its shared node has no usable Lean binding;
the included node changes only `lean`. The following matches are PASS:

- The same complete/cocomplete model category and both functorial systems are
  explicit theorem binders. `q` and `hq` use the same coherent localization,
  and its quasicategory hypothesis is contained in `hq`.
- `CosimplicialFrame` contains the actual cosimplicial object, degree-zero equality,
  augmentation with weak components and the normalized identity in degree zero.
  `FrameLatchingIndex` is the full proper-injective-face slice: monomorphisms in
  the simplex category are the injective order maps, and `len < n` excludes
  identities. Its morphisms are the full commuting triangles. `latching` supplies
  actual colimit cocones; `latching_cofibration` uses their canonical desc maps,
  not arbitrary arrows.
- `frames_exist` and `object_representatives` give all the node's existence clauses.
  `frameHom` is literally `A.op ⋙ yoneda.obj Y`, and its maps are precomposition.
  `hom_kan` supplies the full Kan condition for every frame and fibrant target.
- `comparison` is an isomorphism after localizing simplicial sets at realization
  weak homotopy equivalences. Thus the comparison retains the full homotopy type.
  `actual_maps` fixes each actual edge `q(f)` and its endpoints;
  `component_representatives` covers all components, as maps from the point in
  that localization. `target_naturality` and `frame_naturality` use the actual
  endpoint-evaluation span of the arrow quasicategory. The latter permits every
  frame transformation; its degree-zero map is transported in the correct order.
- `fibration_mapping` uses the Quillen horn right-lifting predicate, and a weak
  fibration additionally yields a realization weak equivalence. This is the Kan
  and trivial Kan fibration assertion, including every fibrant endpoint pair.
- `FrameKanPullbacksAndProducts` replaces every right leg by a weakly equivalent
  Kan-fibration leg and asserts weak equivalence of the actual pullback comparison.
  This is the fibrant-diagram formulation of the strict homotopy-pullback clause.
  Its product map is the actual `Limits.Pi.map`, with `[Finite I]`.
- `FrameLeftQuillenClause` quantifies over every second category, localization and
  ordinary left Quillen adjunction. It asserts Brown preservation, preservation
  of cofibrant objects, and image frames with their actual cosimplicial functor
  and augmentations. The localized functor has an entire coherent comparison on
  the full cofibrant subcategory. The mapping compatibility uses exactly
  `frameFunctorHomMap`, sending `f` to `T(f) ≫ j`. It is tested on bifibrant
  targets; the general fibrant-target clause follows by a trivial fibration from
  a bifibrant replacement, `fibration_mapping`, and target naturality. I checked
  proof-plan step 12's transport rather than treating that restriction as an
  added hypothesis. This supplies evaluation/restriction compatibility when
  those functors satisfy the stipulated left Quillen condition.

Edge cases checked: zero-dimensional latching has an empty index and gives the
initial-to-`X` map; `augmentation_zero` fixes the identity even at `n = 0`.
The finite-product family can be empty, giving the identity on the terminal
simplicial set. Empty mapping spaces are allowed; contractibility requires the
component condition, so an empty space is not inadvertently declared contractible.
An empty ordinary category cannot satisfy the source's initial/terminal existence,
and Lean imposes no further nonempty binder. A terminal model category and pointed
categories with a zero object remain covered. Schemes and coefficient characteristic
are not parameters here, so no scheme/characteristic edge case is discarded.
The object and morphism universes of both categories remain independent and all
mapping constructions are lifted to their maximum with a freely enlargable extra
universe; no size equality was introduced.

Fresh independent searches (recorded by `msearch.py` in `searches.jsonl`):

- LeanFinder, "Left and right Quillen derived functors form adjoint functors
  between quasicategory localizations with coherent unit and counit": eight hits,
  all ordinary `Adjunction.derived`/`localization` variants. I opened
  `Mathlib.CategoryTheory.Functor.Derived.Adjunction`: these conclude ordinary
  adjunctions and do not supply this node. I also opened the upstream derived
  adjunction module; its abelian/K-flat/K-injective adjunction is another setting.
- LeanSearch, "Universal arrows in quasicategories give an adjunction with natural
  equivalences of mapping spaces": eight ordinary-category or Kan-extension hits;
  none uses full quasicategory mapping spaces.
- Loogle, `"Quasicategory", "Adjunction"`: zero hits.
- Grep, `CoherentAdjunction|ReplacementAdjunction|quillenAdjunctionInfinityLocalization|cosimplicial_frame_mapping`:
  zero Mathlib hits. Direct `rg` in upstream `WeilConjectures`, shared `lean/Sheaf`,
  and Mathlib's AlgebraicTopology/CategoryTheory found no competing statement;
  `FiniteReedyLocalization` mentions this theorem only in its proof plan.
- For the prerequisite, LeanFinder with "Augmented Reedy cofibrant cosimplicial
  resolution computes the simplicial function complex naturally in a fibrant
  target" returned eight cosimplicial/ordinary cofibrant-resolution declarations,
  not the theorem. Loogle `"CosimplicialObject", "KanComplex"` and grep
  `cosimplicial.*resolution|Reedy.*cofibrant|mapping.*frame` returned zero hits.
  The already available live prerequisite source is explicitly delivered and
  bound here, as the return requires; no competing recorded declaration exists.

No new definition node or statement correction is present, so no new-node field
check or correction-citer audit is applicable. Each definition has concrete data
or an explicit predicate, with no `sorry` in it. The only postponed proofs are
`quillenAdjunctionInfinityLocalization` and `cosimplicial_frame_mapping`, each
with its own matching existing DAG node and all six/twelve natural-language proof
steps in its docstring. Their `lean.statement` values match the source signatures
verbatim; every listed helper has its owning source/blueprint docstring, and no
line exceeds 100 characters. All universes and variables are bound explicitly.

Mismatches found and changes: the mathematical signatures and definitions needed
no repair. I fixed the worker report's obsolete name `invertingDiagrams` to the
actual `FiniteReedy.localDiagrams`, and repaired its unfinished cross-reference.
I verified the returned-prerequisite repair rather than repeating the superseded
one-module second reading. Both modules, both node bindings, the prerequisite's
BrownLemma proof import, and the repaired report are included in the delivery.

Second-reader validation: the prescribed two-file `scompile.py Q37
lem-coef-model-infinity-derived-adjunction` invocation passed on 2026-10-17,
with no errors or warnings. Both delivered files compiled separately under the
unchanged 60-second limit (11.2 s and 8.1 s for the library checks).
