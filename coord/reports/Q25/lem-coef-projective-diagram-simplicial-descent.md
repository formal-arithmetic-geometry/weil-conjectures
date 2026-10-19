## Worker report

The module `Sheaf.CategoryTheory.ProjectiveDiagramSimplicialDescent` states
`CategoryTheory.ProjectiveDiagramDescent.projective_diagram_simplicial_descent`, with
one `sorry` and no proved theorem. Its seven helpers give the representations of this
node's diagram functor and restriction cones; all definition data are explicit.
There are no new nodes, dependency repairs, or statement corrections.

Source read: [HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
Corollary A.3.6.18 and its proof, printed p.905 (PDF page 923), and the proof of
Proposition the project server, assertion (*), printed p.84 (PDF page 102). The former states
the localized projectively fibrant diagram homotopy-limit result, and the latter
applies it to opposite coherent realizations of simplicial bases. The eight-step
proof docstring follows this node's existing proof, including its one-monic Reedy
span argument and filtered passage from simultaneous chunks.

Hypotheses and clauses, matched to Lean:

- A combinatorial simplicial model category is `{C : Type w} [Category.{u} C]
  [ModelCategory C] [SimplicialCategory C]`, its actual tensor/cotensor datum `T`,
  `hC : CombinatorialModelCategory.{w, u, u} C`, and
  `hSM7 : SimplicialModelLocalization.SatisfiesSM7 C`. These are precisely the
  projective-calculus dependency's conventions. Objects and mapping objects retain
  independent universes `w` and `u`. The model structures and enrichments of the
  diagram categories occur as the existential `D : DiagramSystem T`; they are not
  additional assumptions.
- The specified Dwyer--Kan model structure and enriched localization are
  `B : BergnerModelData.{max u w}` and `L : LocalizationSystem B`. These carry the
  full model axioms and the derived pushout adjoining inverses. They are supplied
  constructions from the localization dependency, rather than an arbitrary map or
  an infinity-category comparison.
- Small bases are `SSet.{u}`. `Index S` is exactly
  `(underlying (SSet.PinchedCube.rigidification.obj S))ᵒᵖ`. It uses the recorded
  simplex-colimit realization and Mathlib's enriched opposite, reversing objects
  and mapping objects without taking component categories.
- `D.enrichment S` is the recorded `SimplicialDiagramEnrichment (Index S) C`:
  its mapping objects represent the full graded-transformation end.
  `D.projective S` is `ProjectiveSimplicialModelStructure T (D.enrichment S)`;
  its weak-equivalence and fibration classes are objectwise. `diagramPair` is
  exactly the dependency's `fibrantPair` for this particular projective model
  structure. Thus objects are projectively fibrant diagrams and marked vertex
  arrows are their objectwise weak equivalences. The full enriched subcategory
  and every mapping simplicial set are retained by `liftBundle` in `fibrantPair`.
- `D.restriction f` is a morphism of precisely these marked enriched categories.
  `restriction_value` fixes its diagram values to precomposition by `C[f]^op`;
  `restriction_action` fixes the entire enriched action by that same precomposition;
  `restriction_mapping` fixes the transformation map on all end projections,
  after the exact degreewise universe lift used in `fibrantPair`. In particular,
  this is not an unconstrained map with the right source and target. Mark
  preservation is part of `PairHom`. `restriction_id` and `restriction_comp`
  give contravariant functoriality. `markedFunctor D` constructs the functor from
  this data and `localizedFunctor D L = markedFunctor D ⋙ L.functor` is the
  asserted `E_A` with exactly the localization's induced restrictions.
- For any cocone of bases `c`, `restrictionCone E c` has point `E.obj (op c.pt)`
  and leg `E.map (c.ι.app j.unop).op`. Its transitions are those of `F.op ⋙ E`.
  `IsDescentCone B E c` applies the recorded `IsDerivedLimit` to this exact cone
  with `B`'s weak-equivalence and cofibration classes. Thus every conclusion is
  about restriction, including its maps, in enriched Bergner homotopy theory.
- The family clause quantifies over every `J : Type u`, `S : J → SSet.{u}` and
  `c : Cofan S` with `IsColimit c`. It first asserts `IsDescentCone` for this
  coproduct. The globally quantified replacement functor `R` has a natural
  weak equivalence `r : 𝟭 _ ⟶ R` and each `R.obj X` is Bergner fibrant.
  The existential `l` with `hl : IsLimit l` is the ordinary product of the
  replaced factors (the index is the opposite of a discrete category).
  The displayed weak equivalence starts at the actual localized coproduct,
  applies `r` at that object, and uses `hl.lift` of the replaced restriction cone.
  Hence the assertion includes the ordinary-product computation, with its
  canonical comparison, rather than just existence of an unrelated product.
- The pushout clause quantifies over `A V W`, both maps `f` and `g`, and every
  `PushoutCocone f g` with `IsColimit c`; its only extra hypothesis is `Mono f`.
  The derived limit of the opposite span is precisely the displayed homotopy
  pullback of the restrictions to `V`, `A`, and `W`. There is no condition on `g`.
- The sequence clause quantifies over `F : ℕ ⥤ SSet.{u}` and assumes only that
  each successive transition is a monomorphism. `IsColimit c` expresses the union
  as any chosen colimit presentation, without requiring literal subtype equality.
  Its restriction cone is over `ℕᵒᵖ` and is asserted to compute the homotopy
  inverse limit.
- All enriched maps are retained. There is no hypothesis involving right
  fibrations, coherent-nerve equivalence, or identification with infinity
  categories. The imported dependency modules contain their own statements,
  but the definitions above use only their explicit enriched infrastructure.

Dependency declarations used:

1. `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`:
   `CategoryTheory.SimplicialDiagramEnrichment`, its `Diagrams`, `value` and
   `projection`, and `CategoryTheory.ProjectiveSimplicialModelStructure`.
2. `Sheaf.CategoryTheory.SimplicialLocalizationComparisonCalculus`:
   `CategoryTheory.SimplicialLocalizationCalculus.Pair`, `PairHom`, `fibrantPair`,
   `LocalizationSystem`, `IsDerivedLimit`, and `IsBergnerFibrant`. Its full source
   and theorem signature were read, as were the projective dependency's.
3. `Sheaf.AlgebraicTopology.PinchedCubeLatching`:
   `SSet.PinchedCube.rigidification` and its maps, using its explicit simplex-colimit
   construction. The source, docstring and signature of `pinched_cube_latching`
   were also read.

The stated proof dependencies are imported privately when distinct from these
public dependencies: `ReedyModelStructure`, `RigidificationBoundaryCube`, and
`SimplicialBoundaryCollapseTest`. The remaining proof dependencies have no
recorded Lean module in the base read for this delivery, so no import can yet be
added for them. Their exact roles remain in the eight-step proof docstring.

Edge cases checked before writing: `J` can be empty; its ordinary product is the
terminal enriched category, and the comparison explicitly still starts at the
localization over the empty coproduct. Empty individual bases and empty diagrams
are admitted. The pushout's second arrow is arbitrary, including collapsing maps;
identity and empty-domain first maps are admitted. Constant sequences and the
empty union are admitted. Monomorphisms are allowed to be any injective
presentations, not only prechosen inclusions. Universe enlargement is the actual
`liftBundle` from the dependency, with mapping simplices lifted degreewise and
no equation between `u` and `w`. No restriction to bifibrant diagrams was made.

Searches performed (logged by `msearch.py` under this item):

- LeanFinder: "Localization of projectively fibrant enriched diagrams over coherent
  realization sends simplicial coproducts pushouts along monomorphisms and increasing
  unions to Dwyer Kan homotopy limits". Eight hits concerned ordinary localization,
  simplicial nerve, Cech conerves, and unrelated constructions; none is this result.
- Loogle: `EnrichedFunctor, PreservesLimitsOfShape`. Zero hits, with the diagnostic
  `unknown identifier 'EnrichedFunctor'`; this diagnostic is not positive evidence
  that enriched functors are absent.
- Mathlib grep through `msearch.py`: `descent|homotopy.*limit|rigidification` in
  `AlgebraicTopology`, zero returned hits.
- LeanSearch: "Enriched projective diagram localization takes simplicial base
  colimits to homotopy limits". Eight hits, all simplicial (co)limit existence or
  ordinary-localization product results; none is enriched diagram descent.
- Direct `rg` of the upstream `WeilConjectures` tree for the item id returned no
  match. Keyword searches of its `CategoryTheory` tree returned only unrelated
  triangulated homotopy limits, and no enriched descent statement. Direct searches
  of project `lean/Sheaf/CategoryTheory` and `AlgebraicTopology` found the existing
  dependencies and downstream proof docstrings, not an existing statement of this
  node. Mathlib's `Enriched.Opposite` and its full instance signatures were read;
  its existing opposite enrichment is used, not copied.

Validation: the prescribed `scompile.py` successfully elaborated the module in
both sandbox and library placements. One unused binder warning on the argument
of the restriction family was corrected by renaming it `_f`. The final delivery
dry run below recompiles the final source and checks the node record and packet.

## Second reading by Q25

I independently read the node's statement and all eight proof steps, the delivered
module, the three statement-dependency nodes, and the source declarations used
from their recorded modules. There is no repair note for this item. The sandbox
contains only the item's module and node; there are no new definition nodes or
dependency modules to audit, and no stage-2 `statement_change`.

Source check: I opened HTT online at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf and read Corollary A.3.6.18
and its proof (printed p.905, PDF page index 922), together with assertion (*) in
the proof of Proposition the project server (printed p.84, PDF page index 101). The general
corollary uses a combinatorial enriched model category and a homotopy-colimit
index cocone; the application uses the opposite coherent realization and
localized projectively fibrant diagrams. Specializing the enrichment to simplicial
sets gives the node's setting. No Stacks tag belongs to this item. I also checked
the standing model/tensor/SM7 conventions through the dependency declarations,
rather than importing extra hypotheses from the right-fibration application.

My checklist of the objects, hypotheses and conclusions, matched item by item:

1. **Coefficient model category.** `{C : Type w}`, `[Category.{u} C]`,
   `[ModelCategory C]`, `[SimplicialCategory C]`,
   `T : SimplicialTensorCotensor C`,
   `hC : CombinatorialModelCategory.{w, u, u} C`, and
   `hSM7 : SimplicialModelLocalization.SatisfiesSM7 C` render precisely the
   dependency's combinatorial simplicial model category. I read
   `SimplicialTensorCotensor` (universal tensor/cotensor elements), `SatisfiesSM7`
   (the actual mapping-corner map), and `CombinatorialModelCategory` (local
   presentability, both generating sets and functorial factorizations).
   There is no properness assumption on C. Verdict: matches.
2. **Enlarged enriched homotopy theory.** `B : BergnerModelData.{max u w}`
   specifies a model structure whose weak equivalences are exactly DK
   equivalences and whose other classes are characterized, not an arbitrary
   model. `L : LocalizationSystem B` includes the localization unit and a
   `LocalizationPresentation` for its derived pushout adjoining inverses.
   These are choices of the constructions specified in the dependency, and
   the assertion is valid for any such choices. Verdict: matches.
3. **Small simplicial bases and their indices.** `S : SSet.{u}` and
   `Index S = (underlying (SSet.PinchedCube.rigidification.obj S))ᵒᵖ` give
   exactly the opposite coherent realization. I opened `coherentSimplex`,
   `rigidification`, and `coherentSimplexUnit`: realization is the left Kan
   extension of the subset-poset coherent simplices along standard simplices.
   Mathlib's `EnrichedCategory.opposite` reverses mapping objects and composition;
   it does not take path components. Verdict: matches.
4. **Enriched diagram category.** `D.enrichment S` has type
   `SimplicialDiagramEnrichment (Index S) C`. I checked its `represents` and
   `represents_projection` fields: they represent the full graded-transformation
   presheaf, with identity/composition projections. Thus this is the category
   of enriched diagrams with its actual transformation simplicial sets, not
   ordinary diagrams or only vertex transformations. Verdict: matches.
5. **Projectively fibrant objects and markings.** `D.projective S` is a
   `ProjectiveSimplicialModelStructure T (D.enrichment S)`. Its
   `weak_equivalence_objectwise` and `fibration_objectwise` fields specify the
   projective classes. `diagramPair` applies the dependency's `fibrantPair`
   using this exact model structure. I read `fibrantPair` and `liftBundle`:
   the objects are all fibrant objects, the enrichment is full, and the marked
   arrows are exactly their model weak equivalences, enlarged by degreewise
   `ULift`. No cofibrancy of diagrams was added. Verdict: matches.
6. **Actual restriction and its functoriality.** `D.restriction f` is a
   `PairHom` between these exact categories. `restriction_value` fixes object
   values by precomposition; `restriction_action` fixes the entire enriched
   diagram action; `restriction_mapping` fixes the transformation map after
   every end projection, including the degreewise lift. Their `HEq`s transport
   endpoint types and do not discard maps. The end representation determines
   those maps. `restriction_id` and `restriction_comp` give the functor laws.
   `markedFunctor D ⋙ L.functor`, namely `localizedFunctor D L`, therefore
   gives the specified contravariant localized functor. Verdict: matches.
7. **The cone is the restriction cone.** For any `c : Cocone F`,
   `restrictionCone E c` has point `E.obj (op c.pt)` and leg
   `E.map (c.ι.app j.unop).op`, over `F.op ⋙ E`. `IsDescentCone B E c`
   applies the recorded `IsDerivedLimit` to this very cone and B's classes.
   I read `IsDerivedLimit` and `IsInjectivelyFibrant`: the canonical comparison
   to a strict limit of an objectwise weakly equivalent injectively fibrant
   diagram must be weak. It is not a claim about an unrelated equivalent object.
   Verdict: matches.
8. **Every small family, including the empty one.** The family clause ranges
   over all `J : Type u`, `S : J → SSet.{u}`, and colimit `Cofan S`.
   Its first conjunct is `IsDescentCone` for the actual restrictions. There is
   no `Nonempty J`, finiteness, or fixed coproduct presentation. Verdict: matches.
9. **Ordinary product after functorial fibrant replacement.** The existential
   `R` and `r : 𝟭 SCat ⟶ R` occur before the family quantifiers. Every component
   of r is weak and every `R.obj X` is Bergner fibrant. For each family, `l`
   with `hl : IsLimit l` is the ordinary product cone on the replaced factors.
   The required weak map is `r.app` at the localized coproduct followed by
   `hl.lift` of the replaced restriction cone. Thus the product computation
   includes the canonical comparison from the original vertex. The opposite
   of the discrete index has exactly the same product interpretation.
   Verdict: matches.
10. **One-monic pushouts.** For all `A V W`, `f : A ⟶ V`, and `g : A ⟶ W`,
    only `Mono f` is assumed. Every colimit `PushoutCocone f g` has its
    restriction cone homotopy limiting. Its indexing diagram is the opposite
    span, so the result is precisely the pullback over the localization at A.
    There is no monicity condition on g. Verdict: matches.
11. **Increasing sequence and union.** For every `F : ℕ ⥤ SSet.{u}` the only
    sequence condition is monicity of each successive transition; compositions
    are then monic too. An arbitrary colimit cocone presents its union up to
    the canonical isomorphism. `IsDescentCone` is over the opposite sequence
    and uses its actual restriction legs. Verdict: matches.
12. **Enriched nature and excluded comparison hypotheses.** The conclusions
    live in `SCat` with Bergner weak equivalences; all mapping simplicial sets
    remain in the constructions. No right-fibration classification,
    coherent-nerve equivalence, or infinity-category identification is an
    argument of the theorem. Existence of D supplies simultaneous models and
    restrictions; it is a conclusion, not an extra existence assumption.
    Verdict: matches.

Edge cases: J can be empty, and the displayed ordinary limiting cone is then a
terminal cone; the comparison still begins at the localized empty coproduct.
Empty bases, an empty attaching domain, identity attaching maps, arbitrary
collapsing second maps, and constant sequences are permitted. The sequence
includes n = 0 without a positive-degree requirement. A sequence of empty bases
is allowed. No coefficient ring, characteristic, scheme, or nonzero-object
hypothesis occurs, so these do not impose further restrictions; in particular
the terminal model category is admitted. Universes u and w remain independent:
bases and family indices are u-small, while enriched diagram object types and
the localized categories are enlarged to max u w. The projective and localization
dependencies explicitly support these sizes. All term and universe variables
are bound with `autoImplicit false`; I found no hidden universe equality or
unbound presentation universe in the signature.

Independent searches, using different wording from the worker:

- LeanFinder through `msearch.py`: "Enriched functor categories projective fibrant
  simplicial descent disjoint unions gluing sequential colimits". Eight hits,
  including `SimplicialThickening.functor`, the enrichment of simplicial objects,
  and simplicial-set colimit instances. None states the three enriched DK
  descent assertions.
- LeanSearch through `msearch.py`: "Localization of categories of enriched
  diagrams transforms a homotopy pushout of simplicial indexing categories
  into a homotopy pullback". Eight hits about ordinary localization and
  opposite pushout/pullback isomorphisms. None is an exact match.
- Loogle through `msearch.py`: `SSet, PreservesColimitsOfShape`. No hits, with
  an unknown-identifier diagnostic; I do not count that diagnostic as evidence
  of absence. The successful LeanFinder and LeanSearch searches above supply
  the semantic searches.
- Direct `rg` across Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
  for projective descent, enriched/simplicial descent, homotopy products and
  increasing unions. I also searched the exact item id and declaration namespace
  against upstream names and sources. No exact existing statement was found.
  I opened the closest project result, the complete module
  `Sheaf.CategoryTheory.EnrichedDiagramHomotopyDescent`: its
  `CategoryTheory.enriched_diagram_homotopy_descent` assumes
  `CoherentNerveComparisonStatement` and states infinity-categorical localization
  and representable limit tests in simplicial sets. It is not this theorem's
  enriched localization in SCat without that hypothesis. Its `Index` also takes
  that comparison datum, so it cannot replace this item's explicit construction
  without adding the very comparison hypothesis the node excludes. The other
  hits concern module descent, towers of spaces or downstream applications.

All seven helper declarations have source/blueprint docstrings and explicit
construction data. The only postponed theorem is
`projective_diagram_simplicial_descent`; its proof is `sorry` and its docstring
tracks all eight DAG proof steps. The short proofs inside definitions merely
construct functors and cones; there is no proved theorem or hollow definition.
I checked the recorded signature against the file and all listed declarations
against the file, as well as the 100-column limit and imports. All currently
recorded proof-dependency modules are imported, with proof-only imports private.
The other five proof dependencies still have no Lean record; this delivery
needs none of their interfaces to type its statement.

Mismatches found: none. Changes: appended this independent review; retained the
Lean module and node record unchanged. No statement correction, definition node,
or dependency repair is necessary. Compilation and delivery-preflight results
are recorded below after running the prescribed wrappers.

Validation: `scompile.py Q25 lem-coef-projective-diagram-simplicial-descent`
compiled the sole module cleanly in sandbox and library placements (3.2 s and
3.6 s), with no diagnostics. `deliver2.py ... --no-push` then printed
`OK (dry run): commit 24844fa69c passes the preflight and compiles; nothing pushed`.
The final delivery command reruns these checks on this report's final contents.

## Maintainer review fix (cc reviewer, 2026-10-17)

The delivered signature began `∃ D : DiagramSystem T, ∃ R r, ...`, so the descent
clauses were asserted only for one witness diagram system. The node's `E_A` is the
diagram construction itself, and a citer that has its own enriched diagram models and
restrictions could not apply the theorem without first proving that the clauses do not
depend on the system. The fix keeps every helper and every clause unchanged and moves
the quantifier:
`Nonempty (DiagramSystem T) ∧ ∃ R r, (fibrant replacement) ∧ ∀ D : DiagramSystem T,
(family ∧ pushout ∧ sequence)`. Existence of a system (the node's "restriction of
enriched diagrams defines the contravariant functoriality") is kept as the first
conjunct. The strengthened statement holds because the `represents`/projection fields of
`SimplicialDiagramEnrichment`, the objectwise classes of
`ProjectiveSimplicialModelStructure` and the `restriction_value/action/mapping`
normalizations determine any two systems up to the unique isomorphisms of the end
representations, compatibly with restriction. `IsDerivedLimit` is invariant under such
isomorphisms. The proof docstring records this in a final paragraph. The fixed module
compiles with `tools/nt_compile.py` and gives no diagnostics.
