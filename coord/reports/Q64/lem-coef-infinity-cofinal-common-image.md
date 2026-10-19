## Worker report

Module: `Sheaf.CategoryTheory.InfinityCofinalCommonImage`.
Main declaration: `SSet.Presentability.exists_equivalence_of_kappaCofinal`.
It states exactly the common-image assertion of HTT Lemma the project server; its only
postponed theorem is this declaration, with whole proof `by sorry`.
Three real Prop-valued definitions expand notions introduced by the item's own
statement: `IsKappaCofinal`, `HasTauSmallKappaFilteredColimits`, and
`PreservesTauSmallKappaFilteredColimits`. They belong to this node and are listed
in `lean.declarations`; none contains postponed data or a new independent notion.
No statement correction, new node, or dependency module is needed.

The source was opened at
[HTT, Lemma the project server](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
printed pp. 444–446 (PDF pages 462–464). The IAS URL timed out in the web reader;
the author's Harvard copy supplied the lemma and proof. Its three numbered
hypotheses and conclusion agree with the node. The detailed proof docstring
follows the DAG's expanded argument, including the separate initial odd stage,
fixed-boundary sharp cone replacements, and the compatible-union step.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Universes U in U′ | Explicit `universe u v`; cardinals in `Cardinal.{u}`, all three quasicategories in `SSet.{max (u + 1) v}`. The containing universe really contains the small one. Helpers work at arbitrary explicitly bound `u v`. |
| Infinite regular κ and τ | `hκ : κ.IsRegular` and `hτ : τ.IsRegular`; Mathlib's definition includes `aleph0_le`. |
| κ < τ | `hκτ : κ < τ`. |
| Three quasicategories | `[Quasicategory X] [Quasicategory Y] [Quasicategory Z]`. No ordinary Category instance replaces them. |
| Coherent functors X → Y ← Z | Simplicial maps `(f : X ⟶ Y) (g : Z ⟶ Y)`. |
| Coherent cocone category on r | The dependency's `SSet.Enhanced.coconeCategory r`, a degreewise comma construction retaining all higher simplices. |
| Constant diagram in that cocone category | The existing cocone construction uses `constantDiagrams` and `diagramVertex`; no replacement definition. |
| Weak cofinality: e → f(d) | In `IsKappaCofinal`, `∀ t, ∃ s e`, with source `δ 1 e = t` and target `δ 0 e = Spaces.mappedCocone f r s`, expands exactly weak cofinality of the induced cocone functor. |
| κ-small weakly contractible L | `∀ L, IsKappaSmall κ L → Enhanced.IsContractible L → ...`; no quasicategory or Kan hypothesis on L. |
| Weakly contractible after groupoid completion | The recorded `Enhanced.IsContractible` is weak contractibility of geometric realization, including components; it models the space obtained by inverting all arrows. |
| Every coherent diagram r : L → X | `∀ (r : L ⟶ X)` in `IsKappaCofinal`. |
| Induced functor on cocones | Its exact vertex image is the existing canonical `CategoryTheory.Spaces.mappedCocone f r s`; the witnessing edge lies in `coconeCategory (r ≫ f)`, so it includes the coherent commuting triangle. No arbitrary comparison map is assumed. |
| X, Y, Z are κ-filtered | Separate binders `hX`, `hY`, `hZ : IsKappaFiltered κ ...`, using the recorded empty-shape-inclusive definition. |
| Each admits every τ-small κ-filtered colimit | Separate binders `hXcol`, `hYcol`, `hZcol`. `HasTauSmallKappaFilteredColimits` quantifies every indexing simplicial set I, its quasicategory witness hI, the actual τ-smallness and κ-filteredness, and every diagram F; it concludes existence of a cocone t with `Enhanced.IsColimiting F t`. |
| f and g preserve all those colimits | `hfcol`, `hgcol : PreservesTauSmallKappaFilteredColimits κ τ ...`. This specializes the dependency's `PreservesColimitsIn` by `IsKappaSmall τ I ∧ ∃ hI, @IsKappaFiltered κ I hI`, retaining every colimiting cocone and its actual postcomposition image. |
| f and g are κ-cofinal | `hf : IsKappaCofinal κ f`, `hg : IsKappaCofinal κ g`, expanded above. |
| x ∈ X and z ∈ Z | Existential vertices `x : X _⦋0⦌`, `z : Z _⦋0⦌`. |
| f(x) ≃ g(z) in Y | An edge `e : Y _⦋1⦌` with source `f.app _ x`, target `g.app _ z`, and `Enhanced.IsEquivalenceEdge Y e`, the existing two-inverse-triangle criterion. |

Dependency declarations read and used:

- `def-coef-presentable-infinity-category`: module
  `Sheaf.CategoryTheory.PresentableInfinityCategory`, recorded main declaration
  `SSet.Presentability.IsPresentable`. Read the full module and its docstrings,
  first with `scompile.py --source` and subsequently from the refreshed shared
  source. The statement actually uses its `IsKappaSmall`, `IsKappaFiltered`, and
  `PreservesColimitsIn`. The node's record became available during this task;
  no dependency repair or duplicate module is delivered.
- `def-cbc-enhanced-diagrams-cones`: module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, recorded main declaration
  `SSet.Enhanced.coneCategory`. Read the full signatures/docstrings of its
  `coconeCategory`, `IsColimiting`, `IsEquivalenceEdge`, and `IsContractible`,
  and the comma/constant-diagram definitions they use.
- The canonical cocone image is `CategoryTheory.Spaces.mappedCocone`, from
  `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`, publicly imported by the
  presentability module. Its signature, construction, and docstring were read;
  it actually postcomposes the apex and the whole coherent cocone edge.
- Mathlib supplies `SSet`, `SSet.Quasicategory`, face maps and simplicial maps,
  and `Cardinal.IsRegular`; the latter was read in
  `Mathlib/SetTheory/Cardinal/Regular.lean`, where infinitude is explicit.

Both statement-dependency modules are public imports. Every currently recorded
proof dependency is imported without `public`: `EnhancedFunctorConeCalculus`,
`BluntSharpJoinEquivalence`, `InfinityJoinConeCalculus`,
`LinearCofinalConeExtension`, `ParameterConeExtension`, and
`RelativeConeEquivalence`. The proof-only node
`lem-coef-infinity-cofinal-comma-criterion` has no Lean record in the shared DAG,
so it contributes no import; its role remains explicit in the proof docstring.
No missing statement notion is needed from that proof-only prerequisite.

Edge cases checked before writing:

- Empty diagram shapes are included in `IsKappaFiltered`; thus X, Y, Z cannot
  be empty. No extra Nonempty hypothesis is inserted. The empty L is excluded
  only from the cofinality test by the actual contractibility predicate,
  whose component condition fails for it.
- κ = aleph_0 is allowed: no uncountability or strict aleph_0 inequality appears.
  τ may be any larger regular cardinal. κ = τ is correctly excluded.
- A singleton weakly contractible shape is included, which is what the proof
  needs at the first odd stage. No initial empty odd diagram is assumed
  weakly contractible.
- Arbitrary τ-small κ-filtered quasicategories are tested, not only ordinal
  nerves or ordinary filtered categories. Arbitrary κ-small weakly contractible
  simplicial sets are tested for cofinality, not only Kan complexes.
- Preservation quantifies all colimiting cocones, not a chosen colimit object;
  no large cocompleteness, accessibility, local smallness or full faithfulness
  hypothesis is added. Both preservation and existence have exactly the
  specified τ bound.
- The conclusion is equivalence in Y rather than literal equality, a path
  component condition, or a categorical isomorphism in a substituted category.
- Faces are correctly oriented: δ 1 is the source and δ 0 is the target.

Searches for an existing statement or notation (2026-10-17):

- `msearch.py ... leanfinder` query: "Two kappa cofinal functors preserving tau
  small kappa filtered colimits between quasicategories have equivalent
  objects in their images". Eight hits: truncated homotopy-category lemmas,
  `SSet.QCat`, ordinary filtered-colimit element lemmas, and ordinary
  `HasCardinalFilteredGenerator.exists_equivalence`; none gives the assertion.
- `msearch.py ... loogle` query: `SSet.Quasicategory, CategoryTheory.Functor.Final`.
  Zero hits.
- `msearch.py ... grep` query: `cofinal|filtered|common.image`, subdirectory
  `AlgebraicTopology/Quasicategory`. Zero hits.
- `msearch.py ... leansearch` query: "Two cofinal functors between filtered
  infinity categories preserving filtered colimits have equivalent objects
  in their images". Eight ordinary-category preservation/colimit results,
  including `CategoryTheory.Limits.PreservesFilteredColimits`; none applies
  to coherent cocones of quasicategories.
- `rg` in both the upstream `WeilConjectures` tree and shared `lean/Sheaf`
  for `cofinal.*(image|Image)|common.*[Ii]mage|[Kk]appa[Cc]ofinal|[Ww]eakly[Cc]ofinal`
  returned only unrelated common-image prose, with no matching notion or theorem.
  An exact node-id search upstream returned no hit. Exact declaration-name
  search in Mathlib, upstream, and shared Lean returned no hit.
- Read the existing presentability module rather than duplicate its notions.
  The three helper predicates only name the class and cofinality convention
  already introduced in this node's own statement.

Validation: the prescribed `scompile.py Q64 lem-coef-infinity-cofinal-common-image
<module>` compiled the sandbox and final module successfully with no errors or
warnings. The only sorry is the main named theorem. The node JSON differs from
its shared source only in `lean`; its signature is copied verbatim from the file.
The delivery dry run is run after this report is written.

## Second reading by Q64

I independently read the shared node and sandbox node, the complete delivered
Lean module, both statement-dependency nodes and their source modules, and the
canonical `mappedCocone` construction in `InfinityCategoryOfSpaces`. No repair
note for this item is present. The sandbox node changes only `lean`; there is
no `statement_change`, new node, or dependency module to audit.

Source check: I opened the author's
[Harvard HTT PDF](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
Definition the project server (printed p. 439), Lemma the project server and its complete proof
(printed pp. 444–446; zero-based PDF pages 461–463). The IAS link in the node
timed out in the web reader. The accessible Harvard copy has the 2009 title
page; its cited definition, three numbered hypotheses, and conclusion match
this node. Section 5.4.6's opening discussion concerns accessible categories,
but Lemma the project server states its own hypotheses and does not assume accessibility,
local smallness, or compact generation. Its cardinal inequality is strict.

My object/hypothesis/conclusion checklist, made against the node before
accepting the Lean:

| Node item | Lean rendering and independent verdict |
| --- | --- |
| A small universe contained in the ambient universe | `universe u v`, cardinals in `Cardinal.{u}`, and `{X Y Z : SSet.{max (u + 1) v}}`. Correct: the ambient universe contains the small universe and can be arbitrarily larger. The helper declarations bind both universes explicitly. |
| Infinite regular cardinals κ and τ, with κ < τ | `(κ τ : Cardinal.{u})`, `hκ`, `hτ`, `hκτ`. Correct: I read `Cardinal.IsRegular` in Mathlib; its `aleph0_le` field supplies infinitude. No uncountability condition is added. |
| Three quasicategories X, Y, Z | Three independent `[Quasicategory ...]` binders. Correct: these are simplicial sets with inner-horn filling, rather than ordinary categories. |
| Coherent functors f : X → Y and g : Z → Y | `(f : X ⟶ Y) (g : Z ⟶ Y)`. Correct: morphisms in `SSet` are simplicial maps, which are the recorded enhanced functors. |
| Cocones on r, with constant target diagram and every higher compatibility | `Enhanced.coconeCategory r`. Correct: I read its defining `comma ... false`, `commaSubcomplex`, `diagramVertex`, and `constantDiagrams`; both endpoint equations hold in every simplicial degree. |
| Weak cofinality points from each target object to an image object | In `IsKappaCofinal`, `∀ t, ∃ s e`, with `δ 1 e = t` and `δ 0 e = Spaces.mappedCocone f r s`. Correct orientation: `δ 1` is the source. This is an edge of the target cocone category and therefore includes the coherent triangle, rather than only an apex arrow. |
| Cofinality tests every κ-small weakly contractible simplicial set L | `∀ (L : SSet.{v}), IsKappaSmall κ L → Enhanced.IsContractible L → ...`. Correct: no Kan-complex or quasicategory restriction on L. `IsKappaSmall` counts all nondegenerate simplices; `HasCardinalLT` compares cardinal lifts, so testing ambient-universe models does not lose small shapes. |
| Weak contractibility after inverting all arrows | `Enhanced.IsContractible L`. Correct: I unfolded its definition through `IsWeakHomotopyEquivalence` to components and positive based homotopy groups of realization, with terminal target `Δ[0]`. This tests the groupoid-completion homotopy type and includes nonemptiness through components. |
| Every coherent diagram r : L → X is tested | `∀ (r : L ⟶ X)` inside `IsKappaCofinal`. Correct order: L and its two properties precede r, then every target cocone precedes the source cocone and witnessing edge. |
| The actual induced image of a source cocone | `CategoryTheory.Spaces.mappedCocone f r s`. Correct: `mappedCoconeData` sends the apex by f and postcomposes the entire coherent edge through the two internal-hom maps. Its named membership theorem supplies only the endpoint proof, not arbitrary cocone data. |
| Each of X, Y, Z is κ-filtered | Separate `hX`, `hY`, `hZ : IsKappaFiltered κ ...`. Correct: the recorded definition tests every κ-small simplicial diagram, including the empty diagram, and asks for a coherent cocone. |
| Each category admits all τ-small κ-filtered colimits | Separate `hXcol`, `hYcol`, `hZcol`. Correct: unfolding `HasTauSmallKappaFilteredColimits` quantifies I, its quasicategory witness, τ-smallness, κ-filteredness, every diagram F, and then a colimiting cocone. The bound is τ, not κ, and no arbitrary choices are made. |
| Both f and g preserve precisely these colimits | `hfcol` and `hgcol`. Correct: `PreservesTauSmallKappaFilteredColimits` specializes the recorded `PreservesColimitsIn` to `IsKappaSmall τ I ∧ ∃ hI, @IsKappaFiltered κ I hI`; the latter preserves every colimiting cocone under its canonical image. The existential quasicategory witness has no additional mathematical content beyond the required indexing quasicategory. |
| Both f and g are κ-cofinal | `hf : IsKappaCofinal κ f` and `hg : IsKappaCofinal κ g`. Correct: each uses all the tests above, not merely cofinality on objects or ordinary categorical finality. Filteredness and regularity are supplied separately in this theorem. |
| Objects x of X and z of Z exist | `∃ (x : X _⦋0⦌) (z : Z _⦋0⦌) ...`. Correct: vertices are the objects of the actual source quasicategories. |
| There is an equivalence f(x) ≃ g(z) in Y | `∃ (e : Y _⦋1⦌), Y.δ 1 e = f.app _ x ∧ Y.δ 0 e = g.app _ z ∧ Enhanced.IsEquivalenceEdge Y e`. Correct: I read the dependency's inverse-edge and two inverse-triangle witnesses. This is an equivalence between the specified vertices, not equality, mere connectedness, or an unrelated isomorphism. |

Edge cases: the empty diagram is included in filteredness, so the hypotheses
already exclude empty X, Y, or Z without an extra `Nonempty` binder. Empty L
is excluded exactly by weak contractibility, while a singleton L is tested;
the proof docstring handles the first odd stage with that singleton. κ = ℵ₀
is allowed and κ = τ is excluded. A terminal quasicategory is included, as
are all higher-dimensional test shapes. The indexing quasicategory in the
colimit predicates can be any τ-small κ-filtered quasicategory, not only an
ordinal nerve. The small/ambient universes remain independent apart from
the prescribed containment; there is no equality of universes or extra
smallness/accessibility assumption on X, Y, Z. Zero objects, empty schemes,
coefficient characteristics, and numerical degree n are not parameters of
this categorical statement, so no such case is silently restricted.

Independent duplicate searches, using different phrasing from the author:

- `msearch.py Q64 lem-coef-infinity-cofinal-common-image leanfinder`
  with "Images of strongly cofinal maps of filtered quasicategories intersect
  up to equivalence when transfinite filtered colimits are preserved": eight
  hits, ordinary filtered-preorder/coequalizer/Mittag–Leffler results and
  simplicial-subcomplex colimits; no matching statement or predicate.
- `msearch.py ... loogle` with `"Quasicategory", "cofinal"`: zero hits.
- `msearch.py ... leansearch` with "Strong cofinality on undercategories gives
  an equivalent pair of image objects for colimit preserving infinity
  functors": eight hits, all ordinary-category colimit preservation facts.
- `msearch.py ... grep` with
  `weaklyCofinal|StronglyCofinal|Cofinal.*equivalence|cofinal.*quasicategory`:
  two unrelated model-theory comments on finite partial equivalences.
- Direct case-insensitive `rg` over upstream `WeilConjectures`, shared
  `lean/Sheaf`, and Mathlib `AlgebraicTopology` for weak/strong cofinality,
  cofinal images/equivalences, common images and the helper names found no
  duplicate. A separate grep of Mathlib's quasicategory directory for
  cofinality, filteredness and common images returned no hits. I checked
  the ordinary `sequentialFunctor_final_aux` signature and the location
  of `HasCardinalFilteredGenerator.exists_equivalence`: their ordinary
  categorical assertions do not replace this coherent common-image lemma.
- The shared DAG has only this statement for HTT the project server. The broader
  filtered-cofinal-pullback node cites it, and does not carry these helper
  predicates as separate definitions. Existing cardinal smallness,
  filteredness, coherent cocones and preservation are used directly.

H5–H9 checks: all three helper predicates have real Prop-valued bodies and
are specializations of notions introduced in this node, recorded in
`lean.declarations`. The only postponed proof is the named main theorem,
whose whole proof is `by sorry`. All four declarations have source and
blueprint docstrings. I matched the main docstring's eight numbered steps
against all eight proof entries of the node, including fixed-boundary
sharp/fat representatives, parity cardinality, the special initial odd
stage, successor extension, limit extension, compatible unions, cofinal
restriction of colimits, and the final equivalence of apices. Both statement
dependency modules are public imports. All six currently recorded proof-only
modules are ordinary imports; the comma criterion has no Lean record and
is retained in the proof plan. No file-local notation, instance, private
declaration, unbound variable, or overlength line is present.

Mismatches and changes: none. I retained the Lean and node exactly as written
and added only this independent second-reading record. A direct extraction
of the main signature, from `theorem` to `:= by`, equals `lean.statement`
verbatim. The prescribed `scompile.py` completed both its sandbox and library
checks with exit code 0 (1.7 s and 2.4 s respectively), no errors or warnings.
The required delivery dry run and push follow this report.
