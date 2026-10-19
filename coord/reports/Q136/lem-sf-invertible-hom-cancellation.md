## Worker report

The module `Sheaf.CategoryTheory.InvertibleHomCancellation` defines the node's specified
map as `CategoryTheory.MonoidalClosed.invertibleHomComparison` and states every conclusion
in `CategoryTheory.MonoidalClosed.invertibleHomCancellation`. The only postponed proof is
that named theorem. The helper is the very map introduced by this node, not an independent
notion or an additional theorem. No new nodes, dependency repairs or statement corrections.

Hypotheses and clauses, matched individually:

- The category is `{C : Type u} [Category.{v} C]`, with independent, explicitly declared
  object and morphism universes. `[MonoidalCategory C]` supplies the specified tensor,
  unit, associators and unitors; `[SymmetricCategory C]` supplies the symmetry and its laws.
- The specified closed structure is `[MonoidalClosed C]`. This is data, not merely a
  proposition asserting existence: for each `A`, it gives a chosen right adjoint
  `Closed.rightAdj` and chosen adjunction `Closed.adj`. The internal Hom bifunctor is
  Mathlib's `MonoidalClosed.internalHom`, whose value at `(V, Y)` is `(ihom V).obj Y`.
  Its contravariant action is `pre`, constructed from the chosen adjunctions.
  The adjunction bijection is `curry`, and evaluation is `(ihom.ev V).app Y`.
  A specified adjoint bifunctor with natural adjunction bijections gives exactly this
  data and the induced first-variable action; no choice of another internal Hom is made.
- `L` and its inverse object `I` are arbitrary objects of `C`. The binder
  `(_e : L ⊗ I ≅ 𝟙_ C)` is precisely the one inverse-factor isomorphism assumed in the
  node. No second inverse-factor datum or triangle normalization is assumed. The map
  itself is independent of `I` and `_e`, as required.
- For every `V`, `invertibleHomComparison V L` has source `(ihom V).obj (𝟙_ C)` and
  target `(ihom (V ⊗ L)).obj L`.
- Its definition is `curry` of the exact pairing. Put `H = (ihom V).obj (𝟙_ C)` for this
  explanation only. The successive arrows are `(α_ V L H).hom`,
  `V ◁ (β_ L H).hom`, `(α_ V H L).inv`, `(ihom.ev V).app (𝟙_ C) ▷ L`,
  and `(λ_ L).hom`. Thus the source is `(V ⊗ L) ⊗ H`, symmetry moves `L` past `H`,
  evaluation acts on `V ⊗ H`, and the left unitor identifies `𝟙 ⊗ L` with `L`.
- The first conjunct, `∀ V : C, IsIso (invertibleHomComparison V L)`, states the
  isomorphism property of this very map. It asserts neither an arbitrary isomorphism
  between the objects nor an existentially chosen replacement comparison.
- The second conjunct handles every `f : V ⟶ W`: precompose `H(W,𝟙)` by `f`, then
  compare at `V`, or compare at `W`, then precompose by `f ▷ L`. The equality has
  source `H(W,𝟙)` and target `H(V ⊗ L,L)`, so it is precisely contravariant naturality.
- The third conjunct handles every `a : L ≅ L'` and every `V`. Comparing at `L'` equals
  comparing at `L`, then acting by `V ◁ a.inv` in the contravariant argument and
  `a.hom` in the covariant argument. This is compatibility with isomorphisms of `L`,
  including automorphisms; it imposes no unnecessary compatibility of inverse data.
  Invertibility of `L'` follows from `a`, so no additional premise is required.

Dependency declarations used:

- `def-sfb-monoidal-category` is a Mathlib leaf: `CategoryTheory.MonoidalCategory`,
  `Mathlib.CategoryTheory.Monoidal.Category`. Its entire structure signature,
  specified data and coherence laws were read. This module is publicly imported
  transitively by the two direct public imports.
- `lem-pod-closed-uncurry-laws` is a Mathlib leaf: `MonoidalClosed.uncurry_curry`,
  `MonoidalClosed.uncurry_natural_left` and `MonoidalClosed.uncurry_eq`, all in
  `Mathlib.CategoryTheory.Monoidal.Closed.Basic`. Their full signatures and the
  definitions/docstrings of `Closed`, `MonoidalClosed`, `ihom`, `ihom.adjunction`,
  `ihom.ev`, `curry`, `uncurry`, `pre`, and `internalHom` were read. The module
  publicly imports this dependency directly and uses its chosen adjunction interface.
- The proof dependency `lem-sf-invertible-factor-hom-cancellation` was read in full.
  It has no recorded Lean declaration in the provided DAG, so there is no proof-only
  module to import. The theorem docstring records the full one-step specialization
  and evaluation comparison from this node's proof, including the second inverse
  isomorphism obtained using symmetry. The declaration statements do not depend on
  an unavailable proof interface.

Edge cases checked before writing:

- `L = 𝟙` is allowed with the canonical unit inverse; no nontriviality assumption.
- `V = 𝟙` and zero/initial objects `V` in categories where they exist are unrestricted.
  Zero objects are not assumed, and the theorem introduces no additive hypothesis.
- Degenerate categories (including the terminal category and a zero tensor unit) are
  allowed. An empty category cannot carry the required monoidal unit, so is not an
  omitted instance of the statement.
- Arbitrary choices of the given inverse isomorphism are allowed; none enter the map.
- The naturality equation has the correct contravariant direction, and the factor
  equation uses `a.inv` on the source and `a.hom` on the target. Identity isomorphisms
  and arbitrary automorphisms are included. For vector spaces and a scalar
  automorphism of a line, these two actions cancel, as the stated comparison requires.
- Object and morphism universes remain independent; no finite-dimensionality,
  dualizability of `V`, strictness of associators or additional inverse datum is imposed.

Searches for an existing statement (all on 2026-10-17):

- `msearch.py ... leanfinder`: “In a symmetric monoidal closed category the evaluation
  transpose from internal Hom V unit to internal Hom V tensor L L is an isomorphism
  for invertible L”. Eight hits, including `MonoidalClosed.unitIsoSelf`,
  `MonoidalClosed.unitNatIso` and evaluation/coevaluation identities. None is this map
  or its cancellation and naturality theorem; the unit-source isomorphism does not
  address cancellation of an invertible factor.
- `msearch.py ... loogle`: `CategoryTheory.MonoidalClosed, CategoryTheory.ihom`.
  Twelve hits, including `internalHom_obj`, `internalHom_map`, parametrized adjunction
  formulas, and subcategory constructions. These supply the interface but not the claim.
- `msearch.py ... grep`: `ihom.*[Ii]so|[Ii]nvertible|expComparison`, restricted to
  `CategoryTheory/Monoidal`. Fourteen hits, notably `ihomCurryIso` and `expComparison`.
  Read `Closed/InternalCurrying.lean`: the former identifies iterated internal Hom,
  rather than the required evaluation-transpose cancellation. The latter is a functor
  comparison, not the map or theorem stated here.
- `rg -n` over `WeilConjectures` and the side library `lean/Sheaf`, using
  `invertibleHom|invertible.*[Cc]ancellation|[Cc]ancellation.*[Ii]hom|lem-sf-invertible-hom-cancellation`:
  only unrelated prose hits in side modules; no existing declaration of this statement.
- Exact candidate-name checks for `invertibleHomComparison` and
  `invertibleHomCancellation` in the project and side sources found no declaration.
  Searching upstream for the exact blueprint id likewise found none.

Validation: prescribed `scompile.py` compiled the module cleanly, both as its sandbox
check and its library path check. There were no errors or warnings. No global build
or source-checkout modifications were performed. The node copy changes only `lean`;
its signature is copied verbatim from the theorem declaration.

## Second reading by Q136

Independent maintainer reading of immutable delivery
`fa1c4d548bf44e88bbe38337f8f5171b54b15fe5`, performed 2026-10-17.
The reviewer did not author this delivery or its earlier reading. The heading follows the
required group convention; this section records the independent maintainer review.

Hypothesis and conclusion audit with the node and module open:

1. Ambient category: `{C : Type u} [Category.{v} C]`, with independently bound `u,v`.
   `[MonoidalCategory C]` supplies precisely the chosen tensor, unit, associators and
   unitors of `def-sfb-monoidal-category`. `[SymmetricCategory C]` supplies the natural
   braiding, both hexagons and symmetry. No strictness or additive hypotheses: correct.
2. Specified internal Hom: `[MonoidalClosed C]` carries a chosen `Closed.rightAdj` and
   `Closed.adj` for each object, not a propositional existence assertion. `ihom`, `curry`,
   `ihom.ev` and `pre` use those choices. The adjunction is to `tensorLeft`, exactly the
   item's convention. `internalHom` has object action `ihom` and morphism action `pre`.
   A specified bifunctor with the stated natural adjunction has this same induced action:
   no different Hom notion or restricted closed structure is substituted. Correct.
3. Invertibility: `(L I : C) (_e : L ⊗ I ≅ 𝟙_ C)` is precisely an arbitrary chosen witness
   to the item's inverse-object existence. Quantification over such witnesses gives the
   asserted implication for every invertible L. No triangle law or separately chosen
   reverse inverse is assumed; symmetry supplies it. Correct.
4. Specified map: `invertibleHomComparison V L` maps `H(V,𝟙)` to `H(V ⊗ L,L)`.
   Its real definition curries the composite
   `α(V,L,H).hom`, `V ◁ β(L,H).hom`, `α(V,H,L).inv`, `ev(V,𝟙) ▷ L`, `λ(L).hom`.
   The successive objects are `(V⊗L)⊗H`, `V⊗(L⊗H)`, `V⊗(H⊗L)`, `(V⊗H)⊗L`,
   `𝟙⊗L`, and `L`. This is exactly the displayed pairing, with all specified
   associators. It does not depend on inverse data. Correct; no arbitrary map or hollow def.
5. Isomorphism clause: `∀ V, IsIso (invertibleHomComparison V L)` concerns that very
   morphism, rather than merely isomorphic objects or an unspecified choice. Correct.
6. Contravariant naturality: for `f : V ⟶ W` both sides of the second conjunct map
   `H(W,𝟙)` to `H(V⊗L,L)`. They are precomposition by f then comparison at V, and
   comparison at W then precomposition by `f ▷ L`. Correct direction and quantifiers.
7. Factor compatibility: the third conjunct quantifies over every `L'`, `a : L ≅ L'`
   and V. `V ◁ a.inv` acts contravariantly, followed by `a.hom` covariantly, giving
   target `H(V⊗L',L')`. This states precisely transport along an isomorphism of L.
   L' inherits invertibility; requiring another inverse witness would be unnecessary.
   Automorphisms, identities and arbitrary choices of inverse are all included. Correct.

Sources and dependencies read:

- Immutable item and both direct statement-dependency JSON files were read in full.
  `def-sfb-monoidal-category` is the exact Mathlib leaf `MonoidalCategory`, not a
  private definition. Read `Monoidal/Category.lean:87–210` and its docstrings, plus
  Stacks `categories.tex` around `definition-monoidal-category` (Tag 0FFK), with
  the chosen-unit convention immediately following. Associator orientation agrees.
- Read `Closed/Basic.lean:34–198,244–307`: `Closed`, `MonoidalClosed`, `ihom`,
  `ihom.adjunction`, `ihom.ev`, `curry`, `uncurry`, `pre`, `internalHom` and their
  docstrings. The exact leaf declarations `uncurry_natural_left` (175),
  `uncurry_curry` (180), `uncurry_eq` (194) match every clause of
  `lem-pod-closed-uncurry-laws`. Read `Braided/Basic.lean:45–74,365–377` for symmetry.
- Read the complete cited blueprint proof of `thm-sf-dual-perfect`, especially Step 5
  (lines 59–82), moving the invertible twist to its inverse. The abstract item's
  generality is intentional; no geometry or perfectness hypothesis is missing from it.
- The snapshot does not include the proof-only node
  `lem-sf-invertible-factor-hom-cancellation`. Read its full current JSON in the
  permitted group clone and its now-published module
  `Sheaf.CategoryTheory.InvertibleFactorHomCancellation`, including both declarations,
  their docstrings and the full theorem signature. Also read Stacks Tags 0FFM and 0GWJ
  (`lemma-invertible`, `remark-internal-hom-monoidal`). Its right-evaluation convention
  is transported by symmetry from Mathlib's left evaluation. Its `ihomTensorBoth`
  specializes at Y = unit, and postcomposition with internal Hom of the left unitor
  gives exactly this item's comparison by naturality of currying. Its naturality and
  factor-compatibility clauses specialize to the two equations here. This proof-only
  dependency is not needed to type the statement and is not an unstated DAG prerequisite.
  The replacement module imports the published dependency for the stage-3 proof plan.

Edge cases and uniqueness searches:

- Unit factor, unit V, zero/initial V where present, terminal category and degenerate
  monoidal categories are covered. An empty category has no monoidal unit. There are
  no scheme, characteristic, dimension, finite-rank or nonzero restrictions; no indexed
  family or numeric parameter is introduced. No dualizability of V is assumed.
- Independent object and Hom universes stay independent; all variables are bound.
  No universe repair, helper construction or statement correction is required.
- Independently searched Mathlib CategoryTheory, upstream WeilConjectures and side
  Sheaf using cancellation/internal-Hom terms and both exact new declaration names.
  No exact existing statement or normalized unit-target map was found. The general
  proof dependency is not the same statement: its target is H(X⊗J,Y⊗J), and it has
  both t and s, reverse normalizations and Y-naturality. This is a specialization, not
  a second definition of its notion. Read the `ihomCurryIso`, `unitIsoSelf` and
  `expComparison` candidate signatures: they concern iterated internal Hom, unit
  source and a functor comparison, respectively. A fresh `msearch.py` Loogle query
  `CategoryTheory.MonoidalClosed, CategoryTheory.ihom` returned 12 interface and
  related-category hits, not this statement. The worker's three search kinds are recorded.

Findings and repairs:

- H11: the delivered second-reading section explicitly said no reading had occurred.
  Replaced that placeholder with this actual hypothesis-by-hypothesis independent audit;
  preserved the complete Worker report above.
- H9 / brief-stage2 §3 proof-import convention: the proof dependency has now landed.
  Added `import Sheaf.CategoryTheory.InvertibleFactorHomCancellation` to the complete
  replacement module. The worker's statement about the originally provided DAG is
  historical; the current dependency's recorded interface was read as described above.
- No H3/H4/H5/H6/H7/H8/H10/H12/H13 mathematical or declaration defect was found.
  The source/blueprint module and declaration docstrings are present and the theorem
  docstring explains the complete one-step node proof, including the transpose comparison.
  The map has genuine data; the sole theorem proof remains exactly `by sorry`.
- Parsed the immutable node and compared `lean.statement` byte-for-byte with the
  declaration text from `theorem` to before `:=`: equal. The repair changes no signature
  or node record. All Lean lines are at most 100 characters; no local notation,
  local instance, private copy, extra theorem, global build or pro-etale substitute.

Compiler evidence:

The immutable file was reproduced with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q136 lem-sf-invertible-hom-cancellation snapshot/lean/Sheaf/CategoryTheory/InvertibleHomCancellation.lean`.
It compiled both sandbox `Sheaf/Stage2/Sandbox0.lean` (4.3 s, temporary local `.lbuild`
overlay reported) and library `Sheaf/CategoryTheory/InvertibleHomCancellation.lean`
(8.5 s), exit 0, no errors or warnings. The wrapper labels its runs as server checks;
its sandbox output also identifies the private local overlay. No separate SSH or build
was run. The fixed complete module was rechecked through the same wrapper: sandbox 3.4 s,
library 3.4 s, exit 0, no errors or warnings. Only authorized review/fixes files were written.
