## Worker report

The module `Sheaf.CategoryTheory.ScalarNormalizedAdjunctionSquare` states
`CategoryTheory.Adjunction.scalarNormalizedAdjunctionSquare`, with `sorry` as its entire
proof. It renders the node unchanged. There are no new nodes, dependency repairs,
statement corrections, or additional postponed lemmas.

Hypotheses, matched individually:

- The four categories are `C`, `D`, `C'`, `D'`, each with its own explicitly named object
  universe and morphism universe. No universe equality or smallness condition is imposed.
- The horizontal adjunctions are `adj : P ⊣ Q` and `adj' : P' ⊣ Q'`. Their `.unit` and
  `.counit` are the node's η, η', ε, ε'.
- The vertical adjunctions are `scalarC : FC ⊣ rC` and `scalarD : FD ⊣ rD`. Their `.unit`
  components are j_C and j_D.
- The full subcategories are `C₀ : ObjectProperty C` and `D₀ : ObjectProperty D`, using
  Mathlib's `.FullSubcategory` and inclusion `.ι`. The binders `hP` and `hQ` state precisely
  the two containments. No closure under isomorphism is imposed.
- The ambient isomorphisms are `b : P' ⋙ rD ≅ rC ⋙ P` and
  `d : Q' ⋙ rC ≅ rD ⋙ Q`. They range over all of C' and D', respectively.
- `α : C₀.ι ⋙ P ⋙ FD ≅ C₀.ι ⋙ FC ⋙ P'` is an isomorphism only on C₀.
  `β : D₀.ι ⋙ Q ⋙ FC ⟶ D₀.ι ⋙ FD ⋙ Q'` is a transformation only on D₀;
  invertibility of β is not assumed.
- `hα` is the first scalar-unit normalization, for every `N : C₀.FullSubcategory`.
  `hβ` is the second normalization, for every `M : D₀.FullSubcategory`.
  `hε : ∀ Z : D', ...` is the ambient restricted-counit compatibility; in particular it
  does not require `rD.obj Z` to belong to D₀. Lean's `f ≫ g` means first f then g,
  reversing the node's right-to-left written compositions in all three formulas.

Conclusions, matched individually:

- The first universal quantifier over M has three conjuncts. The first is the vertical
  transpose of `α_QM ≫ P'.map β_M ≫ ε'`, equal to `ε_M ≫ j_D,M`. Its second conjunct
  equates that expression to the transpose of `FD.map ε_M`. Its third conjunct is the
  resulting equality `FD.map ε_M = α_QM ≫ P'.map β_M ≫ ε'`.
  Here `⟨Q.obj M.obj, hQ M⟩` is the actual object QM in C₀.
- The second universal quantifier over N has two conjuncts. The first uses
  `(adj'.homEquiv ...).symm` to state that the inverse horizontal transpose of
  `FC.map η_N ≫ β_PN ≫ Q'.map α_N` is identity on P'FCN. The second says this composite
  equals `adj'.unit.app (FC.obj N.obj)`. The argument of β is the actual object PN in
  D₀, namely `⟨P.obj N.obj, hP N⟩`.
- The last conjunct states equality with Mathlib's `mateEquiv` of `α.inv`, with
  `G := C₀.ι ⋙ FC` and `H := D₀.ι ⋙ FD`. The unprimed adjunction is restricted using
  `adj.restrictFullyFaithful`, the canonical full inclusions, and the functors
  `D₀.lift (C₀.ι ⋙ P) hP` and `C₀.lift (D₀.ι ⋙ Q) hQ`. Their commuting isomorphisms
  are definitionally `Iso.refl`. `TwoSquare.mk` and `.natTrans` are Mathlib's wrappers,
  not new constructions. Thus this is the specified mate for the restricted adjunction,
  not merely a pointwise assertion of a possibly different convention.
- There is no faithfulness or realizability hypothesis. All objects Z of D' remain in
  the ambient counit hypothesis.

Dependencies read and used:

- `def-weil-pbc-adjunction-mate` is a Mathlib leaf. Its recorded
  `CategoryTheory.mateEquiv` in `Mathlib.CategoryTheory.Adjunction.Mates` was read with
  its full signature, docstring, construction, and counit/unit identities. The final
  conjunct uses this exact declaration and direction.
- The proof dependency `lem-weil-pbc-adjunction-of-natural-bijection` is a Mathlib leaf
  recorded at `CategoryTheory.Adjunction.mkOfHomEquiv` in
  `Mathlib.CategoryTheory.Adjunction.Basic`. Read `CoreHomEquiv`, `mkOfHomEquiv`, and the
  recorded unit/counit formulas. Basic is already publicly imported by Mates and Restrict;
  no redundant import is necessary.
- The restriction uses `CategoryTheory.Adjunction.restrictFullyFaithful` from
  `Mathlib.CategoryTheory.Adjunction.Restrict`, and `ObjectProperty.FullSubcategory`,
  `.ι`, `.fullyFaithfulι`, `.lift`, from
  `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`. Their source signatures and
  docstrings were read. No missing interface or new definition is needed.

Sources checked: Stacks `categories.tex`, definition-adjoint (Tag 0037), lines 3343–3383,
including both adjunct formulas; Bhatt–Scholze Remark 6.8.15, PDF p. 62, via pdftotext.
The latter supplies the ambient adjunction setting, not the abstract calculation; the
module docstring explicitly attributes the calculation to the node's agent extraction.
The theorem docstring carries all six proof steps and the two dependency ids.
The prescribed CompactObject example module is now withdrawn; its node points to
`WeilConjectures.CategoryTheory.CompactObject`. The delivered file follows the required
module header, exposed public section, source docstrings, and explicit universes.

Edge cases checked before writing: empty full subcategories (no nonempty hypotheses;
restricted functors still exist under hP/hQ); full subcategories equal to the ambient
categories; all functors and comparisons identity; one-object scalar categories, where
hε supplies the essential relation between b and d; β not assumed invertible; and
r_D F_D M not in D₀ (permitted, since hε is ambient). The proof uses hα at QM and
naturality of α at η_N, whose endpoints lie in C₀ by hP and hQ. These checks reveal no
statement fault or disputed clause.

Searches performed with the prescribed msearch.py wrapper (2026-10-22):

- LeanFinder: "Squares of adjunctions normalized by the scalar adjunction units preserve
  horizontal counit and unit and identify a mate". Eight hits, including mateEquiv_counit,
  unit_mateEquiv, mateEquiv_apply and mateEquiv_square. These assume the mate construction
  or express its coherence; none deduces it from the three scalar normalizations.
- Loogle: `CategoryTheory.mateEquiv, CategoryTheory.Adjunction`. Twelve hits on mateEquiv
  and its counit, unit, composition and iterated forms; no exact normalized-square theorem.
- Mathlib grep: `mateEquiv_counit|unit_mateEquiv|scalarNormalized` in
  `CategoryTheory/Adjunction`. Five hits, all the existing counit/unit mate identities.
- LeanSearch: "Adjunction squares whose two comparison maps are normalized by vertical
  units preserve horizontal adjunctions". Eight hits on adjoint lifting, naturality,
  localization units, commuting single arrows and mateEquiv_square; no exact match.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and the upstream name index for
  `scalarNormalizedAdjunctionSquare|scalar_normalized_adjunction_square|` followed by
  the item's id: no hit. A wider concept search for scalar-normalized and normalized
  adjunction statements found `Sheaf.CategoryTheory.AdjunctionComparisonSquare`;
  its complete `rightAdjointUniq_square` statement concerns two right-adjoint uniqueness
  comparisons assuming their counit compatibilities, so is not this theorem.

Validation: scompile.py compiled both the sandbox form and the actual library module
on the server (1.4 seconds each), without errors or unexpected warnings.

## Second reading by Q114

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
