## Worker report

The module `Sheaf.CategoryTheory.AdjunctionRightImageExtraDegeneracies` states
`CategoryTheory.Adjunction.exists_rightImageExtraDegeneracies`, with its sole
proof `sorry`. No definitions, helper axioms, dependency repairs, new nodes, or
statement changes are needed.

Source read: `literature/stacks-project/simplicial.tex`, Situation 08N9
(`situation-adjoint-functors`), Lemma 08NC (`lemma-standard-simplicial`), and
Lemma 08ND (`lemma-standard-simplicial-homotopy`), including the triangle
compositions and the formulas for the standard operators. The statement's
explicit elementary extra-degeneracy argument is included step by step in the
theorem docstring.

Hypotheses and objects, clause by clause:

- Ordinary categories S and A are the explicit `Type uS`, `Type uA` and
  `Category.{vS}`, `Category.{vA}` binders; all four universes are independent.
  `F : S ⥤ A`, `U : A ⥤ S`, and `adj : F ⊣ U` give the adjunction, unit and counit.
- `adj.toComonad` is precisely G = FU, with counit `adj.counit` and
  comultiplication FηU (Mathlib's composition is diagrammatic).
- The supplied resolution is `B`, with the given augmentation `e`, and
  `hB : Comonad.IsStandardSimplicialResolution adj.toComonad B e` supplies
  exactly its prescribed powers, operators, and degree-zero augmentation.
- The comma object `{ left := B, right := 𝟭 A, hom := e }` is the given
  augmented simplicial object in endofunctors. Applying
  `SimplicialObject.Augmented.whiskering (A ⥤ A) (A ⥤ S)` to
  `(Functor.whiskeringRight A A S).obj U` applies U to its terms, operators,
  and the actual augmentation. Its augmentation object is `(𝟭 A) ⋙ U`.
  Evaluation at a therefore gives precisely Z_n(a) and Z_{-1}(a).
- The existential `ed : ExtraDegeneracy ...` expresses the five required
  identities for these operators, with no extra equations. Its field
  `s'_comp_ε` is e_0 h_{-1} = 1; `s_comp_δ₀` is d_0 h_n = 1;
  `s₀_comp_δ₁` is d_1 h_0 = h_{-1} e_0; `s_comp_δ` is
  d_{i+1} h_{n+1} = h_n d_i; and `s_comp_σ` is
  s_{i+1} h_n = h_{n+1} s_i. Lean writes composition in diagrammatic order.
- `HEq ed.s' (Functor.whiskerLeft U adj.unit)` fixes h_{-1}(a) = η_{Ua}.
  `∀ n, HEq (ed.s n) (Functor.whiskerLeft
  (Comonad.resolutionPower adj.toComonad.toFunctor (n + 1) ⋙ U) adj.unit)`
  fixes h_n(a) = η at UG^(n+1)a. Heterogeneous equality handles precisely
  the term equalities in hB, rather than choosing arbitrary isomorphisms.
  Every extra-degeneracy map is thus specified by the unit, not arbitrary
  existential data. Existence with these pinned values is equivalent to the
  displayed unit maps satisfying the equations.
- All the structure maps are natural transformations in `A ⥤ S`. Their
  naturality axioms supply the final parameter-naturality clause, including
  augmented degree -1; the equations hold in that functor category itself.

Dependency declarations read and used:
`Sheaf.CategoryTheory.ComonadStandardResolution` exposes
`CategoryTheory.Comonad.resolutionPower` and
`CategoryTheory.Comonad.IsStandardSimplicialResolution`. Its only node is both
the statement and proof dependency here, so the import is public. Mathlib's
`CategoryTheory.Adjunction.toComonad` was read in
`Mathlib.CategoryTheory.Monad.Adjunction`; its definition confirms ε and FηU.
`CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy`, including all
five fields, was read in `Mathlib.AlgebraicTopology.ExtraDegeneracy`.
`Augmented.whiskering` and `whiskeringObj` were read in
`Mathlib.AlgebraicTopology.SimplicialObject.Basic` to check that the actual
augmentation is preserved. No import of the downstream homotopy theorem is
needed, and none is used.

Edge cases checked before writing: n = 0 includes the distinct augmented
boundary equation and d_0 h_0 = 1. `Fin (n + 2)` in the face field includes
both endpoints i = 0 and i = n+1. `Fin (n + 1)` in the degeneracy field
includes i = 0 and i = n, including n = i = 0. The zeroth comonad power is
the identity. Empty categories and identity adjunctions impose no excluded
cases. No limits, additive structures, or equality of category universes is
assumed. There is no statement dispute or node fault.

Searches actually run with `msearch.py Q54` and this item's id:

- leanfinder: “The unit of an adjunction gives all left extra degeneracy
  equations in the right adjoint image of a supplied standard comonad
  simplicial resolution”. Eight hits, including `Comonad.adj_unit`,
  `Adjunction.toComonad_δ`, `ExtraDegeneracy.s'`, and the classifying-space
  special case. None states the arbitrary-adjunction assertion.
- loogle: `"ExtraDegeneracy"`. Twelve hits: the structure, its projections,
  mapping/isomorphism transport, and standard-simplex/Čech constructions.
  The generic structure assumes the identities; it does not supply them
  from the unit of an arbitrary adjunction.
- leansearch: “The unit of an adjunction gives extra degeneracies on the
  underlying augmented standard simplicial resolution”. Eight hits on unit
  declarations; no match for the full assertion.
- grep: `toComonad|ExtraDegeneracy|unit_naturality` in Mathlib/CategoryTheory.
  Twenty-five reported hits, concerning the comonad and adjunction axioms,
  not the extra-degeneracy construction.
- `rg` in both project Lean trees for the item id and extra-degeneracy names
  found the existing downstream homotopy theorem, Čech/specialized bar
  constructions, and no theorem with this statement. The downstream
  homotopy file defines right-image abbreviation helpers; this delivery uses
  Mathlib's existing augmented whiskering directly, with no duplicate helpers.
  Exact proposed-name searches in Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json` gave no matches.

Validation uses the prescribed server `scompile.py` and `deliver2.py` only.
The initial compile identified one missing explicit source-category argument
to `Augmented.whiskering`; this was corrected to `(A ⥤ A) (A ⥤ S)`.
The corrected file passes `scompile.py`: both sandbox and library compilation
exit 0 with no warnings or errors. The server-reported sandbox elapsed time
includes slot acquisition; the normal per-file compiler limit was unchanged.

## Second reading by Q54

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
