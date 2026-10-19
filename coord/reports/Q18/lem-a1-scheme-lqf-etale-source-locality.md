## Worker report

The module `Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteEtaleSource` states
`AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_etale_source`, with proof `sorry`.
It asserts both preservation of Stacks local quasi-finiteness under etale
precomposition and detection under a surjective etale source map. There are no
new definitions or auxiliary nodes, no dependency repair, and no statement correction.
The source is Stacks Project, Descent, Tag 03X4, including its precomposition
paragraph; I read `literature/stacks-project/descent.tex` at lines 6964 onward.
The declaration's docstring carries the node's seven-step proof, including the
standard-open shrinking in step 1 and the empty-refinement case in step 6.

Clause-by-clause correspondence:

- The three arbitrary schemes are `{U V T : Scheme.{u}}`, with an explicit arbitrary
  universe `u`. This uses `AlgebraicGeometry.Scheme` from
  `Mathlib.AlgebraicGeometry.Scheme` (dependency `def-pc-scheme`). I read its full
  local-affineness field and the `Scheme.Hom` declaration and docstrings.
- The maps `p : U ⟶ V` and `g : V ⟶ T` are the node's morphisms.
- The etale hypothesis is `[Etale p]`, using `AlgebraicGeometry.Etale` from
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (dependency
  `def-weil-etale-morphism`). I read the affine-ring-map class signature and its
  docstring, and `Etale.iff_flat_and_formallyUnramified`, which expresses flatness,
  formal unramifiedness and local finite presentation. This is the recorded notion.
- Local quasi-finiteness is `Scheme.Hom.IsLocallyQuasiFinite`, from
  `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism` (dependency `pqf-def-quasifinite`).
  I read that module in full: this means `∀ x, IsQuasiFiniteAtPoint f x`, whose
  affine-neighbourhood witness explicitly includes `Algebra.FiniteType` and
  `Algebra.IsQuasiFiniteAtPrime` at the corresponding prime. The finite-type
  requirement is retained.
- The first clause is exactly
  `IsLocallyQuasiFinite g → IsLocallyQuasiFinite (p ≫ g)`.
  Categorical order `p ≫ g` means the paper's `g ∘ p`.
- The converse is exactly
  `Function.Surjective p → IsLocallyQuasiFinite (p ≫ g) → IsLocallyQuasiFinite g`.
  Coercion of the scheme morphism to a function gives the underlying map of points.
  Surjectivity is local to this conjunct, so the forward direction also applies to
  non-surjective etale maps.
- The conjunction joins precisely these two assertions. There is no
  quasi-compactness, separatedness, Noetherian, affine or base-field hypothesis.

Proof imports follow the available recorded proof dependencies:
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`Mathlib.AlgebraicGeometry.OpenImmersion`,
`Sheaf.AlgebraicGeometry.UnramifiedMorphism`,
`Sheaf.RingTheory.QuasiFiniteComposition`,
`Mathlib.AlgebraicGeometry.Morphisms.Affine`,
`Mathlib.AlgebraicGeometry.Cover.QuasiCompact`,
`Sheaf.RingTheory.Etale.QuasiFiniteAtPrime`,
`Sheaf.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite`,
`Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteResLE`,
`WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`, and
`Sheaf.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite`.
The public imports are the three statement dependencies. The two proof-only DAG
nodes `lem-a1-lft-flat-lfp-source-descent` and
`lem-a1-scheme-lqf-affine-criterion` have no recorded Lean module at this base,
so they are named in the proof docstring and not imported. They supply no notion
needed to type this statement. The current ProperQuasiFinite module was read via
`scompile.py --source`; its recorded theorem retains local finite type on both
sides, as required by its use for the Stacks notion.

Edge cases checked before writing:

- Empty U: forward preservation is vacuous pointwise. For the converse,
  surjectivity forces V empty, so the conclusion is again vacuous.
- Non-surjective open immersion p, including an empty-source map into nonempty V:
  the first conjunct remains available; descent is explicitly conditional and
  does not mistakenly conclude anything about points outside the image.
- Infinite disjoint union of identities mapping to V: p is etale and surjective,
  but need not be quasi-compact. The statement admits it; finite affine refinement
  is used only locally in the proof.
- Identity p: the two directions reduce to the same local quasi-finiteness predicate.
- No separation or Noetherian restriction appears; arbitrary schemes in a common
  ambient universe are allowed. The explicit universe is the dependency's scheme
  universe, with no additional universe equations.

Searches for an existing full statement:

1. `msearch.py ... leanfinder` with query
   "Local quasi finiteness of a scheme morphism is preserved by etale
   precomposition and descends along surjective etale source maps": eight hits,
   including Mathlib composition, base change, `LocallyQuasiFinite.of_comp` and the
   Mathlib class itself. None states surjective etale source descent for the
   Stacks predicate. In particular `of_comp` concludes the property of the first
   arrow p, whereas descent here concludes the property of g.
2. `msearch.py ... loogle '"LocallyQuasiFinite", "Etale"'`: zero hits.
3. `msearch.py ... grep 'LocallyQuasiFinite|locallyQuasiFinite'
   AlgebraicGeometry/Morphisms`: five indexed hits in Mathlib QuasiFinite.lean.
   I opened its full class signature and docstring: it explicitly omits local
   finite type, so the similarly named results do not express this node.
4. `rg -n` for `IsLocallyQuasiFinite` and etale/source-locality patterns in the
   upstream `WeilConjectures` tree and the project `lean/Sheaf` tree: the project
   has the shared predicate, open restrictions, finite-type implication, target
   base change and separated fpqc effective descent. None is this theorem.
5. `rg -n 'lem-a1-scheme-lqf-etale-source-locality'` in the upstream source found
   no declaration. An exact-name search for `isLocallyQuasiFinite_etale_source`
   and `IsLocallyQuasiFiniteEtaleSource` in both source roots and the upstream
   declaration-name index also found no match before writing.

No `STATEMENT-DISPUTED` issue was found. The previous failure confused the N1
stage-1 review with a stage-2 completion: the current item has a reviewed split,
but no `lean` or `reviewed_lean` field. This delivery adds its Lean statement and
leaves that split and all other node fields unchanged.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
