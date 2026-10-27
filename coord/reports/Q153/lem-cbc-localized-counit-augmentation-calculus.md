## Worker report

The module `Sheaf.CategoryTheory.LocalizedCounitAugmentation` states the entire
augmented-arrow calculus as the single theorem
`CategoryTheory.LocalizedCounitAugmentation.calculus`, with proof `sorry`.
Four accompanying real definitions name the node's own maps: `augmentation`,
`resolutionIso`, `comparison`, and `computedMap`. No new independent notion,
postponed helper theorem, dependency repair, or statement correction is needed.
The original node is preserved except for `lean`.

Hypotheses and objects, matched individually:

- The abelian categories are `A : Type uA`, `B : Type uB` with independent
  `Category.{vA}`, `Category.{vB}` and `Abelian` instances.
- Chosen derived categories and their morphism universes are
  `HasDerivedCategory.{wA} A` and `HasDerivedCategory.{wB} B`; neither object nor
  morphism universes are identified between categories.
- `K(A)` and `K(B)` are `HomotopyCategory A (ComplexShape.up ℤ)` and its `B`
  counterpart. Both localization functors are the existing `DerivedCategory.Qh`.
- `G` and `L` have exactly the stated homotopy-category and derived-category
  source and target. No additivity or exactness hypothesis is added.
- `τ : DerivedCategory.Qh ⋙ L ⟶ G ⋙ DerivedCategory.Qh` is the specified
  natural transformation. `P` is an object predicate and
  `hτ : ∀ H, P H → IsIso (τ.app H)` is precisely invertibility on that class.
- `X : Type uX` with `Category.{vX} X` is arbitrary; `S R` are functors to the
  actual homotopy category, `a : S ⟶ R`, and `hS : ∀ x, P (S.obj x)`.
- Every resolution is quantified as its actual arrow `r : H ⟶ R.obj x`,
  membership `hH : P H`, and
  `hr : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) r`.
  These are arguments, never existential assertions that resolutions exist.

Clauses, in the order of the node (Lean composition is left to right):

1. `augmentation` is `inv (τ.app (S.obj x)) ≫ L.map (Qh.map (a.app x))`.
   The only instance installed in this definition is `hτ _ (hS x)`.
2. `resolutionIso` is `(L.mapIso (asIso (Qh.map r))).symm ≪≫ asIso (τ.app H)`.
   This gives precisely `χ_r`, including its inverse, as an actual derived-category
   isomorphism. The quasi-isomorphism supplies invertibility of `Qh(r)` through
   `Localization.inverts`; `mapIso` supplies its functorial image. No arbitrary
   isomorphism is selected from an existence assertion.
3. The theorem's second conjunct states `χ_r.hom ≫ Qh.map (G.map r) = τ.app _`
   and `w_x ≫ χ_r.hom ≫ Qh.map (G.map r) = Qh.map (G.map (a.app x))`.
4. `comparison r s` is `χ_r.symm ≪≫ χ_s`. The third conjunct gives
   `w_x ≫ χ_r.hom ≫ c.hom = w_x ≫ χ_s.hom`, the cocycle as equality of
   these isomorphisms, and `comparison r r = Iso.refl _`. Equality of these
   isomorphisms is equivalent to equality of their hom maps because inverses
   are unique. Three resolutions are quantified together for the cocycle;
   the two- and one-resolution clauses specialize with repeated resolutions.
5. The same conjunct states `∀ h : H ⟶ H', h ≫ s = r → Qh.map (G.map h) = c.hom`.
   It asserts no existence of such an `h`.
6. The first conjunct gives a natural transformation with components exactly
   `augmentation`; the fourth spells out its naturality
   `w_x ≫ L.map (Qh.map (R.map f)) = Qh.map (G.map (S.map f)) ≫ w_y`.
7. The fifth conjunct universally quantifies `W : MorphismProperty X` and the
   two assumptions `W.IsInvertedBy B`, `W.IsInvertedBy D`. It gives a descended
   natural transformation between the canonical `Localization.lift` functors
   on `W.Localization`. Its components at `W.Q.obj x` are explicitly
   `fac_B.hom.app x ≫ w_x ≫ fac_D.inv.app x`, retaining the factorization
   identifications rather than identifying isomorphic objects by fiat.
   The second half of this conjunct is exactly inverse naturality for `f ∈ W`:
   `inv (B.map f) ≫ w_x = w_y ≫ inv (D.map f)`, using the supplied inverses.
8. `computedMap` is the specified coordinate expression
   `χ_r.inv ≫ L.map (Qh.map (R.map f)) ≫ χ_s.hom`. The final conjunct asserts
   `w_x ≫ χ_r.hom ≫ computedMap = B.map f ≫ w_y ≫ χ_s.hom`.
9. At no point is `τ.app (R.obj x)` or `Qh.map (G.map r)` assumed invertible;
   the augmentation has no lift to a resolution among the arguments.

Dependency declarations read and used:

- `def-sp-abelian`: `Mathlib.CategoryTheory.Abelian.Basic`, `CategoryTheory.Abelian`.
  Its full class requires normal monos/epis, finite products, kernels and
  cokernels, the same abelian notion as the DAG node.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Qh`, its `IsLocalization` instance.
  Also read `HomotopyCategory.quasiIso` in
  `Mathlib.Algebra.Homology.Localization`: it means isomorphisms on every
  integer-degree homology object. The recorded general derived-category API
  already includes the homotopy-category localization, so no repair is needed.
- `lem-weil-pbc-localization-universal-property`:
  `Mathlib.CategoryTheory.Localization.Predicate`, `Localization.lift`, `fac`,
  `liftNatTrans`, `liftNatTrans_app`, and `natTrans_ext`. Read the full signatures
  and docstrings: arbitrary morphism properties are supported, without a
  calculus-of-fractions hypothesis. This module is a public statement import
  because the theorem uses `lift` and `fac` directly.

Source read: the node's exact main-20261015 completed-extension-zero proof,
including its invocation of completed pullback; Stacks `derived.tex`,
`lemma-find-existence-computes` (Tag 06XN), the dual resolving-class criterion.
The abstract seven-step calculation belongs to this node and is agent-written,
as its source and proof_origin already record. All seven proof steps are in
`calculus`'s docstring; no stronger computing-resolution hypothesis from the
application was inserted into the abstract statement.

Edge cases checked before writing: with an empty indexing category the natural
transformation and all formulas still make sense; with empty `P` the `hS`
hypothesis rules out precisely the nonempty indexing cases that require good
objects. No global supply of resolutions is imposed. One resolution may be
repeated for all three cocycle arguments. Identity resolutions and `τ = id`
reduce to the usual functorial images of `a`, including identity arrows.
For zero functors and a counit invertible only on good objects the formulas
remain meaningful even when the target counit and `G(r)` are not invertible.
An empty `W` still permits descent; arbitrary `W` requires just the two stated
inversion assumptions. Arbitrary independent category and localization
universes are retained. No disputed statement or node fault was found.

Searches performed for duplication:

- `msearch.py leanfinder`, query “Natural transformation invertible on resolving
  objects compares arbitrary resolutions and transports an augmentation naturally
  through localization”: 8 hits on LocalizerMorphism left/right resolutions,
  cofibrant-object resolutions and Abelian.LeftResolution.transport. These
  specialize different resolution settings and do not give this arbitrary-τ
  augmentation/cocycle/descent conjunction.
- `msearch.py loogle`, query
  `CategoryTheory.Localization.liftNatTrans, CategoryTheory.NatTrans.naturality`:
  0 hits. The known liftNatTrans declaration was read directly and used.
- `msearch.py grep`, regex
  `([Aa]ugment.*[Cc]ounit|[Cc]ounit.*[Aa]ugment|[Rr]esolution.*[Cc]ocycle)`
  in Mathlib CategoryTheory: 0 hits.
- `msearch.py leansearch`, query “Natural counit invertible on resolving objects
  compares arbitrary resolutions and transports augmented arrows”: 8 hits,
  on adjunction counits and projective/injective resolution naturality; all
  require additional specific structures and omit the full abstract calculus.
- Direct `rg` searches in `lean/WeilConjectures`, `lean/Sheaf`, Mathlib
  CategoryTheory and Algebra/Homology for `LocalizedCounitAugmentation`,
  `localizedCounitAugmentation`, `resolutionIso.*augmentation`: no hits.
  Broader counit/augmentation/arbitrary-resolution searches found the specialized
  `DerivedShriekCommaHomology`, `KInjectiveDerivedMapComputation`, etc.; these
  do not state this node. The required node-id grep in `lean/WeilConjectures`
  found no match.

Validation: `scompile.py` compiled both the sandbox and library module forms
cleanly on the server (about two seconds each). Only the main theorem has a
postponed proof. The dry run and delivery results are recorded by the delivery tool.

## Second reading by Q153

No second worker was started, as the dispatcher explicitly forbids subagents.
The maintainer's independent review is the designated independent reading.
For my final self-check I reread the node against the file, matched every
hypothesis and formula above, checked both composition conventions, and checked
that the only inverted maps are the good counits and localized resolution
arrows. No mismatch or statement change was found.
