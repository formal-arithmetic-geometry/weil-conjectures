## Worker report

The module `Sheaf.CategoryTheory.SequenceRelativeHomTelescope` states
`CategoryTheory.sequence_relative_hom_telescope`. It has one theorem with proof
`sorry`, and introduces no definitions. The item node is changed only in `lean`.
No new nodes, dependency repairs, statement corrections, or disputed statements
are needed.

I read the node and all three statement dependencies, their recorded interfaces,
and the source signatures/docstrings in Mathlib. I also read the proof dependency
`lem-weil-pbc-hom-into-triangle-exact` and its three matched lemmas. The source
argument was checked in `literature/stacks-project/derived.tex`, labels
`lemma-compute-colimit` (093W), `lemma-cohomology-of-hocolim` (0CRK), and
`lemma-commutes-with-countable-sums` (094A). The module docstring identifies this
as the sequence-relative version of those arguments, and the theorem docstring
carries all five proof steps of the node, including the quotient universal
property and the canonical stage formula.

Hypotheses and clauses, in the order of the node:

- The triangulated category is `{C : Type u} [Category.{v} C]`, with
  `[Preadditive C] [HasZeroObject C] [HasShift C ℤ]`, additive shifts,
  `[Pretriangulated C]`, and `[IsTriangulated C]`. These are the exact Mathlib
  interfaces in `def-weil-triangulated-category.mathlib_match`, including TR4.
- Small morphism groups in the chosen universe are expressed by
  `[Category.{v} C]`. Hom groups, their sums, and `AddCommGrpCat.{v}` colimits
  all live in `v`. The object universe `u` is independent; it is not forced to
  equal `v`. This is the direct universe implementation of the convention node.
- The object is `(K : C)`. The sequence is `(X : ℕ ⥤ C)`;
  `X.map (homOfLE (Nat.le_succ n))` is precisely its successor map `u_n`.
  A natural-number sequence extends uniquely to this functor by composing its
  successor maps, so no compatibility assumption is added.
- The chosen coproduct and its coprojections are `(B : C)` and
  `(iota : ∀ n : ℕ, X.obj n ⟶ B)`, with
  `(hB : IsColimit (Cofan.mk B iota))`. This asks only for this coproduct;
  it does not assume all countable coproducts exist.
- The forward shift is `(s : B ⟶ B)` and `hs` says
  `iota n ≫ s = X.map (homOfLE (Nat.le_succ n)) ≫ iota (n + 1)`.
  This is the node's equation in Lean's diagrammatic composition order.
- The chosen telescope object and arrows are `H`, `p : B ⟶ H`, and
  `q : H ⟶ B⟦(1 : ℤ)⟧`. The hypothesis `hT` is exactly
  `Triangle.mk (𝟙 B - s) p q ∈ distTriang C`.
- The first comparison hypothesis is `hcomp`: bijectivity of
  `DirectSum.toAddMonoid (fun n ↦ Preadditive.rightComp K (iota n))`.
  On a summand this sends `f` to `f ≫ iota n`, so it is precisely the
  unshifted canonical comparison, not an arbitrary comparison isomorphism.
- The second hypothesis is `hcompShift`: the same construction using
  `Preadditive.rightComp K ((iota n)⟦(1 : ℤ)⟧')`. The source summands
  are `K ⟶ (X.obj n)⟦1⟧` and the target is `K ⟶ B⟦1⟧`. These are
  the actual shifted coprojections, without choosing another coproduct.
- The conclusion's source is the categorical colimit of
  `X ⋙ preadditiveCoyoneda.obj (op K)` in `AddCommGrpCat`. The functor's
  objects are the Hom groups and its maps are postcomposition with `X.map`;
  hence the colimit transitions are exactly the specified `u_n` transitions.
  Existence of this small colimit comes from Mathlib, with no extra binder.
- The resulting `phi` is a morphism to `AddCommGrpCat.of (K ⟶ H)`, hence
  a group homomorphism. The clause on every `n` and `f` reads
  `phi (colimit.ι (...) n f) = f ≫ iota n ≫ p`, exactly the node's
  representative formula. By the colimit universal property these equations
  uniquely determine the map; the existential formulation asserts existence
  of that canonical map, rather than assuming an unspecified map.
  `Function.Bijective phi` is precisely the required conclusion.
- There is no compactness binder, comparison for another family, assumption
  on injectivity/surjectivity of the transitions, or arbitrary additional
  coproduct assumption.

Dependency declarations used:

- `def-weil-triangulated-category`: Mathlib's
  `CategoryTheory.Pretriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, and
  `CategoryTheory.IsTriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Triangulated` (which imports the former).
  The structure, shift, triangle constructor and distinguished-triangle
  notation are the recorded interfaces, with no private replacements.
- `def-weil-size-convention`: its convention record explicitly requires universe
  binders rather than an object/declaration; the independent `u`, `v` binders
  implement it.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone`,
  `IsColimit`, `colimit`, and `colimit.ι` in
  `Mathlib.CategoryTheory.Limits.HasLimits` and its imports. The imported
  `Limits.Shapes.Products` gives `Cofan.mk`, directly using this interface.
- Proof dependency `lem-weil-pbc-hom-into-triangle-exact`:
  `Pretriangulated.comp_distTriang_mor_zero₁₂`,
  `Pretriangulated.Triangle.coyoneda_exact₂`, and
  `Pretriangulated.Triangle.coyoneda_exact₁`, all in the imported
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`. Their full signatures
  were read; these are exactly the zero-composite and factorization clauses
  used in step 3, including rotations.
- The additive Hom functor is Mathlib's `preadditiveCoyoneda` from
  `Mathlib.CategoryTheory.Preadditive.Yoneda.Basic`, whose actual definition
  maps an arrow by postcomposition. Additive composition uses
  `Preadditive.rightComp` from `Preadditive.Basic`; coproduct comparisons use
  `DirectSum.toAddMonoid` from `Mathlib.Algebra.DirectSum.Basic`.

Edge cases checked mathematically before writing: `K = 0` and all `X_n = 0`
give zero groups and the unique bijection. With all transitions zero,
`1-s = 1`, the telescope is zero and the sequential group colimit is zero.
For identity transitions, the group colimit is the constant Hom group and the
formula is unchanged. Non-injective and non-surjective transitions cause no
problem: injectivity of identity minus forward shift follows from its zeroth
coordinate and induction, not from any transition property. The `n = 0`
summand is present, with shift to `1`; the indexing set is the fixed nonempty
natural numbers, so no empty-index assumption is hidden. Arbitrary choices of
coproduct model and telescope triangle are retained as parameters. No equality
of object and Hom universes is assumed.

Searches for an existing statement (executed with `msearch.py` unless noted):

- LeanFinder, `Hom into a sequential telescope in a triangulated category is
  the direct limit if Hom preserves the coproduct of that sequence and its shift`:
  eight hits, including `Functor.homologySequence_comp`,
  `Functor.comp_homologySequenceδ`, and
  `Pretriangulated.preadditiveYoneda_homologySequenceδ_apply`; none states this
  relative telescope comparison. The interrupted attempt's earlier equivalent
  LeanFinder query was also checked in `searches.jsonl` before resuming.
- Loogle, `preadditiveCoyoneda, colimit.desc`: zero hits, with the service
  reporting unknown unqualified identifier `preadditiveCoyoneda`. The actual
  Mathlib source was then read to verify the qualified interface.
- Grep, `hocolim|homotopyColimit|homotopy_colimit|telescope`, subdirectory
  `CategoryTheory`: zero Mathlib hits.
- LeanSearch, `Hom commutes with the sequential telescope if it preserves the
  direct sums of the sequence and its shift`: eight hits on direct-sum maps,
  shifted-Hom additivity and composable arrows; no matching telescope theorem.
- Direct `rg` searches of upstream `WeilConjectures` for the item id,
  `hocolim|homotopyColimit|homotopy_colimit`, and of upstream, Mathlib,
  `dag/lean_names_upstream.json`, and `lean/Sheaf` for the proposed declaration
  name found no duplicate declaration.
- Direct `rg` concept searches in `lean/Sheaf` found and I read
  `CategoryTheory.compact_hom_hocolim` in
  `Sheaf.CategoryTheory.CompactHomHocolim`. It assumes global compactness and
  all coproducts of a chosen size, and uses a colimit of Hom *sets*. It does
  not give this sequence-relative statement about a group homomorphism.
  `IsSequentialHomotopyColimit` in `TruncationsAndHomotopyColimits` similarly
  requires all countable coproducts and existentially hides `p` and `q`, whereas
  this node specifies the actual triangle and canonical map. Neither is
  duplicated or imported to impose its stronger hypotheses.

Validation: `scompile.py Q156 lem-weil-pbc-sequence-relative-hom-telescope`
compiled the final module separately as sandbox and library module, cleanly
with no errors or warnings. All variables and universes are explicitly bound.
The only proof is the required `sorry`; definitions and additional theorems
are not introduced. During elaboration I parenthesized the shifted
coprojection explicitly so the shift applies to `iota n`, not to its additive
postcomposition map.

## Second reading by Q156

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
