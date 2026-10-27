## Worker report

The module `Sheaf.CategoryTheory.ExactPairDetectsIsomorphisms` states
`CategoryTheory.isIso_of_exact_pair_detects_zero`, with its sole proof `sorry`.
The item statement, dependencies, proof and every other existing node field are unchanged;
only `lean` is added. No new notions or dependency repairs are needed.

Statement correspondence, checked against the complete node and module:

- The three abelian categories are `{C : Type u₁} {D : Type u₂} {E : Type u₃}`,
  their `[Category.{v₁} C]`, `[Category.{v₂} D]`, `[Category.{v₃} E]` structures,
  and `[Abelian C] [Abelian D] [Abelian E]`. All six universes are explicitly
  declared and independent; the statement has no smallness or equal-universe condition.
- The two functors are `(J : C ⥤ D) (I : C ⥤ E)`.
- Preservation of zero morphisms is `[J.PreservesZeroMorphisms]` and
  `[I.PreservesZeroMorphisms]`.
- Preservation of finite limits and finite colimits is exactly
  `[PreservesFiniteLimits J] [PreservesFiniteColimits J]` and
  `[PreservesFiniteLimits I] [PreservesFiniteColimits I]`.
- A zero object means initial and terminal: Mathlib `Limits.IsZero` has
  `unique_to` and `unique_from`, unique arrows to and from every object.
  This is the node's specified notion, not a chosen object equal to zero.
- Joint detection is `(hd : ∀ M : C, IsZero (J.obj M) →
  IsZero (I.obj M) → IsZero M)`. Both zero hypotheses are necessary inputs.
- Arbitrary objects and a morphism are `{M N : C} (c : M ⟶ N)`.
- Invertibility of both images is `[IsIso (J.map c)] [IsIso (I.map c)]`.
- The entire conclusion is `IsIso c`, without extra conclusions or restrictions.

Dependency declarations read and used:

- `def-sp-abelian`: Mathlib `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`, lines 105–116: preadditivity, normal
  monos/epis, finite products, kernels and cokernels. This is the recorded
  equivalent structural formulation; the public import supplies that exact class.
- `def-galois-exact-functor`: `CategoryTheory.Limits.PreservesFiniteLimits`
  and `PreservesFiniteColimits`, `Mathlib.CategoryTheory.Limits.Preserves.Finite`,
  lines 41–46 and 193–200. Their docstrings and full signatures quantify over
  finite diagram shapes. `CategoryTheory.exactFunctor` and `exactFunctor_iff`
  in `Mathlib.CategoryTheory.Limits.ExactFunctor`, lines 92–99, identify their
  conjunction with exactness. The statement uses the two recorded classes directly.
- The proof dependency `lem-sp-exact-functor-preserves-homology` is imported
  privately as `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
  Its recorded `CategoryTheory.Functor.preservesHomologyOfExact` at lines 60–61
  supplies `PreservesHomology`; the kernel and cokernel fields and accessors
  at lines 39–57 are the clause (a) needed in Step 1 of the node's proof.
- Zero preservation uses the existing `CategoryTheory.Functor.PreservesZeroMorphisms`
  in `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero`, lines 47–50;
  `IsZero` was read in `Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects`, lines 40–48.

Sources read: Stacks `literature/stacks-project/homology.tex`, Tag 010N,
`lemma-exact-functor`, lines 1545 onward (especially the kernel/equalizer
argument); Tag 00ZZ, `lemma-preadditive-zero`, lines 70–98; and Tag 0109,
`definition-abelian-category`, lines 608 onward. Also read the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/_section.md`
and the existing private helper and its consumer in
`lean/Sheaf/AlgebraicGeometry/ProEtaleRingedOpenExtensionProducts.lean`, lines 35–57
and the call at 168. The public theorem docstring writes all four node proof
steps, including kernel/cokernel uniqueness and construction of an inverse
from a normal monomorphism. No proof is implemented at this stage.

Edge cases checked mathematically before writing:

- If C is a zero category, every morphism is invertible and the statement applies.
- If M or N is zero, the argument still detects the kernel and cokernel and
  asserts invertibility only when both image maps are invertible.
- One functor may be zero; the other must then detect zero objects, as hd says.
  If both are zero and C is nonzero, hd fails: a nonzero object is a counterexample
  to that hypothesis. In particular 0 → ℤ in abelian groups shows why hd cannot
  be omitted even though its two zero-functor images are invertible.
- Distinct target categories and unrelated object/morphism universes remain allowed.
  No index, characteristic, ring, scheme or nonemptiness assumption is introduced.

Searches actually run (2026-10-27):

- `msearch.py ... leanfinder` query “Two exact functors between abelian categories
  jointly detecting zero objects jointly reflect isomorphisms”: eight hits,
  including `Functor.exact_tfae`, `reflects_exact_of_faithful`, and Serre-class
  results. Exactness characterizations and results requiring faithfulness are
  not this criterion.
- `msearch.py ... leansearch` query “Exact functors between abelian categories
  jointly detecting zero objects reflect isomorphisms”: eight hits, including
  `ReflectsIsomorphisms`, `mapZeroObject`, and
  `IsZero.of_full_of_faithful_of_isZero`; none states the joint criterion.
- `msearch.py ... loogle` query `"IsZero", "IsIso", "PreservesFiniteLimits"`:
  zero hits.
- `msearch.py ... grep` query `jointly.*(detect|reflect)|reflects_iso.*zero`,
  subdirectory `CategoryTheory`: 25 hits, principally joint-reflection definitions
  and their consequences. Read `Mathlib/CategoryTheory/Functor/ReflectsIso/Exact.lean`:
  `JointlyReflectIsomorphisms.isZero_iff` assumes joint reflection, which is the
  conclusion here, and so is the reverse direction rather than a matching theorem.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for joint detection, zero detection and proposed names; the exact private
  helper `jointly_detect_iso` is present only in
  `ProEtaleRingedOpenExtensionProducts.lean`. It is private and cannot serve
  as the recorded public declaration. No duplicate public statement was found.
- Node-id search in `lean/WeilConjectures` and `lean/Sheaf` found no public
  declaration for this item. Search for `isIso_of_exact_pair_detects_zero`
  in Mathlib, the project, and the upstream-name index had no hits.

No statement fault or dispute was found. The example `CompactObject.lean` in this
checkout has been withdrawn and contains no declarations; the delivery follows
the current required module/public-import/exposed-public-section convention.

Validation: prescribed `scompile.py` completed successfully, with no errors or
unexpected warnings: sandbox compile 7.0 s; library-module compile 1.3 s.
The required direct `grep -rn` for the item id in `lean/WeilConjectures`
also returned no matches.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
