## Worker report

The module `Sheaf.CategoryTheory.BiprodCokernelCofork` states
`CategoryTheory.Limits.exists_isColimit_biprod_map_cokernelCofork`, with its sole proof
`sorry`. It introduces no definitions, dependency modules, or new nodes, and changes only
this item's `lean` record. The original statement is unchanged and has no disputed clause.

Sources read: Stacks `homology.tex`, `remark-direct-sum`, `definition-additive-category`,
and the cokernel clause of `definition-kernel` (Tags 0103, 0104, 0106); and
`properties.tex`, the proof of `lemma-directed-colimit-diagram-finite-presentation`
(Tag 01PJ), where the direct sum of finitely presented modules is used.
The generic block calculation is the auxiliary result extracted by the node, not a
claim that Tag 01PJ states a generic categorical lemma.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| An additive category A | `{A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A] [HasBinaryBiproducts A]`. These are exactly the first formulation of `def-weil-additive-category`: preadditive, zero object, and every binary biproduct. The recorded `[Preadditive A] [HasFiniteBiproducts A]` is its equivalent finite formulation. |
| For k = 1,2, objects Q_k, P_k, C_k | `{Q₁ Q₂ P₁ P₂ C₁ C₂ : A}`. Object and morphism universes `u` and `v` are independent and explicitly declared. |
| Maps a_k : Q_k → P_k and c_k : P_k → C_k | Explicit binders `a₁`, `a₂`, `c₁`, `c₂`, with those exact types. |
| c_k a_k = 0 | `w₁ : a₁ ≫ c₁ = 0` and `w₂ : a₂ ≫ c₂ = 0`. Lean composition runs left to right. |
| Every map P_k → T killing a_k factors uniquely through c_k | `h₁ : IsColimit (CokernelCofork.ofπ c₁ w₁)` and the analogous `h₂`. Read the full `CokernelCofork.ofπ` and `CokernelCofork.IsColimit.ofπ` signatures in Mathlib: this is the universal property for every object T and every annihilating map, with uniqueness. No ambient existence of arbitrary cokernels or abelianness is assumed. |
| a = i_P1 a_1 p_Q1 + i_P2 a_2 p_Q2 | `biprod.map a₁ a₂`. `biprod.map_eq` is precisely `biprod.fst ≫ a₁ ≫ biprod.inl + biprod.snd ≫ a₂ ≫ biprod.inr`, translating the node's ordinary composition convention. |
| c = i_C1 c_1 p_P1 + i_C2 c_2 p_P2 | `biprod.map c₁ c₂`, by the same Mathlib equality. |
| c is a cokernel of a, including the zero composite | The conclusion starts `∃ w : biprod.map a₁ a₂ ≫ biprod.map c₁ c₂ = 0`, then asserts `Nonempty (IsColimit (CokernelCofork.ofπ (biprod.map c₁ c₂) w))`. `Nonempty` places the subsingleton colimit witness in Prop; it loses none of its universal property. |
| With its stated projection | The cofork is `CokernelCofork.ofπ (biprod.map c₁ c₂) w` itself. Its object is C₁ ⊞ C₂ and its projection is the specified block map, not an arbitrary isomorphic cokernel. |
| Both coforks compatible with the left injection | The first and third equalities in the concluding conjunction: `biprod.inl ≫ biprod.map a₁ a₂ = a₁ ≫ biprod.inl` and `biprod.inl ≫ biprod.map c₁ c₂ = c₁ ≫ biprod.inl`. |
| Both coforks compatible with the right injection | The second and fourth equalities: the corresponding equations for `biprod.inr`, `a₂`, and `c₂`. |

Dependency declarations read and used:

- `def-weil-additive-category` is a Mathlib leaf. Its record points to
  `CategoryTheory.Limits.HasFiniteBiproducts` in
  `Mathlib.CategoryTheory.Limits.Shapes.Biproducts`, with preadditivity. Its statement
  explicitly gives the equivalent zero-object/binary-biproduct formulation used here.
  Binary maps and injections use `HasBinaryBiproducts`, `biprod.map`, `biprod.inl`, and
  `biprod.inr` from `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts`;
  `HasZeroObject` is from `Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects`.
- The stated proof dependency `def-weil-preadditive-category` records
  `CategoryTheory.Preadditive` in `Mathlib.CategoryTheory.Preadditive.Basic`, also read.
- The one public import `Mathlib.CategoryTheory.Preadditive.Biproducts` supplies these
  declarations, `biprod.map_eq`, and the `CokernelCofork`/`IsColimit` API (defined in
  `Mathlib.CategoryTheory.Limits.Shapes.Kernels`). Both recorded dependency modules
  are in its public import closure. There are no private copies or local instances.

Edge cases checked mathematically before writing: both a_k zero with c_k identity;
both a_k identity with C_k zero; one summand zero; multiplication by 2 on each copy
of the abelian group of integers (with the mod-2 quotient maps); the zero target T;
and the all-zero category. Each retains the stated projection and both injection
identities. The category need not be abelian and need not have other cokernels.
There is no variable index set or nonempty restriction. Independent category universes
are retained. All implicit variables are explicit, with `autoImplicit false`.

Searches made (2026-10-23), through the prescribed msearch.py wrapper:

- LeanFinder: "In an additive category the binary biproduct of two cokernel coforks is
  a cokernel of the block diagonal map, compatible with both injections". Eight hits:
  `CommSq.cokernelCofork`, `Square.cokernelCofork`, `biprod.inrCokernelCofork`,
  `biprod.isCokernelInlCokernelFork`, `biprod.inlCokernelCofork`,
  `biprod.isCokernelInrCokernelFork`, `instHasCokernelInl`, `instHasCokernelInr`.
  None is the block pair of arbitrary given cokernels.
- Loogle: `CategoryTheory.Limits.CokernelCofork, CategoryTheory.Limits.biprod.map`.
  Zero hits.
- LeanSearch: "The binary biproduct of two cokernel coforks is a cokernel cofork in an
  additive category". Eight hits involving pushout coforks, split monomorphisms, and
  translation between general coforks and difference cokernels, with no exact match.
- Mathlib grep: `biprod.*(cokernel|Cokernel)|(cokernel|Cokernel).*biprod` in
  `CategoryTheory`. Twenty-four hits: Freyd categories, the abelian pushout cofork,
  kernel-cokernel composition sequences, and cokernels of biproduct injections.
- Project rg: the same regex over `lean/WeilConjectures` and `lean/Sheaf`; and the item
  id over `lean/WeilConjectures` (no occurrence). The named theorem was also checked
  in Mathlib, both project roots, and `dag/lean_names_upstream.json`: no collision.
  `Sheaf.Paper.IntegralLfpLocalTorsionCharts` has a private binary cokernel-object
  isomorphism assuming an abelian category, not this arbitrary-cofork statement.
- The project search also found and I read the full declaration and docstring of
  `CategoryTheory.Limits.isColimitCokernelCoforkBiproductMap` in
  `WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowGLLift`. It provides the closely
  related indexed-biproduct colimit witness, over chosen objects `⨁ P`, with the
  specified indexed projection. It does not state the binary `⊞` result together
  with the four injection compatibility equations required by this node; identifying
  the separately chosen binary and indexed biproducts requires transport. The present
  module only states that full binary conclusion and defines no replacement notion.
  This existing theorem remains an available proof tool for stage 3.

Validation: the first compile diagnosed that Mathlib's finite-to-binary biproduct
conversion is a theorem, not an instance. Rather than install a file-local instance,
the final signature uses the equivalent first formulation in the dependency statement.
The final module passed scompile.py in both sandbox and library mode, with no errors
or non-sorry warnings (1.7 s / 0.8 s). Every theorem body is exactly `by sorry`.

## Second reading by Q16

I reread the node and final module as a separate self-check. This is not claimed to be
an independent-agent review: the dispatch brief prohibits starting other agents and
assigns independent review to the maintainer. The comparison above checks all six
objects, all four input maps, both zero-composite hypotheses and universal properties,
the exact two block maps, the output zero composite and cokernel universal property,
the specified cofork projection, and all four injection identities. No source hypotheses
are omitted and none are added. The only elaboration adjustment was replacing the
finite-biproduct spelling of additivity with its zero-object/binary-biproduct spelling;
no mathematical statement correction was needed. I also checked that the statement
contains no let-bound or file-local terms and no extra tautological conclusion.
