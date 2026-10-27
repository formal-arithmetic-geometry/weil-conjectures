## Worker report

The module `Sheaf.CategoryTheory.LinearRightAdjoint` states
`CategoryTheory.Adjunction.right_adjoint_additive_linear`, with its sole proof `sorry`.
The original node statement, statement dependencies, proof and proof dependencies are
unchanged. No definitions, new nodes or dependency repairs are needed.

Hypothesis and conclusion correspondence:

- The commutative ring A is `{A : Type w} [CommRing A]`.
- The two categories are `{C : Type u₁} {D : Type u₂}` with independently sized
  `[Category.{v₁} C] [Category.{v₂} D]`. The underlying preadditive structures are
  `[Preadditive C] [Preadditive D]`; their A-linear structures are `[Linear A C] [Linear A D]`.
- The functors are `{F : C ⥤ D} {G : D ⥤ C}`. The ordinary adjunction is
  `(adj : F ⊣ G)`. This is Mathlib's ordinary `Adjunction`, whose Hom equivalences are
  equivalences of types, with naturality; no linear Hom equivalence is assumed.
- The two assumptions on F are `[F.Additive] [F.Linear A]`. Both are necessary in this
  interface: Mathlib's `Functor.Linear` supplies scalar compatibility alone, so the separate
  `Additive` hypothesis is retained.
- The conclusion is `G.Additive ∧ G.Linear A`. By the definitions, its first conjunct says
  `G.map (s + t) = G.map s + G.map t` for every pair of parallel arrows, and its second
  says `G.map (a • s) = a • G.map s` for every arrow and scalar. Thus both explicit equations
  in the node, and precisely the full linear-functor notion recorded by its dependency,
  are represented.
- There is no assumption of an abelian or additive category, biproducts, exactness,
  boundedness, nonemptiness, or linearity of the adjunction bijections. All five universe
  variables are declared and `autoImplicit` is disabled.

Dependency declarations read in full:

- `def-weil-linear-category` has the Mathlib match `CategoryTheory.Linear` in
  `Mathlib.CategoryTheory.Linear.Basic`, used with `Category` and `Preadditive` exactly as
  the dependency's `mathlib_match.how` specifies. Its `homModule`, `smul_comp` and
  `comp_smul` supply the module structures and bilinear composition. Addition compatibility
  of composition is in `Preadditive`.
- `def-weil-linear-functor` has the Mathlib match `CategoryTheory.Functor.Linear` in
  `Mathlib.CategoryTheory.Linear.LinearFunctor`, together with `Functor.Additive` from
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`, as its match explicitly specifies.
  These are used directly for F and G; there is no private definition.
- `Mathlib.CategoryTheory.Adjunction.Basic` supplies the ordinary adjunction notation and
  structure. The statement publicly imports this module and the linear-functor module,
  which publicly exposes the linear-category and additive-functor declarations.

Source read: `literature/stacks-project/dga.tex`, lines 2863–2896, definitions
`definition-linear-category` (09MJ) and `definition-functor-linear-categories` (09MK).
These provide definitions, not the adjoint theorem. The node's three explicit counit proof
steps are transcribed in the theorem docstring, with Lean composition order. Also read the
full existing proof bodies and signatures of `CategoryTheory.Adjunction.right_adjoint_linear`
in `WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor` and
`CategoryTheory.Adjunction.right_adjoint_additive` in `Mathlib.CategoryTheory.Adjunction.Additive`.
The former supplies scalar preservation but does not supply additivity; the latter supplies
additivity but does not supply scalar preservation. Neither alone states this node, so a
single combined statement with `sorry` is supplied, without duplicating either definition.
The recorded compact-object example now points to its upstream definition and its old Sheaf
module is withdrawn; the required current module-mode header is used here.

Edge cases checked mathematically against the stated proof: A may be the zero ring; the
categories may be empty if the two functors and adjunction exist; Hom groups may be zero;
`s` or `t` may be zero and `a` may be zero or one. Injectivity of each Hom bijection and the
bilinearity calculation work in all these cases. No object or Hom universe is identified
with the coefficient universe or with the other category's universes. Categories need not
have any biproducts or be abelian.

Searches actually run (2026-10-23):

- `msearch.py ... leanfinder "The right adjoint of an additive linear functor between
  R-linear preadditive categories is additive and R-linear"`: 8 results, including
  `right_adjoint_additive`, `left_adjoint_additive`, `Functor.mapLinearMap` and `homAddEquiv`;
  no combined additive-and-scalar result.
- `msearch.py ... leansearch "The right adjoint of an additive R-linear functor is additive
  and R-linear"`: 8 results, including `right_adjoint_additive`, `left_adjoint_additive` and
  `homAddEquiv`; no combined statement.
- `msearch.py ... loogle "CategoryTheory.Functor.Linear, CategoryTheory.Adjunction"`:
  `Adjunction.extLinearEquiv` only, which concerns Ext in abelian categories with extra
  exactness assumptions and is not this statement.
- `msearch.py ... grep "right_adjoint_linear|right_adjoint_additive|additive.*linear"
  CategoryTheory/Adjunction`: 4 hits, all the additive-adjunction result or its uses.
- `rg -n 'right_adjoint_linear|right_adjoint_additive|lem-sbc-linear-right-adjoint'
  lean/WeilConjectures lean/Sheaf`: the upstream scalar lemma, the additive lemma's uses,
  and citations of this item in `SfRationalSupportedAdjointTransport`; no combined statement.
  The item-id search was performed over the full upstream tree as part of this command.
- `rg -n 'right_adjoint_additive_linear|rightAdjointAdditiveLinear'` over Mathlib, upstream,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing declaration with either name.
- Additional concept search `rg -n 'right adjoint.*additive|Additive.*Linear'` in upstream and
  `lean/Sheaf` found specialized statements and uses, not a general combined theorem.

No statement fault or STATEMENT-DISPUTED issue was found.

Validation: the delivered module is compiled using the prescribed `scompile.py`; the
server dry run and final delivery use `deliver2.py`. Results are recorded below once run.

## Second reading by Q48

Author's second reading for direct delivery; independent review is the maintainer's, as
specified by the dispatch brief. Reopened the node, dependency match records, source
signatures and finished module. The ring binder is CommRing, not a stronger field/domain
assumption. Category and Hom universes remain independent. The ordinary adjunction binder
has no enriched-equivalence condition. Crucially, `Functor.Linear` is not an additive class:
confirmed that both `[F.Additive]` and `[F.Linear A]` occur, and that the conclusion contains
both `G.Additive` and `G.Linear A`. These two conjuncts expand to exactly the node's addition
and scalar equations, with all parallel-arrow pairs and scalars quantified in the classes.
Neither property of G occurs among the hypotheses. No extra categorical or exactness
structure is required. The docstring retains all three proof steps and uses the correctly
oriented counit formula `F.map h ≫ ε_Y`. No mismatch or correction was needed on rereading.

Validation result: `scompile.py` successfully compiled both its sandbox and library views
of `Sheaf.CategoryTheory.LinearRightAdjoint` (7.2 s and 16.4 s). The prescribed
`deliver2.py ... --no-push` returned `OK (dry run)`: preflight passed and the module
compiled, with no errors or disallowed warnings; nothing was pushed during the dry run.
