## Worker report

The module `Sheaf.AlgebraicGeometry.CurveFunctionFieldArithmetic` states both
independent assertions of lem-sfb-curve-function-field-arithmetic. Its two named
theorems have `sorry` proofs; no definition or theorem proof is added. The node's
statement and dependencies are unchanged. No statement dispute, missing notion,
new node, dependency repair, or source correction was needed.

Source read: Stacks `curves.tex`, theorem-curves-rational-maps (0BY1), first and
third proof paragraphs; `varieties.tex`, lemma-dimension-locally-algebraic,
item-dimension-irreducible-trdeg (0B1C); `fields.tex`,
lemma-transcendence-degree-tower (030H) and lemma-algebraic-finitely-generated
(09GH). The extracted statement is more general than dimension-one curves,
as the node explicitly requests; its proof already supplies that generality.

Hypothesis and conclusion correspondence:

- The field k is `(k : Type u) [Field k]` in both theorems.
- The nonempty integral scheme T is `(T : Scheme.{u}) [IsIntegral T]`.
  `IsIntegral.nonempty` includes nonemptiness, so a duplicate hypothesis is not
  needed. No separatedness, smoothness, properness, or curve hypothesis is added.
- The k-structure is the explicit morphism `sT : T ⟶ Spec (.of k)`.
  `[LocallyOfFiniteType sT] [QuasiCompact sT]` is precisely finite type as
  recorded by def-weil-finite-type-morphism.
- The function field K(T) is `T.functionField`, definitionally the generic
  stalk `T.presheaf.stalk (genericPoint T)`. The scalar algebra is explicitly
  the ring homomorphism obtained by composing the inverse global-sections
  isomorphism of Spec k, `sT.appTop`, and the germ at the generic point.
  Thus it is the k-structure induced by sT, not an arbitrary algebra structure.
  This composite is written directly; no duplicate helper definition is made.
- Finite generation as a FIELD is `@IntermediateField.FG ... ⊤` for that algebra.
  Its actual definition is existence of a finite set whose field adjoin is top.
  This includes the empty generating tuple and is not finite generation as an
  algebra (which would be too restrictive for function fields).
- The equality `trdeg_k K(T) = dim T` is expressed by
  `∃ d : ℕ, topologicalKrullDim T = (d : WithBot ℕ∞) ∧
  @Algebra.trdeg ... = (d : Cardinal)`.
  Both dimensions are finite here, so this is their equality in their respective
  codomains without truncating an infinite cardinal via `toNat` or `toENat`.
  Finiteness follows already from field finite generation, and adds no hypothesis.
- The independent field assertion has `(K : Type v) [Field K] [Algebra k K]`
  and `(L : Type w) [Field L] [Algebra k L]`.
- The hypotheses that both extensions are finitely generated are respectively
  `hK : (⊤ : IntermediateField k K).FG` and `hL : ... .FG`.
- The common finite transcendence degree is `(d : ℕ)` with `hKd` and `hLd`
  equating the two transcendence degrees to the cast of d in their respective
  cardinal universes. The fields' universes are independent.
- Every k-embedding is covered by `(φ : K →ₐ[k] L)`: field algebra
  homomorphisms are injective and preserve the specified scalar maps.
- The conclusion `Module.Finite φ.fieldRange L` is exactly finiteness of
  L over φ(K), with the canonical intermediate-field inclusion action.
  The field-tower dependency identifies finite extensions with Module.Finite.
- No hypothesis assumes separability, characteristic, perfection, or algebraic
  closedness in either assertion.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs.
- def-pc-integral-scheme: `AlgebraicGeometry.IsIntegral`,
  Mathlib.AlgebraicGeometry.Properties; its two fields include nonemptiness and
  domain sections on nonempty opens.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType
  and Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- def-sc-function-field: the recorded module
  WeilConjectures.AlgebraicGeometry.FunctionField explicitly delegates its
  arbitrary integral-scheme clause to Mathlib's `Scheme.functionField` and its
  existing field instance. Its component-product definition is not the notion
  used by this node, and no repair is needed to use its documented integral clause.
- def-sc-generic-point: `genericPoint`, `genericPoint_spec`, `IsGenericPoint`,
  Mathlib.Topology.Sober (the generic point has closure equal to the whole space).
- def-kun-transcendence-degree: `Algebra.trdeg`,
  Mathlib.RingTheory.AlgebraicIndependent.Basic; supremum of independent subsets.
- def-kun-topological-krull-dimension: `topologicalKrullDim`,
  Mathlib.Topology.KrullDimension; supremum of irreducible closed chain lengths.
- def-pc-field-extension: `Algebra`, Mathlib.Algebra.Algebra.Defs.
- def-pc-field-tower: Sheaf.FieldTheory.FieldTower, `FieldExtension.degree`;
  its module explicitly records `Module.Finite` as the existing finite-extension
  notion. We import this module and use that notion, without restating degree.

All recorded proof-dependency modules are imported. The affine fraction-field
step uses `functionField_isFractionRing_of_isAffineOpen` from
Mathlib.AlgebraicGeometry.FunctionField. The dimension step imports
`AlgebraicGeometry.topologicalKrullDim_closed_irreducible_eq_trdeg` from
Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg, with the residue-field
notion from Mathlib.AlgebraicGeometry.ResidueField. The field steps import
`trdeg_add_eq` / `lift_trdeg_add_eq` from
Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis,
`trdeg_eq_zero_iff` from Mathlib.RingTheory.AlgebraicIndependent.Transcendental,
and `IntermediateField.finiteDimensional_adjoin` from
Mathlib.FieldTheory.IntermediateField.Adjoin.Basic. Their signatures and the
canonical `AlgHom.fieldRange` / `IntermediateField.FG` definitions were read.
Each theorem docstring includes its corresponding numbered node proof steps.

Edge cases checked before writing:

- The empty scheme is excluded by exactly the node's integrality/nonemptiness.
- Dimension zero is included: Spec of a finite field extension has the common
  natural dimension zero; Spec k permits the empty generator tuple.
- Affine space/function fields are not accidentally required to be finite-type
  k-algebras; field FG permits rational denominators.
- Nonseparated integral finite-type schemes remain permitted.
- The field assertion includes d = 0, identity embeddings, and proper embedded
  subfields. Cancellation of the finite transcendence degrees still works at zero.
- In characteristic p, k(t) embedded in k(t) by t ↦ t^p has finite degree p;
  no separability condition accidentally excludes this case.
- Infinite transcendence degree is excluded only where the node requires finite d.
- Arbitrary sizes of K and L are covered by universes v and w independently;
  the scheme and its base field share the universe of Scheme's morphism category.

Searches actually run (recorded by msearch.py in searches.jsonl):

- LeanFinder: “An integral finite type scheme over a field has finitely generated
  function field with transcendence degree equal to dimension, and embeddings of
  finitely generated fields of equal finite transcendence degree are finite”.
  Eight hits, including `finite_appTop_of_universallyClosed`, `functionField_iff`,
  `Algebra.finite_of_essFiniteType_of_isAlgebraic`, and `trdeg_lt_aleph0`.
  None states these assertions: the properness results have extra hypotheses,
  the number-theoretic function-field API assumes finiteness, and the field
  finiteness criterion assumes algebraicity rather than proving it from degrees.
- Loogle: `"functionField", "trdeg"`; zero hits.
- Mathlib grep: `functionField.*(trdeg|FG)|trdeg.*functionField` in
  AlgebraicGeometry; one unrelated OrderOfVanishing hit.
- LeanSearch: “The function field of an integral finite type scheme is finitely
  generated and has transcendence degree equal to its dimension”. Eight hits:
  the function-field definition, field/fraction-ring instances, `trdeg_lt_aleph0`,
  and `functionField_iff`; none gives the node's conclusion.
- Direct rg of lean/WeilConjectures and lean/Sheaf for the same function-field
  pattern and the item id found curve-specialized statements and dimension
  ingredients, not these general assertions. In particular,
  ProperFunctionFieldMorphisms assumes smooth proper dimension-one curves;
  SmoothStrictLocalFieldModelCoeffFractionTrdeg has a private dimension helper,
  without field finite generation or the independent field assertion.
- Direct rg in Mathlib, WeilConjectures, Sheaf, and dag/lean_names_upstream.json
  confirmed the new full declaration names do not already occur.

Validation: the delivered module was compiled using the required scompile.py
server wrapper, once as sandbox and once as library module. Both passed cleanly.
The delivery dry run and final push are performed after this report is written.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
