## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.IntermediateFieldRealization` states
`AlgebraicGeometry.exists_curve_intermediate_field_realization`. Its only theorem has
proof `sorry`; no definition or proof is added. The node is unchanged outside `lean`.
The source was read in `literature/stacks-project/curves.tex`: Theorem 0BY1
(lines 159–230), Lemma 0BY3 (249–260), and Proposition 0CD2's intermediate-field
factorization sentence (2686–2694). The proposition's characteristic-p context is
not needed for its intermediate-model argument: 0BY1 works over any field and
0BY3 gives smoothness over the perfect, here algebraically closed, base.

Hypotheses and clauses, matched individually:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The curves are schemes `X Y : Scheme.{u}` with structure morphisms `sX sY` to
  `Spec k`, `[IsCurve sX] [IsCurve sY]`, `[IsIntegral X] [IsIntegral Y]`,
  `[Smooth sX] [Smooth sY]`, `[IsProper sX] [IsProper sY]`, and the two equalities
  `topologicalKrullDim X = 1`, `topologicalKrullDim Y = 1`.
- A k-morphism is `f : X ⟶ Y` with `hf : f ≫ sY = sX`. Nonconstancy is exactly
  `¬ ∃ y : Spec (.of k) ⟶ Y, y ≫ sY = 𝟙 _ ∧ sX ≫ y = f`.
- `L` and `K` are the actual generic stalks `X.functionField` and
  `Y.functionField`. The existential `hfη` makes their canonical map
  `(f.functionFieldMap hfη).hom` available without adding generic dominance as a
  hypothesis.
- The arbitrary intermediate field is encoded by a field `E` and field embeddings
  `i : K →+* E`, `j : E →+* L` with `j.comp i = f*`. Every ring homomorphism from
  a field to a field is injective. Thus `j` identifies `E` with exactly a subfield
  containing `f*(K)`. Conversely any intermediate subfield gives these two maps.
  This uses the node's explicit identification of `K` with its image; it imposes
  no new assumption and also allows isomorphic field representatives.
- `@Module.Finite K E ... i.toAlgebra` states finiteness of E/K;
  `@Module.Finite E L ... j.toAlgebra` states finiteness of L/E.
- The scalar map k → E is `i.comp sY.curveFunctionFieldBaseMap`. Under its
  explicitly supplied algebra structure, `@IntermediateField.FG ... ⊤` states
  finite field generation and `@Algebra.trdeg ... = 1` states transcendence
  degree one. Finite generation is not finite generation as an algebra.
- The model is `∃ Z sZ (_ : IsIntegral Z) (θ : Z.functionField ≃+* E) ...` with
  `IsCurve sZ ∧ Smooth sZ ∧ IsProper sZ ∧ topologicalKrullDim Z = 1`.
  `IsCurve` already includes finite type and separatedness.
- The equation `θ.toRingHom.comp sZ.curveFunctionFieldBaseMap =
  i.comp sY.curveFunctionFieldBaseMap` says θ is a k-isomorphism.
- The morphisms `a : X ⟶ Z`, `b : Z ⟶ Y` are over k by `a ≫ sZ = sX` and
  `b ≫ sY = sZ`. The two negated rational-point factorizations state their
  nonconstancy. The factorization `f = b ∘ a` is `a ≫ b = f`.
- `haη` and `hbη` specify the generic-point images so the canonical pullbacks
  are typed. Their equalities are `a* = j.comp θ.toRingHom` and
  `b* = θ.symm.toRingHom.comp i`, exactly the displayed equations of the node.
- The last two clauses are `a*.fieldRange = j.fieldRange` and
  `b*.fieldRange.map θ.toRingHom = i.fieldRange`. The first uses the identity on
  L to identify the induced extension with L/E; the second uses θ to identify
  the other induced extension with E/K. These are the explicit “in particular”
  clauses, not additional finiteness or separability conclusions.

Dependency interfaces read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` (publicly available through the
  correspondence module): `IsAlgClosed`, the algebraically closed part of
  `def-weil-algebraic-closure`.
- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve`, whose
  fields are separatedness, locally finite type, quasi-compactness and dimension
  at most one. Its full declaration and docstring were read.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`:
  `Scheme.functionFieldOfComponents`; for the node's integral case the recorded
  module explicitly prescribes Mathlib's `Scheme.functionField`, the generic
  stalk. That is what is used; no component-product copy is introduced.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `RingHom.toAlgebra`.
- `Sheaf.FieldTheory.FieldTower`: `FieldExtension.degree`; its module docstring
  prescribes `Module.Finite` for the node's finite-extension clause, as used here.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Sheaf.AlgebraicGeometry.Curve.ProperFunctionFieldMorphisms`:
  `Scheme.Hom.curveFunctionFieldBaseMap` is the existing scalar map used in the
  signature; `proper_curve_function_field_morphisms` and its identity/composition
  clauses give the proof correspondence. Their complete signatures and docstrings
  were read. The canonical pullback is the existing `Scheme.Hom.functionFieldMap`
  from `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`, also read.
- All recorded proof modules are imported, including
  `Sheaf.AlgebraicGeometry.Curve.AlgClosedCurveModel` (whose full signature and
  proof docstring were read), `Mathlib.FieldTheory.IntermediateField.Algebraic`
  (both finite-dimensional tower clauses), the finite-dimensional definition,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, the transcendence-basis and
  transcendental modules, and `Mathlib.AlgebraicGeometry.ResidueField`.

Edge cases checked: E=K gives the Y-model and identity second arrow; E=L gives
X and identity first arrow. Identity f is permitted. Empty schemes and points
are excluded by integrality and the stated dimension-one assumptions, exactly
as in the node. Positive characteristic inseparable maps are included: there
is no separability, characteristic-zero, or generically etale hypothesis.
Arbitrary algebraically closed base fields and arbitrary curves fitting in
universe u are allowed; isomorphic field representatives and all intermediate
subfields fit that same universe. No independent smaller test universe is
introduced. Ring isomorphisms preserve the actual scalar maps explicitly.
No statement correction, missing notion, dependency repair, or
STATEMENT-DISPUTED issue was found.

Searches (the launcher records exact search output in `searches.jsonl`):

- `msearch.py ... leanfinder`: “An intermediate field of the function fields of
  smooth proper integral curves is realized by a compatible factorization
  through a smooth proper curve”. Eight hits, including number-theoretic
  `FunctionField`, rational-map constructors and Weierstrass function fields;
  none states this global proper-curve factorization.
- `msearch.py ... loogle`: `"functionField", "RationalMap"`. Seven hits, including
  `RationalMap.ofFunctionField`, `fromFunctionField`, `equivFunctionField`, and
  `equivFunctionFieldOver`. They describe rational maps, rather than a smooth
  proper intermediate model and both global arrows.
- `msearch.py ... leansearch`: “An intermediate field between function fields of
  smooth proper curves is realized by a factorization of the curve morphism”.
  Eight intermediate-field construction/structure hits, no factorization theorem.
- `msearch.py ... grep`: `intermediate.*(curve|functionField)|(curve|functionField).*intermediate`
  in Mathlib `AlgebraicGeometry`: zero hits.
- `rg -n` with that pattern in both `lean/WeilConjectures` and `lean/Sheaf`:
  no upstream hit; project hits are other relative-curve models, Frobenius
  factorization, linear-group actions, and sheaf intermediate extension. None
  states this node. The Frobenius factorization module was read and is a
  different specialization. The exact node-id search in upstream Lean has no
  match. The proposed full declaration name was also searched in upstream,
  project Lean and `dag/lean_names_upstream.json`: no match.

Validation: the delivered file is compiled individually using the prescribed
`scompile.py` server wrapper. The required dry run and push are performed with
`deliver2.py`; no direct Git command, live source edit, local Lean compile or
library build is used.

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
