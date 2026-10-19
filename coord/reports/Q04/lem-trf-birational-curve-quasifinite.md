## Worker report

Item: `lem-trf-birational-curve-quasifinite`, group Q04.
Module: `Sheaf.AlgebraicGeometry.DominantIntegralCurveQuasiFinite`.
Declaration: `AlgebraicGeometry.quasiFiniteAtPoint_of_dominant_integral_curves`.
One theorem, with proof `sorry`; no definitions or additional nodes.
The repository node is copied with only its `lean` field changed.

I read the item, all eight statement-dependency nodes and their recorded declaration
sources/docstrings, the five proof steps and the proof-dependency records. Source checked:
`literature/stacks-project/varieties.tex`, lines 3186–3265,
`lemma-quasi-finite-in-codim-1`, condition (1) (Tag 0AB6, confirmed in `tags/tags`).
The target is the stated integral-curve specialization of that result, without changing
its hypotheses. No repair note exists for this item in the shared checkout.

Hypothesis and conclusion correspondence:

- “k a field”: `{k : Type u} [Field k]`.
- “C and E schemes”: `{C E : Scheme.{u}}`.
- “over k”: `[C.Over (Spec (.of k))] [E.Over (Spec (.of k))]`.
- “integral”: `[IsIntegral C] [IsIntegral E]`, including nonemptiness.
- “separated”: `IsSeparated` on each of the two structure morphisms `C ↘ Spec (.of k)`
  and `E ↘ Spec (.of k)`; no unnecessary properness assumption is imposed.
- “of finite type”: both `LocallyOfFiniteType` and `QuasiCompact` on each structure
  morphism, exactly the recorded finite-type convention.
- “each of dimension 1”: `hC : topologicalKrullDim C = 1` and
  `hE : topologicalKrullDim E = 1`, using the underlying scheme topologies.
- “p:E → C”: `(p : E ⟶ C)`.
- “k-morphism”: `[p.IsOver (Spec (.of k))]`, expressing that the structure triangle commutes.
- “dominant”: `[IsDominant p]`, the dense-range condition.
- “locally of finite type”: `[LocallyOfFiniteType p]`.
- “induces a finite extension k(C) ⊆ k(E)”: the hypothesis
  `hfinite : (p.stalkMap (genericPoint E)).hom.Finite`.
  By definition this is finite generation of the target module through this particular
  stalk homomorphism. Its target is definitionally `E.functionField`. Its source is
  `C.presheaf.stalk (p (genericPoint E))`. Dominance and continuity imply
  `p (genericPoint E) = genericPoint C`: the image of the generic point is generic
  because its closure contains the dense image of E, and C is sober and T0.
  Transport along this equality identifies the source with `C.functionField`, which
  `def-sc-function-field` explicitly defines as the generic stalk in the integral case.
  Both generic stalks are fields, so finite generation as a module is exactly a finite
  field extension; the unital field map is automatically injective. There is no arbitrary
  algebra structure or independently chosen homomorphism. No additional equality
  hypothesis or theorem is needed in the signature for this equivalent encoding.
- “quasi-finite at every point of E”: `∀ x : E, p.IsQuasiFiniteAtPoint x`.
  This uses the dependency's Stacks finite-type affine-neighbourhood definition, rather
  than silently substituting Mathlib's weaker stalk-only `QuasiFiniteAt`.

Statement-dependency declarations reused (full signatures and docstrings read):

- `Mathlib.Algebra.Field.Defs`: `Field` (available through the public geometry imports).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.FunctionField`: the node's integral-scheme clause reuses
  `AlgebraicGeometry.Scheme.functionField` from `Mathlib.AlgebraicGeometry.FunctionField`.
  The recorded `functionFieldOfComponents` is for nonintegral component products and
  is not substituted for the integral generic stalk.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`.
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its separatedness import:
  `AlgebraicGeometry.IsSeparated`, one of the dependency's recorded declarations.

Other existing interfaces: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`:
`IsDominant`; `Mathlib.AlgebraicGeometry.Scheme`: `Scheme.Hom.stalkMap`;
`Mathlib.RingTheory.Finiteness.Defs`: `RingHom.Finite`;
`Mathlib.Topology.Sober`: `genericPoint` and `genericPoint_spec`.

Proof-dependency imports are non-public:
`Sheaf.AlgebraicGeometry.ClosedPointField` supplies
`closedPoint_iff_residueField_trdeg_zero_and_finite`;
`Sheaf.AlgebraicGeometry.FiniteClosedPoints` supplies
`IsClosed.finite_of_finiteType_over_field_of_closed_points`;
`WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite` supplies
`Scheme.Hom.discreteTopology_fiber_and_quasiFiniteAt`.
The last source is absent in the older slopmaster2 checkout, so I read the live module
using `scompile.py --source`. It concludes Mathlib pointwise quasi-finiteness under
local finite type; the future proof must express its affine finite-type witnesses to
reach the recorded Stacks predicate. The statement does not replace that predicate.
Sobriety, integrality, dimension and residue fields are available from the public imports.
The docstring preserves all five DAG proof steps and names their cited nodes.

Edge cases checked: the empty scheme and zero-dimensional spectra are excluded by the
node's integrality and dimension-one hypotheses themselves. A constant map of curves
is excluded by dominance. An open immersion omitting closed points has empty fibres,
which the conclusion permits. Finite maps t ↦ t^n, including inseparable maps in
positive characteristic, satisfy the same statement: no separability or characteristic
assumption appears. Singular integral curves are permitted (no smoothness or normality
assumption). Arbitrary non-algebraically-closed fields are permitted. Both curves and
the field use the usual common scheme universe u; a larger universe can contain any
particular data, and there is no small test-object quantifier to become vacuous.
Separatedness and the finite generic extension are retained even though the DAG's
direct proof does not use them. No statement fault or disputed statement was found.

Searches actually run with `msearch.py Q04 lem-trf-birational-curve-quasifinite`:

- LeanFinder: “A dominant locally finite type morphism between integral curves over a
  field is quasi-finite”. Eight hits: `finite_appTop_of_universallyClosed`, ring-level
  quasi-finiteness and generic `LocallyQuasiFinite` declarations. None states this theorem.
- LeanSearch: “A dominant morphism of integral one dimensional finite type schemes
  over a field is locally quasi-finite”. Eight hits, including `LocallyQuasiFinite.mk`,
  `.recOn`, finite/immersion instances, `locallyQuasiFinite_iff`, and `IsDominant`.
  None is the curve theorem.
- Loogle: `AlgebraicGeometry.Scheme.functionField, AlgebraicGeometry.IsDominant`.
  Zero hits; no function-field morphism matching these names found by this query.
- Mathlib grep: `quasiFiniteAt|quasi-finite.*curve|functionField.*[mM]ap` in
  `AlgebraicGeometry`. Sixteen returned hits, in FunctionField, RationalMap,
  ZariskisMainTheorem and Morphisms/QuasiFinite; characterizations or different results.
- Direct `rg` in `WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry`
  for function-field map names/definitions and quasi-finite curve theorems found
  component-product function fields, divisor constructions, unrelated quasi-finiteness
  theorems, and no duplicate of this theorem. Direct `grep -rn` for the item id in
  `WeilConjectures/` returned no match.
- Read the entire pinned Mathlib `AlgebraicGeometry/FunctionField.lean`: the function
  field is the generic stalk; no new definition or auxiliary map is needed here.
- Exact proposed declaration-name search in `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` returned no match.

## Second reading by Q04

This is a second reading by the same dispatcher-started worker: the brief prohibits
starting another agent, and independent maintainer review follows delivery.
I reopened the item and the completed signature and matched the hypotheses again.
There are two integral separated finite-type k-schemes, both dimension one; p is
explicitly a dominant k-morphism locally of finite type. The finite-extension binder
uses p's actual generic stalk map, so it cannot be satisfied by choosing an unrelated
field embedding. The conclusion quantifies over every source point using the exact
recorded `IsQuasiFiniteAtPoint` predicate. No nonempty-fibre restriction, separability,
normality, properness or smoothness has appeared. The eight original statement
dependencies and all other original node fields are unchanged.
I checked that the proof docstring includes the generic/closed-point classification,
generic-point image, closed-point images, finite fibres including empty ones, and the
last quasi-finiteness conversion. No mismatch or source correction was found.
