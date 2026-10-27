## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.ProperFunctionFieldMorphisms` states every
clause of `lem-sfb-proper-curve-function-field-morphisms`. Its three theorem proofs are
`sorry`; the only new definition, `Scheme.Hom.curveFunctionFieldBaseMap`, has real data.
The node's statement, dependencies and proof are unchanged. Q14's existing review is
stage 1, not a Lean attachment: the current item had no `lean` record or module. The
previous retry left no Lean file or node in this sandbox.

The main declaration is `AlgebraicGeometry.proper_curve_function_field_morphisms`.
Here is the hypothesis and conclusion correspondence, including the two additional
clause declarations in the same module:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The schemes and their fixed structures over k are `(X Y : Scheme.{u})` and
  `(sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))`.
- Integral is `[IsIntegral X] [IsIntegral Y]`, using the recorded Mathlib notion.
- Curves are `[IsCurve sX] [IsCurve sY]`; this is the recorded upstream class for
  separated finite-type schemes of topological dimension at most one.
- Smooth and proper are `[Smooth sX] [Smooth sY] [IsProper sX] [IsProper sY]`.
- Dimension one is exactly `topologicalKrullDim X = 1` and the analogous equality
  for Y. Integrality already supplies nonemptiness and irreducibility; no geometric
  integrality, projectivity, flatness or separability hypothesis is added.
- `X.functionField` and `Y.functionField` are the generic stalks specified by
  def-sc-function-field's integral-scheme clause, not the component-product carrier.
  They have Mathlib's canonical field instances.
- The canonical scalar map is the composite `(ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
  X.presheaf.germ ⊤ (genericPoint X) trivial`. The helper merely names this real
  composite and never chooses an unrelated field extension. It belongs to the
  function-field correspondence's own notion and is listed in `lean.declarations`.
- Finite generation of each function field is `IntermediateField.FG ⊤` for the
  explicit algebra induced by that scalar map. This is finite generation as a
  FIELD extension, not the stronger `Algebra.FiniteType k X.functionField`.
- Transcendence degree is `Algebra.trdeg ... = 1`, again for that explicit algebra.
- A k-morphism f is `f : X ⟶ Y` with `f ≫ sY = sX`.
- Nonconstant means exactly `¬ ∃ y : Spec (.of k) ⟶ Y,
  y ≫ sY = 𝟙 _ ∧ sX ≫ y = f`: there is no factorization through a rational point.
- Its generic-point image is the witness `hf : f (genericPoint X) = genericPoint Y`.
- Its induced embedding is the EXISTING `(f.functionFieldMap hf).hom`, not a freely
  chosen embedding. Injectivity is explicitly asserted. The ring-hom equation
  `fieldMap.comp sY.curveFunctionFieldBaseMap = sX.curveFunctionFieldBaseMap`
  says precisely that it fixes k. Ring homomorphisms between these fields are
  automatically injective, so the inverse clause quantifies over all compatible
  ring homomorphisms with no additional injectivity assumption.
- Finiteness is `Module.Finite Y.functionField X.functionField` with the module
  induced by this actual field map's `.toAlgebra`, not an unrelated scalar action.
  This is exactly finiteness over the embedded target field, as in def-pc-field-tower.
- Bijectivity is stated by the graph: for EVERY compatible φ there exists exactly
  one f in the subtype of nonconstant k-morphisms whose actual generic-stalk map
  equals φ. Together with the forward clause, this is exactly the bijection of the
  node. The equality proof hf is proof-irrelevant, so no extra choice is involved.
- `proper_curve_function_field_identity` states that the identity is nonconstant
  and its actual function-field map is `RingHom.id X.functionField` for every proof
  of its generic-point equality. It has the same single-curve hypotheses.
- `proper_curve_function_field_composition` binds X,Y,Z with the same hypotheses,
  two nonconstant k-morphisms f,g, and asserts nonconstancy of `f ≫ g`, all three
  generic-point equalities, and `fieldMap (f ≫ g) = fieldMap f .comp (fieldMap g)`.
  Thus the contravariant composition formula has the correct order.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs.
- def-weil-algebraic-closure: `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic
  (publicly imported through its recorded AlgebraicClosure module). We need the
  algebraic-closedness clause, not a new chosen algebraic closure.
- def-sc-curves: `AlgebraicGeometry.IsCurve`, WeilConjectures.AlgebraicGeometry.Curve,
  including its full signature and docstring and the separate smooth/proper convention.
- def-pc-integral-scheme: `AlgebraicGeometry.IsIntegral`,
  Mathlib.AlgebraicGeometry.Properties.
- def-sc-function-field: WeilConjectures.AlgebraicGeometry.FunctionField and its
  `Scheme.functionFieldOfComponents` docstring explicitly direct integral schemes
  to Mathlib's `Scheme.functionField`. This is the generic stalk used here.
- def-pc-field-extension: `Algebra` and `RingHom.toAlgebra`, Mathlib.Algebra.Algebra.Defs.
- def-kun-transcendence-degree: `Algebra.trdeg`,
  Mathlib.RingTheory.AlgebraicIndependent.Basic.
- def-pc-field-tower: `FieldExtension.degree`, Sheaf.FieldTheory.FieldTower; its
  module docstring specifies `Module.Finite` for the finite-extension clause.
- The existing `Scheme.Hom.functionFieldMap`, including its full implementation
  and docstring, is from WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback:
  stalk specialization along hf followed by the morphism's stalk map.

The module imports recorded modules for the stated proof dependencies, including the
local-ring and dimension results, Nullstellensatz, closed-immersion factorization,
transcendence-degree tower, algebraic generators, properness and stalk functor. The
valuation-extension node has no Lean record yet; its exact general upstream extension
`Scheme.exists_hom_of_valuationRing_stalk` is already in
WeilConjectures.Mathlib.AlgebraicGeometry.Birational.RationalMap, which is imported.
No dependency notion needs repair and no new DAG node is introduced.

The source was read at `literature/stacks-project/curves.tex`, theorem-curves-rational-maps,
lines 159--228, especially the third proof paragraph, matching Stacks 0BY1. Each theorem
has a source/blueprint docstring and its natural-language proof. The main docstring
carries steps 1--8, and the identity/composition docstrings carry step 9.

Edge cases checked: the empty scheme is excluded by integrality and dimension one;
Spec k is excluded by dimension one; a constant rational-point map fails exactly the
nonconstant predicate; identity maps satisfy it and induce degree-one extensions;
Frobenius in positive characteristic is included, with no separability condition;
curves with no maps would give empty corresponding hom sets, handled by the graph
form; the theorem uses an arbitrary universe u and does not specialize characteristic.
No statement fault or STATEMENT-DISPUTED remains.

Searches performed for this delivery:

- msearch.py leanfinder: “Nonconstant morphisms of smooth proper integral curves
  correspond bijectively to embeddings of their function fields”: eight hits, headed
  by Scheme.RationalMap.fromFunctionField_ofFunctionField and related rational-map
  interfaces. None gives the everywhere-defined proper-curve correspondence.
- msearch.py loogle: `functionFieldMap, functionField, IsDominant`: zero hits,
  unknown identifier functionFieldMap in its index. Source search resolves that name.
- msearch.py grep, AlgebraicGeometry:
  `nonconstant.*functionField|functionField.*(fullyFaithful|homEquiv|nonconstant)`:
  zero Mathlib hits.
- rg over WeilConjectures and Sheaf for functionField/map/equivalence/nonconstant:
  found DivisorPullback.functionFieldMap, dominantFunctionFieldAlgebra, and existing
  FrobeniusSeparableFactorization's canonical generic-point diagram; no complete
  correspondence theorem. Searching the item id in WeilConjectures gave no hit.
- DAG search for functionFieldMap/IsFunctionFieldAlgebra found
  def-sfb-dominant-function-field-map and its existing generic-stalk algebra; this is
  not the base-field-to-generic-stalk scalar composite or the correspondence theorem.
  The new helper is only that explicit scalar composite, not another function-field
  map, field extension, or curve definition.

Validation: scompile.py compiled sandbox and final module cleanly (6.2s and 7.3s),
with no warnings or errors. The first compile exposed the explicit argument order of
IntermediateField.FG and a nonempty-top instance request; both were repaired by reading
its signature and using the direct germ at the already available generic point.
Only the three requested theorem proofs are postponed. The final import list is
checked again by the required dry run.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
