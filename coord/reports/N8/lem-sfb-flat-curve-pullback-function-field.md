## Worker report

The module `Sheaf.AlgebraicGeometry.FlatCurvePullbackFunctionField` states
`AlgebraicGeometry.flatCurvePullback_functionField`, with its whole proof `sorry`.
No definitions, extra nodes, dependency repairs, or statement corrections are needed.
The existing node is copied with only `lean` changed.

Hypotheses, individually:

- The base field is `{k : Type u} [Field k]`.
- The three schemes are `{B V P : Scheme.{u}}`, with their three `Over (Spec (.of k))`
  instances. The maps' `IsOver` instances express that these are maps of the given
  k-schemes, rather than maps with unrelated structure maps.
- Integrality is exactly `[IsIntegral B] [IsIntegral V] [IsIntegral P]`.
- Each scheme is of finite type over k: for each of B, V, P its structure morphism
  has both `LocallyOfFiniteType` and `QuasiCompact`, as the recorded finite-type node
  prescribes. No separatedness or properness is assumed.
- `v : V ⟶ B` is flat, finite type, dominant: `[Flat v]`,
  `[LocallyOfFiniteType v] [QuasiCompact v]`, `[IsDominant v]`.
  `IsDominant` means precisely dense image.
- `hred` says, for every `b : B`, that the pullback along
  `Spec.map (algebraMap (B.residueField b) (AlgebraicClosure (B.residueField b)))`
  followed by `B.fromSpecResidueField b` is reduced. This uses the exact scheme-valued
  geometric fibre of `def-weil-geometric-fibre`, and tests reducedness at a chosen
  algebraic closure, without replacing it by an extra hypothesis about all field points.
- `hgeneric : GeometricallyIntegral (v.fiberToSpecResidueField (genericPoint B))`
  is geometric integrality of the generic fibre. For integral B its generic residue
  field is canonically its generic stalk, namely `B.functionField = K`.
- `h : P ⟶ B` is dominant through `[IsDominant h]`. The sole finiteness hypothesis
  `hfinite` is `RingHom.Finite` on `h.functionFieldMap
  h.apply_genericPoint_of_isDominant`, the actual induced map K → M. By definition this
  is `Module.Finite K M` for that map's algebra structure, hence exactly finite
  function-field extension. There is no flatness hypothesis on h.

Conclusions, individually:

- W is exactly `pullback v h : Scheme.{u}`, the ordinary fibre product throughout;
  it is neither a reduction nor a normalization.
- `IsReduced (pullback v h)` is its reducedness, and the existential binder
  `∃ (_ : IsIntegral (pullback v h)), ...` gives integrality. The binder permits using
  the standard integral-scheme function-field instance in the rest of the conclusion;
  it is a conclusion, not an assumed integral pullback.
- `GeometricallyIntegral ((pullback.snd v h).fiberToSpecResidueField (genericPoint P))`
  is geometric integrality of W's generic fibre over P, over its generic residue field.
- The `∀ (F : Type u) [Field F] (b : Spec (.of F) ⟶ B)` clause states reducedness of
  the ordinary pullback of v to every field-valued point, including empty fibres.
- `hp` and `hq` say that the two projections carry W's generic point to the factors'
  generic points. These are the domain identifications for the canonical maps on
  function fields. Their existence expresses the generic maps invoked by the node's
  canonical-identification clause; neither is an additional hypothesis.
- The object `pushout (v.functionFieldMap ...) (h.functionFieldMap ...)` in
  `CommRingCat` is L ⊗_K M, with the K-actions induced by the given morphisms.
  Mathlib's `CommRingCat.pushoutCocone K L M` has point `CommRingCat.of (L ⊗[K] M)`;
  `pushoutCoconeIsColimit K L M` proves that this is the categorical pushout, and
  `pushoutCocone_inl` and `pushoutCocone_inr` identify its arrows with l ↦ l ⊗ 1 and
  m ↦ 1 ⊗ m. This uses the existing construction and does not redefine a tensor product.
- `∃ e : pushout ... ≅ (pullback v h).functionField, ...` gives the claimed
  ring identification. Both equations `pushout.inl ... ≫ e.hom = ...` and
  `pushout.inr ... ≫ e.hom = ...` fix its values on the two factors to the projections'
  actual `functionFieldMap`s. Thus the identification is canonical, with pure-tensor
  formula l ⊗ m ↦ p*(l) q*(m); it is not just existence of an unrelated field isomorphism.
- `IsField (pushout ... : CommRingCat.{u})` says the tensor ring is a nonzero field.
  `(pushout.inl ...).hom.Finite` says it is finite over L through its canonical
  inclusion. `IsField` avoids choosing different ring operations or a new field carrier.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, including its inherited
  nontriviality and nonzero inverse laws.
- `def-pc-integral-scheme` and `def-pc-reduced-scheme`: `AlgebraicGeometry.IsIntegral`
  and `AlgebraicGeometry.IsReduced`, `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`.
- `def-weil-flat-morphism`: `Flat`, `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  with its documented stalkwise equivalence `Flat.iff_flat_stalkMap`.
- `def-weil-geometric-fibre` and `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`
  and its projections, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  `Scheme.Hom.fiberToSpecResidueField` from `Mathlib.AlgebraicGeometry.Fiber`.
- `def-pc-geometrically-irreducible`: `GeometricallyIntegral`,
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`. Its full signature and docstring,
  and the reduced/irreducible classes and field-extension characterization were read.
- `def-sc-function-field`: `WeilConjectures.AlgebraicGeometry.FunctionField` expressly
  uses Mathlib's `Scheme.functionField` for arbitrary integral schemes; that is the
  integral-scheme clause used here. The component-product declaration is not used for
  these integral schemes. The full module and Mathlib generic-stalk definition were read.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, and
  `RingHom.toAlgebra`, used by the recorded generic-stalk maps and tensor construction.
- `def-pc-field-tower`: `Sheaf.FieldTheory.FieldTower` explains that the finite clause
  reuses `Module.Finite`, rather than defining a separate finite-extension predicate.
  `RingHom.Finite` unfolds to that clause for the specified map. Its degree declaration
  was read; a numerical degree is not required by this node.
- The canonical maps are the existing `Scheme.Hom.functionFieldMap` in
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`, and the already proved
  `Scheme.Hom.apply_genericPoint_of_isDominant` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`. These use the generic
  stalk map, transported by the equality of generic points.
- All proof-only dependency modules are imported without `public`: flat torsion-free
  modules (`Mathlib.RingTheory.Flat.TorsionFree`), localization-tensor compatibility
  (`Mathlib.RingTheory.Localization.BaseChange`), finite-dimensional domains
  (`Mathlib.LinearAlgebra.FiniteDimensional.Basic`), geometric-integrality transfer
  (`WeilConjectures.AlgebraicGeometry.FieldFractionRingGeometricIntegrality`), and the
  algebraic-closure test (`Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest`).
  The affine and open fibre-product and affine function-field dependencies are already
  publicly imported by the statement dependencies. Their source declarations were read.

Sources and edge checks:

- Read Stacks `divisors.tex`, `lemma-flat-over-integral-integral-fibre` (Tag 0BCM),
  including its torsion-free generic-localization proof, and the Mathlib geometric
  reducedness, integral-scheme and affine tensor constructions named by the node.
- Opened de Jong's primary PDF at https://www.numdam.org/item/10.5802/aif.1575.pdf,
  Theorem 5.9 proof, printed p.617 (PDF page 19, zero-based). Its final paragraph uses
  the ordinary fibre product. The detailed function-field verification is the
  agent-formulated argument recorded in this node, not a quotation from de Jong.
- Read the current blueprint direct-image unit in `literature/blueprint/latest/`.
- Integral input schemes are necessarily nonempty. A missing special fibre can be empty;
  the geometric-reducedness hypothesis and field-point reducedness conclusion allow it.
  The geometrically integral generic fibre is nonempty and forces nonempty W.
- Degree-one/identity base change gives the original function field and family.
  A finite inseparable extension is allowed; generic geometric integrality ensures
  the tensor is still a domain. No perfectness, separability or characteristic
  restriction is imposed. Positive-dimensional generic fibres are allowed: despite
  the title, the node imposes no relative dimension-one hypothesis, and neither does Lean.
- h need not be flat. There is no implicit flat instance required for it in any binder.
  Affineness, normality, smoothness, properness and separatedness are not assumed.
- The common scheme universe u includes all their residue fields, function fields,
  algebraic closures and finite tensor products. Field-valued tests use `Type u`,
  matching Mathlib's geometric property on `Scheme.{u}`, rather than an independently
  smaller universe. Larger test fields reduce to these tests by the usual affine
  geometric-reducedness criterion; there is no extra universe-equality hypothesis.

Searches before writing (recorded by msearch.py in searches.jsonl):

- LeanFinder: “The function field of the fibre product of integral schemes in a flat
  family with geometrically integral generic fibre is the tensor product of function
  fields under a generically finite base change” (8 hits). A second shorter query
  also returned 8 hits. These are the residue-field tensor at a pullback triplet,
  `Triplet.tensor`, `tensorInl`, `tensorInr`, `SpecTensorTo` and `ofPointTensor`;
  none asserts integrality of the entire pullback or this function-field identification.
- Loogle: `AlgebraicGeometry.Flat, AlgebraicGeometry.IsIntegral` (4 hits).
  The integral-base-change results require geometrically integral ALL fibres, which
  is stronger than this node's generic-fibre hypothesis. No exact statement exists.
- Mathlib grep: `functionField.*[Tt]ensor|[Tt]ensor.*functionField|generic.*[Ii]ntegral`
  in `AlgebraicGeometry` (1 hit, affine generic point in FunctionField.lean).
- LeanSearch: “Function field of fibre product of flat integral schemes with
  geometrically integral generic fibre is tensor product of function fields” (8 hits).
  Hits include the generic-stalk function field, affine fraction-ring property,
  field instance, residue-field pullback comparison and unrelated arithmetic function
  fields. None states the node.
- rg searches in both `lean/WeilConjectures` and `lean/Sheaf` for functionField/tensor,
  functionFieldMap and the item id located the reusable generic-stalk map but no
  existing node theorem. The final declaration name and item id have no occurrence in
  either source root or `dag/lean_names_upstream.json`.

Validation: the first compile diagnosed category inference at generic-point and ring
coercions; explicit `Scheme.{u}` and `CommRingCat.{u}` annotations repaired it. The
server compile then passed in 51 seconds under the fixed 60-second limit, with no
compiler warning. Expected proof obligation is the single named theorem with its
whole proof `sorry`; its nine-step docstring retains every step of the DAG argument.
The final dry run and delivery recompile the full delivered module.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
