## Worker report

Item: `lem-sfb-integral-finite-etale-generic-field`. The delivery adds one theorem,
`AlgebraicGeometry.integral_finite_etale_generic_field`, in
`Sheaf.AlgebraicGeometry.IntegralFiniteEtaleGenericField`. Its only proof is `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The node is copied with only its `lean` field added.

Sources opened: Stacks `morphisms.tex`, `lemma-etale-over-field` (02GL), including
part (2) and its proof, and `lemma-integral-scheme-rational-functions` (01RV),
including its proof and the following function-field definition. The seven-step
accepted DAG proof is reproduced in the theorem docstring. The tensor and
localization calculation is the one in those accepted steps (Algebra 00CP/00DK).

Hypothesis and clause correspondence:

- Integral schemes X and Z: `{X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]`.
  The universe is explicit and arbitrary; no Noetherian, normal, separated,
  finite-type-over-a-field, or characteristic assumptions have been added.
- The named map is `(f : Z ⟶ X)`, with exactly `[IsFinite f] [Etale f]
  `[Surjective f]`.
- F and L are the actual `X.functionField` and `Z.functionField`, the generic
  stalks, rather than unspecified isomorphic fields. This is the integral-scheme
  clause of `def-sc-function-field`, whose recorded upstream module is imported.
- The induced extension is the existential `a : Algebra X.functionField
  Z.functionField`, fixed by `a = (f.functionFieldMap
  f.apply_genericPoint_of_flat).hom.toAlgebra`. Thus no arbitrary embedding is
  substituted for the canonical stalk map. The algebra binder binds the scalar
  instance for every subsequent clause. The equality selects existing data; it
  is not an additional hypothesis on f. The same map is used in the recorded
  `dominantFunctionFieldAlgebra`, which obtains its generic-point equality from
  dominance instead of flatness. Proof irrelevance identifies the equalities.
- Finite and separable extension: `FiniteDimensional X.functionField
  Z.functionField` and `Algebra.IsSeparable X.functionField Z.functionField`
  for this precise algebra structure. Over fields finite-dimensional means a
  finite field extension; Mathlib separability also includes algebraicity.
- The canonical generic fibre identification is `∃! e : Spec Z.functionField ≅
  pullback f X.fromSpecFunctionField`. This is the inverse orientation of the
  isomorphism printed in the node; its inverse gives exactly the node's display.
  The two equations with `pullback.fst` and `pullback.snd` identify its projections
  with `Z.fromSpecFunctionField` and `Spec.map` of the canonical `algebraMap`.
  Uniqueness is taken with precisely these two equations, and expresses the
  node's canonicity, not an extra arbitrary normalization of the isomorphism.
- The canonical generic-point morphisms are the existing
  `Scheme.fromSpecFunctionField`, definitionally `fromSpecStalk (genericPoint _)`.
  At a generic point of an integral scheme the stalk is a field, so this is the
  `fromSpecResidueField` map specified in the node after the canonical residue
  field identification. No unrelated map from the spectrum has been chosen.
- Every nonempty affine open is quantified as `∀ (V : X.Opens)
  (_ : IsAffineOpen V) (_ : Nonempty V)`. The proof binder supplies the nonempty
  instance for the germ algebra; it does not exclude any nonempty open.
- Its inverse image is `f ⁻¹ᵁ V`. The conclusion supplies its `Nonempty` proof
  and `IsAffineOpen` proof, so its ring is the actual `Γ(Z, f ⁻¹ᵁ V)`, B.
  A is the actual `Γ(X,V)`. Nonempty affines are spectra of these rings by their
  canonical affine-open identifications; arbitrary coordinate presentations
  introduce no extra data.
- Injectivity of A→B is `Function.Injective (f.app V)`.
  `IsFractionRing Γ(X,V) X.functionField` and
  `IsFractionRing Γ(Z,f ⁻¹ᵁ V) Z.functionField` use the existing germ algebra
  instances and thus assert the required germ-induced fraction identifications.
  Both A and B are domains by `IsIntegral.component_integral`.
- The scalar structure `ab : Algebra Γ(X,V) Γ(Z,f ⁻¹ᵁ V)` is fixed to
  `(f.app V).hom.toAlgebra` by equality. It binds all subsequent B tensor and
  module localization expressions. There is no extra assumption on the section map.
- S is `Γ(X,V)⁰`, Mathlib's non-zero-divisors submonoid. In the domain A this
  is exactly A minus zero. The localization is `LocalizedModule S B`, which
  Mathlib equips with the commutative ring structure from the actual A-algebra B.
  It is B localized at the image of S, with fractions `LocalizedModule.mk b s`.
  This uses the dependency's recorded `LocalizedModule`, rather than a private
  replacement of that notion.
- The tensor product is precisely `B ⊗[A] F`, with B's section algebra and F's
  germ algebra. The equivalences `α : B ⊗[A] F ≃+* S⁻¹B` and
  `β : S⁻¹B ≃+* L` are ring equivalences together with an explicit structural
  ring map `c : F →+* S⁻¹B`. The equations
  `α (1 ⊗ₜ t) = c t` and `β (c t) = algebraMap F L t` say exactly that these
  are F-algebra equivalences. This spells out the scalar commutation conditions
  without introducing competing global instances for the tensor's right algebra.
  In particular c is forced by α, not an unconstrained map.
- The first fraction formula is the quantified equation
  `α (b ⊗ₜ (g_X(r)/g_X(s))) = LocalizedModule.mk ((f.app V r)*b) s`.
  This is b tensor a/s ↦ ab/s with the A-action through the actual section map.
- The second formula is
  `β (LocalizedModule.mk b s) = g_Z(b)/g_Z(f.app V s)`.
  It is the specified quotient in the actual L.
- Compatibility of the composite with both affine projections is also explicit:
  `β (α (b ⊗ₜ t)) = g_Z(b) * algebraMap F L t` for every b,t.
  Putting t=1 or b=1 recovers each structural map. Under the affine spectrum
  pullback identification this gives the same two projection equations as e,
  so pullback uniqueness identifies the chart map with the global map e.
- Chart independence and restriction compatibility are not left as existence of
  unrelated field equivalences. The unique e has the two intrinsic generic-stalk
  projections, and the last clause computes β(b/s) after restriction to every
  nonempty open W ≤ f⁻¹V using `Z.presheaf.map (homOfLE hW).op`. Thus restrictions
  on any common affine refinement have the same quotient in L. Any two
  nonempty affine charts intersect at the generic point and admit such a
  refinement; no affineness of their entire intersection is assumed.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, including its nonempty
  and domain-of-sections fields.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`, affine preimage and
  finite section map; the node's integral-morphism alternative is not an
  assumption in this item.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, its affine-local signature.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the component-product
  declaration/docstring and its explicit instruction to reuse Mathlib
  `Scheme.functionField` for arbitrary integral schemes.
- `Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.functionField`,
  `Scheme.germToFunctionField`, its algebra instance, field instance, and
  `functionField_isFractionRing_of_isAffineOpen`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `RingHom.toAlgebra`, `algebraMap`.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift` and their full signatures.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, `TensorProduct.tmul`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`,
  `LocalizedModule.mk`, its fraction relation and its ring/algebra constructions.
- `Mathlib.AlgebraicGeometry.ResidueField`: `fromSpecResidueField`,
  `Hom.SpecMap_residueFieldMap_fromSpecResidueField`, `Spec.residueFieldIso`;
  these are the relevant maps of the Mathlib-only morphism-from-field dependency.
- `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`:
  `Scheme.fromSpecFunctionField`, the actual existing canonical generic map.
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`:
  `Hom.apply_genericPoint_of_flat`, `Hom.functionFieldMap` (generic stalk map).
- The recorded proof dependency module `Sheaf.TraceFormula.LocalDimensionFormula`
  is imported without `public`; its `Hom.dominantFunctionFieldAlgebra` was read
  in full. Other proof-only imports provide the unramified residue-field input,
  finite-dimensional-domain input, and algebra tensor pushout interface. The
  affine fibre product and residue naturality inputs occur in the imported
  Mathlib `Pullbacks` and `ResidueField` modules.

Edge cases checked before writing: the identity cover gives F=L and the identity
fraction formulas; a field base gives the usual finite separable field extension
and its spectrum; a non-normal or non-Noetherian integral base is allowed;
positive characteristic is allowed. Purely inseparable nontrivial field maps
are excluded by étaleness, and a reducible cover is excluded by integrality.
Empty X or Z cannot satisfy IsIntegral. Empty affine V is deliberately excluded
by the node, and the inverse image of any admitted V is nonempty by surjectivity.
A nonempty overlap need not itself be affine; the final clause handles its
nonempty open refinements. Zero numerators are allowed; denominators are exactly
nonzero elements of a domain, not all elements including zero.

Searches actually run with `msearch.py Q39 lem-sfb-integral-finite-etale-generic-field`:

- LeanFinder: “For a surjective finite etale morphism of integral schemes the
  generic fibre is the spectrum of its function field, a finite separable
  extension”. Eight hits; no exact combined statement.
- LeanFinder: “generic fiber of integral finite etale scheme canonical function
  field spectrum”. Eight hits, including `Scheme.functionField`,
  `Scheme.RationalMap.fromFunctionField_ofFunctionField`, and the existing field
  and fraction-ring instances. None states this theorem's projections and charts.
- Loogle: `"functionField", "fiber"`, twice: zero hits.
- Mathlib grep: `functionField.*[Ee]tale|[Ee]tale.*functionField|functionField.*fiber|fiber.*functionField`
  in AlgebraicGeometry: zero hits.
- LeanSearch: “The function field of a surjective integral finite etale cover is
  a finite separable extension and its spectrum is the generic fibre”. Eight
  hits; function-field and etale-algebra classification inputs, no exact statement.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  functionField/Etale combinations found related generic-fibre and curve modules,
  not this combined statement. A dedicated rg for
  `integral_finite_etale_generic_field` (including `dag/lean_names_upstream.json`)
  found no declaration. The prescribed grep of the item id in WeilConjectures
  also found no occurrence.

Validation: `scompile.py` compiled the file in both its sandbox and library module
contexts without errors or unexpected warnings. All variables and universes are
explicit (`set_option autoImplicit false`). There are no helper declarations,
local instances, local notations, axioms, or data constructions using sorry.

## Second reading by Q39

A separate rereading pass compared the accepted node with the final signature,
particularly its scalar binders, directions of Spec maps, and all chart clauses.
The direction of e is Spec L to the pullback, so its hom has the two stated
projections and its inverse supplies the displayed isomorphism in the node.
The algebra data a and ab are fixed by equalities, and neither is an extra
assumption. F-algebra compatibility is expressed by c and the first two
conjuncts; merely asserting ring equivalences would have missed that clause.
The pure-tensor composite equation links these affine isomorphisms to the
intrinsic projection maps. The final restriction formula and uniqueness clause
supply the chart-independence assertion. Nonempty V and its explicitly supplied
nonempty inverse image bind the correct germ instances. No mismatch or source
error was found. This is the worker's second pass, not a claim of review by a
second agent: the dispatcher explicitly prohibited starting other agents, and
the maintainer supplies the independent review of this delivery.
