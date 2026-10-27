## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.NonconstantGenericCriterion` states
`AlgebraicGeometry.curve_nonconstant_generic_criterion`, with one `sorry` and no
new definitions. The node is unchanged except for `lean`.

Source read: `literature/stacks-project/curves.tex`, Tag 0BY1,
`theorem-curves-rational-maps`, the preceding paragraph defining constant morphisms,
and the third proof paragraph taking the map of generic local rings. The node
expands the generic-point argument to arbitrary integral sources using its recorded
closed-point and reduced-source factorization dependencies. No source correction
is needed.

Hypothesis and conclusion correspondence:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Integral k-scheme T: `(T : Scheme.{u})`, `[IsIntegral T]`, and
  `(sT : T ⟶ Spec (.of k))`. In particular T is nonempty; no finite-type,
  separatedness, smoothness, or dimension condition is imposed on T.
- Smooth integral dimension-one k-curve C: `(C : Scheme.{u})`, `[IsIntegral C]`,
  `(sC : C ⟶ Spec (.of k))`, `[IsCurve sC]`, `[Smooth sC]`, and
  `(hCdim : topologicalKrullDim C = 1)`. The recorded `IsCurve` includes
  separatedness, locally finite type, quasi-compactness, and dimension at most one.
  Explicit structure morphisms are appropriate because the node names sT and
  `IsCurve` takes the structure morphism as its argument.
- Generic points eta_T and eta_C: `genericPoint T` and `genericPoint C`.
  Mathlib's `genericPoint_spec` gives `IsGenericPoint ... Set.univ`; scheme
  sobriety and integrality supply its instances. Uniqueness makes choosing these
  generic points equivalent to naming arbitrary generic points of T and C.
- A k-morphism u: `(u : T ⟶ C) (hu : u ≫ sC = sT)`.
- The equivalence: the first conjunct is exactly
  `u (genericPoint T) = genericPoint C ↔ ¬ ∃ c, c ≫ sC = 𝟙 _ ∧ sT ≫ c = u`.
  The first equation makes c a section, hence a k-point. Category composition
  `sT ≫ c = u` is precisely u = c composed with sT.
- Nongeneric case: the second conjunct is conditional on
  `u (genericPoint T) ≠ genericPoint C`. It asserts `IsClosed {u (genericPoint T)}`
  and `Set.range u = {u (genericPoint T)}`, so the image is exactly the indicated
  single closed point, not merely contained in it.
- The residue-field assertion kappa_C(y) = k: the same conjunct asserts
  `Function.Bijective (sC.residueFieldAlgebraMap (u (genericPoint T)))`.
  This is bijectivity of the actual structural unital field map k to kappa_C(y).
  It expresses equality as a structural extension, including the k-compatibility,
  rather than an unrelated abstract isomorphism of fields.
- The constant-case factorization: `∃ c, c ≫ sC = 𝟙 _ ∧ sT ≫ c = u`.
  Together with the singleton image and the nonemptiness of T, this section is
  the rational point at y. No arbitrary map is substituted for the point.
- Generic case: for every proof `h : u (genericPoint T) = genericPoint C`,
  `Function.Injective (u.functionFieldMap h).hom` concerns the actual induced
  function-field map. The source is C.functionField and target T.functionField;
  both are fields by the integral instances.
- The assertion that this is a k-homomorphism: the next equality says the composite
  of the canonical k-to-global-sections map `(Scheme.ΓSpecIso (.of k)).inv`,
  pullback `sC.appTop`, and the generic germ, followed by `u.functionFieldMap h`,
  is the corresponding composite for T and sT. This is exactly preservation of
  the two structural embeddings of k, using explicit canonical maps without
  selecting an arbitrary algebra structure or defining a duplicate scalar map.
- Germ formula: for every `U : C.Opens`, `hU : genericPoint C ∈ U`, and
  `a : Γ(C, U)`, the last equality sends the germ of a to the germ of `u.app U a`
  on `u ⁻¹ᵁ U`. The term `Eq.mpr (congrArg (fun x : C ↦ x ∈ U) h) hU`
  supplies membership of the source generic point in this inverse image. It is
  explicit equality transport, not an added hypothesis or a chosen comparison.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` for def-weil-field.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` and its Basic import:
  `IsAlgClosed` for the algebraically closed clause of def-weil-algebraic-closure.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral` for
  def-pc-integral-scheme (nonempty and domain sections).
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver`, and
  `Scheme.Hom.isOver_iff`, used in their equivalent explicit-morphism/equation form
  for def-weil-scheme-over-base.
- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve`, the
  recorded declaration of def-sc-curves; smoothness is `Smooth sC`.
- `Mathlib.Topology.Sober`: `genericPoint`, `genericPoint_spec`, `IsGenericPoint`
  for def-sc-generic-point.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map` for
  def-weil-affine-spectrum; the statement uses Spec itself.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, the exact
  local-ring residue field of def-weil-residue-field, and `Scheme.Hom.residueFieldMap`.
  `WeilConjectures.ZetaSeries` supplies its canonical structural specialization
  `Scheme.Hom.residueFieldAlgebraMap`; its body composes the actual induced residue
  map with the field-spectrum residue identification.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded
  `Scheme.functionFieldOfComponents`, whose docstring explicitly directs the
  arbitrary integral-scheme clause of def-sc-function-field to Mathlib's
  `Scheme.functionField`. The theorem uses that existing generic stalk, exactly
  as required by the project FUNCTION FIELD convention.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, the recorded field-extension notion;
  k-compatibility is rendered as an equality of structural ring maps, an
  equivalent ring-homomorphism presentation of the same extension notion.
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`:
  `Scheme.Hom.functionFieldMap`, the existing actual generic stalk map. Its full
  signature assumes only integral source/target and equality of generic images.
  Its body is `stalkSpecializes` along that equality followed by `u.stalkMap`.
  No flatness, properness, or other hypothesis from later results in that module
  is imposed here. No second definition is introduced.

Plain imports record all additional stated proof dependencies:
`Mathlib.Topology.KrullDimension` (`topologicalKrullDim`),
`Mathlib.AlgebraicGeometry.AlgClosed.Basic` (`residueFieldIsoBase` and
`SpecMap_residueFieldIsoBase_inv`),
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (`IsClosedImmersion`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
(`IsClosedImmersion.existsUnique_fac_of_range_subset_range`),
`Sheaf.AlgebraicGeometry.ClosedPointField`
(`closedPoint_iff_residueField_trdeg_zero_and_finite`),
`WeilConjectures.AlgebraicGeometry.RationalFunctionsGenericStalks`
(`Scheme.exists_ringEquiv_rationalFunctionRing_pi_stalk`), and
`WeilConjectures.Topology.PresheafModuleStalkFunctor`
(`PresheafOfModules.moduleStalkFunctor`). The sober-scheme proof dependency is
already covered by the public Properties and Sober imports. No proof import is
omitted for an import cycle.

Edge cases checked before writing:

- T = Spec k and a rational-point morphism: generic image is closed, the first
  equivalence is false on both sides, and the constant clause gives the section.
- T = C with the identity: the generic case gives the identity field injection
  and the usual germ identity. The dimension-one condition excludes treating
  Spec k as a target curve in this test.
- T = Spec k(C) with its canonical generic-point morphism: T has no curve or
  finite-type assumption, and the statement retains this important case.
- Integral sources that are not of finite type, or not quasi-compact, remain
  allowed; factorization uses reducedness, not finite type of T.
- Empty T or C are excluded by precisely their stated integrality; a
  zero-dimensional C is excluded by precisely the stated dimension-one clause.
- All characteristics are retained, including purely inseparable morphisms.
  Injectivity of the induced field map does not assert separability.
- The universe u is arbitrary. Schemes and the field are in a common universe,
  and any such objects can be placed in a common larger universe; no equality of
  site universes or additional smallness condition is imposed.
- The residue-field conclusion uses the structural map, and the germ formula
  quantifies over every neighborhood and section, including zero sections.

Searches actually run through msearch.py:

- `leanfinder`: "A morphism from an integral scheme to a smooth integral curve
  over an algebraically closed field is nonconstant exactly when it sends
  generic point to generic point". Eight candidates, including
  `genericPoint_eq_of_isOpenImmersion`, `IsDominant`, and rational-map/function-field
  correspondences. None gives this criterion with arbitrary integral source and
  both additional conclusions.
- `loogle`: `"genericPoint", "IsDominant"`. Zero hits.
- `grep`, Mathlib AlgebraicGeometry: `nonconstant|constant.*genericPoint|genericPoint.*constant`.
  Zero hits.
- `leansearch`: "Nonconstant morphisms from integral schemes to smooth integral
  curves are dominant and induce injective function field maps". Eight hits,
  concerning dominance and germ injections, not the full statement.
- Direct `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for nonconstant/constant-generic-point patterns
  and the exact item id found downstream curve statements, including
  ProperFunctionFieldMorphisms and CompleteCurveConnectedLinearAction, but no
  theorem stating this item. Their source signatures were checked: the former
  assumes proper dimension-one source curves, so cannot be used as an exact
  existing match for arbitrary integral T.
- Direct declaration searches found the existing `Scheme.Hom.functionFieldMap`
  and `Scheme.Hom.residueFieldAlgebraMap`; those constructions are reused.
  Exact-name search for `curve_nonconstant_generic_criterion` in Mathlib/project
  records found no existing declaration.

Validation: scompile.py compiled both the sandbox and library module successfully,
with no errors or warnings (2.4 s and 2.7 s on the clean run). The first compiler
pass rejected an under-specified equality cast for inverse-image membership;
replacing it by the explicit proposition equality above repaired elaboration.
All variables and the universe are bound explicitly; autoImplicit is disabled.
There are no new nodes, dependency repairs, statement changes, or disputes.

## Second reading by Q98

A separate second pass by the same worker reopened the node and finished module;
no additional agent was started, as required by the dispatcher brief. The maintainer
will supply the independent review. This pass checked every binder and all three
conjuncts against the node, not just successful elaboration.

`IsCurve sC` retains separatedness and finite type; `hCdim` retains dimension
exactly one, and `Smooth sC` retains smoothness. T is integral with an arbitrary
structure map, with no accidental curve hypothesis. The over-k equation has the
correct composition order. The two existential rational-point clauses both
require the section equation as well as factorization. The range equality and
closed singleton are both present. Bijectivity refers to the structural residue
map, so it does not weaken kappa(y) = k to an arbitrary abstract isomorphism.

The final conjunct uses the existing function-field map, with injectivity and
an explicit equality of canonical constant maps. Its germ equation uses the
same h to identify the target generic stalk and to transport inverse-image
membership. Every germ near the target generic point is covered. The explicit
cast was the only mismatch found during elaboration; the mathematical statement
needed no correction. The source proof's five steps are all in the declaration
docstring and their recorded available modules are imported. A source comparison
confirmed that only lean changes in the JSON, and its signature is verbatim.
