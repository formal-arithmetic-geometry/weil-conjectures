## Worker report

The delivery states `AlgebraicGeometry.finite_normal_cover_affine_field_data` in
`Sheaf.AlgebraicGeometry.FiniteNormalCoverAffineFieldData`, with one whole-proof
`sorry`. There are no definitions, new nodes, dependency repairs, or statement
corrections. Only the item's `lean` field is changed. The previous worker's
stage-1 supersession is not a stage-2 obstruction: the current node has a passing
Q146 stage-1 review, is split, appears in `coord/queue.tsv` at stage 2, and has
no Lean record. The 2026-10-22 handoff in `coord/brief-stage2.md` explicitly covers
this situation. No repair note for this item is present.

Source read: `literature/stacks-project/divisors.tex`,
`lemma-norm-in-normal-case` (Tag 0BD3), statement and proof, especially the first
paragraph and its square of rings and fraction fields. The node expands the
normality and generic-point identifications needed for that construction.
The accepted node statement and proof are preserved.

Hypothesis and clause correspondence:

- Schemes and integral source and target: `{Y Z : Scheme.{u}} [IsIntegral Y]
  [IsIntegral Z]`. Mathlib's integral scheme is nonempty and has domain section
  rings on all nonempty opens, equivalently the node's affine-local definition.
- Finite and surjective morphism: `(p : Y ⟶ Z) [IsFinite p] [Surjective p]`.
  These are the recorded definitions, not additional finiteness or dominance
  assumptions.
- Every local ring of the base is an integrally closed domain: `hZ` quantifies
  over every `z : Z` and states `IsDomain (Z.presheaf.stalk z) ∧
  IsIntegrallyClosed (Z.presheaf.stalk z)`. This is exactly the inline normal-domain
  convention of `def-weil-pbc-normal-ring`.
- The generic points are `genericPoint Y` and `genericPoint Z`. The first
  existential `hη` is the conclusion `p (genericPoint Y) = genericPoint Z`,
  not an assumed generic-point preservation property.
- `K` and `L` are `Y.functionField` and `Z.functionField`: the existing Mathlib
  abbreviations for the actual structure-sheaf stalks at these generic points.
  Their field structures are Mathlib instances for integral schemes.
- The embedding is precisely `(p.functionFieldMap hη).hom`. Its existing
  construction is the stalk map at `genericPoint Y`, preceded by stalk transport
  along `hη`. `Function.Injective` is asserted, and its `RingHom.Finite` clause
  states that `K` is a finite module, equivalently finite-dimensional over `L`,
  for this particular ring map's algebra structure.
- The natural number `d` is explicitly equal to `Module.finrank` with module
  structure `(p.functionFieldMap hη).hom.toAlgebra.toModule`, followed by `1 ≤ d`.
  There is no independently assumed field action or chosen degree.
- Every nonempty affine open is covered by `∀ (U : Z.Opens)
  (_hU : IsAffineOpen U) [Nonempty U]`. The associated affine ring `B` is the
  actual ring `Γ(Z, U)`. Writing an affine open as its spectrum is encoded by
  `IsAffineOpen`, the standard scheme interface; no affine presentation is fixed.
- The actual inverse image is `p ⁻¹ᵁ U`. The conclusion supplies its nonemptiness
  as an existential proof `_hpre`, then asserts `IsAffineOpen (p ⁻¹ᵁ U)`.
  This proof supplies the nonempty-open instance used by the later germs. Its
  coordinate ring `A` is the actual ring `Γ(Y, p ⁻¹ᵁ U)`.
- `IsDomain Γ(Z, U) ∧ IsDomain Γ(Y, p ⁻¹ᵁ U)` supplies both domain assertions.
  The section homomorphism is the canonical `(p.app U).hom`. Its injectivity and
  `RingHom.Finite` are the next two clauses. The latter is exactly finite
  generation over `B` via this ring homomorphism, not cardinal finiteness.
- `IsIntegrallyClosed Γ(Z, U)` states integral closedness of `B` in its fraction
  field using the recorded Mathlib predicate.
- The embeddings `ρ_U` and `σ_U` are the existing maps
  `(Z.germToFunctionField U).hom` and
  `(Y.germToFunctionField (p ⁻¹ᵁ U)).hom`. Both are explicitly injective.
- `IsFractionRing Γ(Z, U) Z.functionField` and
  `IsFractionRing Γ(Y, p ⁻¹ᵁ U) Y.functionField` use the existing germ-induced
  algebra instances. For domains and field targets this says exactly that every
  field element is the quotient of images of ring elements with nonzero
  denominator. These are not arbitrary algebra structures or abstract fields.
- The square is the elementwise equation, for every `b : Γ(Z, U)`,
  `Y.germToFunctionField (p ⁻¹ᵁ U) (p.app U b) =
  p.functionFieldMap hη (Z.germToFunctionField U b)`.
- For each nested nonempty affine `W`, the final universally quantified clause
  takes `hWU : W ≤ U` and states the two restriction identities. Downstairs it
  uses `Z.presheaf.map (homOfLE hWU).op`; upstairs it uses
  `Y.presheaf.map (homOfLE (p.preimage_mono hWU)).op`. Both equations identify
  the restricted section's generic germ with its original generic germ.
  The upstairs nonemptiness proof is universally quantified here: it is already
  guaranteed for every such `W` by the earlier affine-open clause, and all its
  choices are propositionally equal. It is not a new global hypothesis.
- All affine extensions have the same degree `d`: throughout the quantification
  over `U` and `W`, the square uses the one actual map `p.functionFieldMap hη`
  and the one outer `d`. The fraction-ring clauses and the square identify each
  induced affine fraction-field extension with that map: on `ρ(b)/ρ(c)` it must
  be `σ(p#b)/σ(p#c)`. Every element has this form. Thus there is no independently
  varying extension or degree hidden by the affine presentations. This renders
  the node's final “Thus” conclusion by its single common extension, without
  introducing a duplicate fraction-field construction.

Dependencies and declaration interfaces read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`,
  its `app` and `stalkMap` interfaces, and `IsAffineOpen` through the finite-map
  imports. The definition of a scheme and its local affine presentations was read.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`, whose fields are
  affineness and `(p.app U).hom.Finite` on affine opens; its integral-morphism
  dependency is imported by that module.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`, meaning
  surjectivity of the underlying point map.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, with nonempty carrier
  and domain sections on nonempty opens.
- `Mathlib.Topology.Sober`: `genericPoint`, `genericPoint_spec`, `IsGenericPoint`.
- `Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.functionField`,
  `Scheme.germToFunctionField`, the field, germ-algebra and stalk-domain
  instances, `germ_injective_of_isIntegral`, and
  `functionField_isFractionRing_of_isAffineOpen`. These also supply the
  recorded Mathlib proof dependencies on affine fractions and stalk embeddings.
- `WeilConjectures.AlgebraicGeometry.FunctionField`:
  `Scheme.functionFieldOfComponents`; its docstring expressly directs the
  arbitrary integral-scheme case of this dependency to Mathlib's generic stalk
  `Scheme.functionField`, as used here. The module is publicly imported.
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`:
  `Scheme.Hom.functionFieldMap`; its full signature requires only integral
  schemes and generic-point equality, not flatness or curve hypotheses.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, recorded for general module stalks.
  Its implementation reuses Mathlib stalks; here only the underlying ring
  stalks, germs, and structure-sheaf restrictions are needed.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`:
  `LocallyRingedSpace.Hom` and its canonical local stalk maps, inherited by
  `Scheme.Hom`; no replacement morphism or stalk construction is introduced.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `RingHom.toAlgebra`;
  `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, through `RingHom.Finite`;
  `Mathlib.LinearAlgebra.Dimension.Finrank`: `Module.finrank`;
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`.
- Proof-only imports: `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`
  supplies the recorded `Scheme.exists_germToFunctionField_eq` gluing theorem;
  `Mathlib.RingTheory.Algebraic.Integral` supplies the recorded finite-dimensional
  fraction-ring instance for finite torsion-free domain algebras. The complete
  six-step accepted proof plan is included in the theorem docstring.

Edge cases checked before writing: identity maps give degree one and ordinary
restriction identities. A finite extension of fields gives precisely its finite
field degree. Purely inseparable finite covers are allowed: there is no
separability hypothesis. The source need not be normal; a nonnormal integral
finite cover of a normal integral base is not excluded. There is no Noetherian,
finite-type-over-a-field, dimension, or flatness restriction. Both schemes are
nonempty by integrality, so their generic stalks are fields and the degree cannot
be zero. Empty affine opens are intentionally outside the node's quantified
clause. No finite affine cover or quasi-compactness of the whole base is assumed.
The universe `u` is explicitly bound and arbitrary; there are no independent
universes that could make a test-object condition vacuous. Every variable is
bound explicitly; there are no file-local notations, instances or helper copies.

Searches performed through the prescribed `msearch.py` wrapper:

- LeanFinder: “Finite surjective morphism of integral schemes induces a finite
  extension of function fields with normal affine base section rings” — eight
  hits, including `finite_appTop_of_universallyClosed`, finite/integral morphism
  and normalization facts. No complete statement matching this node.
- Loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.Scheme.functionField` —
  zero hits.
- Mathlib grep in `AlgebraicGeometry`:
  `functionField.*[Ff]inite|[Ff]inite.*functionField|isIntegrallyClosed.*[Ss]ection|[Ss]ection.*isIntegrallyClosed`
  — three hits in `Birational/RationalMap.lean`; none is this statement.
- LeanSearch: “Finite surjective morphism of integral schemes gives a finite
  extension of function fields and integrally closed affine base sections” —
  eight hits, the definitions of finite/surjective/integral morphisms and the
  theorem `Scheme.Hom.finite_app`, rather than the assembled statement.
- Direct `rg` with that conceptual pattern in `lean/WeilConjectures` and
  `lean/Sheaf` finds curve-specific and normalization statements and the
  existing normal-section theorem, not this full statement. A separate search
  for generic field-map names found `Scheme.Hom.functionFieldMap`; its exact
  definition and docstring were read and it is reused. No extra notion is needed.
- `grep -rn 'lem-sfb-finite-normal-cover-affine-field-data' lean/WeilConjectures`
  and the corresponding `rg` search in `lean/Sheaf` returned no declaration.
  Searches for `finite_normal_cover_affine_field_data` likewise returned none.

Validation: `scompile.py Q65 lem-sfb-finite-normal-cover-affine-field-data` on the
single delivered file succeeded in both sandbox and actual library module mode
(9.6 seconds and 6.0 seconds respectively), with no errors or unexpected warnings.
There is no disputed statement or unresolved node fault.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
