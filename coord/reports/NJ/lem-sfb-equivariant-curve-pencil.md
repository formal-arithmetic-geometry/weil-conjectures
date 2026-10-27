## Worker report

The delivery states `AlgebraicGeometry.exists_equivariant_curve_pencil` in
`Sheaf.AlgebraicGeometry.EquivariantCurvePencil`. Its only theorem has proof `sorry`.
There are no definitions, helper theorems, new nodes, dependency repairs or statement
corrections. The item node changes only in `lean`; all its other fields are preserved.

The preceding worker's BLOCKED diagnosis confused a stage-1 landing with a stage-2
statement. The current item is split and independently reviewed by NE, but has no `lean`
record and no existing theorem. Its stage-1 review therefore does not supersede this
stage-2 task. The preserved sandbox contained only dispatcher brief markers.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| Field k | `(k : Type u) [Field k]` |
| Finite-type k-scheme X | `(X : Scheme.{u}) (p : X ⟶ Spec (.of k))`; finite type follows from `[IsProper p]`, whose parents give `LocallyOfFiniteType p` and, through `UniversallyClosed`, `QuasiCompact p` |
| Normal X: every local ring integrally closed domain | `hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)` |
| Proper X | `[IsProper p]` |
| Geometrically integral X | `[GeometricallyIntegral p]`; `[IsIntegral X]` explicitly supplies the integral scheme structure needed to name its function field, already implied over a field |
| Dimension d ≥ 2 | `(d : ℕ) (hd : 2 ≤ d) (hdim : topologicalKrullDim X = (d : WithBot ℕ∞))` |
| Finite group H | `(H : Type v) [Group H] [Finite H]`; group and scheme universes are independent |
| Action on X | `α : H →* Aut X` |
| Action on k | `β : H →* (k ≃+* k)` |
| Compatibility with p | `hsemilinear : ∀ h, (α h).hom ≫ p = p ≫ Spec.map (CommRingCat.ofHom (β h⁻¹).toRingHom)` |
| No faithfulness required | No injectivity hypothesis on either α or β |
| Schemes X' and Y over k | Existential `X' Y`, structure morphisms `p'` and `q`, and `IsIntegral` witnesses |
| Normal X' and Y | The two pointwise `IsDomain ∧ IsIntegrallyClosed` conjuncts |
| Proper geometrically integral finite-type X' and Y | `IsProper p' ∧ GeometricallyIntegral p'` and `IsProper q ∧ GeometricallyIntegral q`; finite type is again included in properness |
| Compatible H-actions on X' and Y | Existential monoid homomorphisms `α'` and `γ`, and their compatibility equations with p', q and the same β |
| Morphisms π : X' → X and g : X' → Y over k | Existential π and g with `π ≫ p = p'` and `g ≫ q = p'` |
| H-equivariance of π and g | `(α' h).hom ≫ π = π ≫ (α h).hom` and `(α' h).hom ≫ g = g ≫ (γ h).hom` for every h |
| H-projective surjective π | `IsHProjective π ∧ Surjective π` |
| π is an isomorphism over a dense open of X | `∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (π ∣_ U)` |
| π identifies the function fields | `∃ hη : π (genericPoint X') = genericPoint X, Function.Bijective (X.presheaf.stalkSpecializes (specializes_of_eq hη) ≫ π.stalkMap (genericPoint X') : X.functionField ⟶ X'.functionField)`; the transport is the canonical stalk identification along the displayed generic-point equality, followed by π's actual pullback on stalks |
| H-projective dominant g | `IsHProjective g ∧ IsDominant g` |
| Projective Y over k | `IsHProjective q`, the exact blueprint convention rather than a different projective-bundle convention |
| dim Y = d−1 | `topologicalKrullDim Y = ((d - 1 : ℕ) : WithBot ℕ∞)` |
| Geometrically integral generic curve fibre | `GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint Y))` and `topologicalKrullDim (g.fiber (genericPoint Y)) = (1 : WithBot ℕ∞)`; finite type over the residue field follows by base change of the H-projective g |
| No smoothness assertion | There is no `Smooth` conclusion or hypothesis |

`Spec` reverses arrows, so inversion in the field action is essential for the action
convention and agrees with the landed consumer
`exists_equivariant_marked_plurinodal_field_alteration`. For a ring action β, the associated
left scheme action is h ↦ Spec(β(h⁻¹)). Thus the compatibility equations allow precisely
the compatible field/scheme actions of the informal node. No map is chosen arbitrarily:
the function-field map is the structural pullback on generic stalks.

Statement dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`; this includes locally finite type and quasi-compactness.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, together with `QuasiCompact`; both are supplied
  by properness, so separate redundant finite-type hypotheses are unnecessary.
- `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Integral`,
  `AlgebraicGeometry.GeometricallyIntegral`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim` with codomain `WithBot ℕ∞`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective`, not a private redefinition.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`; this is a proof dependency, not a requirement that either
  pencil morphism be finite. Its recorded module is publicly imported.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective`, publicly available through the projectivity imports.
- `def-sc-function-field`: `WeilConjectures.AlgebraicGeometry.FunctionField`, whose
  docstring explicitly delegates arbitrary integral schemes to Mathlib's
  `Scheme.functionField`, the stalk at `genericPoint`. These are higher-dimensional
  integral schemes, so the component-product definition for nonintegral curves is not
  the applicable clause of this dependency.

The other public imports expose Mathlib's canonical scheme-theoretic fibres and
`IsIntegrallyClosed`. Every currently recorded proof-dependency module is imported
without `public` unless already a public statement dependency. Invariant separating
parameters and normal Stein constant fields have no Lean statements yet and are therefore
not imported. They are only proof dependencies and are not needed to state this theorem.
The theorem docstring reproduces all sixteen DAG proof steps and their named uses.

Edge cases checked before writing:

- The trivial H and actions with kernels are included; no freeness, faithful action,
  effective action or invertibility of |H| in k is imposed.
- All characteristics and imperfect fields are allowed. Geometric integrality is used
  without replacing the generic fibre by a smooth one.
- `d = 2` yields a one-dimensional projective base and one-dimensional generic fibre.
  `d = 0` and `d = 1` are exactly the cases excluded by the node's `d ≥ 2`, so natural
  subtraction in `d - 1` loses no case.
- The empty scheme is excluded by the node's geometric integrality; explicit integral
  instances impose no extra condition. Properness supplies finite type, rather than
  restricting to projective X, which the node does not assume.
- Dense open means dense in X, and the isomorphism is the actual restriction of π over
  that open, not an unrelated abstract birational equivalence. The generic-point equality
  and bijective stalk pullback identify the actual function fields.
- Both the generic fibre and its base are the canonical Mathlib schemes. Since Y is
  integral, `genericPoint Y` is its unique generic point.
- Scheme and field universes are u; the finite group may live in any universe v.

Searches made with the prescribed tools:

- `msearch.py ... leanfinder "An equivariant projective birational modification of a
  proper normal geometrically integral variety admits a projective pencil with
  geometrically integral generic curve fibre"`: eight hits about Proj properness,
  rational-map representatives and rational maps from function fields; no pencil theorem.
- `msearch.py ... leansearch "equivariant curve pencil birational proper projective
  scheme"`: eight hits about properness and rational maps; no equivariant pencil theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsHProjective,
  AlgebraicGeometry.Scheme.functionField, AlgebraicGeometry.IsNormal"`: no hits,
  `unknown identifier 'AlgebraicGeometry.IsHProjective'` (it belongs to upstream).
- `msearch.py ... grep "equivariant.*pencil|[Bb]irational|functionFieldMap"
  AlgebraicGeometry`: birational/rational-map framework matches only; none states this
  existence result.
- `rg -n 'equivariant.*pencil|[Bb]irational|functionFieldMap'` over both
  `lean/WeilConjectures` and `lean/Sheaf`: found canonical generic-stalk maps and existing
  group-free curve factorizations, but no equivariant projective pencil theorem. The
  group-free `GeometricallyIntegralCurveFactorization` does not include the prescribed
  group action or this projectivity conclusion.
- `grep -rn 'lem-sfb-equivariant-curve-pencil' lean/WeilConjectures`: no match.
- Additional `rg` for `→* Aut`, `genericPoint`, and `fiberToSpecResidueField` located the
  existing semilinear convention and the exact canonical fibre interface.

Source checked: the publisher PDF at
https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf was read online at Lemma 5.2,
printed pp. 612–613. It gives the equivariant projective modification, normal choice of X',
and normal Stein construction with geometrically integral generic fibre. The node's
explicit equivariant Chow preparation supplies its H-projective convention for arbitrary
proper X, as recorded by its reviewed proof. No source-based correction is needed.

Validation: the prescribed `scompile.py NJ lem-sfb-equivariant-curve-pencil` compiled the
file both as a sandbox module and at its delivery module name, each in 3.2 seconds, with
no errors or unexpected warnings. The final public-import header is checked again by
the dry run. All Lean lines are at most 100 characters; universes and variables are
explicitly bound. The only postponed proof is this node's named theorem.

## Second reading by NJ

This is a second sequential reading by the same worker; no additional agent was started,
as the dispatch brief prohibits that. The maintainer supplies the independent review.
I reopened the node and the complete signature and matched every clause in the table.
I checked in particular that H-projective is the published `IsHProjective`, that the
field action uses β(h⁻¹), that neither action is assumed faithful, and that both π and g
are over k and equivariant for the same actions. I checked the dense open lies in X, the
stalk transport has source `X.functionField`, the base dimension uses d−1, and the fibre
is the canonical fibre over `genericPoint Y` with dimension one and geometric integrality.
Normality is present for all three schemes. Finite type is implied by every stated
properness hypothesis/conclusion, so it is not missing. The finite-morphism dependency
is not incorrectly asserted of π or g. No mismatch or statement change was found.
