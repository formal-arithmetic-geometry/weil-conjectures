## Worker report

The module `Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve` states
`AlgebraicGeometry.exists_stein_smooth_generic_curve`. Its sole proof is `sorry`.
It introduces no definitions, helper theorems, arbitrary algebra structures or choices.
The original natural-language statement is unchanged. No statement fault or
STATEMENT-DISPUTED flag remains.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Schemes C and S | `{C S : Scheme.{u}}`, with explicit universe `u` |
| Integral C and S | `[IsIntegral C] [IsIntegral S]` |
| Noetherian C and S | `[IsNoetherian C] [IsNoetherian S]` |
| Excellent C and S | `hC : Orgogozo.IsExcellentScheme C`, `hS : Orgogozo.IsExcellentScheme S` |
| Proper dominant f:C→S | `(f : C ⟶ S) [IsProper f] [IsDominant f]` |
| η generic in S | `(η : S) (hη : IsGenericPoint η Set.univ)` |
| Smooth irreducible generic fibre | `[Smooth (f.fiberToSpecResidueField η)] [IrreducibleSpace (f.fiber η)]` |
| Generic curve dimension 1 | `hdim : topologicalKrullDim (f.fiber η) = 1` |
| Factorization through a scheme S₀ | `∃ (S₀ : Scheme.{u}) (q : S₀ ⟶ S) (g : C ⟶ S₀), ... g ≫ q = f` |
| S₀ integral, Noetherian, excellent | `IsIntegral S₀ ∧ IsNoetherian S₀ ∧ Orgogozo.IsExcellentScheme S₀` |
| q finite, dominant, bundle-projective | `IsFinite q ∧ IsDominant q ∧ IsProjectiveBundle q` |
| g proper with geometrically connected fibres | `IsProper g ∧ GeometricallyConnected g` |
| S₀ = relative Spec of f_*O_C, with the specified affine charts | `∀ (U : S.Opens), IsAffineOpen U → IsIso (g.app (q ⁻¹ᵁ U))`, together with `IsFinite q` and `g ≫ q = f` |
| η₀ generic in S₀ | `∀ (η₀ : S₀), IsGenericPoint η₀ Set.univ → ...` |
| Generic residue field over κ(η) | `q η₀ = η`, with the canonical residue map `q.residueFieldMap η₀` |
| Finite extension | `(q.residueFieldMap η₀).hom.Finite` |
| Separable extension, in the recorded general sense | `@Algebra.IsSeparableExtension (S.residueField (q η₀)) (S₀.residueField η₀) _ _ (q.residueFieldMap η₀).hom.toAlgebra` |
| New generic curve smooth, geometrically integral, dimension 1 | `Smooth (g.fiberToSpecResidueField η₀) ∧ GeometricallyIntegral (g.fiberToSpecResidueField η₀) ∧ topologicalKrullDim (g.fiber η₀) = 1` |
| κ(η₀) = H⁰(C_η,O) canonically | The final `∃ t`, with `t ≫ S₀.fromSpecResidueField η₀ = f.fiberι η ≫ g` and `IsIso ((Scheme.ΓSpecIso (S₀.residueField η₀)).inv ≫ t.appTop)` |

The affine clause is the canonical relative-spectrum characterization, not just a
noncanonical isomorphism between rings. For an affine U of S, finiteness of q makes
`q ⁻¹ᵁ U` affine, and `g.app (q ⁻¹ᵁ U)` is the canonical O_S-algebra map
Γ(S₀,q⁻¹U) → Γ(C,g⁻¹q⁻¹U). The factorization identifies its target with
Γ(C,f⁻¹U). Its inverse followed by Spec, composed with `toSpecΓ` of q⁻¹U, is the
canonical isomorphism q⁻¹U ≅ Spec Γ(C,f⁻¹U). These maps respect restrictions because
`g.app` is a sheaf morphism. Thus they identify q with Spec_S(f_*O_C), including its
O_S-algebra structure. This uses the recorded affine-morphism/relative-Spec interface,
without introducing another construction or an arbitrary equivalence.

The final t is likewise constrained: the residue-field inclusion is a monomorphism
(`IsPreimmersion` in Mathlib), so its displayed composition fixes t uniquely.
The map from κ(η₀) to H⁰(C_η,O) is exactly ΓSpecIso.inv followed by t.appTop; its
being an isomorphism expresses the canonical field identification without equating
unrelated Lean carrier types. The field extension uses the actual residue-field map
of q. The equality q η₀ = η identifies its base field with κ(η); no independent
Algebra instance is hypothesized. Compatibility over κ(η) follows by composing the
displayed equation with q and using the two fibre squares. The new generic fibre is
`g.fiber η₀`, not the generally larger field base change of `f.fiber η`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, used by the recorded
  scheme class `AlgebraicGeometry.IsNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`. The residue fields and their canonical inclusions/maps
  are from `Mathlib.AlgebraicGeometry.ResidueField`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`.
- `Sheaf.Paper.OrgogozoInductionData`: `AlgebraicGeometry.Orgogozo.IsExcellentScheme`,
  whose entire definition is `∀ U : S.affineOpens, IsExcellent Γ(S,U)`.
  Its existing node `def-trf-orgogozo-induction-data` is added to stmt_deps, so the
  existing scheme predicate is reused rather than copied privately.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `AlgebraicGeometry.IsProjectiveBundle`;
  its canonical symmetric-graded relative-Proj construction was also read.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected` and `.Integral`:
  `AlgebraicGeometry.GeometricallyConnected` and `GeometricallyIntegral`, as given in
  `def-pc-geometrically-irreducible.mathlib_match` (that node needs no lean repair).
- `WeilConjectures.FieldTheory.SeparableExtension`: `Algebra.IsSeparableExtension`.
  The current published source was read through `scompile.py --source`, and matches
  the full general definition in the dependency node.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, from def-sc-generic-point.mathlib_match.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`. Its existing Mathlib node
  `def-kun-topological-krull-dimension` is added to stmt_deps.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `IsDominant` (dense range).
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Scheme.ΓSpecIso`.

All currently recorded proof-dependency modules are imported without `public` unless
already required publicly by the signature, including the recorded affine Stein,
coherent-pushforward, global-sections, flat fraction-field-base-change, regularity,
excellence and etale inputs. Mathlib-match proof inputs are imported from Etale,
FlatMono, Separated, Noetherian and QuasiCompact. The proof-only node
`lem-trf-finite-projective-bundle` has no Lean declaration on the read base, so there
is no module yet to import for that future proof input. Its conclusion is stated here
using its existing defining predicate; no extra hypothesis replaces it. No import
cycle was introduced. The docstring records all five source-based proof steps.

Edge cases checked:

- Integral schemes and an irreducible generic curve are nonempty. No extra
  nonemptiness or surjectivity assumption was imposed; geometrically connected g
  itself includes nonempty geometric fibres.
- A base which is the spectrum of a field is allowed. A proper smooth curve with
  nontrivial finite separable constants gets that constants field as its Stein base;
  no geometric irreducibility is incorrectly required over the original field.
- Arbitrary characteristic is allowed. Smoothness rules out inseparable constants
  by geometric reducedness, rather than by a characteristic-zero hypothesis.
- No normality, regularity, flatness of f, or geometrically integral original
  generic fibre is assumed.
- The empty affine open is included in the canonical section condition; both
  section rings are the zero ring and its map is an isomorphism.
- Dimension is the recorded topological Krull dimension, with value exactly one;
  empty or zero-dimensional generic fibres are excluded exactly by the node.
- The universe u is explicit and arbitrary. No bound on the dimensions of C or S
  and no separate small universe for field extensions was introduced; the Mathlib
  geometric predicates provide the recorded field-base-change quantifiers.

Searches made with msearch.py (and direct source grep), with returned types inspected:

- LeanFinder: `proper smooth generic curve Stein factorization finite base geometrically connected fibres`.
  Eight hits, including Smooth, IsFinite, fiberι and IsIntegralHom; none is the
  stated global factorization and smooth generic-curve theorem.
- LeanSearch: `Stein factorization proper smooth integral generic curve geometrically integral finite separable global sections`.
  Eight hits, including `finite_appTop_of_universallyClosed` and generic-property
  lemmas; none includes the finite excellent Stein base and generic conclusions.
- Loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.IsSmooth, AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsIntegralHom, CategoryTheory.Functor`.
  No hits (the external index does not recognize the old IsSmooth spelling).
- Loogle: `"stein"`. Twelve unrelated Schroeder--Bernstein and Eisenstein hits.
- msearch grep: `steinFactor|stein_factor|Stein`, restricted to AlgebraicGeometry.
  No Mathlib match.
- `rg -n 'steinFactor|stein_factor|SteinFactor|exists_stein_smooth_generic_curve'`
  on the upstream WeilConjectures tree and project lean/Sheaf: upstream has only
  the affine `Scheme.Hom.steinFactorizationBase` and its finiteness theorem;
  side modules have affine Stein, fibre and henselian results. None states this
  global generic-curve result.
- Direct source grep of `lem-trf-stein-smooth-generic-curve`: no upstream declaration.
- Direct searches for `IsExcellent`, `IsExcellentScheme`, `IsProjectiveBundle`,
  `GeometricallyConnected`, `IsSeparableExtension`, generic-point, fibre and curve
  interfaces found the dependency declarations listed above.

Sources checked: local Stacks more-morphisms.tex, theorem-stein-factorization-Noetherian
(Tag 03H0), and varieties.tex, lemma-proper-geometrically-reduced-global-sections
(Tag 0BUG) and lemma-baby-stein (Tag 0FD1), against the node's source and all five
proof steps. These give the actual canonical relative spectrum, finite constants,
separability and geometric connectedness. No source-based statement correction is
needed.

Validation: scompile.py compiled the single module cleanly in both its sandbox and
library-name checks. The initial reversed-Spec expression was repaired to the
canonical section-isomorphism condition before recording the final signature.
The required delivery dry run and final delivery are performed after this report.

## Second reading by Q141

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
