## Worker report

The module `Sheaf.AlgebraicGeometry.SemilinearNormalizationFiniteModel` states
`AlgebraicGeometry.Scheme.semilinear_normalization_finite_model`, with its only proof `sorry`.
It uses the upstream normalization, function field, and pullback constructions. There are no
new definitions, dependency repairs, or statement corrections. The node copy changes only `lean`.
The theorem docstring contains all six proof steps and their dependency names.

Hypothesis-by-hypothesis correspondence:

| Node hypothesis | Lean |
| --- | --- |
| A field k | `{k : Type u} [Field k]` |
| An integral k-scheme S | `(S : Scheme.{u}) [IsIntegral S] [S.Over (Spec (.of k))]` |
| Normality of S, with the stated local-ring meaning | `hS : ∀ s, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)` |
| Projectivity over k by a finite projective-space embedding | `[IsHProjective (S ↘ Spec (.of k))]` |
| Finite type over k | `[LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]` |
| A finite group H with actions on S and k | `[Group H] [Finite H]`, `aS : H →* Aut S`, `ak : H →* (k ≃+* k)` |
| Compatibility of those actions | `hbase`, a commuting square using `Spec.map` of `ak h⁻¹` |
| K = k(S) | `S.functionField`, without another carrier or extra identification |
| The prescribed finite separable extension M/K | `(M : Type u) [Field M] [Algebra S.functionField M] [FiniteDimensional S.functionField M] [Algebra.IsSeparable S.functionField M]` |
| A finite group J and surjective rho | `[Group J] [Finite J]`, `ρ : J →* H`, `hρ : Function.Surjective ρ` |
| A homomorphism sigma into field automorphisms | `σ : J →* (M ≃+* M)`; these are ring automorphisms, allowing movement of k |
| sigma restricts to the inverse-geometric-pullback left action | `hσ`: `σ j (algebraMap ... x) = algebraMap ... ((functionFieldAut (aS (ρ j)⁻¹)).hom x)` |
| W and a are the specified normalization and map | All conclusions use exactly `S.normalizationIn M` and `S.fromNormalizationIn M` |

Clause-by-clause correspondence:

| Node conclusion | Lean |
| --- | --- |
| W normal | First conjunction: every stalk is a domain and integrally closed |
| W integral | `IsIntegral (S.normalizationIn M)` (also available from the normalization construction to type its function field) |
| W projective over k | `IsHProjective (S.fromNormalizationIn M ≫ (S ↘ Spec (.of k)))` |
| W finite type over k | `LocallyOfFiniteType` and `QuasiCompact` of that composite |
| Its function field is canonically M | Existential `e : (S.normalizationIn M).functionField ≃+* M`, whose `Spec.map` composed with `fromSpecFunctionField` is the actual normalization lift from `Spec M` |
| a finite and surjective | `IsFinite (S.fromNormalizationIn M) ∧ Surjective (S.fromNormalizationIn M)` |
| Dense open V with etale restriction | `∃ V : S.Opens, Dense (V : Set S) ∧ Etale (S.fromNormalizationIn M ∣_ V)` |
| Every nonempty affine U has integral-closure inverse image | For every `U`, `[Nonempty U]`, `hU : IsAffineOpen U`, an isomorphism `(a ⁻¹ᵁ U).toScheme ≅ Spec (.of (integralClosure Γ(S,U) M))`, commuting with the ring algebra map and `hU.fromSpec` |
| The generic fibre is Spec M | `∃ e : Spec (.of M) ≅ pullback a S.fromSpecFunctionField`, with first projection equal to the normalization lift and second equal to `Spec.map (algebraMap S.functionField M)` |
| A J-action on W | Existential `aW : J →* Aut (S.normalizationIn M)`; its identity and multiplication laws are bundled |
| Generic geometric action is Spec(sigma inverse) | `Spec.map` of `(σ j).symm.toRingHom`, composed with the canonical normalization lift, equals the lift followed by `(aW j).hom` |
| a composed with j equals rho(j) composed with a | `(aW j).hom ≫ a = a ≫ (aS (ρ j)).hom` |
| The action on k is the original one composed with rho | The structure-map square uses `Spec.map (ak (ρ j)⁻¹).toRingHom` |
| The induced left field action is exactly sigma | `e ((functionFieldAut (aW j⁻¹)).hom x) = σ j (e x)` |

In the affine clause the quantified `Algebra Γ(S,U) M` and scalar tower express precisely the
composite of the canonical germ algebra `Γ(S,U) → S.functionField` with the given extension.
This does not assume extra algebra data or permit a different embedding: the scalar-tower
identity determines it uniquely, and this composite always supplies such a structure.
CategoryTheory.Aut multiplication is composition as a left action; Spec reverses ring maps.
Thus the base squares use `ak h⁻¹`, the generic geometric map uses `sigma j` inverse, and the
left field-action equality uses `aW j⁻¹`, as required. No action is required to be faithful.

Dependency declarations read and used:

- `def-fin-normalization-extension`: `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`,
  `Scheme.normalizationIn`, `Scheme.fromNormalizationIn`, and `fromSpecOfAlgebraFunctionField`.
  The definitions are the existing relative normalization of the generic-point field map.
- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective`, whose field is a finite-coordinate projective embedding.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `.QuasiCompact`, `LocallyOfFiniteType` and `QuasiCompact`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `IsFinite`.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective` (underlying map surjectivity).
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `Etale`.
- `def-sc-function-field`: `WeilConjectures.AlgebraicGeometry.FunctionField` explicitly directs
  the integral-scheme clause to Mathlib `Scheme.functionField`, the stalk at its generic point.
  The component-product declaration is intentionally not substituted for this integral clause.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra` and `algebraMap`.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable`, whose docstring includes algebraicity.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `pullback`, `pullback.fst`, and `pullback.snd`.
- Existing helper `WeilConjectures.AlgebraicGeometry.StalkAut`, `Scheme.functionFieldAut`:
  it is the generic stalk pullback, with its Spec compatibility read in the source.

Statement imports are public. Available proof dependencies are plain imports:
`Sheaf.AlgebraicGeometry.FiniteOverProjective`,
`Sheaf.AlgebraicGeometry.NormalizationExtendsCover`,
`WeilConjectures.AlgebraicGeometry.SpreadFiniteSeparableExtension`,
`Mathlib.RingTheory.Localization.Integral`, and `.BaseChange`.
The affine fraction-field and affine fibre-product proof dependencies are already publicly
available through the normalization module's imports. The finite-normalization functoriality
proof node has no recorded Lean module, so no fictional import is added.

Edge cases checked before writing:

- M = K: normalization of normal S is S; all conclusions reduce to the given actions and
  identity generic fibre. No nontrivial extension or degree bound is imposed.
- Dimension zero and any characteristic: no dimension, smoothness, perfection, or
  characteristic restriction occurs.
- Nonfaithful H and J actions, nontrivial kernel of rho, and trivial groups: no injectivity
  assumption on any action is imposed; kernel elements can still act on M over K.
- A moving action on k: automorphisms are ring equivalences, not k-algebra equivalences;
  the inverse in the geometric Spec map accounts for contravariance.
- Empty affine opens are explicitly excluded by the node and `[Nonempty U]`; S itself
  is nonempty by integrality. Dense V is not required invariant, agreeing with proof step 4.
- Non-Galois separable extensions are allowed: sigma is only the prescribed action; no
  Galois or normal extension hypothesis is introduced. Inseparable extensions are excluded
  exactly by the node's separability hypothesis.
- Scheme, base field, and finite extension use a common arbitrary universe u, as the recorded
  normalization API does. Finite group universes v and w remain independent.

Searches actually run:

1. `msearch.py ... leanfinder`: “A finite separable extension of the function field of a normal
   projective scheme has a finite projective normalization with compatible semilinear finite
   group action and dense etale locus”. Eight hits, all relative-normalization constructions
   or their integral/dominant properties; none states this collection of clauses.
2. `msearch.py ... loogle 'AlgebraicGeometry.Scheme.normalizationIn'`: zero hits, with
   “unknown identifier” because the search service indexes Mathlib, not this upstream helper.
3. `msearch.py ... grep 'normalizationIn|fromNormalizationIn' AlgebraicGeometry`: zero
   Mathlib hits; these extension-specific names are upstream rather than Mathlib.
4. `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item ID and declaration name:
   no existing exact statement. Searches for normalizationIn/fromNormalizationIn found the
   upstream canonical construction and existing normalization consumers; none is this theorem.
5. `rg` for function-field automorphisms found and led to reading `StalkAut.lean`, so the
   statement uses its existing pullback rather than defining another field action.

Source checks: read local Stacks `morphisms.tex`, normalization definition and universal
property (035H/035I), and Nagata normalization finiteness (0AVK); read the latest blueprint
unit and its direct-image statement. The inherited agent proof's six steps were preserved in
full in the theorem docstring. No source correction is needed and no statement is disputed.

Validation: `scompile.py Q06 lem-sfb-semilinear-normalization-finite-model` compiled the module
in sandbox and library modes, respectively 3.0 s and 2.4 s, with no errors or warnings.

## Second reading by Q06

The dispatcher explicitly requires this worker to deliver directly and forbids other agents;
this section records the author's second pass, not an independent agent review. The maintainer
performs the independent review. I reread the node alongside the completed source and checked
all rows of the two correspondence tables. Particular checks were the three inverse conventions,
all affine and generic-fibre maps, normal local domains, finite type including quasi-compactness,
and the absence of faithful-action, Galois, invariant-open, or characteristic hypotheses.
No mismatch or statement change was found. All binders and universes are explicit, and the
only theorem proof is `sorry`; definitions are reused, with no new postponed data.
