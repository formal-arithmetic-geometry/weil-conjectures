/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.AlgebraicGeometry.Limits

/-!
# A finite chart-pair fibre gives an étale quasi-compact residual relation

Source: Stacks Project, Decent Spaces, Tag 03JU (lemma-R-finite-above-x), first proof
paragraph and implication (2) to (3)
(blueprint: lem-sfb-chart-pair-finite-residual-relation).

The chart relation and the residual self-relation are specified by representing
pullback squares of Yoneda presheaves on schemes over the base.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finiteness of the chart relation above `(u,u)` implies that both projections of
`Spec κ(u) ×_X Spec κ(u)` are étale and quasi-compact. The residual spectrum has its
canonical structure map to the base, and each map to `X` is induced by the canonical
residue-field map followed by `a`. No surjectivity of the chart is assumed.
Source: Stacks Project, Decent Spaces, Tag 03JU (lemma-R-finite-above-x), first proof
paragraph and implication (2) to (3)
(blueprint: lem-sfb-chart-pair-finite-residual-relation).
Proof:
1. Set `T = Spec κ(u)` and `i = U.fromSpecResidueField u`. The map `i` is monic by
[lem-sfb-residue-field-point-monomorphism]. Representability of the diagonal of `X`
[def-trf-algebraic-space] represents `E = T ×_X T` by a scheme. The sheaf pullback
universal property [lem-trf-space-fibre-products-etale-covers] gives `E → R`.
Cancellation through `i` in both coordinates shows that this map is monic.
2. The field-valued criterion [def-weil-radicial-morphism] makes this monomorphism
universally injective, hence injective on points. Its image lies in the finite pair
fibre by the two projection identities, so the underlying set of `E` is finite.
3. For either projection, factor `E → T` through `D = T ×_X U` (or `U ×_X T`).
The map `D → T` is étale by the scheme-test definition [def-trf-algebraic-space]
applied to `a`; the map `E → D` is monic by cancellation through `i` and the
pullback universal property, as in step 1.
4. The étale fibre classification [lem-weil-pbc-etale-fibre-discrete-separable-points]
writes `D` as a coproduct of spectra of finite separable extensions of `κ(u)`.
By [lem-sfb-monomorphism-into-field-coproduct], `E → D` is the inclusion of a
subset of those components.
5. The component inclusions are open immersions [lem-weil-pbc-scheme-coproduct-family,
def-weil-open-immersion], so their union is an open immersion. Open immersions
are étale and composites of étale maps are étale
[lem-weil-pbc-etale-composition-cancellation]. This gives étaleness of both projections.
6. A finite space is quasi-compact: choose one member of an open cover for each
point. Thus `E` is quasi-compact [def-weil-pbc-quasi-compact-scheme]. The field
spectrum `T` has only the empty and full opens. Each inverse image of an affine
open is consequently empty or all of `E`, proving quasi-compactness of both maps. -/
theorem chart_pair_finite_residual_relation {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : Over S) (a : yoneda.obj U ⟶ X.obj.obj) (ha : IsEtale a) (u : U.left)
    (R : Over S) (p₁ p₂ : R ⟶ U)
    (hR : IsPullback (yoneda.map p₁) (yoneda.map p₂) a a)
    (hfinite : Set.Finite {r : R.left | p₁.left r = u ∧ p₂.left r = u}) :
    ∃ (E : Over S)
      (q₁ q₂ : E ⟶ Over.mk (U.left.fromSpecResidueField u ≫ U.hom)),
      IsPullback (yoneda.map q₁) (yoneda.map q₂)
        (yoneda.map (Over.homMk (U.left.fromSpecResidueField u) rfl) ≫ a)
        (yoneda.map (Over.homMk (U.left.fromSpecResidueField u) rfl) ≫ a) ∧
      (Etale q₁.left ∧ QuasiCompact q₁.left) ∧
      (Etale q₂.left ∧ QuasiCompact q₂.left) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
