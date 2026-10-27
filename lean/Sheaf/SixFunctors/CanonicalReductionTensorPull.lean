/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge

/-! # Pullback and tensor under ordinary coefficient reduction

Source: blueprint fix-prop-coherence, individual coefficient comparisons; Stacks 07A4.
-/

@[expose] public section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralSystemRealization

attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleCanonicalTensorComparison

/-- The normalized reduction/pullback comparison preserves the ordinary tensor map.
Source: blueprint sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md,
"tensor reassociation, evaluation, and adjunction units and counits", and
lem-fix-operation-reduction; Stacks 07A4, 07A6 and 0941.
(blueprint: lem-sf-canonical-reduction-tensor-pull).

Proof: resolve K and H by flat-term K-flat complexes. Use the total tensor of these
representatives for their tensor product. The tensorRepresentative field identifies
this representative with the tensor in the coefficient calculus, and the model field
of the realization identifies reductionPull with the ordinary quotient/pullback mate.
At the ordinary level that mate is determined by its adjoint limit comparison:
postcomposing with each limit projection is the specified coefficient projection.
Its inverse-image transpose is thus the usual scalar-association map. In each total
tensor summand both composites in the displayed equation send b tensor (x tensor y)
to (b tensor x) tensor (1 tensor y). The defining pure-tensor formulas for the ringed
and system pullback/tensor maps, and the reductionTensor normalization, identify the
four sides with these maps. Pure tensors generate the module tensor product; tensor
sheafification and inverse image preserve this identity. The formula respects the
signed total differential and every adjacent quotient transition, so it is an equality
of whole strict system complexes. Localize it. The representative normalizations
cancel the K-flat factorization isomorphisms and give the equation on the chosen
resolutions. Naturality transports it along their resolving isomorphisms to K and H.
Zero inputs and identity scheme maps use exactly the same summand calculation. -/
theorem canonicalReductionTensorPull
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (m : RealizationModel l E o) (d : RingedModels l E)
    {U V : Scheme.{u}} (f : U ⟶ V) (K H : Integral l E V) :
    let μ (W : Scheme.{u}) :
        (d.tensor W).ordinary.tensor ⋙ (calculus l E W).reduction ⟶
          (calculus l E W).reduction.prod (calculus l E W).reduction ⋙
            (calculus l E W).systemClosed.tensor :=
      Functor.whiskerRight (eqToIso (d.tensorClosed W)).hom (calculus l E W).reduction ≫
        (calculus l E W).reductionTensor.hom
    (m.reductionPull f).hom.app ((d.tensor V).ordinary.tensor.obj (K, H)) ≫
        (pull l E f).map ((μ V).app (K, H)) ≫
        (pullbackTensorSystemComparison l E f).hom.app
          ((calculus l E V).reduction.obj K, (calculus l E V).reduction.obj H) =
      (calculus l E U).reduction.map ((ringedTensorPull l E d f).hom.app (K, H)) ≫
        (μ U).app ((ringedPull l E f).obj K, (ringedPull l E f).obj H) ≫
        (calculus l E U).systemClosed.tensor.map
          (Prod.mkHom ((m.reductionPull f).hom.app K) ((m.reductionPull f).hom.app H)) := by
  sorry

end WeilConjectures.IntegralSystemRealization
