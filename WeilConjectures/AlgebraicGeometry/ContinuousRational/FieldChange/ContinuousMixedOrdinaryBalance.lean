/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousAmbientMixedCoherence

/-! # The mixed balancing cube before completion

Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tag 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational
variable (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]

/-- Flatten integral scalar extension and then insert the rational coefficient factor.
This is a specified pair of derived tensor associators, independent of the realization.
Source: BS 6.8.14--6.8.15; Stacks 0D6D
(blueprint: lem-per-continuous-mixed-ordinary-balance). -/
def FieldChange.integralBalance (i : E →ₐ[ℚ_[l]] F) (X : Base.{u} l)
    (aE : At l E X) (aF : At l F X) (b : FieldChange l E F i X aE aF)
    (K : PbcCompletedDerived X.scheme (pbcIntegralDatum l E)) :
    (pbcDerivedExtend (aF.integralIso.hom ≫ aF.inclusion)).obj
        ((pbcEmbeddingAmbientTensor l E F i X.scheme).obj K) ≅
      (pbcDerivedExtend b.coefficient).obj
        ((pbcDerivedExtend (aE.integralIso.hom ≫ aE.inclusion)).obj K) :=
  pbcReductionNormalization (pbcScalarCoefficientMap l E F i X.scheme)
      (aF.integralIso.hom ≫ aF.inclusion)
      (aE.integralIso.hom ≫ aE.inclusion ≫ b.coefficient) b.square K ≪≫
    (pbcReductionNormalization (aE.integralIso.hom ≫ aE.inclusion) b.coefficient
      (aE.integralIso.hom ≫ aE.inclusion ≫ b.coefficient) rfl K).symm

/-- The derived mixed cube for ordinary pullback and integral-to-rational extension.
There is no completion unit, constructibility condition, raw rationalization, or
realization functor in this equation, and K is any ambient integral derived object.
Source: BS Remark 6.8.15; Stacks Tag 0D6D
(blueprint: lem-per-continuous-mixed-ordinary-balance).

Proof: compute all functors on a common flat-term K-flat resolution. The two
FieldChange integralBalance maps flatten the two coefficient extensions and insert
the rational factor. The Along balance maps, the integral scalar/pullback map,
and the AmbientMixed map are specified on pulled tensor generators. Both paths
send a scalar times an integral scalar times a pulled generator to the product
of their coefficient images times that generator. The two coefficient squares
and AmbientMixed.coefficient identify those images. Tensor balancing and the
universal property of sheafification give equality on ordinary modules; applying
it termwise gives equality on complexes. The normalized computation counits of
Along and AmbientMixed and the derived tensor associator identify these chain
maps with the displayed derived maps. Their counits are invertible on the common
resolving class, so the equality descends to every derived object. -/
theorem continuousMixedOrdinaryBalance (i : E →ₐ[ℚ_[l]] F)
    {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (aXE : At l E X) (aYE : At l E Y) (aXF : At l F X) (aYF : At l F Y)
    (agE : Along l E g aXE aYE) (agF : Along l F g aXF aYF)
    (bX : FieldChange l E F i X aXE aXF) (bY : FieldChange l E F i Y aYE aYF)
    (m : AmbientMixed l E F i g aXE aYE aXF aYF agE agF bX bY)
    (K : PbcCompletedDerived Y.scheme (pbcIntegralDatum l E)) :
    (derivedPull g agF.coefficient).map
        (bY.integralBalance l E F i Y aYE aYF K).hom ≫
        m.ambient.hom.app ((pbcDerivedExtend (aYE.integralIso.hom ≫ aYE.inclusion)).obj K) ≫
        (pbcDerivedExtend bX.coefficient).map (agE.ambient.hom.app K) =
      agF.ambient.hom.app ((pbcEmbeddingAmbientTensor l E F i Y.scheme).obj K) ≫
        (pbcDerivedExtend (aXF.integralIso.hom ≫ aXF.inclusion)).map
          ((pbcScalarOrdinaryPullIso l E F i g).hom.app K) ≫
        (bX.integralBalance l E F i X aXE aXF
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K)).hom := by sorry

end AlgebraicGeometry.Scheme.ContinuousRational
