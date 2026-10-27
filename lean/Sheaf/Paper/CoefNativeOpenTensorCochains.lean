/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefOpenTensorEvaluationData
public import Sheaf.SixFunctors.OpenTensorCochainData

/-! # Ordinary native open tensor representatives

Source: Stacks 0E8I, 0G7E and Homology 012Z
(blueprint: lem-coef-native-open-tensor-cochains).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Sequence-site specialization of ordinary open tensor data.
Source: Stacks 0E8I (blueprint: lem-coef-native-open-tensor-cochains). -/
abbrev SystemOpenCochains {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  letI := ProEtale.VaryingRing.extensionAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.extensionLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.extensionColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  @OpenTensorCochainData.{u + 1, u, u} (ℕ × Z.ProEt) _
    (ProEtale.VaryingRing.sequenceSiteSmall Z)
    (coefficientSequenceTopology (ProEt.topology Z)) (coefficientSequenceCommRingSheaf.{u, u} l E Z)
    (ℕ × X.ProEt) _ (ProEtale.VaryingRing.sequenceSiteSmall X)
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf.{u, u} l E X)
    (ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.extensionAdditive (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.pullAdditive (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.baseChange j) (pullSection l E j)

/-- Finite-coefficient specialization of ordinary open tensor data.
Source: Stacks 0E8I (blueprint: lem-coef-native-open-tensor-cochains). -/
abbrev FiniteOpenCochains {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (n : ℕ) :=
  letI := ProEtale.StrictTower.moduleJ_additive (compactSupportSystemLevel l E n) j
  letI := ProEtale.StrictTower.moduleJ_finiteLimits (compactSupportSystemLevel l E n) j
  letI := ProEtale.StrictTower.moduleJ_finiteColimits (compactSupportSystemLevel l E n) j
  letI := proEtaleRingModulePullback_additive j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  letI := proEtaleRingModulePullback_preservesFiniteLimits j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  letI := proEtaleRingModulePullback_preservesFiniteColimits j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  @OpenTensorCochainData.{u + 1, u, u} Z.ProEt _
    (ProEtale.VaryingRing.siteSmall Z) (ProEt.topology Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    X.ProEt _ (ProEtale.VaryingRing.siteSmall X) (ProEt.topology X)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j)
    (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) j)
    _ _
    (ProEtale.StrictTower.moduleJAdj (compactSupportSystemLevel l E n) j)
    (proEtaleBaseChange j) (finitePullSection l E j n)

/-- Native restriction and projection data before derived localization.
Source: Stacks sites-modules.tex, lemma-j-shriek-and-tensor (0E8I),
sites-cohomology.tex, lemma-pullback-K-flat (0G7E), and Homology 012Z
(blueprint: lem-coef-native-open-tensor-cochains).

Proof: identify the open pro-etale site with localization of the ambient site,
and make the same identification after product with the coefficient index.
The constant-section ring maps identify the open ring with the restricted ring;
these identifications commute with every quotient transition. Uniqueness of
adjoints identifies localized extension and restriction with the fixed native
functors and identifies their units. The open object is subterminal, so its
adjunction unit is invertible. Restriction of sheafification of sectionwise
tensor yields pullTensor, its pure-section formula and naturality. Restriction
preserves flat sheaves and K-flat complexes by 0G7E, giving pullFlat and pullKFlat.
Take right to be the fixed module direct image and pullAdjunction its native
adjunction. The inverse of the ordinary projection is the adjoint of unit tensor
identity followed by pullTensor inverse. The ringed-slice projection formula
0E8I makes this map invertible: its target is an extension object, and on the
open it is the specified pure tensor identity. Naturality follows from naturality
of the unit and of restriction tensor. Totalize this natural comparison using
coproduct preservation by the left adjoint extension. On each bidegree its map
is the ordinary comparison followed by the target coproduct insertion. Its
naturality for each differential makes it commute with d tensor 1 plus
(-1)^a times 1 tensor d. The same equations give chainNaturality. Apply this
construction to the sequence site itself, retaining every horizontal map, and
to each finite coefficient ring. The empty open, zero rings, n=0 (the first
positive quotient), and unbounded complexes require no exceptions. -/
theorem nativeOpenTensor_cochains_exists {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] :
    ∃ (D : SystemOpenCochains l E j) (Dn : ∀ n : ℕ, FiniteOpenCochains l E j n), True := by
  sorry

end WeilConjectures.CoefSupportOpenTensor
