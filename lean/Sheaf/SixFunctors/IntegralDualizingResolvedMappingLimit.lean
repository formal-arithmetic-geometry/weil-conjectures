/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower
public import Sheaf.SixFunctors.IntegralDualizingResolvedGlobalHom

/-! # Ordinary global Hom models for a resolved strict tower

Source: Stacks 0A95, 0A96 and 0941. This comparison concerns the mapping-tower side
only. It neither mentions the dualizing limit in module sheaves nor a DVR tower.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The same strict mapping tower on every source object, before constructibility.
Source: Stacks 0A95, 0941
(blueprint: lem-coef-integral-dualizing-resolved-mapping-limit). -/
def integralDualizingAmbientMappingTower
    (Z : DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E X)) :
    (DerivedCategory (scalarReductionSource l E X))ᵒᵖ ⥤ coefPairingDerived l E :=
  (coefHomDerivedConstant l E X).op ⋙
    (Functor.curry.obj (coefHomConstantInternalHom l E X)).flip.obj
      ((coefHomEquivalence l E X).inverse.mapDerivedCategory.obj Z) ⋙
        coefHomConstantDerivedSections l E X

/-- Global Hom into the evaluated complexes of a strict tower, followed by the
ordinary limit in complexes and localization. No derived limit occurs in this model.
Source: Stacks 08JA, 0941
(blueprint: lem-coef-integral-dualizing-resolved-mapping-limit). -/
def integralDualizingResolvedHomLimit
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) :
    (CochainComplex (scalarReductionSource l E X) ℤ)ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  integralDualizingResolvedHom l E X ⋙
    (Functor.whiskeringLeft _ _ _).obj I.asFunctor ⋙ lim ⋙ DerivedCategory.Q

/-- A resolved strict mapping tower is computed by the ordinary limiting complex
of global Hom cochains, naturally in its source complex.

Source: Stacks 0A95, 0A96, 08JA and 0941; blueprint prop-coef-integral-dualizing,
second displayed paragraph, and the resolved-tower model in its mapping-limit step.
(blueprint: lem-coef-integral-dualizing-resolved-mapping-limit).

Proof: the section-preserving constant-ring sequence equivalence carries I to a
K-injective sequence-site complex. For flat-term K-flat P, its constant sequence
is K-flat; the sequence internal-Hom and derived-sections comparison therefore
computes the strict signed complex Hom(P,I_n), with postcomposition transitions.
The slice restriction and reconstruction formulas for coefHomSequenceSections_iso
commute with precomposition, so this identification is natural in P. For arbitrary
P, precompose a K-flat resolution; K-injectivity of I and its evaluations makes
both global Hom complexes invert this quasi-isomorphism. Integral scalar actions
are unchanged by the section-preserving equivalence. Each term of I is an injective
tower, so consecutive transitions split. The same splittings act by postcomposition
on global Hom cochains. Thus 1-shift on their product is degreewise surjective:
start with x_0=0 and lift x_n-b_n recursively along each transition. Its kernel is
the ordinary limit. Exact products of integral modules identify its kernel-to-Roos
cone inclusion as a quasi-isomorphism, computing CoefTower.totalLimit. These
inclusions and all previous comparisons commute with precomposition. This proves
the stated natural isomorphism, including for zero inputs or zero transitions. -/
theorem integralDualizing_resolved_mappingLimit
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ)
    [I.IsKInjective] (hinj : ∀ q : ℤ, Injective (I.X q)) :
    Nonempty (DerivedCategory.Q.op ⋙
      integralDualizingAmbientMappingTower l E X (DerivedCategory.Q.obj I) ⋙
        CoefTower.totalLimit (integralDualizingCoefficients l E) ≅
      integralDualizingResolvedHomLimit l E X I) := by sorry

end WeilConjectures
