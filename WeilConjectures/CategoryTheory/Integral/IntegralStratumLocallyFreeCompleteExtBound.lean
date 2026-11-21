/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralStratumLocallyFreeExtBound
public import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductions
public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesFiniteCdIntegralExt
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution

import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsSupportWindow
import all WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductions
import all WeilConjectures.CategoryTheory.Brown.BrownHypothesesFiniteCdIntegralExt
import all WeilConjectures.AlgebraicGeometry.SixFunctors.QcqsIntegralFiniteModelCompleteness
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence

/-!
# `Ext` out of the extension by zero of a locally free integral module

Let `i : Z ⟶ X` be a closed immersion of noetherian schemes with open complement `j : V ⟶ X`,
with `ℓ` invertible on `X`, and `v : S ⟶ Z` an open immersion. Let `L` be a locally free module
over the continuous integral coefficient ring `𝒪_{E,S}`. For every constructible `𝒪_{E,X}`-module
`N`,

`Hom(i_* v_! L, N[r]) = 0` for `r > cd_ℓ(j) + cd_ℓ(S) + 2`

(`CategoryTheory.subsingleton_hom_lowerStar_openImmersionLowerShriek_shift_of_isLocallyFree`).

## Implementation details

For the reductions of `N` modulo powers of the uniformizer the bound is `cd_ℓ(j) + cd_ℓ(S) + 1`
(`CategoryTheory.integralStratumFiniteCdReductions_of_isLocallyFree`): the supported sections of
a reduction live in degrees `[-1, cd_ℓ(j) + 1]`, and tensoring with the dual of `L` does not
raise this bound since `L` is locally free
(`CategoryTheory.subsingleton_hom_singleFunctor_shift_of_isLocallyFree`). Since `N` is derived
complete, it is the derived limit of its reductions, and the Milnor triangle costs one degree.
This follows `CategoryTheory.brownHypotheses_integral_uniformExtBound_of_finite_cd`, which allows
torsion in the source and reaches only `cd_ℓ(j) + cd_ℓ(S) + 3`.
-/

@[expose] public section

set_option autoImplicit false

attribute [-instance] WeilConjectures.strictDvrSiteSmall
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

section

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory

/-- Let `i : Z ⟶ X` be a closed immersion with open complement `j : V ⟶ X` of noetherian schemes,
with `ℓ` invertible on `X`, let `v : S ⟶ Z` be an open immersion and `L` a locally free
`𝒪_{E,S}`-module. For every constructible `𝒪_{E,X}`-module `N`
and every reduction `N_n` of `N`, `Hom(i_* v_! L, N_n[r]) = 0` for
`r > cd_ℓ(j) + cd_ℓ(S) + 1`. -/
theorem integralStratumFiniteCdReductions_of_isLocallyFree
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X Z S V : Scheme.{u}) [IsNoetherian X] [IsNoetherian S]
    (hl : IsUnit (l : Γ(X, ⊤)))
    (i : Z ⟶ X) (v : S ⟶ Z) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion v] [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range j.base = (Set.range i.base)ᶜ)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S))
    (hL : IsLocallyFree (condensedRingObj (IntegralQuotient.integral l E) S) L)
    (c s : ℕ) (hc : relativeCohomologicalDimension l (Fact.out : l.Prime) j ≤ c)
    (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) X))
    (hN : IsConstantModelConstructible (IntegralQuotient.integral l E) X N)
    (n : ℕ) (r : ℤ) (hr : (c : ℤ) + s + 1 < r)
    (f : (DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar (IntegralQuotient.integral l E) i).obj
          ((CondensedRing.openImmersionLowerShriek (IntegralQuotient.integral l E) v).obj L)) ⟶
      ((IntegralQuotient.restrict l E X n).obj
        ((IntegralQuotient.scalar l E X n).obj
          ((DerivedCategory.singleFunctor _ 0).obj N)))⟦r⟧) :
    f = 0 := by
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    rw [hcomp, compl_compl]
  have hK := integralStratumFiniteCdReductions_support_window l E X Z S V hl i v j
    hcomp c hc N hN n
  apply stratum_hom_zero (IntegralQuotient.integral l E) i v j hij L _ r _ f
  exact subsingleton_hom_singleFunctor_shift_of_isLocallyFree l E S L hL s hs _ (-1)
    ((c : ℤ) + 1) (by omega) hK.1 hK.2 r (by omega)

end

section

attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
attribute [local instance 40000] nativeCondensedMonoidal

/-- The reduction bound of `integralStratumFiniteCdReductions_of_isLocallyFree`, for an arbitrary
morphism of coefficient rings. -/
private def locallyFreeReductionBound
    (X Z S : Scheme.{u}) (i : Z ⟶ X) (v : S ⟶ Z) [IsOpenImmersion v]
    (r : ℤ)
    (a : Arrow (CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))) : Prop :=
  match a with
  | ⟨@CommMon.mk _ _ _ _ Λ mΛ cΛ, @CommMon.mk _ _ _ _ Γ mΓ cΓ,
      ⟨@Mon.Hom.mk _ _ _ _ _ φ hφ⟩⟩ =>
    letI := mΛ
    letI := mΓ
    letI := cΛ
    letI := cΓ
    let φ' : Λ ⟶ Γ := φ
    letI : IsMonHom φ' := hφ
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
    letI : IsCommMonObj (condensedRingObj Λ X) :=
      Functor.isCommMonObj_obj (F := upperStarFromPoint X)
    letI : IsCommMonObj (condensedRingObj Γ X) :=
      Functor.isCommMonObj_obj (F := upperStarFromPoint X)
    ∀ (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj Λ S)), IsLocallyFree (condensedRingObj Λ S) L →
    ∀ (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)), IsConstantModelConstructible Λ X N →
    ∀ f : (DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar Λ i).obj
          ((CondensedRing.openImmersionLowerShriek Λ v).obj L)) ⟶
        ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap (Λ := Λ) (Λ' := Γ) φ' X)).mapDerivedCategory.obj
          ((Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (coefficientMap (Λ := Λ) (Λ' := Γ) φ' X)).leftDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj N)))⟦r⟧, f = 0

private theorem locallyFree_finite_reduction_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X Z S V : Scheme.{u}) [IsNoetherian X] [IsNoetherian S]
    (hl : IsUnit (l : Γ(X, ⊤)))
    (i : Z ⟶ X) (v : S ⟶ Z) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion v] [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range j.base = (Set.range i.base)ᶜ)
    (c s : ℕ)
    (hc : relativeCohomologicalDimension l (Fact.out : l.Prime) j ≤ c)
    (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (n : ℕ) (r : ℤ) (hr : (c : ℤ) + (s : ℤ) + 1 < r) :
    locallyFreeReductionBound X Z S i v r
      (coefficientArrow (DerivedNakayama.reductionRing l E (n + 1))) := by
  have hb : locallyFreeReductionBound X Z S i v r
      (coefficientArrow (IntegralQuotient.reduction l E n)) := by
    intro L hL N hN f
    exact integralStratumFiniteCdReductions_of_isLocallyFree l E X Z S V hl i v j hcomp
      L hL c s hc hs N hN n r hr f
  exact (congrArg (locallyFreeReductionBound X Z S i v r) (reductionArrow_eq l E n)).mp hb

attribute [local instance 40000] AdicCompletion.ringMonoidalObject
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.modulesDerived
  AdicCompletion.finiteModulesDerived AdicCompletion.modulesMonoidal

private theorem locallyFree_completion_reduction_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X Z S V : Scheme.{u}) [IsNoetherian X] [IsNoetherian S]
    (hl : IsUnit (l : Γ(X, ⊤)))
    (i : Z ⟶ X) (v : S ⟶ Z) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion v] [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range j.base = (Set.range i.base)ᶜ)
    (c s : ℕ)
    (hc : relativeCohomologicalDimension l (Fact.out : l.Prime) j ≤ c)
    (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (n : ℕ) (r : ℤ) (hr : (c : ℤ) + (s : ℤ) + 1 < r) :
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
    ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (DerivedNakayama.integerRing l E) S),
      IsLocallyFree (condensedRingObj (DerivedNakayama.integerRing l E) S) L →
    ∀ N : AdicCompletion.Modules l E X,
      IsConstantModelConstructible (DerivedNakayama.integerRing l E) X N →
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar (DerivedNakayama.integerRing l E) i).obj
          ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E) v).obj L)) ⟶
        (AdicCompletion.integralLevel l E X
          ((DerivedCategory.singleFunctor _ 0).obj N) n)⟦r⟧) := by
  intro L hL N hN
  have hf := locallyFree_finite_reduction_bound l E X Z S V hl i v j hcomp c s hc hs n r hr
  exact subsingleton_of_all_eq _ (hf L hL N hN)

/-- The statement of
`subsingleton_hom_lowerStar_openImmersionLowerShriek_shift_of_isLocallyFree`, elaborated with the
local completion instances of this section; the public statement uses the global instances. -/
private theorem subsingleton_hom_lowerStar_openImmersionLowerShriek_shift_of_isLocallyFree_aux
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X Z S V : Scheme.{u}) [IsNoetherian X] [IsNoetherian S]
    (hl : IsUnit (l : Γ(X, ⊤)))
    (i : Z ⟶ X) (v : S ⟶ Z) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion v] [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range j.base = (Set.range i.base)ᶜ)
    (c s : ℕ)
    (hc : relativeCohomologicalDimension l (Fact.out : l.Prime) j ≤ c)
    (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.integerRing l E) S))
    (hL : IsLocallyFree (condensedRingObj (DerivedNakayama.integerRing l E) S) L)
    (N : AdicCompletion.Modules l E X)
    (hN : IsConstantModelConstructible (DerivedNakayama.integerRing l E) X N)
    (r : ℤ) (hr : (c : ℤ) + (s : ℤ) + 2 < r) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar (DerivedNakayama.integerRing l E) i).obj
          ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E) v).obj L)) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj N)⟦r⟧) := by
  have : CompactSpace X := inferInstance
  have : QuasiSeparatedSpace X := inferInstance
  obtain ⟨B, hB, ⟨eB⟩, hη⟩ := complete_sheaf l E X N hN
  let := AdicCompletion.modules_countableAB4Star l E X
  let := derivedCategory_hasCountableProducts (AdicCompletion.Modules l E X)
  obtain ⟨p, δ, htri, _⟩ := AdicCompletion.roos_isDerivedLimit l E X
    ((DerivedCategory.singleFunctor _ 0).obj N) B hB eB
  have : IsIso (AdicCompletion.completionMap l E X
      ((DerivedCategory.singleFunctor _ 0).obj N) B eB) := by
    dsimp only [AdicCompletion.completionMap]
    infer_instance
  let e := asIso (AdicCompletion.completionMap l E X
    ((DerivedCategory.singleFunctor _ 0).obj N) B eB)
  apply hom_roos_iso_zero _ ((DerivedCategory.singleFunctor _ 0).obj N)
    (DerivedCategory.Q.obj (AdicCompletion.roos l E X B))
    (AdicCompletion.integralLevel l E X ((DerivedCategory.singleFunctor _ 0).obj N))
    (AdicCompletion.integralStep l E X ((DerivedCategory.singleFunctor _ 0).obj N)) p δ htri e r
  · intro n
    exact locallyFree_completion_reduction_bound l E X Z S V hl i v j hcomp c s hc hs n (r - 1)
      (by omega) L hL N hN
  · intro n
    exact locallyFree_completion_reduction_bound l E X Z S V hl i v j hcomp c s hc hs n r
      (by omega) L hL N hN

end

/-- Let `i : Z ⟶ X` be a closed immersion with open complement `j : V ⟶ X` of noetherian schemes,
with `ℓ` invertible on `X`, let `v : S ⟶ Z` be an open immersion and `L` a locally free
`𝒪_{E,S}`-module. For every constructible `𝒪_{E,X}`-module `N`,
`Hom(i_* v_! L, N[r]) = 0` for `r > cd_ℓ(j) + cd_ℓ(S) + 2`. -/
theorem subsingleton_hom_lowerStar_openImmersionLowerShriek_shift_of_isLocallyFree
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X Z S V : Scheme.{u}) [IsNoetherian X] [IsNoetherian S]
    (hl : IsUnit (l : Γ(X, ⊤)))
    (i : Z ⟶ X) (v : S ⟶ Z) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion v] [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range j.base = (Set.range i.base)ᶜ)
    (c s : ℕ)
    (hc : relativeCohomologicalDimension l (Fact.out : l.Prime) j ≤ c)
    (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.integerRing l E) S))
    (hL : IsLocallyFree (condensedRingObj (DerivedNakayama.integerRing l E) S) L)
    (N : AdicCompletion.Modules l E X)
    (hN : IsConstantModelConstructible (DerivedNakayama.integerRing l E) X N)
    (r : ℤ) (hr : (c : ℤ) + (s : ℤ) + 2 < r) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar (DerivedNakayama.integerRing l E) i).obj
          ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E) v).obj L)) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj N)⟦r⟧) :=
  subsingleton_hom_lowerStar_openImmersionLowerShriek_shift_of_isLocallyFree_aux l E X Z S V hl i v
    j hcomp c s hc hs L hL N hN r hr

end CategoryTheory
